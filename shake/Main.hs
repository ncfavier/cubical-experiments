import Agda.Compiler.Backend hiding (getEnv)
import Agda.Interaction.FindFile
import Agda.Interaction.Imports
import Agda.Interaction.Options
import Agda.TypeChecking.Errors
import Agda.Utils.FileName
import Agda.Utils.Monad

import Control.Monad.Error.Class

import Data.Foldable
import Data.Text qualified as T

import Development.Shake
import Development.Shake.Classes
import Development.Shake.FilePath

import HTML.Backend
import HTML.Base

import Text.Regex.TDFA

newtype ModuleCompileQ = ModuleCompileQ FilePath
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

type instance RuleResult ModuleCompileQ = ()

sourceDir, buildDir, htmlDir, siteDir, everythingLoadPrimitives, everythingNoLoadPrimitives :: FilePath
sourceDir = "src"
buildDir = "_build"
htmlDir = buildDir </> "html"
siteDir = buildDir </> "site"
everythingLoadPrimitives = buildDir </> "EverythingLoadPrimitives.agda"
everythingNoLoadPrimitives = buildDir </> "EverythingNoLoadPrimitives.agda"

myHtmlBackend :: Backend
myHtmlBackend = Backend htmlBackend'
  { options = initialHtmlFlags
    { htmlFlagDir = htmlDir
    , htmlFlagHighlightOccurrences = True
    , htmlFlagCssFile = Just "style.css"
    , htmlFlagHighlight = HighlightCode
    }
  }

-- | Should this file be compiled with --load-primitives?
-- Modules that depend on 1lab require --no-load-primitives while
-- modules that depend on cubical require --load-primitives, and those
-- flags conflict so we have to split them into separate Everything files...
loadPrimitives :: FilePath -> Action Bool
loadPrimitives f = do
  contents <- readFile' (sourceDir </> f)
  pure $ not $ contents =~ ("import *(1Lab|Cat)\\." :: String)

filenameToModule :: FilePath -> String
filenameToModule f = dropExtension f

makeEverythingFile :: [FilePath] -> String
makeEverythingFile = unlines . map (\ m -> "import " <> filenameToModule m)

readFileText :: FilePath -> Action T.Text
readFileText = fmap T.pack . readFile'

main :: IO ()
main = shakeArgs shakeOptions do
  compileModule <- addOracle \ (ModuleCompileQ f) -> do
    librariesFile <- getEnv "AGDA_LIBRARIES_FILE"
    traced "agda" do
      sourceFile <- SourceFile <$> absolute f
      runTCMTopPrettyErrors do
        setCommandLineOptions defaultOptions
          { optOverrideLibrariesFile = librariesFile
          , optDefaultLibs = False
          }
        stBackends `setTCLens` [myHtmlBackend]
        source <- parseSource sourceFile
        checkResult <- typeCheckMain TypeCheck source
        callBackend "HTML" IsMain checkResult

  -- I realise this is not how a Shakefile should be structured, but I got
  -- bored trying to figure it out and this is enough for my needs.
  -- I should probably look into Development.Shake.Forward ...
  siteDir </> "index.html" %> \ index -> do
    agdaFiles <- getDirectoryFiles sourceDir ["//*.agda"]
    (no, yes) <- partitionM loadPrimitives agdaFiles
    writeFile' everythingLoadPrimitives (makeEverythingFile yes)
    writeFile' everythingNoLoadPrimitives (makeEverythingFile no)
    compileModule (ModuleCompileQ everythingLoadPrimitives)
    compileModule (ModuleCompileQ everythingNoLoadPrimitives)
    moduleTemplate <- readFileText "module.html"
    for_ agdaFiles \ agdaFile -> do
      -- Poor man's template engine
      agda <- readFileText (htmlDir </> agdaFile -<.> "html")
      writeFile' (siteDir </> agdaFile -<.> "html")
        $ T.unpack
        $ T.replace "@agda@" agda
        $ T.replace "@moduleName@" (T.pack $ dropExtension agdaFile)
        $ T.replace "@filename@" (T.pack agdaFile)
        $ moduleTemplate
    indexTemplate <- readFileText "index.html"
    everything <- (<>) <$> readFileText (htmlDir </> "EverythingLoadPrimitives.html")
                       <*> readFileText (htmlDir </> "EverythingNoLoadPrimitives.html")
    writeFile' index
      $ T.unpack
      $ T.replace "@agda@" everything
      $ indexTemplate
    copyFile' "style.css" (siteDir </> "style.css")
    copyFile' (htmlDir </> "highlight-hover.js") (siteDir </> "highlight-hover.js")

  phony "all" do
    need [siteDir </> "index.html"]

  want ["all"]

runTCMTopPrettyErrors :: TCM a -> IO a
runTCMTopPrettyErrors tcm = do
  r <- runTCMTop' $ (Just <$> tcm) `catchError` \err -> do
    warnings <- fmap (map show) . prettyTCWarnings' =<< getAllWarningsOfTCErr err
    errors  <- show <$> prettyError err
    let everything = filter (not . null) $ warnings ++ [errors]
    unless (null errors) . liftIO . putStr $ unlines everything
    pure Nothing

  maybe (fail "Agda compilation failed") pure r
