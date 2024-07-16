import Agda.Compiler.Backend hiding (getEnv)
import Agda.Interaction.FindFile
import Agda.Interaction.Imports
import Agda.Interaction.Options
import Agda.TypeChecking.Errors
import Agda.Utils.FileName
import Agda.Utils.Monad

import Control.Monad.Error.Class

import Data.Foldable
import Data.List
import Data.Map qualified as Map
import Data.Text qualified as T

import Development.Shake
import Development.Shake.Classes
import Development.Shake.FilePath

import HTML.Backend
import HTML.Base

import Text.HTML.TagSoup

newtype CompileDirectory = CompileDirectory (FilePath, FilePath)
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
type instance RuleResult CompileDirectory = ()

sourceDir, source1labDir, buildDir, htmlDir, siteDir, everything, everything1lab :: FilePath
sourceDir = "src"
source1labDir = "src-1lab"
buildDir = "_build"
htmlDir = buildDir </> "html"
siteDir = buildDir </> "site"
everything = sourceDir </> "Everything.agda"
everything1lab = source1labDir </> "Everything-1lab.agda"

myHtmlBackend :: Backend
myHtmlBackend = Backend htmlBackend'
  { options = initialHtmlFlags
    { htmlFlagDir = htmlDir
    , htmlFlagHighlightOccurrences = True
    , htmlFlagCssFile = Just "style.css"
    , htmlFlagHighlight = HighlightCode
    , htmlFlagLibToURL = Map.fromList
      [ ("agda-builtins", Just "https://agda.github.io/cubical")
      , ("standard-library-2.1", Just "https://agda.github.io/agda-stdlib/experimental")
      , ("cubical-0.7", Just "https://agda.github.io/cubical")
      , ("1lab", Just "https://1lab.dev")
      , ("cubical-experiments", Nothing)
      ]
    }
  }

filenameToModule :: FilePath -> String
filenameToModule f = dropExtension f

makeEverythingFile :: [FilePath] -> String
makeEverythingFile = unlines . map (\ m -> "import " <> filenameToModule m)

readFileText :: FilePath -> Action T.Text
readFileText = fmap T.pack . readFile'

importToModule :: String -> String
importToModule s = innerText tags
  where tags = parseTags s

main :: IO ()
main = shakeArgs shakeOptions do
  -- I realise this is not how a Shakefile should be structured, but I got
  -- bored trying to figure it out and this is good enough for now.
  -- I should probably look into Development.Shake.Forward ...
  compileModule <- addOracle \ (CompileDirectory (sourceDir, everything)) -> do
    librariesFile <- getEnv "AGDA_LIBRARIES_FILE"
    sourceFiles <- filter (not . ("Everything*" ?==)) <$>
      getDirectoryFiles sourceDir ["//*.agda"]
    writeFile' everything (makeEverythingFile sourceFiles)
    traced "agda" do
      root <- absolute sourceDir
      sourceFile <- SourceFile <$> absolute everything
      runTCMTopPrettyErrors do
        setCommandLineOptions' root defaultOptions
          { optOverrideLibrariesFile = librariesFile
          , optDefaultLibs = False
          }
        stBackends `setTCLens` [myHtmlBackend]
        source <- parseSource sourceFile
        checkResult <- typeCheckMain TypeCheck source
        callBackend "HTML" IsMain checkResult
    moduleTemplate <- readFileText "module.html"
    for_ sourceFiles \ sourceFile -> do
      -- Poor man's template engine
      agda <- readFileText (htmlDir </> sourceFile -<.> "html")
      writeFile' (siteDir </> sourceFile -<.> "html")
        $ T.unpack
        $ T.replace "@agda@" agda
        $ T.replace "@moduleName@" (T.pack $ dropExtension sourceFile)
        $ T.replace "@path@" (T.pack $ sourceDir </> sourceFile)
        $ moduleTemplate

  siteDir </> "index.html" %> \ index -> do
    compileModule (CompileDirectory (sourceDir, everything))
    compileModule (CompileDirectory (source1labDir, everything1lab))
    indexTemplate <- readFileText "index.html"
    everythingAgda <- (<>)
      <$> readFileLines (htmlDir </> "Everything.html")
      <*> readFileLines (htmlDir </> "Everything-1lab.html")
    writeFile' index
      $ T.unpack
      $ T.replace "@agda@" (T.pack $ unlines $ sortOn importToModule $ everythingAgda)
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
