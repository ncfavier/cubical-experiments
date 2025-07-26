import Agda.Compiler.Backend hiding (getEnv)
import Agda.Interaction.Imports
import Agda.Interaction.Library.Base
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
import Text.Pandoc
import Text.Pandoc.Filter
import Text.Pandoc.Walk

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
    , htmlFlagLibToURL = \ (LibName lib version) ->
      let v = intercalate "." (map show version) in
      Map.lookup lib $ Map.fromList
        [ ("agda-builtins", "https://agda.github.io/agda-stdlib/master")
        , ("standard-library", "https://agda.github.io/agda-stdlib/v" <> v)
        , ("cubical", "https://agda.github.io/cubical")
        , ("1lab", "https://1lab.dev")
        , ("cubical-experiments", "")
        ]
    }
  }

filenameToModule :: FilePath -> String
filenameToModule f = dropExtensions f

makeEverythingFile :: [FilePath] -> String
makeEverythingFile = unlines . map (\ m -> "import " <> filenameToModule m)

readFileText :: FilePath -> Action T.Text
readFileText = fmap T.pack . readFile'

importToModule :: String -> String
importToModule s = innerText tags
  where tags = parseTags s

patchBlock :: Block -> Block
-- Add anchor links next to headers
patchBlock (Header i a@(ident, _, _) inl) | ident /= "" = Header i a $
  inl ++ [Link ("", ["anchor"], [("aria-hidden", "true")]) [] ("#" <> ident, "")]
patchBlock b = b

main :: IO ()
main = shakeArgs shakeOptions do
  -- I realise this is not how a Shakefile should be structured, but I got
  -- bored trying to figure it out and this is good enough for now.
  -- I should probably look into Development.Shake.Forward ...
  compileModule <- addOracle \ (CompileDirectory (sourceDir, everything)) -> do
    librariesFile <- getEnv "AGDA_LIBRARIES_FILE"
    sourceFiles <- filter (not . ("Everything*" ?==)) <$>
      getDirectoryFiles sourceDir ["//*.agda", "//*.lagda.md"]
    writeFile' everything (makeEverythingFile sourceFiles)
    traced "agda" do
      root <- absolute sourceDir
      runTCMTopPrettyErrors do
        setCommandLineOptions' root defaultOptions
          { optOverrideLibrariesFile = librariesFile
          , optDefaultLibs = False
          }
        stBackends `setTCLens` [myHtmlBackend]
        sourceFile <- srcFromPath =<< liftIO (absolute everything)
        source <- parseSource sourceFile
        checkResult <- typeCheckMain TypeCheck source
        callBackend "HTML" IsMain checkResult
    moduleTemplate <- readFileText "module.html"
    for_ sourceFiles \ sourceFile -> do
      let
        htmlFile = dropExtensions sourceFile <.> "html"
        literateFile = dropExtensions sourceFile <.> takeExtension sourceFile -- .lagda.md → .md
      contents <- case takeExtensions sourceFile of
        ".lagda.md" -> do
          markdown <- readFileText (htmlDir </> literateFile)
          traced "pandoc" $ runIOorExplode do
            pandoc <- readMarkdown def {
              readerExtensions = foldr enableExtension pandocExtensions [Ext_autolink_bare_uris]
            } markdown
            pandoc <- pure $ walk patchBlock pandoc
            pandoc <- applyJSONFilter def [] "pandoc-katex" pandoc
            writeHtml5String def pandoc
        ".agda" -> do
          html <- readFileText (htmlDir </> htmlFile)
          pure $ "<pre class=\"Agda\">" <> html <> "</pre>"
        _ -> fail ("unknown extension for file " <> sourceFile)
      writeFile' (siteDir </> htmlFile)
        $ T.unpack
        $ T.replace "@contents@" contents
        $ T.replace "@moduleName@" (T.pack $ filenameToModule sourceFile)
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
      $ T.replace "@contents@" (T.pack $ unlines $ sortOn importToModule $ everythingAgda)
      $ indexTemplate
    copyFile' "style.css" (siteDir </> "style.css")
    copyFile' "main.js" (siteDir </> "main.js")
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
