import Agda.Compiler.Backend hiding (getEnv)
import Agda.Interaction.Imports
import Agda.Interaction.Library.Base
import Agda.Interaction.Options (CommandLineOptions(..), defaultOptions)
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

import System.Console.GetOpt

import Text.HTML.TagSoup
import Text.Pandoc
import Text.Pandoc.Filter
import Text.Pandoc.Walk

newtype CompileDirectory = CompileDirectory (FilePath, FilePath)
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
type instance RuleResult CompileDirectory = ()

newtype RenderModule = RenderModule (FilePath, FilePath)
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
type instance RuleResult RenderModule = T.Text

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

shakeOpts :: ShakeOptions
shakeOpts = shakeOptions {
  shakeColor = True
}

data Flags = SkipAgda deriving Eq

optDescrs :: [OptDescr (Either String Flags)]
optDescrs =
  [ Option [] ["skip-agda"] (NoArg (Right SkipAgda)) "Skip typechecking Agda."
  ]

data SourceType = HTML FilePath | Markdown FilePath

-- Takes a base source directory and a source filename and returns the
-- corresponding Markdown source and the path to the output file generated
-- by Agda.
getSourceFile :: FilePath -> FilePath -> Action (T.Text, SourceType)
getSourceFile sourceDir sourceFile = do
  source <- readFileText (sourceDir </> sourceFile)
  case takeExtensions sourceFile of
    ".agda" -> pure (T.unlines ["```agda", source, "```"], HTML $ htmlDir </> dropExtensions sourceFile <.> "html")
    ".lagda.md" -> pure (source, Markdown $ htmlDir </> dropExtensions sourceFile <.> takeExtension sourceFile)
    _ -> fail ("unsupported extension for file " <> sourceFile)

main :: IO ()
main = shakeArgsWith shakeOpts optDescrs \ flags _ -> pure $ Just do
  let skipAgda = SkipAgda `elem` flags

  -- Render a single type-checked module to HTML.
  renderModule <- (. RenderModule) <$> addOracle \ (RenderModule (sourceDir, sourceFile)) -> do
    let
      renderMarkdown markdown = do
        traced ("pandoc: " <> sourceFile) $ runIOorExplode do
          pandoc <- readMarkdown def {
            readerExtensions = foldr enableExtension pandocExtensions [Ext_autolink_bare_uris]
          } markdown
          pandoc <- pure $ walk patchBlock pandoc
          pandoc <- applyJSONFilter def [] "pandoc-katex" pandoc
          writeHtml5String def pandoc
    (markdown, agdaOutputFile) <- getSourceFile sourceDir sourceFile
    if skipAgda then renderMarkdown markdown
    else do
      case agdaOutputFile of
        HTML file -> do
          html <- readFileText file
          pure $ "<pre class=\"Agda\">" <> html <> "</pre>"
        Markdown file -> do
          markdown <- readFileText file
          renderMarkdown markdown

  -- Invoke Agda on a source directory and render all the modules in it.
  compileDirectory <- (. CompileDirectory) <$> addOracle \ (CompileDirectory (sourceDir, everything)) -> do
    librariesFile <- getEnv "AGDA_LIBRARIES_FILE"
    sourceFiles <- filter (not . ("Everything*" ?==)) <$>
      getDirectoryFiles sourceDir ["//*.agda", "//*.lagda.md"]
    -- Write Everything.agda
    writeFile' everything (makeEverythingFile sourceFiles)
    -- Run Agda on Everything.agda
    unless skipAgda $ traced "agda" do
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
    -- Render modules as needed and insert the results into the module template.
    moduleTemplate <- readFileText "module.html"
    for_ sourceFiles \ sourceFile -> do
      let htmlFile = dropExtensions sourceFile <.> "html"
      html <- renderModule (sourceDir, sourceFile)
      writeFile' (siteDir </> htmlFile)
        $ T.unpack
        $ T.replace "@contents@" html
        $ T.replace "@moduleName@" (T.pack $ filenameToModule sourceFile)
        $ T.replace "@path@" (T.pack $ sourceDir </> sourceFile)
        $ moduleTemplate

  -- Compile all modules.
  "modules" ~> do
    compileDirectory (sourceDir, everything)
    compileDirectory (source1labDir, everything1lab)

  -- Generate the index.
  siteDir </> "index.html" %> \ index -> do
    need ["modules"]
    indexTemplate <- readFileText "index.html"
    everythingAgda <-
      if skipAgda then pure []
      else (<>)
        <$> readFileLines (htmlDir </> "Everything.html")
        <*> readFileLines (htmlDir </> "Everything-1lab.html")
    writeFile' index
      $ T.unpack
      $ T.replace "@contents@" (T.pack $ unlines $ sortOn importToModule $ everythingAgda)
      $ indexTemplate
    unless skipAgda do
      copyFile' (htmlDir </> "highlight-hover.js") (siteDir </> "highlight-hover.js")

  siteDir </> "style.css" %> \ out -> do
    copyFileChanged "style.css" out

  siteDir </> "main.js" %> \ out -> do
    copyFileChanged "main.js" out

  "all" ~> do
    need
      [ siteDir </> "index.html"
      , siteDir </> "style.css"
      , siteDir </> "main.js"
      ]

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
