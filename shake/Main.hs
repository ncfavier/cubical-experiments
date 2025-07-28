import Agda.Compiler.Backend hiding (getEnv)
import Agda.Interaction.Imports
import Agda.Interaction.Library.Base
import Agda.Interaction.Options (CommandLineOptions(..), defaultOptions)
import Agda.TypeChecking.Errors
import Agda.Utils.FileName
import Agda.Utils.Monad

import Control.Monad.Error.Class

import Data.ByteString.Lazy qualified as LBS
import Data.Digest.Pure.SHA
import Data.Foldable
import Data.List
import Data.Map qualified as Map
import Data.Maybe
import Data.Text qualified as T
import Data.Text.Encoding qualified as T

import Development.Shake
import Development.Shake.Classes
import Development.Shake.FilePath

import HTML.Backend
import HTML.Base

import System.Console.GetOpt
import System.Directory

import Text.HTML.TagSoup
import Text.Pandoc
import Text.Pandoc.Filter
import Text.Pandoc.Walk

newtype RenderDiagram = RenderDiagram T.Text
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
type instance RuleResult RenderDiagram = FilePath

newtype CompileDirectory = CompileDirectory (FilePath, FilePath)
  deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
type instance RuleResult CompileDirectory = ()

sourceDir, source1labDir, buildDir, htmlDir, siteDir, diagramsDir, everything, everything1lab :: FilePath
sourceDir = "src"
source1labDir = "src-1lab"
buildDir = "_build"
htmlDir = buildDir </> "html"
siteDir = buildDir </> "site"
diagramsDir = buildDir </> "diagrams"
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

-- | Takes a base source directory and a source filename and returns the
-- corresponding Markdown source and the path to the output file generated
-- by Agda.
getSourceFile :: FilePath -> FilePath -> Action (T.Text, SourceType)
getSourceFile sourceDir sourceFile = do
  source <- readFileText (sourceDir </> sourceFile)
  case takeExtensions sourceFile of
    ".agda" -> pure (T.unlines ["```agda", source, "```"], HTML $ htmlDir </> sourceFile -<.> "html")
    ".lagda.md" -> pure (source, Markdown $ htmlDir </> dropExtensions sourceFile <.> "md")
    _ -> fail ("unsupported extension for file " <> sourceFile)

-- | Compute the scaled height of a diagram (given in SVG), to use as a @style@ tag.
diagramHeight :: FilePath -> Action Double
diagramHeight fp = do
  contents <- readFile' fp
  let
    height (TagOpen "svg" attrs:_) | Just h <- lookup "height" attrs =
      fromMaybe h (T.unpack <$> T.stripSuffix "pt" (T.pack h))
    height (_:t) = height t
    height [] = error $ "Diagram SVG has no height: " <> fp
    it :: Double
    it = read (height (parseTags contents)) * 1.9 -- 🔮
  pure $! it

main :: IO ()
main = shakeArgsWith shakeOpts optDescrs \ flags _ -> pure $ Just do
  let skipAgda = SkipAgda `elem` flags

  renderDiagram <- (. RenderDiagram) <$> addOracle \ (RenderDiagram contents) -> do
    let
      digest = take 12 . showDigest . sha1 . LBS.fromStrict $ T.encodeUtf8 contents
      diagramName = digest <.> "light.svg"
      output = siteDir </> diagramName
      texPath = diagramsDir </> digest <.> "tex"
    template <- readFileText "diagram.tex"
    writeFile' texPath
      $ T.unpack
      $ T.replace "__BODY__" contents
      $ template
    Stdout (_ :: LBS.ByteString) <- command [] "pdflatex"
      ["-output-directory", diagramsDir, "-synctex=1", "-interaction=nonstopmode", texPath]
    liftIO $ createDirectoryIfMissing True siteDir
    command_ [] "pdftocairo" ["-svg", texPath -<.> "pdf", output]
    pure diagramName

  let
    patchBlock :: Block -> Action Block
    -- Add anchor links next to headers
    patchBlock (Header i a@(ident, _, _) inl) | ident /= "" = pure $ Header i a $
      inl ++ [Link ("", ["anchor"], [("aria-hidden", "true")]) [] ("#" <> ident, "")]
    -- Render commutative diagrams
    patchBlock (CodeBlock (id, classes, attrs) contents) | "quiver" `elem` classes = do
      let
        title = fromMaybe "commutative diagram" (lookup "title" attrs)
      diagramName <- renderDiagram contents

      height <- diagramHeight (siteDir </> diagramName)
      let attrs' = ("style", "height: " <> T.pack (show height) <> "px;"):attrs

      pure $ Div ("", ["diagram-container"], [])
        [ Plain [ Image (id, "diagram":classes, attrs') [] (T.pack diagramName, title) ]
        ]
    patchBlock b = pure b

  -- Render a single type-checked module to HTML.
  let
    renderModule (sourceDir, sourceFile) = do
      let
        renderMarkdown markdown = do
          pandoc <- traced ("pandoc read: " <> sourceFile) $ runIOorExplode do
            readMarkdown def {
              readerExtensions = foldr enableExtension pandocExtensions [Ext_autolink_bare_uris]
            } markdown
          pandoc <- walkM patchBlock pandoc
          pandoc <- applyJSONFilter def [] "pandoc-katex" pandoc
          traced ("pandoc write: " <> sourceFile) $ runIOorExplode do
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
