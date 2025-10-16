module Home where

-- project
import Config
import Util.Typst

-- shake
import Development.Shake
import Development.Shake.FilePath
import Development.Shake.Forward

-- slick
import Slick

-- text
import Data.Text qualified as T


type Tag = String

-- | Build home

buildHome :: Action ()
buildHome = cacheAction ("build" :: T.Text, "site/home.md" :: FilePath) $ do
  liftIO . putStrLn $ "Rebuilding home page from site/home.md, writing to " <> outputFolder </> "index.html"
  homeData <- typstAndMetaDataToHTML "site/home"
  template <- compileTemplate' "site/templates/home.html"
  writeFile' (outputFolder </> "index.html") . T.unpack $ substitute template (withSiteMeta homeData)
