module Posts where

-- aeson
import Data.Aeson
import Data.Aeson.Lens

-- base
import Data.List
import Data.Ord

-- generics
import GHC.Generics

-- lens
import Control.Lens

-- project
import Config
import Index
import Util.Typst

-- shake
import Development.Shake
import Development.Shake.Classes
import Development.Shake.FilePath
import Development.Shake.Forward

-- slick
import Slick

-- text
import Data.Text qualified as T

type Tag = String

data Post =
  Post
    { title       :: String
    , author      :: String
    , content     :: String
    , url         :: String
    , date        :: String
    , tags        :: [Tag]
    , description :: String
    , image       :: Maybe String
    } deriving (Generic, Eq, Ord, Show, FromJSON, ToJSON, Binary)

buildPost :: FilePath -> Action Post
buildPost srcPath = cacheAction ("build" :: T.Text, srcPath) $ do
  liftIO . putStrLn $ "Rebuilding post: " <> srcPath
  postData <- typstAndMetaDataToHTML srcPath
  let postUrl = T.pack . dropDirectory1 $ srcPath -<.> "html"
      withPostUrl = _Object . at "url" ?~ String postUrl
      fullPostData = withSiteMeta . withPostUrl $ postData
  template <- compileTemplate' "site/templates/post.html"
  writeFile' (outputFolder </> T.unpack postUrl) . T.unpack $ substitute template fullPostData
  convert fullPostData

buildPosts :: Action [Post]
buildPosts = do
  pPaths <- getDirectoryFiles "." ["site/posts//*.yaml"]
  sortOn (Down . date) <$> forP pPaths (buildPost . dropExtension)

type PostIndexInfo = IndexInfo Post

buildPostIndex :: PostIndexInfo -> Action ()
buildPostIndex = buildIndex
