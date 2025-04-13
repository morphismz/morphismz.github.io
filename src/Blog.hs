module Blog where

-- | Control

import Control.Lens

-- | Data

import Data.Aeson
import Data.Aeson.Lens

import Data.List

import Data.Ord

import Data.Text qualified as T

-- | Generics

import GHC.Generics

-- | Project

import Config
import Index

-- | Shake

import Development.Shake
import Development.Shake.Classes
import Development.Shake.FilePath
import Development.Shake.Forward

-- | Slick

import Slick

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
  postContent <- readFile' srcPath
  postData <- markdownToHTML . T.pack $ postContent
  let postUrl = T.pack . dropDirectory1 $ srcPath -<.> "html"
      withPostUrl = _Object . at "url" ?~ String postUrl
      fullPostData = withSiteMeta . withPostUrl $ postData
  template <- compileTemplate' "site/templates/post.html"
  writeFile' (outputFolder </> T.unpack postUrl) . T.unpack $ substitute template fullPostData
  convert fullPostData

buildPosts :: Action [Post]
buildPosts = do
  pPaths <- getDirectoryFiles "." ["site/posts//*.md"]
  sortOn (Down . date) <$> forP pPaths buildPost

type PostIndexInfo = IndexInfo Post

buildPostIndex :: PostIndexInfo -> Action ()
buildPostIndex = buildIndex
