module Atom where


-- | Project

import Blog
import Config

-- | Data

import Data.Aeson

import Data.Text qualified as T

import Data.Time

-- | Generics

import GHC.Generics

-- | Shake

import Development.Shake
import Development.Shake.FilePath

-- | Slick

import Slick

data AtomData =
  AtomData
    { title        :: String
    , domain       :: String
    , author       :: String
    , posts        :: [Post]
    , currentTime  :: String
    , atomUrl      :: String
    } deriving (Generic, ToJSON, Eq, Ord, Show)

buildFeed :: [Post] -> Action ()
buildFeed posts' = do
  now <- liftIO getCurrentTime
  let atomData =
        AtomData
          { title = siteTitle siteMeta
          , domain = baseUrl siteMeta
          , author = siteAuthor siteMeta
          , posts = mkAtomPost <$> posts'
          , currentTime = toIsoDate now
          , atomUrl = "/atom.xml"
          }
  atomTempl <- compileTemplate' "site/templates/atom.xml"
  writeFile' (outputFolder </> "atom.xml") . T.unpack $ substitute atomTempl (toJSON atomData)
  where
    mkAtomPost :: Post -> Post
    mkAtomPost p = p { date = formatDate $ date p}
