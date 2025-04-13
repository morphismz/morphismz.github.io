module Talks where

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

data Talk =
  Talk
    { title       :: String
    , author      :: String
    , content     :: String
    , talkType    :: String
    , url         :: String
    , date        :: String
    , tags        :: [Tag]
    , description :: String
    , image       :: Maybe String
    , video       :: Maybe String
    } deriving (Generic, Eq, Ord, Show, FromJSON, ToJSON, Binary)

buildTalk :: FilePath -> Action Talk
buildTalk srcPath = cacheAction ("build" :: T.Text, srcPath) $ do
  liftIO . putStrLn $ "Rebuilding talk: " <> srcPath
  talkContent <- readFile' srcPath
  talkData <- markdownToHTML . T.pack $ talkContent
  let talkUrl = T.pack . dropDirectory1 $ srcPath -<.> "html"
      withTalkUrl = _Object . at "url" ?~ String talkUrl
      fullTalkData = withSiteMeta . withTalkUrl $ talkData
  template <- compileTemplate' "site/templates/talk.html"
  writeFile' (outputFolder </> T.unpack talkUrl) . T.unpack $ substitute template fullTalkData
  convert fullTalkData

buildTalks :: Action [Talk]
buildTalks = do
  pPaths <- getDirectoryFiles "." ["site/talks//*.md"]
  sortOn (Down . date) <$> forP pPaths buildTalk

buildTalkIndex :: IndexInfo Talk -> Action ()
buildTalkIndex = buildIndex
