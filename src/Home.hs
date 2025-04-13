module Home where

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

-- | Build home

buildHome :: Action ()
buildHome = cacheAction ("build" :: T.Text, "site/home.md" :: FilePath) $ do
  liftIO . putStrLn $ "Rebuilding home page from site/home.md, writing to " <> outputFolder </> "index.html"
  homeContent <- readFile' "site/home.md"
  homeData <- markdownToHTML . T.pack $ homeContent
  template <- compileTemplate' "site/templates/home.html"
  writeFile' (outputFolder </> "index.html") . T.unpack $ substitute template (withSiteMeta homeData)
