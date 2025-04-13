module Redirect where

-- | Control

import Control.Lens

-- | Data

import Data.Aeson
import Data.Aeson.Lens

import Data.Text qualified as T

-- | Generics

import GHC.Generics

-- | Project

import Config

-- | Shake

import Development.Shake
import Development.Shake.Classes
import Development.Shake.FilePath
import Development.Shake.Forward

-- | Slick

import Slick

data Redirect =
  Redirect
    { fromUrl :: String --without base url
    , toUrl :: String -- without base url
    } deriving (Generic, Eq, Ord, Show, FromJSON, ToJSON)

buildRedirect :: Redirect -> Action ()
buildRedirect r@Redirect{..} = do
  liftIO . putStrLn $ "Rebuilding redirect: from " <> fromUrl <> " to " <> toUrl
  template <- compileTemplate' "site/templates/redirect.html"
  writeFile' (outputFolder </> fromUrl) . T.unpack $ substitute template (withSiteMeta $ toJSON r)
