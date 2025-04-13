module Index where

-- | Data

import Data.Aeson
import Data.Text (unpack)

import Data.Char
-- | Generics

import GHC.Generics

-- | Project

import Config

-- | Shake

import Development.Shake
import Development.Shake.FilePath

-- | Slick

import Slick

data IndexInfo a = IndexInfo
  { pageType :: String
  , pageList :: [a]
  } deriving (Generic, Show, ToJSON, FromJSON)

buildIndex :: (ToJSON a) => IndexInfo a -> Action ()
buildIndex index@IndexInfo{..} = do
  indexT <- compileTemplate' "site/templates/index.html"
  writeFile' (outputFolder </> (map toLower pageType) </> "index.html") (unpack $ substitute indexT $ withSiteMeta $ toJSON index)
