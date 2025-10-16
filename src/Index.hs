module Index where

-- aeson
import Data.Aeson
import Data.Text (unpack)

-- base
import Data.Char

-- generics
import GHC.Generics

-- project
import Config

-- shake
import Development.Shake
import Development.Shake.Classes
import Development.Shake.FilePath

-- slick
import Slick

data IndexInfo a = IndexInfo
  { pageType :: String
  , pageList :: [a]
  } deriving (Generic, Show, ToJSON, FromJSON, Binary)

buildIndex :: (ToJSON a) => IndexInfo a -> Action ()
buildIndex index@IndexInfo{..} = do
  indexT <- compileTemplate' "site/templates/index.html"
  writeFile' (outputFolder </> map toLower pageType </> "index.html") (unpack $ substitute indexT $ withSiteMeta $ toJSON index)
