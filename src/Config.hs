module Config where

-- | Data

import Data.Aeson
import Data.Aeson.KeyMap

import Data.Time
import Data.Time.Format.ISO8601

-- | Generics

import GHC.Generics

data SiteMeta =
  SiteMeta
    { siteAuthor :: String
    , baseUrl :: String
    , siteTitle :: String
    , mastodonPage :: Maybe String  --full link
    , githubUser :: Maybe String
    }
    deriving (Generic, ToJSON)
    
withSiteMeta :: Value -> Maybe Value
withSiteMeta (Object obj) =
  case toJSON siteMeta of
    Object siteMetaObj ->
      Just $ Object $
        union obj siteMetaObj
    _ -> Nothing
withSiteMeta _ = Nothing


siteMeta :: SiteMeta
siteMeta =
  SiteMeta
    { siteAuthor = "Raymond Baker"
    , baseUrl = "https://morphismz.github.io"
    , siteTitle = "Raymond Baker"
    , mastodonPage = Just "https://mathstodon.xyz/@isAdisplayName"
    , githubUser = Just "morphismz"
    }

outputFolder :: FilePath
outputFolder = "docs/"

formatDate :: String -> String
formatDate humanDate = toIsoDate parsedTime
  where
    parsedTime =
      parseTimeOrError True defaultTimeLocale "%b %e, %Y" humanDate :: UTCTime

toIsoDate :: UTCTime -> String
toIsoDate = formatShow (utcTimeFormat (calendarFormat BasicFormat) (timeOfDayFormat BasicFormat))
