module Projects where

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

data Project =
  Project
    { title :: String
    , content :: String
    , url :: String
    } deriving (Generic, Eq, Ord, Show, FromJSON, ToJSON, Binary)
    
buildProject :: FilePath -> Action Project
buildProject srcPath = cacheAction ("build" :: T.Text, srcPath) $ do
  liftIO . putStrLn $ "Rebuilding project: " <> srcPath
  projectContent <- readFile' srcPath
  projectData <- markdownToHTML . T.pack $ projectContent
  let projectUrl = T.pack . dropDirectory1 $ srcPath -<.> "html"
      withProjectUrl = _Object . at "url" ?~ String projectUrl
      fullProjectData = withSiteMeta . withProjectUrl $ projectData
  template <- compileTemplate' "site/templates/project.html"
  writeFile' (outputFolder </> T.unpack projectUrl) . T.unpack $ substitute template fullProjectData
  convert fullProjectData

buildProjects :: Action [Project]
buildProjects = do
  pPaths <- getDirectoryFiles "." ["site/projects//*.md"]
  sortOn title <$> forP pPaths buildProject

buildProjectIndex :: IndexInfo Project -> Action ()
buildProjectIndex = buildIndex
