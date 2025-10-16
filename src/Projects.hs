module Projects where

-- aeson
import Data.Aeson
import Data.Aeson.Lens

-- base
import Control.Lens

import Data.List
import Data.Ord

-- generics
import GHC.Generics

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

data Project =
  Project
    { title :: String
    , content :: String
    , url :: String
    , image :: Maybe String
    } deriving (Generic, Eq, Ord, Show, FromJSON, ToJSON, Binary)
    
buildProject :: FilePath -> Action Project
buildProject srcPath = cacheAction ("build" :: T.Text, srcPath) $ do
  liftIO . putStrLn $ "Rebuilding project: " <> srcPath
  projectData <- typstAndMetaDataToHTML srcPath
  let projectUrl = T.pack . dropDirectory1 $ srcPath -<.> "html"
      withProjectUrl = _Object . at "url" ?~ String projectUrl
      fullProjectData = withSiteMeta . withProjectUrl $ projectData
  template <- compileTemplate' "site/templates/project.html"
  writeFile' (outputFolder </> T.unpack projectUrl) . T.unpack $ substitute template fullProjectData
  convert fullProjectData

buildProjects :: Action [Project]
buildProjects = do
  pPaths <- getDirectoryFiles "." ["site/projects//*.yaml"]
  sortOn title <$> forP pPaths (buildProject . dropExtension)

buildProjectIndex :: IndexInfo Project -> Action ()
buildProjectIndex = buildIndex
