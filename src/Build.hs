module Build (build) where

-- | Functors

import Data.Functor

-- | Generics
import GHC.Generics

-- | Data
import Data.Aeson
import Data.Aeson.KeyMap
import Data.Aeson.Lens

import Data.Text qualified as T

-- | Lenses

import Control.Lens

-- | Monads

-- import Control.Monad

-- | Project

import Atom
import Blog
import Config
import Home
import Index
import Projects
--import Redirect
import Talks

-- | Shake
import Development.Shake
import Development.Shake.FilePath
import Development.Shake.Forward

-- | Slick

import Slick

-- | Copy all static files from the listed folders to their destination
copyStaticFiles :: Action ()
copyStaticFiles = do
  filepaths <- getDirectoryFiles "./site/" ["images//*", "css//*", "js//*", "files//*"]
  void $ forP filepaths $ \filepath ->
    copyFileChanged ("site" </> filepath) (outputFolder </> filepath)

-- | Build    
buildSite :: Action ()
buildSite = do
  allPosts <- buildPosts
  buildPostIndex $ IndexInfo "Posts" allPosts
  buildFeed allPosts
  allTalks <- buildTalks
  buildTalkIndex $ IndexInfo "Talks" allTalks
  allProjects <- buildProjects
  buildProjectIndex $ IndexInfo "Projects" allProjects
  buildHome
  copyStaticFiles

build :: IO ()
build = do
  let shOpts = shakeOptions { shakeVerbosity = Verbose, shakeLintInside = ["\\"]}
  shakeArgsForward shOpts buildSite
