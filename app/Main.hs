{-# LANGUAGE OverloadedStrings #-}
module Main where

import Build (build)
import Network.Wai.Handler.Warp (run)
import Network.Wai.Application.Static (staticApp, defaultFileServerSettings)

main :: IO ()
main = do
  build
  putStrLn "Serve files (Y/n)?"
  input <- getLine
  case input of
    "n" -> pure ()
    _ -> serveFiles

serveFiles :: IO ()
serveFiles = do
  let port = 8080
      -- Point this to your target directory (e.g., current directory ".")
      directory = "docs" 
      settings = defaultFileServerSettings directory

  putStrLn $ "Serving static files from " ++ directory ++ " on port " ++ show port
  run port (staticApp settings)
