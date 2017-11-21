module Main where

import Heuristicas

import System.Environment

main = do
  [f] <- getArgs :: IO [FilePath]
  sol <- satSolver heuristicaFrecuencia f
  print sol
