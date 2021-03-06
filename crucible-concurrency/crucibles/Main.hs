{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
module Main where

import qualified Data.Text.IO as T
import qualified Options.Applicative.Simple as Opts
import           System.IO

import qualified Crux
import Cruces.CrucesMain
import Paths_crucible_concurrency (version)

main :: IO ()
main = Crux.loadOptions Crux.defaultOutputConfig "cruces" version cruciblesConfig $ run
