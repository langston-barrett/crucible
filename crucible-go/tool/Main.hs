-- | Command line interface to crucible-go
{-# Language OverloadedStrings #-}
module Main where

import qualified Data.ByteString.Lazy as BS

import System.Exit (exitWith)

import qualified Data.Parameterized.Context as Ctx

-- crucible/crucible
import Lang.Crucible.Simulator

-- crux
import qualified Crux
import qualified Crux.Model   as Crux
import qualified Crux.Types   as Crux

-- Go
import Language.Go.Parser
import Lang.Crucible.Go.Simulate (setupCrucibleGoCrux)
import Lang.Crucible.Go.Types
import Paths_crucible_go (version)

-- | A simulator context
type SimCtxt sym = SimContext (Crux.Model sym) sym Go

data GoOptions = GoOptions { }

defaultOptions :: GoOptions
defaultOptions = GoOptions { }

cruxGoConfig :: Crux.Config GoOptions
cruxGoConfig = Crux.Config
  { Crux.cfgFile = pure defaultOptions
  , Crux.cfgEnv = []
  , Crux.cfgCmdLineFlag = []
  }

simulateGo :: Crux.CruxOptions -> GoOptions -> Crux.SimulatorCallback
simulateGo copts _opts = Crux.SimulatorCallback $ \sym _maybeOnline -> do
   let files = Crux.inputFiles copts
   let verbosity = Crux.simVerbose copts
   file <- case files of
             [f] -> return f
             _ -> fail "crux-go requires a single file name as an argument"

   -- Load the file
   json <- BS.readFile file
   let fwi = either error id $ parseMain json

   -- Initialize arguments to the function
   let regmap = RegMap Ctx.Empty

   -- Set up initial crucible execution state
   initSt <- setupCrucibleGoCrux 32 fwi verbosity sym Crux.emptyModel regmap

   -- TODO: add failure explanations
   let explainFailure _evalFn _gl = return mempty

   return (Crux.RunnableState initSt, explainFailure)


-- | Entry point, parse command line options
main :: IO ()
main =
  Crux.loadOptions Crux.defaultOutputConfig "crux-go" version cruxGoConfig $
    \(cruxOpts, goOpts) ->
      exitWith =<< Crux.postprocessSimResult cruxOpts =<<
        Crux.runSimulator (cruxOpts { Crux.outDir = "report"
                                    , Crux.skipReport = False })
        (simulateGo cruxOpts goOpts)
