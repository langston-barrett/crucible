{-# LANGUAGE LambdaCase #-}
module Main where

import Control.Applicative
import Control.Monad.ST

import Data.Monoid
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Lang.Crucible.Syntax.Concrete
import Lang.Crucible.Syntax.SExpr
import Lang.Crucible.Syntax.Atoms
import Lang.Crucible.CFG.SSAConversion


import qualified Text.Megaparsec as MP

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden
import System.FilePath (takeBaseName, replaceExtension)


for = flip map

main :: IO ()
main = roundTrips >>= defaultMain

testParser :: FilePath -> FilePath -> IO ()
testParser inFile outFile =
  do contents <- T.readFile inFile
     outContents <-
       case MP.parse (many (sexp atom) <* MP.eof) inFile contents of
         Left err ->
           pure $ T.pack $ MP.parseErrorPretty' contents err
         Right v ->
           do let printed = T.concat $ map printExpr v
              cfgs <- mapM (stToIO . top . cfg) v
              let res =
                    T.concat $ for cfgs $
                      \case
                        Left err -> T.pack (show err)
                        Right (ACFG _ _ theCfg) -> T.pack $ show (toSSA theCfg)
              pure $ printed <> T.pack "\n" <> res
     T.writeFile outFile outContents

roundTrips :: IO TestTree
roundTrips =
  do inputs <- findByExtension [".cbl"] "test-data"
     return $ testGroup "Crucible parsing round-trips"
       [ goldenVsFileDiff
          (takeBaseName input) -- test name
          (\x y -> ["diff", "-u", x, y])
          goodFile -- golden file path
          outFile
          (testParser input outFile) -- action whose result is tested
       | input <- inputs
       , let outFile = replaceExtension input ".out"
       , let goodFile = replaceExtension input ".out.good"
       ]