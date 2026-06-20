module Main where
import System.Environment (getArgs)
import qualified Trans

main :: IO ()
main = getArgs >>= Trans.main