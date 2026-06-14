module Main where
import System.Environment (getArgs)
import Trans

main :: IO ()
main = getArgs >>= Trans.main