module Main where

import Tokenizer
import Parser

main = do
  input <- getLine
  putStrLn $ show $ parse $ alexScanTokens input
