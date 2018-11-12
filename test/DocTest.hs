module Main
( main
) where

import Test.DocTest
main = doctest $ words "-isrc -pgmL markdown-unlit docs/Readme.lhs"
