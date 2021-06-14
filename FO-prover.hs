{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances, LambdaCase #-}

module Main where

import Data.List

import System.IO
import System.Random
import System.Timeout

import Text.Printf

import Control.Monad.State

import Test.QuickCheck hiding (Fun, (===))

import Formula
import Parser hiding (one)
import Utils

prover phi = prover_ $ quantiFix $ nnf $ Not phi
prover_ phi = debug "nnf" phi `seq` True

nnf :: Formula -> Formula 

nnf (Implies phi psi) = Or (nnf (Not phi)) (nnf psi)
nnf (Iff phi psi) = Or (And (nnf (Not phi)) (nnf (Not psi))) (And (nnf phi) (nnf psi))
nnf (Not(Or phi psi)) = And (nnf (Not phi)) (nnf (Not psi))
nnf (Not(And phi psi)) = Or (nnf (Not phi)) (nnf (Not psi))
nnf (Not (Not phi)) = nnf phi
nnf (Not (Exists var phi)) = Forall var (nnf (Not phi))
nnf (Not (Forall var phi)) = Exists var (nnf (Not phi))
nnf (Not (Implies phi psi)) = And (nnf phi) (nnf (Not psi))
nnf (Not (Iff phi psi)) = And (Or (nnf phi) (nnf psi)) (Or (nnf (Not phi)) (nnf (Not psi)))
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Exists var phi) = Exists var (nnf phi)
nnf (Forall var phi) = Forall var (nnf phi)
nnf phi = phi


quantiFix :: Formula -> Formula
quantiFix_ :: Formula -> Formula 
quantiFixFV :: Formula -> [VarName] -> Formula

quantiFix_ (Exists v phi) = if not $ elem v (fv phi) then quantiFix_ phi else Exists v (quantiFix_ phi)
quantiFix_ (Forall v phi) = if not $ elem v (fv phi) then quantiFix_ phi else Forall v (quantiFix_ phi)
quantiFix_ (Not phi) = Not $ quantiFix_ phi
quantiFix_ (And phi psi) = And (quantiFix_ phi) (quantiFix_ psi)
quantiFix_ (Or phi psi) = Or (quantiFix_ phi) (quantiFix_ psi)
quantiFix_ phi = phi
quantiFix phi = quantiFixFV  phi (fv phi)
quantiFixFV phi [] = quantiFix_ phi
quantiFixFV phi (h:t) = Exists h (quantiFixFV phi t)

main :: IO ()
main = do
    eof <- hIsEOF stdin
    if eof
        then return ()
        else do
                line <- getLine -- read the input
                let phi = parseString line -- call the parser
                let res = prover phi -- call the prover
                if res
                  then putStrLn "1" -- write 1 if the formula is a tautology
                  else putStrLn "0" -- write 0 if the formula is not a tautology
