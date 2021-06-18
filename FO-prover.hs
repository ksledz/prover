{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances, LambdaCase #-}

module Main where

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import System.IO
import System.Random
import System.Timeout

import Text.Printf

import Control.Monad.State

import Test.QuickCheck hiding (Fun, (===))

import Formula
import Parser hiding (one)
import Utils

prover phi = prover_ $ skolemize $ quantiFix $ nnf $ Not phi
prover_ phi = debug "pseudo-skolemized formula and herbrand universe" phi `seq` True

-- NNF conversion
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

-- NNF optimizations
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

-- pseudo-skolemization
data STerm = SVar Int | SFun Int [STerm] | SConst Int deriving (Eq, Show)
-- SRel : 1st argument is True if relation is negated
data SForm = SAnd SForm SForm | SOr SForm SForm | SRel Bool String [STerm] | SForAll SForm deriving (Eq, Show)

-- number of constants, arities of functions, whether there are foralls, map of constants, map of functions
type SState = (Int, [Int], Bool, Map String Int, Map String Int)
type SMonad a = State SState a

type HerbrandUniverse = (Int, [Int], Bool)

getConst :: String -> SMonad Int
getFun :: String -> Int -> SMonad Int
setForAll ::  SMonad ()
makeConst :: SMonad Int
makeFun :: Int -> SMonad Int

getConst s = do
  (nr, a, b, map, c) <- get
  case Map.lookup s map of
    Just i -> return i
    Nothing -> do
      let newMap = Map.insert s nr map
      put (nr+1, a, b, newMap, c)
      return nr
getFun s ar = do
  (a, ars, b, c, map) <- get
  case Map.lookup s map of
    Just i -> return i
    Nothing -> do
      let newNr = length ars
      let newMap = Map.insert s newNr map
      let newArs = ars ++ [ar]
      put (a, newArs, b, c, newMap)
      return newNr

setForAll = do
  (a, b, _, c, d) <- get
  put (a, b, True, c, d)
  return ()

makeConst = do
  (nr, a, b, c, d) <- get
  put (nr+1, a, b, c, d)
  return nr

makeFun ar = do
  (a, ars, b, c, d) <- get
  let newNr = length ars
  let newArs = ars ++ [ar]
  put (a, newArs, b, c, d)
  return newNr

skolemizeTerm :: Map String STerm -> Term -> SMonad STerm
skolemizeForm :: Map String STerm -> Int -> Formula -> SMonad SForm
skolemize :: Formula -> (SForm, HerbrandUniverse)

skolemizeTerm vars (Var name) = do
  return (vars Map.! name)
skolemizeTerm _ (Fun name []) = do
  id <- getConst name
  return (SConst id)
skolemizeTerm vars (Fun name args) = do
  funId <- getFun name (length args)
  newArgs <- mapM (skolemizeTerm vars) args
  return (SFun funId newArgs)
  
skolemizeForm vars depth (And f1 f2) = do
  sf1 <- skolemizeForm vars depth f1
  sf2 <- skolemizeForm vars depth f2
  return (SAnd sf1 sf2)

skolemizeForm vars depth (Or f1 f2) = do
  sf1 <- skolemizeForm vars depth f1
  sf2 <- skolemizeForm vars depth f2
  return (SOr sf1 sf2)

skolemizeForm vars depth (Rel name args) = do
  newArgs <- mapM (skolemizeTerm vars) args
  return (SRel False name newArgs)

skolemizeForm vars depth (Not (Rel name args)) = do
  newArgs <- mapM (skolemizeTerm vars) args
  return (SRel True name newArgs)

skolemizeForm vars depth (Forall name f) = do
  let newVars = Map.insert name (SVar depth) vars
  sf <- skolemizeForm newVars (depth+1) f
  setForAll
  return (SForAll sf)

skolemizeForm vars depth (Exists name f) = do
  newVars <- case depth of
    0 -> do
      id <- makeConst
      return (Map.insert name (SConst id) vars)
    _ -> do
      funId <- makeFun depth
      let funVars = map SVar [0..depth-1]
      return (Map.insert name (SFun funId funVars) vars)
  skolemizeForm newVars depth f

skolemize formula = do
  let initState = (0, [], False, Map.empty, Map.empty)
  let (sf, (a, b, c, _, _)) = runState (skolemizeForm Map.empty 0 formula) initState
  (sf, ((if a == 0 then 1 else a), b, c))

-- main
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
