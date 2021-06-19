{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances, LambdaCase #-}

module Main where

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import System.IO
import System.Random
import System.Timeout

import Text.Printf

import Control.Monad.State

import Test.QuickCheck hiding (Fun, (===))

import Formula
import Parser hiding (one)
import Utils

prover phi = do
  let pass1 = relPolarityOptimize $ nnf $ Not phi
  if pass1 == T then False else prover_ $ skolemize $ quantiFix pass1

prover_ (sf, hud) = do
  let initHU = makeHU hud
  let (_, funcArs, hasForAll) = hud
  if funcArs == [] || not hasForAll then do 
    let (pf, nVars) = evalSForm sf initHU
    let cnff = tseytin pf nVars
    not (satSolver cnff)
  else  
    proverLoop sf hud initHU

proverLoop :: SForm -> HUDesc -> HUState -> Bool
proverLoop sf hud hu = do
  let (pf, nVars) = evalSForm sf hu
  let cnff = tseytin pf nVars
  if satSolver cnff then do
    let (_, newHU) = runState (growHU hud) hu
    proverLoop sf hud newHU
  else True

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
-- first set is not-negated relations, second negated
type RelState = (Set VarName, Set VarName)
type RelMonad a = State RelState a
relPolarityOptimize :: Formula -> Formula
relPolarityOptimize f =
  let (_, state) = runState (relPolarityAnalyze f) (Set.empty, Set.empty)
  in relPolarityReplace f state
relPolarityAnalyze :: Formula -> RelMonad ()
relPolarityAnalyze (Not (Rel name _)) = do
   (posi, neg) <- get
   let newNeg = Set.insert name neg 
   put (posi, newNeg)
relPolarityAnalyze (Rel name _) = do
  (posi, neg) <- get
  let newPosi = Set.insert name posi
  put (newPosi, neg)
relPolarityAnalyze (And f1 f2) = do
  relPolarityAnalyze f1
  relPolarityAnalyze f2
relPolarityAnalyze (Or f1 f2) = do
  relPolarityAnalyze f1
  relPolarityAnalyze f2
relPolarityAnalyze (Forall v f) = relPolarityAnalyze f
relPolarityAnalyze (Exists v f) = relPolarityAnalyze f

relPolarityReplace :: Formula -> RelState -> Formula
relPolarityReplace (Rel name terms) (posi, neg) =  if Set.notMember name neg then T else Rel name terms
relPolarityReplace (Not (Rel name terms)) (posi, neg) = if Set.notMember name posi then T else Not (Rel name terms)
relPolarityReplace (And f1 f2) state = do
  let sf1 = relPolarityReplace f1 state
  let sf2 = relPolarityReplace f2 state
  if sf1 == T then sf2
  else if sf2 == T then sf1 else And sf1 sf2
relPolarityReplace (Or f1 f2) state = do
  let sf1 = relPolarityReplace f1 state
  let sf2 = relPolarityReplace f2 state
  if sf1 == T || sf2 == T then T else Or sf1 sf2
relPolarityReplace (Forall v f) state = do
  let sf = relPolarityReplace f state
  if sf == T then T else Forall v sf
relPolarityReplace (Exists v f) state = do
  let sf = relPolarityReplace f state
  if sf == T then T else Exists v sf

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

type HUDesc = (Int, [Int], Bool)

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
skolemize :: Formula -> (SForm, HUDesc)

skolemizeTerm vars (Var name) = return (vars Map.! name)
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

-- herbrand universe growth
-- number of items in hu, map of function evaluations, number of propositional vars used, map of relation evaluations (into propositional variables)
type HUState = (Int, Map (Int, [Int]) Int, Int, Map (String, [Int]) Int)
type HerbrandMonad a = State HUState a

evalFunc :: Int -> [Int] -> HerbrandMonad Int
evalFunc id args = do
  (nItems, map, a, b)  <- get
  case Map.lookup (id, args) map of
    Just herbrandId -> return herbrandId
    Nothing -> do
      put (nItems+1, Map.insert (id, args) nItems map, a, b)
      return nItems

makeHU :: HUDesc -> HUState
makeHU (nrConst, _, _) = (nrConst, Map.empty, 0, Map.empty)

growHU :: HUDesc -> HerbrandMonad ()
growHU (_, funArs, _) = do
  (origItems, _, _, _) <- get
  mapM_ (growHUByFunc origItems) (zip [0..] funArs) 

growHUByFunc :: Int -> (Int, Int) -> HerbrandMonad ()
growHUByFunc origItems (funId, funAr) = do
  mapM_ (evalFunc funId) (makeArgs funAr origItems)

makeArgs :: Int -> Int -> [[Int]]
makeArgs 0 _ = [[]]
makeArgs n k = [h:t | t <- makeArgs (n-1) k, h <- [0..(k-1)] ]

-- skolem form -> propositional form
data PForm = PAnd [PForm] | POr [PForm] | PVar Int Bool deriving (Show, Eq)

evalRel :: String -> [Int] -> HerbrandMonad Int
evalRel id args = do
  (a, b,nrPVars, map) <- get
  case Map.lookup (id, args) map of
    Just pVarId -> return pVarId
    Nothing -> do
      put (a, b, nrPVars+1, Map.insert (id, args) nrPVars map)
      return nrPVars

evalTerm :: [Int] -> STerm -> HerbrandMonad Int
evalTerm varVals (SVar varId) = return (varVals !! varId)
evalTerm varVals (SFun funId funTerms) = do
  evaledTerms <- mapM (evalTerm varVals) funTerms
  evalFunc funId evaledTerms
evalTerm varVals (SConst constId) = return constId

evalSForm :: SForm -> HUState -> (PForm, Int)
evalSForm f hu = let (origItems, _, _, _) = hu in let (pf, (_, _, nrVars, _)) =  runState (evalFormula [] origItems f) hu in (pf, nrVars)

evalFormula :: [Int] -> Int -> SForm -> HerbrandMonad PForm
evalFormula varVals origItems (SAnd f1 f2) = do
  pf1 <- evalFormula varVals origItems f1
  pf2 <- evalFormula varVals origItems f2
  return (makePAnd [pf1, pf2])
evalFormula varVals origItems (SOr f1 f2) = do
  pf1 <- evalFormula varVals origItems f1
  pf2 <- evalFormula varVals origItems f2
  return (makePOr [pf1, pf2])
evalFormula varVals _ (SRel negated name terms) = do
  evaledTerms <- mapM (evalTerm varVals) terms
  evaledRel <- evalRel name evaledTerms
  return (PVar evaledRel negated)
evalFormula varVals origItems (SForAll f) = do
  forms <- mapM (\x -> evalFormula (varVals ++ [x]) origItems f) [0..origItems-1] 
  return (makePAnd forms)

makePAnd :: [PForm] -> PForm
makePAnd forms = PAnd $ concat (map breakPAnd forms)
breakPAnd :: PForm -> [PForm]
breakPAnd (PAnd forms) = forms
breakPAnd x = [x]


makePOr :: [PForm] -> PForm
makePOr forms = POr $ concat (map breakPOr forms)
breakPOr :: PForm -> [PForm]
breakPOr (POr forms) = forms
breakPOr x = [x]

-- tseytin
type CNFLiteral = (Int, Bool)
type CNFClause = [CNFLiteral]
type CNFForm = [CNFClause]
-- how many vars used, already emitted clauses, end cache
type TseytinState = (Int, [CNFClause], Map [CNFLiteral] CNFLiteral)
type TseytinMonad a = State TseytinState a
negateLiteral :: CNFLiteral -> CNFLiteral
negateLiteral (i, b) = (i, not b)
emitAnd :: [CNFLiteral] -> TseytinMonad CNFLiteral
emitAnd literals = do
  (vars, clauses, cache) <- get
  case Map.lookup literals cache of
    Just literal -> return literal
    Nothing -> do
      let newLiteral = (vars, False)
      let clause1 = newLiteral:(map negateLiteral literals)
      let clauses2 = map (\x -> [x, negateLiteral newLiteral]) literals
      let newClauses = clause1:clauses2
      put (vars+1, newClauses ++ clauses, Map.insert literals newLiteral cache)
      return newLiteral
tseytin :: PForm -> Int -> CNFForm
tseytinForm :: PForm -> TseytinMonad CNFLiteral

tseytinForm (PAnd forms) = do
  literals <- mapM tseytinForm forms
  emitAnd literals

tseytinForm (POr forms) = do
  literals <- mapM tseytinForm forms
  andLiteral <- emitAnd (map negateLiteral literals)
  return (negateLiteral andLiteral)

tseytinForm (PVar i b) = do
  return (i, b)

tseytin p i = do
  let initState = (i, [], Map.empty)
  let (finalLiteral, (_, clauses, _)) = runState (tseytinForm p) initState
  [finalLiteral]:clauses

-- SAT solver
propagateUnits :: CNFForm -> Maybe CNFForm
propagateUnits formula = do
  let units = findUnits formula -- units is a set
  if Set.null units then Just formula 
  else if unitsConsistent units then do
    let newFormula = filter (nonPositiveClause units) formula
    let newerFormula = map (deleteNegations units) newFormula
    propagateUnits newerFormula
  else Nothing

findUnits :: CNFForm -> Set CNFLiteral
findUnits formula = Set.fromList $ map (\[x] -> x) (filter singularClause formula)
singularClause :: CNFClause -> Bool
singularClause [_] = True
singularClause clause = False
nonPositiveClause :: Set CNFLiteral -> CNFClause -> Bool
nonPositiveClause units clause = all (\x -> Set.notMember x units) clause
unitsConsistent :: Set CNFLiteral -> Bool
unitsConsistent units = all (\x -> Set.notMember (negateLiteral x) units) units
deleteNegations :: Set CNFLiteral -> CNFClause -> CNFClause
deleteNegations units clause = filter (\x -> Set.notMember (negateLiteral x) units) clause


cleanClauses :: CNFForm -> CNFForm
cleanClauses formula = map Set.toList $ filter unitsConsistent (map Set.fromList formula) 


optimizePureLiterals :: CNFForm -> CNFForm
optimizePureLiterals formula = do
  let allLiterals = Set.fromList $ concat formula
  let pureLiterals = Set.filter (\x -> Set.notMember (negateLiteral x) allLiterals) allLiterals
  if Set.null pureLiterals then formula else do
    let newFormula = filter (nonPositiveClause pureLiterals) formula
    optimizePureLiterals newFormula

satSolver :: CNFForm -> Bool
satSolver f = do 
  let f2 = cleanClauses f
  case propagateUnits f2 of
    Just f3 -> do
      let f4 = optimizePureLiterals f3
      if f4 == [] then True 
      else if elem [] f4 then False 
      else do
        let var = pickResolveVar f4
        let f5a =  [(var, True)]:f4
        let f5b = [(var, False)]:f4
        satSolver f5a || satSolver f5b
    Nothing -> False
  
pickResolveVar :: CNFForm -> Int
-- TODO better heuristics
pickResolveVar (((var, _):_):_) = var

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
