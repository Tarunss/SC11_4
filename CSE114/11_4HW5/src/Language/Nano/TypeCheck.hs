{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = parseFile f >>= typeOfExpr

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseString s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Problem 1: Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TVar]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars t     = case t of
    TInt -> [] -- TInt has no free variables
    TBool -> [] -- TBool has no free variables
    TVar t -> [t] -- t is the only free variable
    (t1 :=> t2) -> L.nub (freeTVars t1 ++ freeTVars t2) -- we need to delete the duplicates of this list
    TList t -> freeTVars t --map freeTVars onto list of types (Lists are homogenious)
-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
  freeTVars  s = case s of
    Mono s -> freeTVars s --if its a mono type, we just find the values of it
    Forall var poly -> L.delete var (freeTVars poly) --we delete var from list of free variables since its a binder
-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars gamma   = concat [freeTVars s | (x, s) <- gamma]  
  
-- | Lookup a variable in the type environment  
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))

-- | Extend the type environment with a new biding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Lookup a type variable in a substitution;
--   if not present, return the variable unchanged
lookupTVar :: TVar -> Subst -> Type
lookupTVar a [] = TVar a
lookupTVar a sub = if a == fst x then snd x else lookupTVar a xs
  where (x:xs) = sub

-- | Remove a type variable from a substitution
removeTVar :: TVar -> Subst -> Subst
removeTVar _ [] = []
removeTVar a sub = if a == fst x then L.delete x sub else removeTVar a xs
  where (x:xs) = sub
     
-- | Things to which type substitutions can be apply
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
instance Substitutable Type where  
  apply sub t = case t of
    TInt -> TInt --need to check and see if there is a TInt in sub
    TBool -> TBool
    TVar var -> lookupTVar var sub
    TList var2 -> TList (apply sub var2)
    (t1 :=> t2) -> (apply sub t1 :=> apply sub t2)
-- | Apply substitution to poly-type
instance Substitutable Poly where    
  apply sub s         = case s of
    Mono s -> Mono (apply sub s)
    Forall var poly -> apply (removeTVar var sub) poly -- we have to delete the bindings off of sub for var, and recall on poly

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply sub to = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip to
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply sub gamma = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
extendSubst :: Subst -> TVar -> Type -> Subst
extendSubst sub tvar t = (tvar, apply sub t) : sub

   --add a and t to subst env

      
--------------------------------------------------------------------------------
-- Problem 2: Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving (Eq,Show)

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- |Fresh type variable number n
freshTV n = TVar $ "a" ++ show n      
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TVar -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
unifyTVar :: InferState -> TVar -> Type -> InferState
unifyTVar (InferState sub n) a (TVar t) 
  | a == t = InferState sub n
unifyTVar (InferState sub n) a t 
  |a `elem` (freeTVars t) = throw (Error "type error")
  |otherwise = extendState (InferState sub n) a t
  

    
-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
unify :: InferState -> Type -> Type -> InferState
unify (InferState sub n) (TVar t1) t2 = unifyTVar (InferState sub n) t1 t2 -- link to unifyTVAR
unify (InferState sub n) t1 (TVar t2) = unifyTVar (InferState sub n) t2 t1
unify (InferState sub n) TInt TBool = throw (Error "type error") --RAW TYPES
unify (InferState sub n) TBool TInt = throw (Error "type error")
unify (InferState sub n) TInt TInt = InferState sub n
unify (InferState sub n) TBool TBool = InferState sub n
unify (InferState sub n) (TList l) TBool = unify (InferState sub n) l TBool --LISTS
unify (InferState sub n) TBool (TList l) = unify (InferState sub n) l TBool
unify (InferState sub n) (TList l) TInt = unify (InferState sub n) l TInt
unify (InferState sub n) TInt (TList l) = unify (InferState sub n) l TInt
unify (InferState sub n) (TList l1) (TList l2) = unify (InferState sub n) l1 l2
unify (InferState sub n) (t1 :=> t2) (t3 :=> t4) = unify (InferState subsEnv n) (apply (subsEnv) t2) (apply (subsEnv) t4) --FUNCTIONS
  where subsEnv = stSub (unify (InferState sub n) t1 t3)
unify (InferState sub n) (t1 :=> t2) (TVar t3) = unifyTVar (InferState sub n) t3 (t1:=>t2) -- TVar statements I forgot about
unify (InferState sub n) (TVar t1) (t2 :=> t3)  = unifyTVar (InferState sub n) t1 (t2:=>t3)
unify (InferState sub n) (TInt :=> TInt) (TInt) = throw (Error "type error")
unify (InferState sub n) (TInt) (TInt :=> TInt) = throw (Error "type error")


--unify (InferState sub n) (TList l) (TBool) = InferState 

--------------------------------------------------------------------------------
-- Problem 3: Type Inference
--------------------------------------------------------------------------------    
  
infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
infer st _   (EInt _)          = (st,TInt)
infer st _   (EBool _)         = (st,TBool)

--EVAR --------------------------------------------------------------------------
infer st gamma (EVar x)        = case lookupVarType x gamma of
  Mono x -> (st, x)
  Forall tvar poly -> (st', newType)
    where 
      (newCount,newType) = instantiate (stCnt st) poly
      st' = InferState (stSub (extendState st x newType)) (newCount)

--ELAM ---------------------------------------------------------------------------
infer st gamma (ELam x body)   = (finalInferState, (typeOfFormal :=> typeOfBody))
  where
    st' = InferState (stSub st) n
    gamma' = extendTypeEnv x (Mono (freshTV n)) gamma
    n = stCnt st
    finalInferState = fst (infer st' gamma' body)
    typeOfFormal = apply (stSub finalInferState) (freshTV n)
    typeOfBody = snd (infer st' gamma' body)


--EAPP
infer st gamma (EApp e1 e2)    = (st'',freshType')
  where
    (st',functype) = infer st gamma e1
    (st'',argtype) = infer st' gamma e2
    freshType = freshTV (stCnt st'')
    step3d = unify st'' functype (argtype :=> freshType)
    freshType' = apply (stSub step3d) freshType  



infer st gamma (ELet x e1 e2)  = error "TBD: infer ELet"



infer st gamma (EBin op e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp opVar e1) e2
    opVar = EVar (show op)
infer st gamma (EIf c e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp (EApp ifVar c) e1) e2
    ifVar = EVar "if"    
infer st gamma ENil = infer st gamma (EVar "[]")

-- | Generalize type variables inside a type
generalize :: TypeEnv -> Type -> Poly
generalize gamma t = 
 helper (freeTVars t L.\\ freeTVars gamma)
  where
    helper [] = Mono t
    helper (x : xs) = Forall x (helper xs) 
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n (Mono x) = (n,x)
instantiate n (Forall tvar poly) =instantiate (n+1) polytype
  where 
    fakeSubst = extendSubst [] tvar (freshTV n)
    polytype = apply fakeSubst poly
      
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono $ TInt :=> TInt :=> TInt)
  , ("-",    error "TBD: -")
  , ("*",    error "TBD: *")
  , ("/",    error "TBD: /")
  , ("==",   error "TBD: ==")
  , ("!=",   error "TBD: !=")
  , ("<",    error "TBD: <")
  , ("<=",   error "TBD: <=")
  , ("&&",   error "TBD: &&")
  , ("||",   error "TBD: ||")
  , ("if",   error "TBD: if")
  -- lists: 
  , ("[]",   error "TBD: []")
  , (":",    error "TBD: :")
  , ("head", error "TBD: head")
  , ("tail", error "TBD: tail")
  ]
