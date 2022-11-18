{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- Imports for Monads

import Control.Monad

-- AST and Type Definitions
data TERMLANG where
  Num :: Int -> TERMLANG
  Boolean :: Bool -> TERMLANG
  Id :: String -> TERMLANG
  Plus :: TERMLANG -> TERMLANG -> TERMLANG
  Minus :: TERMLANG -> TERMLANG -> TERMLANG
  Mult :: TERMLANG -> TERMLANG -> TERMLANG
  Div :: TERMLANG -> TERMLANG -> TERMLANG
  If :: TERMLANG -> TERMLANG -> TERMLANG -> TERMLANG
  And :: TERMLANG -> TERMLANG -> TERMLANG
  Or :: TERMLANG -> TERMLANG -> TERMLANG
  Leq :: TERMLANG -> TERMLANG -> TERMLANG
  IsZero :: TERMLANG -> TERMLANG
  Lambda :: String -> TYPELANG -> TERMLANG -> TERMLANG
  App :: TERMLANG -> TERMLANG -> TERMLANG
  Bind :: String -> TERMLANG -> TERMLANG -> TERMLANG
  deriving (Show,Eq)

data TYPELANG where
  TNum :: TYPELANG
  TBool :: TYPELANG
  (:->:) :: TYPELANG -> TYPELANG -> TYPELANG
  deriving (Show,Eq)

data VALUELANG where
  NumV :: Int -> VALUELANG
  BoolV :: Bool -> VALUELANG
  ClosureV :: String -> TERMLANG -> ValueEnv -> VALUELANG
  deriving (Show,Eq)

type TypeEnv = [(String,TYPELANG)]  
type ValueEnv = [(String,VALUELANG)]

--Part 1: Type Inference --
typeof :: TypeEnv -> TERMLANG -> (Maybe TYPELANG)
typeof g (Num n) = if n >= 0 then return TNum else Nothing
typeof g (Boolean b) = return TBool
typeof g (Plus l r) = 
    do {TNum <- typeof g l;
        TNum <- typeof g r;
        return TNum}
typeof g (Minus l r) = 
    do {TNum <- typeof g l;
        TNum <- typeof g r;
        return TNum}
typeof g (Mult l r) = 
    do {TNum <- typeof g l;
        TNum <- typeof g r;
        return TNum}
typeof g (Div l r) = 
    do {TNum <- typeof g l;
        TNum <- typeof g r;
        return TNum}
typeof g (And l r) = 
    do {TBool <- typeof g l;
        TBool <- typeof g r;
        return TBool}
typeof g (Or l r) = 
    do {TBool <- typeof g l;
        TBool <- typeof g r;
        return TBool}
typeof g (Leq l r) = 
    do {TNum <- typeof g l;
        TNum <- typeof g r;
        return TBool}
typeof g (IsZero x) = 
    do {TNum <- typeof g x;
        return TBool}
typeof g (If c t e) = 
    do {TBool <- typeof g c;
        t' <- typeof g t;
        e' <- typeof g e;
        if t' == e'
            then return t'
            else Nothing}
typeof g (Lambda i d b) = 
    do {r <-typeof ((i,d):g) b;
        return (d :->: r)}
typeof g (App f a) = 
    do {a' <- typeof g a;
        d :->: r <- typeof g f;
        if a' == d then return r else Nothing}
typeof g (Bind i v b) = 
    do{tv <- typeof g v;
        typeof ((i,tv):g) b}
typeof g (Id i) = (lookup i g)

--Part 2: Evaluation --
evalM :: ValueEnv -> TERMLANG -> (Maybe VALUELANG)
evalM e (Num x) = if x < 0 then Nothing else Just (NumV x)
evalM e (Boolean b) = Just (BoolV b)
evalM e (Plus l r) = 
  do {(NumV l') <- evalM e l;
      (NumV r') <- evalM e r;
      return (NumV (l'+r'))}
evalM e (Minus l r) = 
  do {(NumV l') <- evalM e l;
      (NumV r') <- evalM e r;
      let x = (l'-r') in
        if x < 0
          then Nothing
          else return (NumV (l'-r'))}
evalM e (Mult l r) = 
  do {(NumV l') <- evalM e l;
      (NumV r') <- evalM e r;
      return (NumV (l'*r'))}
evalM e (Div l r) = 
  do {(NumV l') <- evalM e l;
      (NumV r') <- evalM e r;
      if r' == 0
        then Nothing
        else return (NumV (div l' r'))}
evalM e (And l r) = 
    do {(BoolV l') <- evalM e l;
        (BoolV r') <- evalM e r;
        return (BoolV (l' && r'))}
evalM e (Or l r) = 
    do {(BoolV l') <- evalM e l;
        (BoolV r') <- evalM e r;
        return (BoolV (l' || r'))}
evalM e (Leq l r) = 
    do {(NumV l') <- evalM e l;
        (NumV r') <- evalM e r;
        if l'<= r'
            then return (BoolV True)
            else return (BoolV False)}
evalM e (IsZero x) = 
    do {(NumV x') <- evalM e x;
        if x' == 0
            then return (BoolV True)
            else return (BoolV False)}
evalM e (If c t el) = 
    do {(BoolV c') <- evalM e c;
        if c' == (True)
            then 
                do{t' <- evalM e t;
                    return (t')}
            else 
                do{el' <- evalM e el;
                    return (el')}}
evalM e (Bind i v b) = 
    do {v' <- evalM e v;
        (evalM ((i,v'):e) b)}
evalM e (Id i) = (lookup i e)
evalM e (Lambda i d b) = return (ClosureV i b e)
evalM e (App f a) =
    do{(ClosureV i b j) <- evalM e f;
        a' <- evalM e a;
        evalM ((i,a'):j) b} 

--Part 3: Fixed Point Operator --

--Part 4: New Language Feature --

--Part 5: Interpretation --