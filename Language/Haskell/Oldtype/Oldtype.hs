{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeSynonymInstances, GeneralizedNewtypeDeriving #-}

module Oldtype (
  oldtype
  ) where

import Control.Applicative
import Control.Monad.Cont
import Control.Monad.Reader
import Control.Monad.State
import Data.List
import Data.Maybe
import Language.Haskell.TH.Syntax hiding (lift)

type Env = [(Name, Type)]
data ContTableEntry = Continuation (TypeOrPartial -> R TypeOrPartial) | Variable Name
type ContTable = [((Env, Type), ContTableEntry)]
newtype R a = R { runR :: ReaderT ContTable (ContT Type (StateT Env Q)) a } deriving (Functor, Monad, MonadReader ContTable, MonadState Env, MonadCont)
-- The Env state is write-only and contains a list of generated definitions.
-- The ContTable is a list of continuations to jump back to when a loop is detected.

data TypeOrPartial = Type Type | Partial Env [Name] Type
-- a Type should not be a partially applied type synonym or newtype, but it can contain one.
-- a Partial should have a nonempty list of argument names.

liftQ :: Q a -> R a
liftQ = R . lift . lift . lift

expand :: Type -> R TypeOrPartial
expand (ForallT vars cxt t) = Type . ForallT vars cxt <$> expandType t
expand v@(VarT _) = return $ Type v
expand t@(ConT n) = do
  info <- liftQ $ reify n
  case info of
    TyConI (TySynD _ args body) -> partial [] args body
    TyConI (NewtypeD _ _ args con _) -> do
      let body = case con of
            NormalC _ [(_, f)] -> f
            RecC _ [(_, _, f)] -> f
            _ -> error "Impossible newtype constructor"
      partial [] args body
    _ -> return $ Type t
expand (AppT t1 t2) = do
  t1' <- expand t1
  case t1' of
    Type t1'' -> Type . AppT t1'' <$> expandType t2
    Partial env (arg:args) t1'' -> partial ((arg, t2) : env) args t1''
    _ -> error "Type synonym or newtype applied to too many arguments--this shouldn't happen"
expand t = return $ Type t

partial :: Env -> [Name] -> Type -> R TypeOrPartial
partial env [] t = do
  let t' = subst env t
  mCont <- asks (lookup (env, t))
  case mCont of
    Nothing -> callCC $ \cont -> local (((env, t), Continuation cont) :) $ expand t'
    Just (Continuation cont) -> do
      var <- liftQ $ newName "x"
      t'' <- local ((((env, t), Variable var) :) . filter (isVariable . snd)) $ expandType t'
      modify ((var, t'') :)
      cont $ Type (VarT var)
        where isVariable (Variable _) = True
              isVariable _ = False
    Just (Variable var) -> return $ Type (VarT var)
partial env args t = return $ Partial env args t

subst :: Env -> Type -> Type
subst env t@(ForallT vars _ _) = case vars `intersect` map fst env of
  [] -> t
  _ -> error "Huh?  A forall tried to bind a variable already in scope"
subst env t@(VarT v) = case lookup v env of
  Just t' -> t'
  _ -> t
subst env (AppT t1 t2) = AppT (subst env t1) (subst env t2)
subst _ t = t

expandType :: Type -> R Type
expandType t = do
  t' <- expand t
  case t' of
    Type t'' -> return t''
    _ -> error "Unexpected partially applied type synonym or newtype"

oldtype :: Type -> Q (Type, [(Name, Type)])
oldtype t = ((runR (expandType t) `runReaderT` []) `runContT` return) `runStateT` []
