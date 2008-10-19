module Untype (
  untype
  ) where

import Control.Applicative
import Control.Monad.Reader
import Data.List
import Data.Maybe
import Language.Haskell.TH.Syntax hiding (lift)

type Env = [(Name, Type)]
type R = ReaderT Env Q
data TypeOrPartial = Type Type | Partial Env [Name] Type
                                 -- a Type should not be a partially applied type synonym, but it can contain one.
                                 -- a Partial should have a nonempty list of argument names.

expand :: Type -> R TypeOrPartial
expand (ForallT vars cxt t) = Type . ForallT vars cxt <$> do
  checkUnbound vars
  expandType t
expand v@(VarT n) = do
  t <- asks (lookup n)
  case t of
    Just t' -> expand t'
    _ -> return $ Type v
expand t@(ConT n) = do
  info <- lift $ reify n
  case info of
    TyConI (TySynD _ args body) -> partial [] args body
    _ -> return $ Type t
expand (AppT t1 t2) = do
  t1' <- expand t1
  case t1' of
    Type t1'' -> Type . AppT t1'' <$> expandType t2
    Partial env (arg:args) t1'' -> partial ((arg, t2) : env) args t1''
    _ -> error "Type synonym applied to too many arguments--this shouldn't happen"
expand t = return $ Type t

checkUnbound :: [Name] -> R ()
checkUnbound vars = do
  scopeVars <- map fst <$> ask
  when (not . null $ vars `intersect` scopeVars) (error "Huh?  A forall tried to bind a variable already in scope")

partial :: Env -> [Name] -> Type -> R TypeOrPartial
partial env [] t = local (env ++) $ expand t
partial env args t = return $ Partial env args t

expandType :: Type -> R Type
expandType t = do
  t' <- expand t
  case t' of
    Type t'' -> return t''
    _ -> error "Unexpected partially applied type synonym"

untype :: Type -> Q Type
untype t = runReaderT (expandType t) []
