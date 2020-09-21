module Main where

import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Data.IORef
import Data.Map.Strict as M
import Data.STRef
import System.IO.Unsafe
import Control.Monad

type Varname = String

type Level = Int

-- level, gensymは手抜きでグローバル変数
-- 真面目にやるならStateなりSTなり使って
currentLevel :: IORef Int
currentLevel = unsafePerformIO do newIORef 1

enterLevel :: IO ()
enterLevel = do
  modifyIORef' currentLevel (+ 1)

leaveLevel :: IO ()
leaveLevel = do
  modifyIORef' currentLevel (\x -> x - 1)

genSymCount :: IORef Int
genSymCount = unsafePerformIO $ newIORef 0

genSym :: IO String
genSym = do
  x <- readIORef genSymCount
  modifyIORef' genSymCount (+ 1)
  pure $ show x

data Exp
  = Var Varname
  | App Exp Exp
  | Lam Varname Exp
  | Let Varname Exp Exp
  deriving (Show)

type Qname = String

data TV = Unbound String Level | Link Typ
  deriving (Show)

data Typ
  = TVar (IORef TV)
  | QVar Qname
  | TArrow Typ Typ
  deriving (Show)

type Env = M.Map Varname Typ

instance Show (IORef TV) where
  show ref = unsafePerformIO do show <$> readIORef ref

occurs :: IORef TV -> Typ -> IO ()
occurs tvref = 
  \case
    TVar tvref' -> do 
      when (tvref == tvref')
         $ error "occurs check"
      tvr' <- readIORef tvref'
      case tvr' of 
        Unbound s l' -> do
          tvr <- readIORef tvref
          min_level <- case tvr of 
                         Unbound _ l -> pure $ min l l' 
                         _ -> pure l'
          writeIORef tvref' $ Unbound s min_level
        Link ty -> occurs tvref ty
    TArrow tl tr -> do 
      occurs tvref tl
      occurs tvref tr
    _ -> pure ()

unify :: Typ -> Typ -> IO ()
unify (TVar tv) t' = do
  tv' <- readIORef tv
  case tv' of
    Unbound _ lvl -> do
      occurs tv t'
      writeIORef tv (Link t')
    Link t1 -> do
      unify t1 t'
unify t' t@(TVar tv) = unify t t'
unify (TArrow l1 l2) (TArrow r1 r2) = do
  unify l1 r1
  unify l2 r2

-- Typ内のQVarをgensymしたTVarにする
inst :: Typ -> IO Typ
inst ty = fst <$> go M.empty ty
  where
    go :: M.Map String Typ -> Typ -> IO (Typ, M.Map String Typ)
    go subst (QVar name) = case M.lookup name subst of
      Just x -> pure (x, subst)
      Nothing -> do
        tv <- newvar
        pure (tv, M.insert name tv subst)
    go subst (TVar ty) = do
      link <- readIORef ty
      case link of
        Link t -> go subst t
        Unbound s lvl -> pure (TVar ty, subst)
    go subst (TArrow l r) = do
      (lt, subst) <- go subst l
      (rt, subst) <- go subst r
      pure (TArrow lt rt, subst)

newvar :: IO Typ
newvar = do
  s <- genSym
  lvl <- readIORef currentLevel
  tv <- newIORef $ Unbound s lvl
  pure $ TVar tv

gen :: Typ -> IO Typ
gen (TVar tv) = do
  tv' <- readIORef tv
  current <- readIORef currentLevel
  case tv' of
    Unbound s lvl -> if lvl > current then pure do QVar s else pure do TVar tv
    Link t -> gen t
gen (TArrow l r) = do
  l' <- gen l
  r' <- gen r
  pure $ TArrow l' r'
gen t = pure t

typeof :: Env -> Exp -> IO Typ
typeof env (Var x) = inst (env M.! x)
typeof env (Lam x e) = do
  ty_x <- newvar
  ty_e <- typeof (M.insert x ty_x env) e
  pure $ TArrow ty_x ty_e
typeof env (App f x) = do
  ft <- typeof env f
  xt <- typeof env x
  rt <- newvar
  unify ft (TArrow xt rt)
  pure rt
typeof env (Let x e e2) = do
  enterLevel
  et <- typeof env e
  leaveLevel
  et' <- gen et
  e2t <- typeof (M.insert x et' env) e2
  typeof (M.insert x et' env) e2


-- これがないと TArrow (TVar Link (TVar Unbound "6" 1)) (TVar Unbound "6" 1) のようになる
-- fun x -> let f = fun a -> a in f x のケース参照
pathCompression :: Typ -> IO Typ
pathCompression t@(TVar tvref) = do 
   tv <- readIORef tvref
   case tv of 
     Link t' -> pathCompression t'
     _ -> pure t
pathCompression (TArrow l r) = TArrow <$> pathCompression l <*> pathCompression r
pathCompression t = pure t

main :: IO ()
main = do
  let e0 =
        Lam "x" (Var "x")
  print =<< pathCompression =<< typeof (M.empty) e0

  -- fun x -> let f = fun a -> a in f x
  let e1 =
        Lam
          "x"
          ( Let
              "f"
              (Lam "a" (Var "a"))
              (App (Var "f") (Var "x"))
          )
  print =<< pathCompression =<< typeof (M.empty) e1

  -- fun x -> let y = x in y
  let e2 =
        Lam
          "x"
          ( Let
              "y"
              (Var "x")
              (Var "y")
          )
  print =<< pathCompression =<< typeof (M.empty) e2

