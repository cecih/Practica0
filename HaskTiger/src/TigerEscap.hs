{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module TigerEscap where

import           Data.Functor.Identity
import qualified Data.Map.Strict       as M
import           Data.Maybe
import           Prelude               hiding (error, lookup)
import qualified Prelude               as P (error)
import           TigerAbs
import           TigerEnv
import           TigerErrores

import           TigerSymbol

import           Control.Monad         (when)
import           Control.Monad.Except
import           Control.Monad.Trans.Class
import           Control.Monad.State   (get, put)
import qualified Control.Monad.State   as ST

-- Debugging
import           Debug.Trace

data Errores =  NotFound Symbol
                | Interno Symbol

instance Show Errores where
    show (NotFound e) = "No se encuentra la variable "++ show e
    show (Interno e) = "Error interno " ++ show e

eappend (NotFound e) e1 = NotFound (append e e1)
eappend (Interno e) e1 = Interno (append e e1)

type Depth = Int
type Dat = (Int , Bool)
type Env = M.Map Symbol Dat
data Estado = S { lvl :: Int, env :: Env}
    deriving Show

data SEstado = Step { l :: Int, e :: [Env]}
    deriving Show

class (Daemon m, Monad m) => Escapator m where
    -- Depth Operators
    depth :: m Depth
    up :: m a -> m a
    -- Funciones cpor default, o de debugging
    -- debugging
    printEnv :: m () --
    -- errores
    -- putNum :: Pos -> Symbol -> m a
    -- putNum ln er = derror $ append er $ pack $ printPos ln
    raise :: Symbol -> m a
    raise = internal
    ---
    -- | Actualiza hardcore el entorno
    update :: Symbol -> Bool -> m ()
    -- | Busca el symbolo en el entorno
    lookup :: Symbol -> m (Maybe (Int, Bool))
    -- | Permite agregar variables a un entorno local.
    -- ```insert name esc computacion```
    -- computacion tiene un entorno[name -> esc]
    insert :: Symbol -> Bool -> m a -> m a

lookUpLvl :: (Escapator m) => Symbol -> m Int
lookUpLvl nm = lookup nm >>= (\case Nothing -> notfound nm
                                    Just (l, esc) -> return l
                             )

travVar :: (Escapator m) => Var -> m Var
travVar (SimpleVar s) = do
    lvl <- lookUpLvl s
    actLvl <- depth
    when (actLvl > lvl) (update s True)
    return (SimpleVar s)
travVar (FieldVar v p) = do
    v' <- travVar v -- v._
    return (FieldVar v' p)
travVar (SubscriptVar v e) = do
        v' <- travVar v
        e' <- travExp e
        return (SubscriptVar v' e')

travExp :: (Escapator m) => Exp -> m Exp
travExp (VarExp v p) = do
    v' <- adder (travVar v) (pack $ printPos p )
    return (VarExp v' p)
travExp (CallExp s args p) = do
    args' <- mapM travExp args
    return (CallExp s args' p)
travExp (OpExp l op r p) = do
    l' <- travExp l
    r' <- travExp r
    return (OpExp l' op r' p)
travExp (RecordExp es s p) = do
    es' <- mapM (\(s,e) -> do
                                e' <- travExp e
                                return (s,e')) es
    return (RecordExp es' s p)
travExp (SeqExp es p) = do
    es' <- mapM travExp es
    return (SeqExp es' p)
travExp (AssignExp v e p) = do
    v' <- adder (travVar v) (pack $ printPos p)
    e' <- travExp e
    return (AssignExp v' e' p)
travExp (IfExp c t Nothing p) = do
    c' <- travExp c
    t' <- travExp t
    return (IfExp c' t' Nothing p)
travExp (IfExp c t (Just e) p) = do
    c' <- travExp c
    t' <- travExp t
    e' <- travExp e
    return (IfExp c' t' (Just e') p)
travExp (WhileExp c b p) = do
    c' <- travExp c
    b' <- travExp b
    return (WhileExp c' b' p)
travExp (ForExp s e lo hi body p) = do
    lo' <- travExp lo
    hi' <- travExp hi
    -- body es analizado en un entorno expandido con s.
    body' <- insert s e (travExp body)
    return (ForExp s e lo' hi' body' p)
travExp (LetExp ds e p) = do
   (ds', e') <- travDecs ds ( do
                                e' <- travExp e
                                ds' <- mapM (\case
                                                (VarDec name _ typ exp p) -> do
                                                  chk <- lookup name
                                                  maybe (internal $ pack $ "666+1 -- Linea:" ++ show p)
                                                        (\(_,esc) -> return (VarDec name esc typ exp p)
                                                           ) chk
                                                l -> return l) ds
                                return (ds', e')
                            )
   return (LetExp ds' e' p)
travExp (ArrayExp typ size init p) = do
    s' <- travExp size
    init' <- travExp init
    return (ArrayExp typ s' init' p)
travExp v = return v

travF :: (Escapator m) => (Symbol,[Field], Maybe Symbol, Exp, Pos) -> m (Symbol,[Field], Maybe Symbol, Exp, Pos)
travF (name, params, res, body, p) = do
    (body', params') <- bulkInsert (map (\(a,b,_) -> (a,b)) params) (do
      body' <- travExp body
      ds' <- mapM (\(s,_,ty) -> do
                                mb <- lookup s
                                case mb of
                                    Nothing -> internal $ pack $ "666+2 -- Linea:" ++ show p
                                    Just (_,esc) -> return (s,esc,ty)) params
      return (body', ds'))
    return (name, params', res, body', p)

bulkInsert :: (Escapator m) => [(Symbol, Bool)] -> m a -> m a
bulkInsert xs m = foldr (\(name, esc) res -> insert name esc res) m xs

travDecs :: (Escapator m) => [Dec] -> m a -> m a
travDecs [] m = m
travDecs ((FunctionDec ls) : xs) m = do
  ls' <- up (mapM travF ls)
  travDecs xs m
travDecs ((VarDec name esc typ init p) : xs) m = do
  init' <- travExp init
  insert name esc (travDecs xs m)
travDecs (l : xs) m = travDecs xs m

-- initialSt :: Estado
-- initialSt = S 1 M.empty

-- calcularEsc :: Exp -> Exp
-- calcularEsc e = ST.evalState (travExp e) initialSt

-- showEnv :: Exp -> (Exp,Estado)
-- showEnv e = ST.runState (travExp e) initialSt

-- calcularEEsc :: Exp -> Either Errores Exp
-- calcularEEsc e = ST.evalStateT (travExp e) initialSt

-- initialStepper :: SEstado
-- initialStepper = Step 1 [M.empty]

-- debbugEnv :: Exp -> Either Errores (Exp,SEstado)
-- debbugEnv e = ST.runStateT (travExp e) initialStepper

-- type Mini = ExceptT Errores (ST.State Estado)
type Mini = ST.StateT Estado (Either Errores)

instance Daemon Mini where
  derror e  = throwError $ Interno $ pack ""
  adder w s = catchError w (\e -> throwError $ eappend e s)

instance Escapator Mini where
  depth = get >>= return . lvl
  up m = do
    old <- get
    put (old{lvl = lvl old + 1})
    m' <- m
    put old
    return m'
  update name esc = do
    est <- get
    (lvl, _) <- maybe (notfound name) return (M.lookup name (env est))
    ST.modify (\(S l env) -> S l (M.insert name (lvl, esc) env))
  lookup name = get >>= return . M.lookup name . env
  insert name esc m = do
    old <- get
    put old{env = M.insert name (lvl old, esc) (env old)}
    m' <- m
    put old
    return m'
  printEnv = get >>=  \env -> traceM $ "PrintEnv " ++ (show env)

initSt :: Estado
initSt = S 1 M.empty

calcularEEsc :: Exp -> Either Errores Exp
calcularEEsc e = ST.evalStateT (travExp e) initSt

