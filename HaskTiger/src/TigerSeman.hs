{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}
module TigerSeman where

import           TigerAbs
import           TigerErrores         as E
import           TigerSres
import           TigerTips

import           TigerSymbol

import           Control.Conditional  as C
import           Control.Monad
import           Control.Monad.Except (throwError)
import           Control.Monad.State
import           Data.List            as List
import qualified Data.Map.Strict      as M
import           Prelude              as P

import qualified Data.Graph           as G
import qualified Data.Text            as T

import           Debug.Trace

class (Daemon w, Monad w) => Manticore w where
  -- | Inserta una Variable al entorno
    insertValV :: Symbol -> ValEntry -> w a -> w a
  -- | Inserta una Función al entorno
    insertFunV :: Symbol -> FunEntry -> w a -> w a
  -- | Inserta una Variable de sólo lectura al entorno
    insertVRO :: Symbol -> w a -> w a
  -- | Inserta una variable de tipo al entorno
    insertTipoT :: Symbol -> Tipo -> w a -> w a
  -- | Busca una función en el entorno
    getTipoFunV :: Symbol -> w FunEntry
  -- | Busca una variable en el entorno
    getTipoValV :: Symbol -> w ValEntry
  -- NOTA: La busquedas de valores en los entorno
  -- no deberían fallar. Ya que se analizó en la etapa anterior.
  -- | Busca un tipo en el entorno
    getTipoT :: Symbol -> w Tipo
  -- | Funciones de Debugging!
    showVEnv :: w ()
    showTEnv :: w ()
    --
    -- | Función monadica que determina si dos tipos son iguales.
    -- 
    tiposIguales :: Tipo -> Tipo -> w Bool
    tiposIguales (RefRecord s) l@(TRecord _ u) = do
        st <- getTipoT s
        case st of
            TRecord _ u1 -> return (u1 == u)
            ls@(RefRecord s') -> tiposIguales ls l
            _ -> E.internal $ pack $ "No son tipos iguales... 123+1"
    tiposIguales l@(TRecord _ u) (RefRecord s) = do
        st <- getTipoT s
        case st of
            TRecord _ u1 -> return (u1 == u)
            ls@(RefRecord s') -> tiposIguales l ls
            _ -> E.internal $ pack $ "No son tipos iguales... 123+2"
    tiposIguales (RefRecord s) (RefRecord s') = do
        s1 <- getTipoT s
        s2 <- getTipoT s'
        tiposIguales s1 s2
    tiposIguales TNil  (RefRecord _) = return True
    tiposIguales (RefRecord _) TNil = return True
    tiposIguales (RefRecord _) _ = E.internal $ pack $ "No son tipos iguales... 123+3"
    tiposIguales  e (RefRecord s) = E.internal $ pack $ "No son tipos iguales... 123+4" ++ (show e ++ show s)
    tiposIguales a b = return (intiposIguales a b)
    --
    ugen :: w Unique -- unique generator
    --
    addTypos :: [(Symbol, Ty, Pos)] -> w ()

addpos :: (Daemon w, Show b) => w a -> b -> w a
addpos t p = E.adder t (pack $ show p)

-- Un ejemplo de estado que alcanzaría para realizar todas la funciones es:
data EstadoG = G {unique :: Int, vEnv :: [M.Map Symbol EnvEntry], tEnv :: [M.Map Symbol Tipo]}
    deriving Show

-- Acompañado de un tipo de errores
data SEErrores = NotFound T.Text | DiffVal T.Text | Internal T.Text
    deriving Show

type OurState = StateT EstadoG (Either SEErrores) 

instance Daemon OurState where
  derror s   = throwError $ Left  

-- Podemos definir el estado inicial como:
initConf :: EstadoG
initConf = G {unique = 0
            , tEnv = [M.insert (T.pack "int") (TInt RW) (M.singleton (T.pack "string") TString)]
            , vEnv = [M.fromList
                      [(T.pack "print", Func (1,T.pack "print",[TString], TUnit, True))
                      ,(T.pack "flush", Func (1,T.pack "flush",[],TUnit, True))
                      ,(T.pack "getchar",Func (1,T.pack "getchar",[],TString,True))
                      ,(T.pack "ord",Func (1,T.pack "ord",[TString],TInt RW,True)) -- Ojota con este intro...
                      ,(T.pack "chr",Func (1,T.pack "chr",[TInt RW],TString,True))
                      ,(T.pack "size",Func (1,T.pack "size",[TString],TInt RW,True))
                      ,(T.pack "substring",Func (1,T.pack "substring",[TString,TInt RW, TInt RW],TString,True))
                      ,(T.pack "concat",Func (1,T.pack "concat",[TString,TString],TString,True))
                      ,(T.pack "not",Func (1,T.pack "not",[TInt RW],TInt RW,True))
                      ,(T.pack "exit",Func (1,T.pack "exit",[TInt RW],TUnit,True))
                      ]]}

-- Utilizando alguna especie de run de la monada definida, obtenemos algo así
--runLion :: Exp -> Either SEErrores Tipo
--runLion e = run (transExp e) initConf

-- Un ejemplo de estado que alcanzaría para realizar todas la funciones es:
-- data EstadoG = G {unique :: Int, vEnv :: [M.Map Symbol EnvEntry], tEnv :: [M.Map Symbol Tipo]}
--     deriving Show
--
-- Acompañado de un tipo de errores
-- data SEErrores = NotFound T.Text | DiffVal T.Text | Internal T.Text
--     deriving Show
--
-- type OurState = State EstadoG (Either SEErrores Tipo)
--
-- instance Daemon OurState where
--   derror s = re
-- 
--
--
--  Podemos definir el estado inicial como:
-- initConf :: EstadoG
-- initConf = G {unique = 0
--             , tEnv = [M.insert (T.pack "int") (TInt RW) (M.singleton (T.pack "string") TString)]
--             , vEnv = [M.fromList
--                     [(T.pack "print", Func (1,T.pack "print",[TString], TUnit, True))
--                     ,(T.pack "flush", Func (1,T.pack "flush",[],TUnit, True))
--                     ,(T.pack "getchar",Func (1,T.pack "getchar",[],TString,True))
--                     ,(T.pack "ord",Func (1,T.pack "ord",[TString],TInt RW,True)) -- Ojota con este intro...
--                     ,(T.pack "chr",Func (1,T.pack "chr",[TInt RW],TString,True))
--                     ,(T.pack "size",Func (1,T.pack "size",[TString],TInt RW,True))
--                     ,(T.pack "substring",Func (1,T.pack "substring",[TString,TInt RW, TInt RW],TString,True))
--                     ,(T.pack "concat",Func (1,T.pack "concat",[TString,TString],TString,True))
--                     ,(T.pack "not",Func (1,T.pack "not",[TInt RW],TInt RW,True))
--                     ,(T.pack "exit",Func (1,T.pack "exit",[TInt RW],TUnit,True))
--                     ]]}
--
-- Utilizando alguna especie de run de la monada definida, obtenemos algo así
-- runLion :: Exp -> Either SEErrores Tipo
-- runLion e = run (transExp e) initConf

depend :: Ty -> [Symbol]
depend (NameTy s)    = [s]
depend (ArrayTy s)   = [s]
depend (RecordTy ts) = concatMap (\(_,_,t) -> depend t) ts


okOp :: Tipo -> Tipo -> Oper -> Bool
okOp TNil TNil EqOp  = False
okOp TUnit _ EqOp    = False
okOp _ _ EqOp        = True
okOp TNil TNil NeqOp = False
okOp TUnit _ NeqOp   = False
okOp _ _ NeqOp       = True

cmpZip :: (Manticore m) =>  [(Symbol, Tipo)] -> [(Symbol, Tipo, Int)] -> m Bool
cmpZip [] [] = return True
cmpZip [] _  = return False
cmpZip _ []  = return False
cmpZip ((sl,tl):xs) ((sr,tr,p):ys) = 
  do b <- tiposIguales tl tr
     if b  && (sl == sr) then cmpZip xs ys
       else return False

buscarM :: Symbol -> [(Symbol, Tipo, Int)] -> Maybe Tipo
buscarM s [] = Nothing
buscarM s ((s',t,_):xs) 
  | s == s' = Just t
  | otherwise = buscarM s xs

transVar :: (Manticore w) => Var -> w Tipo
transVar (SimpleVar s)      = getTipoValV s
transVar (FieldVar v s)     =
  do v' <- transVar v
     case v' of
       TRecord fields _ ->
         if not (null (filter (\(x, y, z) -> x == s) fields)) then return v'
           else P.error "El record no posee el campo deseado"       
       RefRecord text   ->
         P.error "Error interno" -- Nunca debería darse 
       _                ->
         P.error "No es un record"
transVar (SubscriptVar v e) =
  do v' <- transVar v
     case v' of
       TArray typ _ ->
         do e' <- transExp e 
            C.unlessM (tiposIguales e' (TInt RW)) $ P.error "La variable no es del tipo que se le quiere asignar"
            return typ
       _            ->
         P.error "No es un array"
          
transTy :: (Manticore w) => Ty -> w Tipo
transTy (NameTy s)      = getTipoT s
transTy (RecordTy flds) =
  do u <- ugen
     let (x, y, z) = unzip3 flds
     flds' <- mapM transTy z --TODO: ¿Qué int le asignamos?
     return (TRecord (zip3 x flds' [0..length y]) u)
transTy (ArrayTy s)     = 
  do u <- ugen
     s' <- getTipoT s
     return (TArray s' u) 

fromTy :: (Manticore w) => Ty -> w Tipo
fromTy (NameTy s) = getTipoT s
fromTy _ = P.error "no debería haber una definición de tipos en los args..."

-- Acá agregamos los tipos, clase 04/09/17
transDecs :: (Manticore w) => [Dec] -> w a -> w a
transDecs (FunctionDec{} : xs) = id
transDecs (VarDec{}: xs)       = id
transDecs (TypeDec{}: xs)      = id


transExp :: (Manticore w) => Exp -> w Tipo
transExp (VarExp v p)             = addpos (transVar v) p
transExp (UnitExp {})             = return TUnit
transExp (NilExp {})              = return TNil
transExp (IntExp {})              = return $ TInt RW
transExp (StringExp {})           = return TString
-- No podemos tener funciones con el mismo nombre como en Erlang
transExp (CallExp nm args p)      = 
  do tfunc <- getTipoFunV nm
     args' <- mapM transExp args
     C.unlessM (length args == thd tfunc) $ P.error "Difiere en la cantidad de argumentos"
     mapM_ (\(x, y) -> C.unlessM (tiposIguales x y) $ P.error "Error en los tipos de los argumentos") (zip args' (thd tfunc))
     return $ foth tfunc 
  where thd  (_, _, c, _, _) = c  
        foth (_, _, _, d, _) = d
transExp (OpExp el' oper er' p)   = 
  do -- Esta va gratis
    el <- transExp el'
    er <- transExp er'
    C.unlessM (tiposIguales el er) (P.error "Tipos diferentes")
    case oper of
      EqOp     -> do C.unless (okOp el er oper) (P.error ("Tipos no comparables " ++ show el ++ show er ++ show oper))
                     return $ TInt RW
      NeqOp    -> do C.unless (okOp el er oper) (P.error ("Tipos no comparables " ++ show el ++ show er ++ show oper))
                     return $ TInt RW
      PlusOp   -> do C.unlessM (tiposIguales el $ TInt RW) (P.error ("Tipo " ++ show el' ++ " no es un entero"))
                     return $ TInt RW
      MinusOp  -> do C.unlessM (tiposIguales el $ TInt RW) (P.error ("Tipo " ++ show el' ++ " no es un entero"))
                     return $ TInt RW
      TimesOp  -> do C.unlessM (tiposIguales el $ TInt RW) (P.error ("Tipo " ++ show el' ++ " no es un entero"))
                     return $ TInt RW
      DivideOp -> do C.unlessM (tiposIguales el $ TInt RW) (P.error ("Tipo " ++ show el' ++ " no es un entero"))
                     return $ TInt RW
      LtOp     -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                      (return $ TInt RW )
                      (P.error ("Elementos de tipo" ++ show el ++ "no son comparables"))
      LeOp     -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                      (return $ TInt RW)
                      (P.error ("Elementos de tipo" ++ show el ++ "no son comparables"))
      GtOp     -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                      (return $ TInt RW )
                      (P.error ("Elementos de tipo" ++ show el ++ "no son comparables"))
      GeOp     -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                      (return $ TInt RW)
                      (P.error ("Elementos de tipo" ++ show el ++ "no son comparables"))
transExp(RecordExp flds rt p)     = return TUnit -- Completar
transExp(SeqExp es p)             = 
  do -- Va gratis
    es' <- mapM transExp es
    return $ last es'
transExp(AssignExp var val p)     = 
  do tvar <- transVar var
     tval <- transExp val
     C.unlessM (tiposIguales tvar tval) $ P.error "La variable no es del tipo que se le quiere asignar"
     return TUnit 
transExp(IfExp co th Nothing p)   = 
  do co' <- transExp co
     C.unlessM (tiposIguales co' $ TInt RW) $ P.error "Error en la condición"
     th' <- transExp th
     C.unlessM (tiposIguales th' TUnit) $ P.error "La expresión del then no es de tipo unit"
     return TUnit
transExp(IfExp co th (Just el) p) = 
  do co' <- transExp co
     C.unlessM (tiposIguales co' $ TInt RW) $ P.error "Error en la condición"
     th' <- transExp th
     el' <- transExp el
     C.unlessM (tiposIguales th' el') $ P.error "Las ramas del if difieren en el tipo" 
     return th' --FIXME: ver valor de retorno 
transExp(WhileExp co body p)      = 
  do co' <- transExp co
     C.unlessM (tiposIguales co' $ TInt RO) $ P.error "Error en la condición" --TODO: chequear el RO
     body' <- transExp body
     C.unlessM (tiposIguales body' TUnit) $ P.error "El cuerpo del while está retornando algún valor" 
     return TUnit
transExp(ForExp nv mb lo hi bo p) = return TUnit -- Completar
transExp(LetExp dcs body p)       = transDecs dcs (transExp body)
transExp(BreakExp p)              = return TUnit -- Va gratis ;)
transExp(ArrayExp sn cant init p) = return TUnit -- Completar
