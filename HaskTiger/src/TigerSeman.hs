{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}
module TigerSeman where

import           TigerAbs
import           TigerErrores         as E
import           TigerSres
import           TigerTips

import           TigerSymbol
import           PrintEnv

import           Control.Conditional as C ((<||>), ifM, unless, unlessM)
import           Control.Monad
import           Control.Monad.Error.Class
import           Control.Monad.Except (throwError, catchError)
import           Control.Monad.State
import           Data.List            as List
import qualified Data.Map.Strict      as M
import           Prelude              as P

import qualified Data.Graph           as G
import qualified Data.Text            as T
import Text.PrettyPrint.HughesPJ

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
    showVEnv :: w (IO ())
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
data EstadoG = G {unique :: Int, vEnv :: M.Map Symbol EnvEntry, tEnv :: M.Map Symbol Tipo}
    deriving Show

-- Acompañado de un tipo de errores
data SEErrores = NotFound T.Text | DiffVal T.Text | Internal T.Text
    deriving Show

type OurState = StateT EstadoG (Either SEErrores) 

errAppend :: SEErrores -> Symbol -> SEErrores
errAppend (NotFound t) s = NotFound (addStr (unpack t) s) 
errAppend (DiffVal t) s  = DiffVal (addStr (unpack t) s) 
errAppend (Internal t) s = Internal (addStr (unpack t) s) 

instance Daemon OurState where
  derror s   = throwError $ Internal s  
  adder  w s = catchError w (\e -> let ea = errAppend e s 
                                   in case ea of
                                        NotFound t -> notfound t
                                        DiffVal t  -> diffval t
                                        Internal t -> internal t)  

instance Manticore OurState where
  insertValV s ve w  = do st <- get
                          res <- withStateT (\st' -> st' {vEnv = M.insert s (Var ve) (vEnv st)}) w  
                          put st
                          return res
  insertFunV s fe w  = do st <- get
                          res <- withStateT (\st' -> st' {vEnv = M.insert s (Func fe) (vEnv st)}) w 
                          put st
                          return res 
  insertVRO s w      = insertValV s (TInt RO) w 
  insertTipoT s ty w = do st <- get
                          res <- withStateT (\st' -> st' {tEnv = M.insert s ty (tEnv st)}) w  
                          put st
                          return res 
  getTipoFunV s      = do st <- get
                          case M.lookup s (vEnv st) of
                            Just (Func f) -> return f 
                            Nothing       -> internal s   
  getTipoValV s      = do st <- get
                          case M.lookup s (vEnv st) of
                            Just (Var v) -> return v 
                            Nothing      -> internal s   
  getTipoT s         = do st <- get
                          case M.lookup s (tEnv st) of
                            Just ty -> return ty 
                            Nothing -> internal s   
  showVEnv           = do st <- get
                          return $ print $ concat (map (\(k, v) -> unpack k ++ renderEnv v) (M.toList $ vEnv st))    
  ugen               = do u <- get                             
                          put (u {unique = unique u + 1})
                          return $ unique u + 1 

-- Podemos definir el estado inicial como:
initConf :: EstadoG
initConf = G {unique = 0
            , tEnv = M.insert (T.pack "int") (TInt RW) (M.singleton (T.pack "string") TString)
            , vEnv = M.fromList
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
                      ]}

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
     let (x, y, z) = unzip3 (sortBy ourOrder flds)
     flds' <- mapM transTy z 
     return (TRecord (zip3 x flds' [0..length y]) u)
transTy (ArrayTy s)     = 
  do u  <- ugen
     s' <- getTipoT s
     return (TArray s' u) 

ourOrder :: (Eq a, Ord a) => (a, b, c) -> (a, b, c) -> Ordering
ourOrder (x1, _, _) (x2, _, _) = if x1 > x2 then GT else
                                     if x1 == x2 then EQ else LT

fromTy :: (Manticore w) => Ty -> w Tipo
fromTy (NameTy s) = getTipoT s
fromTy _ = P.error "no debería haber una definición de tipos en los args..."

-- Acá agregamos los tipos, clase 04/09/17
transDecs :: (Manticore w) => [Dec] -> w a -> w a
transDecs [] w                                      = w 
{-transDecs (FunctionDec fs : xs) w = 
  do
   t <- trDec (FunctionDec fs) w
   insertFunV w -}
transDecs (VarDec name  escape typ init' pos':xs) w = 
  do t <- trDec (VarDec name  escape typ init' pos') w --w Tipo
     insertValV name t (transDecs xs w)
transDecs (TypeDec ds:xs) w                         = 
  do trDec (TypeDec ds) w
     transDecs xs w
    

trDec :: (Manticore w) => Dec -> w a -> w Tipo
{-trDec (FunctionDec xs) w = 
 do venv' <- foldr (\(symb,params,result,body,pos) -> insdec symb params result body pos  w) [] xs
    tybodys <- map (\(_,_,_,body,_) -> transExp body) xs 
    return TUnit --Revisar -}
trDec (VarDec symb escape typ einit pos) w =
  do tyinit' <- transExp einit --w Tipo
     case typ of
       Nothing -> do b <- tiposIguales tyinit' TNil
                     if b then P.error "El tipo de la expresion no debe ser nil" else return tyinit'
       Just s  -> do t' <- transTy (NameTy s) --w Tipo
                     C.unlessM(tiposIguales tyinit' t') $ P.error "Los tipos son distintos"
                     return t'
trDec (TypeDec []) w                       = return TUnit                    
trDec (TypeDec ((sym,ty,pos):ds)) w        =
 do ty' <- transTy ty
    insertTipoT  sym ty' (trDec (TypeDec ds) w) 
  
                    
{-insdec :: Symbol -> [Field] -> Maybe Symbol -> Exp -> Pos  -> w a -> w a
insdec symb params result body pos w = 
  do
    params' <- map (\(sym,esc,ty) -> transTy ty) params
    result' <- case result of
                    Nothing -> TUnit
                    Just s  -> transTy (NameTy s)
    u       <- ugen                
    venv    <-  insertFunV symb (Func (u, pack symb, params', result',False)) w
    return venv --Revisar  -}

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
     C.unless (length args == length (thd tfunc)) $ P.error "Difiere en la cantidad de argumentos"
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
     return (if th' == TNil then el' else th')   
transExp(WhileExp co body p)      = 
  do co' <- transExp co
     C.unlessM (tiposIguales co' $ TInt RW) $ P.error "Error en la condición" 
     body' <- transExp body
     C.unlessM (tiposIguales body' TUnit) $ P.error "El cuerpo del while está retornando algún valor" 
     return TUnit
transExp(ForExp nv mb lo hi bo p) =
  do lo' <- transExp lo
     hi' <- transExp hi
     C.unlessM (tiposIguales lo' $ TInt RW) $ P.error "La cota inferior debe ser entera"
     C.unlessM (tiposIguales hi' $ TInt RW) $ P.error "La cota superior debe ser entera"
     bo' <- insertVRO nv (transExp bo)
     C.unlessM (tiposIguales bo' TUnit) $ P.error "El cuerpo del for está retornando algun valor"
     return TUnit 
transExp(LetExp dcs body p)       = transDecs dcs (transExp body)
transExp(BreakExp p)              = return TUnit -- Va gratis ;)
transExp(ArrayExp sn cant init p) =
  do u <- ugen
     sn'   <- getTipoValV sn
     cant' <- transExp cant
     C.unlessM (tiposIguales cant' $ TInt RW) $ P.error "El índice debe ser un entero"
     init' <- transExp init
     C.unlessM (tiposIguales sn' init') $ P.error "El tipo del init debe coincidir con el de la variable"
     return $ TArray sn' u
