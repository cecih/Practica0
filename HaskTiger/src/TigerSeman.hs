{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}

module TigerSeman where

import           PrintEnv
import           TigerAbs
import           TigerErrores         as E
import           TigerFrame
import           TigerSres
import           TigerSymbol
import           TigerTrans           as Trans
import           TigerTemp
import           TigerTips

import           Control.Conditional as C ((<||>), ifM, unless, unlessM)
import           Control.Monad
import           Control.Monad.Error.Class
import           Control.Monad.Except (throwError, catchError)
import           Control.Monad.Loops
import           Control.Monad.State
import qualified Data.Graph           as G
import           Data.Maybe (isJust, fromJust)
import           Data.List as List
import qualified Data.Map.Strict as M
import qualified Data.Set             as S(fromAscList)
import qualified Data.Text            as T
import           Debug.Trace
import           Prelude as P
import           Text.PrettyPrint.HughesPJ

-- \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\ --
-- Definimos tipos de datos, monadas e instancias --
-- ////////////////////////////////////////////// --

-- Daemon ya esta definida en TigerErrores
addpos :: (Daemon w, Show b) => w a -> b -> w a
addpos t p = E.adder t (pack $ show p)

-- Un ejemplo de estado que alcanzaría para realizar todas la funciones es:
data EstadoG = G {unique :: Int, 
                  vEnv :: M.Map Symbol EnvEntry, 
                  tEnv :: M.Map Symbol Tipo,
                  auxEnv :: M.Map Symbol Tipo}
    deriving Show

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
                      ]
            , auxEnv = M.empty}



type OurState = StateT EstadoG (Either SEErrores) 

instance Daemon OurState where
  derror e   = throwError e  
  notfound s = derror $ ENotFound $ addStr "Not found: " s
  diffval s  = derror $ EDiffVal $ addStr "Different values: " s
  internal s = derror $ EInternal $ addStr "Internal: " s
  user s     = derror $ EUser $ addStr "User: " s
  adder  w s = catchError w (\e -> let ea = errAppend e s 
                                   in case ea of
                                        ENotFound t -> notfound t
                                        EDiffVal t  -> diffval t
                                        EInternal t -> internal t
                                        EUser t     -> user t)  

errAppend :: SEErrores -> Symbol -> SEErrores
errAppend (ENotFound t) s = ENotFound $ addStr (unpack t) s 
errAppend (EDiffVal t) s  = EDiffVal $ addStr (unpack t) s 
errAppend (EInternal t) s = EInternal $ addStr (unpack t) s 
errAppend (EUser t) s     = EUser $ addStr (unpack t) s 

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
  -- | Función monadica que determina si dos tipos son iguales.
  tiposIguales :: Tipo -> Tipo -> w Bool
  tiposIguales (RefRecord s) l@(TRecord _ u) = 
    do st <- getTipoT s
       case st of
         TRecord _ u1 -> return (u1 == u)
         ls@(RefRecord s') -> tiposIguales ls l
         _ -> E.internal $ pack $ "No son tipos iguales... 123+1"
  tiposIguales l@(TRecord _ u) (RefRecord s) = 
    do st <- getTipoT s
       case st of
         TRecord _ u1 -> return (u1 == u)
         ls@(RefRecord s') -> tiposIguales l ls
         _ -> E.internal $ pack $ "No son tipos iguales... 123+2"
  tiposIguales (RefRecord s) (RefRecord s') = 
    do s1 <- getTipoT s
       s2 <- getTipoT s'
       tiposIguales s1 s2
  tiposIguales TNil  (RefRecord _) = return True
  tiposIguales (RefRecord _) TNil = return True
  tiposIguales (RefRecord _) _ = E.internal $ pack $ "No son tipos iguales... 123+3"
  tiposIguales  e (RefRecord s) = E.internal $ pack $ "No son tipos iguales... 123+4" ++ (show e ++ show s)
  tiposIguales a b = return (intiposIguales a b)
  -- | Unique generator
  ugen :: w Unique 
  -- | Funcion auxiliar para agregar tipos
  addTypos :: [(Symbol, Ty, Pos)] -> w a -> w a

instance Manticore OurState where
  insertValV s ve w  = trace ("Insertamos Val " ++ unpack s) $ 
                       do st  <- get
                          res <- withStateT (\st' -> st' {vEnv = M.insert s (Var ve) (vEnv st)}) w  
                          put st
                          return res
  insertFunV s fe w  = trace ("Insertamos Fun " ++ unpack s) $ 
                       do st  <- get
                          res <- withStateT (\st' -> st' {vEnv = M.insert s (Func fe) (vEnv st)}) w 
                          put st
                          return res 
  insertVRO s w      = insertValV s (TInt RO, InFrame 0, 0) w 
  insertTipoT s ty w = trace ("Insertamos Tipo " ++ unpack s) $
                       do st  <- get
                          res <- withStateT (\st' -> st' {tEnv = M.insert s ty (tEnv st)}) w  
                          put st
                          return res 
  getTipoFunV s      = trace ("Buscamos Fun " ++ unpack s) $ 
                       do st <- get
                          case M.lookup s (vEnv st) of
                            Just (Func f) -> return f 
                            Nothing       -> notfound $ pack $ "La funcion " ++ (unpack s) ++ " no esta definida"  
  getTipoValV s      = trace ("Buscamos Val " ++ unpack s) $ 
                       do st <- get
                          case M.lookup s (vEnv st) of
                            Just (Var v) -> return v 
                            Nothing      -> internal $ pack $ "La variable " ++ (unpack s) ++ " no esta en el entorno"   
                            other        -> user $ pack $ (show $ fromJust other) ++ " no es una variable" 
  getTipoT s         = trace ("Buscamos Tipo " ++ unpack s) $
                       do st <- get
                          case M.lookup s (tEnv st) of
                            Just ty -> return ty 
                            Nothing -> internal $ pack $ "El tipo " ++ (unpack s) ++ " no esta en el entorno" 
  showVEnv           = do st <- get
                          trace (show $ vEnv st) (return ())    
  showTEnv           = do st <- get
                          trace (show $ tEnv st) (return ())    
  ugen               = do u <- get                             
                          put (u {unique = unique u + 1})
                          return $ unique u + 1 
  addTypos tys w     = insHeaders tys' (insBodys  tys' w)
    where tys' = M.fromList $ map (\(x, y, z) -> (x, y)) tys
  
-- Insertamos todos los bodys de los tipos
insBodys :: Manticore w => M.Map Symbol Ty -> w a -> w a
insBodys tys w = 
  M.foldrWithKey (\k ty man -> 
                   do t <- getTipoT k
                      case isRefRecord t of
                        True  -> 
                          either (\n -> do tn <- getTipoT n --transTy n
                                           insertTipoT n tn man) 
                                 (\fs -> foldr
                                         (\(sym, b, tyf) manf -> do tf <- transTy tyf
                                                                    insertTipoT sym tf manf) 
                                         man
                                         fs) 
                                 (stripTy ty)  
                        False -> w) w tys
 
stripTy :: Ty -> Either Symbol [Field]
stripTy (NameTy name)     = Left name
stripTy (ArrayTy name)    = Left name
stripTy (RecordTy fields) = Right fields

-- Funcion auxiliar
isRefRecord :: Tipo -> Bool
isRefRecord (RefRecord _) = True
isRefRecord _             = False

-- Insertamos todos los headers
insHeaders :: Manticore w => M.Map Symbol Ty -> w a -> w a
insHeaders tys w = M.foldrWithKey (\k ty man -> do t <- insHeader k ty tys 
                                                   insertTipoT k t man) w tys

-- Insertamos un unico header
insHeader :: Manticore w => Symbol -> Ty -> M.Map Symbol Ty -> w Tipo 
insHeader name nam@(NameTy sym) tys          
  | M.member sym tys = return $ RefRecord T.empty 
  | otherwise        = transTy nam 
insHeader name rec@(RecordTy fields) tys 
  | or $ map (\(x, y, z) -> x == name || M.member x tys) fields = return $ RefRecord T.empty   
  | otherwise                                                   = transTy rec  
insHeader name arr@(ArrayTy sym) tys    
  | M.member sym tys = return $ RefRecord T.empty 
  | otherwise        = transTy arr

-- Funcion auxiliar para escribir menos
insRefRecord :: Manticore w => Symbol -> w a -> w a
insRefRecord name w = insertTipoT name (RefRecord T.empty) w

ourOrder :: (Eq a, Ord a) => (a, b, c) -> (a, b, c) -> Ordering
ourOrder (x1, _, _) (x2, _, _) = if x1 > x2 then GT else
                                     if x1 == x2 then EQ else LT  

-- Utilizando alguna especie de run de la monada definida, obtenemos algo así
runLion :: Exp -> Either SEErrores Tipo
runLion e = P.error "Estoy testeando, no hinchei" --evalStateT (transExp e) initConf

-- \\\\\\\\\\\\\\\\\\\\\\\ --
-- Traduccion de variables --
-- /////////////////////// --

-- El objetivo de esta función es obtener el tipo
-- de la variable a la que se está accediendo
transVar :: (MemM w, Manticore w) => Var -> w (BExp, Tipo)
transVar (SimpleVar s)      = do (t, acc, lv) <- getTipoValV s
                                 bexp         <- simpleVar acc lv 
                                 return (bexp, t)
-- TODO: sacar el nombre de la fieldvar?
transVar (FieldVar v s)     =
  do (bexp, v') <- transVar v
     case v' of
       TRecord fields _ ->
         let res = filter (\(x, y) -> x == s) (map (\(x, y, z) -> (x, y)) fields)
         in if not $ null res then return $ (bexp, snd (head res))
              else user $ pack "El record no posee el campo deseado"       
       RefRecord text   ->
         internal $ pack "Error interno" -- Nunca debería darse 
       _                ->
         internal $ pack "No es un record"
transVar (SubscriptVar v e) =
  do (bexp, v') <- transVar v
     case v' of
       TArray typ _ ->
         do (be, te) <- transExp e 
            C.unlessM (tiposIguales te (TInt RW)) $ user $ pack "El indice no es un entero"
            return (bexp, typ)
       _            ->
         user $ pack "La variable a la cual se intenta acceder no es un array"
          
-- \\\\\\\\\\\\\\\\\\\ --
-- Traduccion de tipos --
-- /////////////////// --

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

fromTy :: (Manticore w) => Ty -> w Tipo
fromTy (NameTy s) = getTipoT s
fromTy _          = user $ pack "No debería haber una definición de tipos en los args..."

-- \\\\\\\\\\\\\\\\\\\\\\\\\\\ --
-- Traduccion de declaraciones --
-- /////////////////////////// --

transDecs dcs w 
  | isInterrupted dcs             = user $ pack "Se corta el batch de definiciones consecutivas" 
  | or $ map hasRepeatedNames dcs = user $ pack "Hay nombres repetidos en algun batch de definiciones consecutivas"
  | otherwise                     = foldr trDec w dcs

hasRepeatedNames :: Dec -> Bool
hasRepeatedNames dec = or $ map (\x -> elem x (names \\ [x])) names
  where names = getNamesDec dec
 
-- Chequeamos si hay una interrupcion en la definicion de funciones o tipos
-- mutuamente recursivos
isInterrupted :: [Dec] -> Bool
isInterrupted [] = False
isInterrupted (d:dcs)
  | isFunc d = or $ map (referencesAnother dcs) (concat $ map getCalls (stripFunc d)) -- Funciones llamadas en d 
  | isVar d  = False
  | isType d = or $ map (referencesAnother dcs) (concat $ map getTys (stripType d)) -- Tipos referenciados en d
 
referencesAnother :: [Dec] -> Symbol -> Bool
referencesAnother dcs name = elem name $ concat $ map getNamesDec dcs
 
getNamesDec :: Dec -> [Symbol]
getNamesDec (FunctionDec f)       = map (\(a, _, _, _, _) -> a) f
getNamesDec (VarDec name _ _ _ _) = [name]
getNamesDec (TypeDec t)           = map (\(a, _, _) -> a) t
 
-- Obtenemos las llamadas de funcion realizadas en una expresion
-- Lo uso para analizar las llamadas a otras funciones dentro del body
-- de una funcion
getCalls :: Exp -> [Symbol]
getCalls (VarExp _ _)            = []
getCalls (UnitExp _)             = []
getCalls (BreakExp _)            = []
getCalls (NilExp _)              = []
getCalls (IntExp _ _)            = []
getCalls (StringExp _ _)         = []
getCalls (CallExp name exps _)   = name : (concat $ map getCalls exps)  
getCalls (OpExp e1 _ e2 _)       = getCalls e1 ++ getCalls e2
getCalls (RecordExp flds _ _)    = concat $ map (\(s, e) -> getCalls e) flds
getCalls (SeqExp exps _)         = concat $ map getCalls exps
getCalls (AssignExp _ e _)       = getCalls e
getCalls (IfExp e1 e2 e3 _)
  | isJust e3 = mixCalls ++ getCalls (fromJust e3) 
  | otherwise = mixCalls
  where mixCalls = getCalls e1 ++ getCalls e2
getCalls (WhileExp e1 e2 _)      = getCalls e1 ++ getCalls e2
getCalls (ForExp _ _ e1 e2 e3 _) = getCalls e1 ++ getCalls e2 ++ getCalls e3
getCalls (LetExp _ e _)          = getCalls e
getCalls (ArrayExp _ e1 e2 _)    = getCalls e1 ++ getCalls e2
 
getTys :: Ty -> [Symbol]
getTys (NameTy name)  = [name]
getTys (RecordTy f)   = concat $ map (\(sym, _, ty) -> sym : (getTys ty)) f  
getTys (ArrayTy name) = [name]
 
-- Funciones auxiliares
stripFunc :: Dec -> [Exp]
stripFunc (FunctionDec f) = map (\(_, _, _, d, _) -> d) f
 
stripType :: Dec -> [Ty]
stripType (TypeDec t) = map (\(_, b, _) -> b) t
 
isFunc :: Dec -> Bool
isFunc (FunctionDec _) = True
isFunc _               = False
 
isVar :: Dec -> Bool
isVar (VarDec _ _ _ _ _) = True
isVar _                  = False
 
isType :: Dec -> Bool
isType (TypeDec _) = True
isType _           = False

trDec :: (MemM w, Manticore w) => Dec -> w a -> w a
trDec (FunctionDec fs) w                   =
  let checkFs    = foldr (\(name , params, result, body, _) w' ->
                           case result of
                             Nothing -> w'
                             Just r  -> 
                               do (tyb, tyt) <- foldr insVar (transExp body) params
                                  tyr        <- getTipoT r 
                                  b          <- tiposIguales tyt tyr
                                  if b then w' 
                                    else user $ pack $ "El valor de retorno de la funcion"
                                                        ++ (unpack name) 
                                                        ++ "no tiene el tipo indicado en la signatura de la función")
  in foldr insDec (checkFs w fs) fs  
trDec (VarDec symb escape typ einit pos) w =
  do (binit, tyinit') <- transExp einit 
     case typ of
       Nothing -> if isNil tyinit' then user $ pack $ "La variable " ++ (unpack symb) ++ " no puede inicializarse en nil" 
                    else do lvl <- getActualLevel
                            acc <- Trans.allocLocal False --FIXME: ¿A donde metemos la variable?
                            insertValV symb (tyinit', acc, lvl) w  
       Just s  -> do t' <- transTy (NameTy s) --w Tipo
                     b  <- tiposIguales tyinit' t'
                     if not b then user $ pack $ show tyinit' ++ show t' ++ " Los tipos son distintos\n" 
                              else do lvl <- getActualLevel
                                      acc <- Trans.allocLocal False --FIXME: ¿A donde metemos la variable?
                                      insertValV symb (t', acc, lvl) w 
  where isNil TNil = True
        isNil _    = False --TODO: CHEQUEAR ESTA FUNCION GRONCHA
trDec (TypeDec ts) w                       = addTypos ts w                    

insVar :: (MemM w, Manticore w) => (Symbol, Bool, Ty) -> w a -> w a
insVar (symb, _, ty) w = do ty' <- transTy ty
                            lvl <- getActualLevel
                            acc <- Trans.allocLocal False --FIXME: ¿A donde metemos la variable?
                            insertValV symb (ty', acc, lvl) w

-- insdec toma la tupla de una funcion y el entorno de ese momento. Devolvemos
-- el entorno con la funcion y sus parametros agregados.
--type FunEntry = (Level, Label, [Tipo], Tipo, Bool)
insDec :: (Manticore w) => (Symbol, [Field], Maybe Symbol, Exp, Pos) -> w a -> w a
insDec (symb, params, result, body, pos) w = 
  do params' <- mapM (\(sym,esc,ty) -> transTy ty) params
     u       <- ugen -- TODO: debemos cambiarlo por tipo level que es una lista de [(Frame, Int)]. 
                       -- Level seria como el stack en todo momento
     case result of --dado que result es un Maybe, analizo que tipo debo ingresar en el entorno
          Nothing -> insertFunV symb (u, symb, params', TUnit, False) w
          Just s  -> do t <- transTy (NameTy s)  
                        insertFunV symb (u, symb, params', t, False) w
                          
-- \\\\\\\\\\\\\\\\\\\\\\\\\ --
-- Traduccion de expresiones --
-- ///////////////////////// --

transExp :: (MemM w, Manticore w) => Exp -> w (BExp, Tipo)
transExp (VarExp v p)             = addpos (transVar v) p
transExp (UnitExp {})             = do bexp <- unitExp
                                       return (bexp, TUnit)
transExp (NilExp {})              = do bexp <- nilExp
                                       return (bexp, TNil)
transExp (IntExp i _)             = do bexp <- intExp i
                                       return (bexp, TInt RW)
transExp (StringExp s _)          = do bexp <- stringExp (pack s)
                                       return (bexp, TString)
--TODO: hacer esto! ¿Que hago con los argumentos?
{-transExp (CallExp name args p)      = 
  do tfunc <- getTipoFunV name
     args' <- mapM transExp args  
     C.unless (length args == length (thd tfunc)) $ P.error "Difiere en la cantidad de argumentos"
     mapM_ (\((x, y), z) -> C.unlessM (tiposIguales y z) $ P.error "Error en los tipos de los argumentos") 
           (zip args' (thd tfunc))
     lvl  <- mapM () args'
     cexp <- callExp name False False lvl (map fst args') --FIXME: ¿Que son los bools?
     return $ (cexp, foth tfunc) 
  where thd  (_, _, c, _, _) = c  
        foth (_, _, _, d, _) = d
-}
transExp (OpExp el' oper er' p)   = 
  do -- Esta va gratis
    (bel, el) <- transExp el'
    (ber, er) <- transExp er'
    C.unlessM (tiposIguales el er) (user $ pack $ "Los tipos de los operandos difieren")
    case oper of
      EqOp     -> do C.unless (okOp el er oper) (user $ pack $ "Tipos no comparables " ++ show el ++ show er ++ show oper)
                     bexp <- binOpIntRelExp bel oper ber
                     return (bexp, TInt RW)
      NeqOp    -> do C.unless (okOp el er oper) (user $ pack $ "Tipos no comparables " ++ show el ++ show er ++ show oper)
                     bexp <- binOpIntRelExp bel oper ber
                     return (bexp, TInt RW)
      PlusOp   -> do C.unlessM (tiposIguales el $ TInt RW) (user $ pack $ "Tipo " ++ show el' ++ " no es un entero")
                     bexp <- binOpIntExp bel oper ber
                     return (bexp, TInt RW)
      MinusOp  -> do C.unlessM (tiposIguales el $ TInt RW) (user $ pack $ "Tipo " ++ show el' ++ " no es un entero")
                     bexp <- binOpIntExp bel oper ber
                     return (bexp, TInt RW)
      TimesOp  -> do C.unlessM (tiposIguales el $ TInt RW) (user $ pack $ "Tipo " ++ show el' ++ " no es un entero")
                     bexp <- binOpIntExp bel oper ber
                     return (bexp, TInt RW)
      DivideOp -> do C.unlessM (tiposIguales el $ TInt RW) (user $ pack $ "Tipo " ++ show el' ++ " no es un entero")
                     bexp <- binOpIntExp bel oper ber
                     return (bexp, TInt RW)
      LtOp     -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                      (do bexp <- binOpIntRelExp bel oper ber
                          return (bexp, TInt RW))
                      (user $ pack $ "Elementos de tipo" ++ show el ++ "no son comparables")
      LeOp     -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                      (do bexp <- binOpIntRelExp bel oper ber
                          return (bexp, TInt RW))
                      (user $ pack $ "Elementos de tipo" ++ show el ++ "no son comparables")
      GtOp     -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                      (do bexp <- binOpIntRelExp bel oper ber
                          return (bexp, TInt RW))
                      (user $ pack $ "Elementos de tipo" ++ show el ++ "no son comparables")
      GeOp     -> ifM ((tiposIguales el $ TInt RW) <||> (tiposIguales el TString))
                      (do bexp <- binOpIntRelExp bel oper ber
                          return (bexp, TInt RW))
                      (user $ pack $ "Elementos de tipo" ++ show el ++ "no son comparables")
transExp(RecordExp flds rt p)     = 
  do let (sym, e) = unzip $ sortBy  order' flds
     e' <- mapM transExp e
     id <- getTipoT rt
     bexp <- recordExp $ zip (map fst e') [0..length e]
     return (bexp, TRecord (zip3 sym (map snd e') [0..length e]) (getId id)) 
        where order' (sym1, _) (sym2, _) = if sym1 < sym2 then LT 
                                             else if sym1 > sym2 then GT
                                                    else EQ 
              getId (TRecord _ u)        = u
transExp(SeqExp es p)             = 
  do -- Va gratis
    es' <- mapM transExp es
    return $ last es'
transExp(AssignExp var val p)     = 
  do (bvar, tvar) <- transVar var
     (bval, tval) <- transExp val
     C.unlessM (tiposIguales tvar tval) $ user $ pack "La variable no es del tipo que se le quiere asignar"
     bexp <- assignExp bvar bval
     return (bexp, TUnit) 
transExp(IfExp co th Nothing p)   = 
  do (bco', co') <- transExp co
     C.unlessM (tiposIguales co' $ TInt RW) $ user $ pack "La variable de la condicion del if no es de tipo entero"
     (bth', th') <- transExp th
     C.unlessM (tiposIguales th' TUnit) $ user $ pack "La expresión del then no es de tipo unit"
     bexp       <- ifThenExp bco' bth'
     return (bexp, TUnit)
transExp(IfExp co th (Just el) p) = 
  do (bco', co') <- transExp co
     C.unlessM (tiposIguales co' $ TInt RW) $ user $ pack "La variable de la condicion del if no es de tipo entero"
     (bth', th') <- transExp th
     (bel', el') <- transExp el
     C.unlessM (tiposIguales th' el') $ user $ pack "Las ramas del if difieren en el tipo" 
     if th' == TUnit then do iexp <- ifThenElseExpUnit bco' bth' bel' 
                             return (iexp, TUnit)
       else do iexp <- ifThenElseExp bco' bth' bel'
               return (iexp, if th' == TNil then el' else th')
transExp(WhileExp co body p)      =
  do (bco', co') <- transExp co
     C.unlessM (tiposIguales co' $ TInt RW) $ user $ pack "La expresion de la condicion del while no es de tipo entero"
     preWhileforExp
     (bbo, body') <- transExp body
     C.unlessM (tiposIguales body' TUnit) $ user $ pack "El cuerpo del while está retornando algún valor"
     posWhileforExp
     bexp <- whileExp bco' bbo
     return (bexp, TUnit)
{-transExp(ForExp namev mb lo hi body p) =
  do (blo, lo') <- transExp lo
     (bhi, hi') <- transExp hi
     C.unlessM (tiposIguales lo' $ TInt RW) $ P.error "La cota inferior debe ser entera"
     C.unlessM (tiposIguales hi' $ TInt RW) $ P.error "La cota superior debe ser entera"
     preWhileforExp
     (bbody, tbody) <- insertVRO namev (transExp body)
     C.unlessM (tiposIguales tbody TUnit) $ P.error "El cuerpo del for está retornando algun valor"
     posWhileforExp
     --bnv <- alguna funcion de codigo intermedio relacionado con nv revisar TODO
     fexp <- forExp blo bhi bnv bbody 
     return (bexp, TUnit) 
-}
transExp(LetExp dcs body p)       = transDecs dcs (transExp body)
transExp(BreakExp p)              = do bexp <- breakExp
                                       return (bexp, TUnit)
transExp(ArrayExp name cant init p) =
  do u     <- ugen
     name' <- getTipoT name
     (bcant, tcant) <- transExp cant
     C.unlessM (tiposIguales tcant $ TInt RW) $ user $ pack "El índice de acceso al array debe ser un entero"
     (binit, tinit) <- transExp init
     C.unlessM (tiposIguales (unwrap name') tinit) $ user $ pack "El tipo del init debe coincidir con el de la variable para el array"
     bexp <- arrayExp bcant binit
     return (bexp, name')
  where unwrap (TArray t _) = t

okOp :: Tipo -> Tipo -> Oper -> Bool
okOp TNil TNil EqOp  = False
okOp TUnit _ EqOp    = False
okOp _ _ EqOp        = True
okOp TNil TNil NeqOp = False
okOp TUnit _ NeqOp   = False
okOp _ _ NeqOp       = True










