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
import           Control.Monad.Loops
import           Control.Monad.Error.Class
import           Control.Monad.Except (throwError, catchError)
import           Control.Monad.State
import           Data.List            as List
import qualified Data.Map.Strict      as M
import           Prelude              as P

import qualified Data.Graph           as G
import qualified Data.Text            as T
import qualified Data.Set             as S(fromAscList)
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
    showVEnv :: w () --debugtrace funcion para printear
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
    addTypos :: [(Symbol, Ty, Pos)] -> w a -> w a

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
  insertValV s ve w  = trace ("Insertamos Val " ++ unpack s) $ 
                       do st <- get
                          res <- withStateT (\st' -> st' {vEnv = M.insert s (Var ve) (vEnv st)}) w  
                          put st
                          return res
  insertFunV s fe w  = trace ("Insertamos Fun " ++ unpack s) $ 
                       do st <- get
                          res <- withStateT (\st' -> st' {vEnv = M.insert s (Func fe) (vEnv st)}) w 
                          put st
                          return res 
  insertVRO s w      = insertValV s (TInt RO) w 
  insertTipoT s ty w = trace ("Insertamos Tipo " ++ unpack s) $
                       do st <- get
                          res <- withStateT (\st' -> st' {tEnv = M.insert s ty (tEnv st)}) w  
                          put st
                          return res 
  getTipoFunV s      = trace ("Buscamos Fun " ++ unpack s) $ 
                       do st <- get
                          case M.lookup s (vEnv st) of
                            Just (Func f) -> return f 
                            Nothing       -> internal (append s (pack "44"))  
  getTipoValV s      = trace ("Buscamos Val " ++ unpack s) $ 
                       do st <- get
                          case M.lookup s (vEnv st) of
                            Just (Var v) -> return v 
                            Nothing      -> internal (append s (pack "55"))   
  getTipoT s         = trace ("Buscamos Tipo " ++ unpack s) $
                       do st <- get
                          case M.lookup s (tEnv st) of
                            Just ty -> return ty 
                            Nothing -> internal (append s (pack "66"))  
  showVEnv           = do st <- get
                          trace (show $ vEnv st) (return ())    
  showTEnv           = do st <- get
                          trace (show $ tEnv st) (return ())    
  ugen               = do u <- get                             
                          put (u {unique = unique u + 1})
                          return $ unique u + 1 
  addTypos tys w  = 
    {-let res  = trace ("Agregamos!") $ foldr replace w ref 
        recs = trace ("Recs!") $ foldr (insRecs frs) res rs' 
        refs = trace ("Refs!") $ foldr 
        insRefs recs ref
        in trace ("AddLoop!") $ addLoop ts m refs -}
    let addL ts ht = addLoop ts ht  
        refs e1    = foldr insRefs e1 ref
        recs e2    = foldr (insRecs frs) e2 rs'
        rep e3     = foldr replace e3 ref
    in do st <- get
          let m = tenvToList $ tEnv st
          addL (topoSort $ sim ++ m) (M.fromList $ sim ++ m) (refs (recs (rep w)))
    where (rs, tys')          = partition (\(x, y) -> isRecord y) (map (\(x, y, _) -> (x, y)) tys)
          (ref, sim)          = partition (\(x,y) -> elem (name y) frs) tys'
          rs'                 = map (\(s, ty) -> (s, sortBy ourOrder $ fList ty)) rs
          frs                 = map fst rs
          fList (RecordTy fl) = fl

name :: Ty -> Symbol
name (ArrayTy sym)  = sym
name (NameTy sym)   = sym
name _              = P.error "Error interno"                     

tenvToList :: M.Map Symbol Tipo -> [(Symbol, Ty)]
tenvToList m = map (\(symb, _) -> (symb, NameTy symb)) (M.toList m)   

insRefs :: Manticore w => (Symbol, Ty) -> w a -> w a
insRefs (symb, ty) w = trace "insRefs" $ insertTipoT symb (RefRecord $ name ty) w 

insRecs :: Manticore w => [Symbol] -> (Symbol, [Field]) -> w a -> w a
insRecs recs (symb, flds) w = trace "insRecs" $ do let (symbs, bools, tys) = unzip3 flds  
                                                   ty' <- mapM (\t -> let nt = name t
                                                                      in if elem nt recs then return $ RefRecord nt 
                                                                                         else getTipoT nt) tys
                                                   u   <- ugen
                                                   insertTipoT symb (TRecord (zip3 symbs ty' [0..length $ flds]) u) w 

replace :: Manticore w => (Symbol, Ty) -> w a -> w a
replace (symb, ty) w = trace "replace" $  do t <- getTipoT $ name ty
                                             insertTipoT symb t w 

isRecord :: Ty -> Bool
isRecord (RecordTy _) = True
isRecord _            = False

addLoop :: Manticore w => [Symbol] -> M.Map Symbol Ty -> w a -> w a 
addLoop sims m w = foldr (insTipo m) w sims

insTipo :: Manticore w => M.Map Symbol Ty -> Symbol -> w a -> w a
insTipo m symb w = do let ty = m M.! symb
                      ty' <- transTy ty
                      insertTipoT symb ty' w  
                                                   
topoSort :: [(Symbol, Ty)] -> [Symbol] 
topoSort elems 
  | ciclo ps elemsmap = P.error "Hay ciclo\n"
  | otherwise       = 
    fromEdges (G.topSort $ G.buildG (1, len) (toEdges ps m)) (M.toList m) 
  where ps       = filter (\(x, y) -> x /= y) (concat $ map predSucc elems)
        elemsmap = map head (group $ sort (map fst elems))
        len      = length elemsmap
        m        = M.fromList $ zip elemsmap [1..len]

toEdges :: [(Symbol, Symbol)] -> M.Map Symbol Int -> [G.Edge]
toEdges pares ht = map (\(x, y) -> (ht M.! x, ht M.! y)) pares

fromEdges :: [G.Vertex] -> [(Symbol, Int)] -> [Symbol]
fromEdges [] _     = []
fromEdges (x:xs) m = case find (\y -> x == snd y) m of
                       Nothing -> []
                       Just v  -> fst v : (fromEdges xs m)   

-- Arma pares pred/succ     
predSucc :: (Symbol, Ty) -> [(Symbol, Symbol)]
predSucc (sym, NameTy ns)   = [(ns, sym)]
predSucc (sym, ArrayTy as)  = [(as, sym)]
predSucc (sym, RecordTy fl) = concat $ map (\(s, _, t) -> case t of
                                                            RecordTy _ -> []
                                                            _          -> [(s, sym)]) fl

ciclo :: [(Symbol, Symbol)] -> [Symbol] -> Bool
ciclo pares elems = null $ preds pares elems
    where preds x y = y -??- map (\(f, s) -> s) x

infixl -?-
infixl -??-

(-?-) :: Eq a => [a] -> a -> [a]
[] -?- _    = []
(h:t) -?- e = if h == e then t -?- e else h : (t -?- e)

(-??-) :: Eq a => [a] -> [a] -> [a]
l1 -??- l2 = aux l1 l2

aux :: Eq a => [a] -> [a] -> [a]
aux l1 [] = l1
aux l1 l2 = if null rest then res1 else aux res1 rest   
  where rest = tail l2
        res1 = l1 -?- (head l2)

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
runLion :: Exp -> Either SEErrores Tipo
runLion e = evalStateT (transExp e) initConf

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
  
ourOrder :: (Eq a, Ord a) => (a, b, c) -> (a, b, c) -> Ordering
ourOrder (x1, _, _) (x2, _, _) = if x1 > x2 then GT else
                                     if x1 == x2 then EQ else LT  

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


fromTy :: (Manticore w) => Ty -> w Tipo
fromTy (NameTy s) = getTipoT s
fromTy _ = P.error "no debería haber una definición de tipos en los args..."

-- Acá agregamos los tipos, clase 04/09/17
transDecs :: (Manticore w) => [Dec] -> (w a -> w a)
transDecs ds w = foldr trDec w ds

trDec :: (Manticore w) => Dec -> w a -> w a
trDec (FunctionDec fs) w                   =
  let env' f m = foldr f m
      checkFs  = mapM_ (\(_ , params, result, body, _) ->
                         case result of
                           Nothing -> return ()
                           Just r  -> do tyb <- env' insVar (transExp body) params
                                         tyr <- getTipoT r 
                                         b   <- tiposIguales tyb tyr
                                         if b then return () 
                                           else P.error "El valor de retorno no tiene el tipo indicado en la signatura de la función")
  in checkFs fs >> env' insDec w fs 
trDec (VarDec symb escape typ einit pos) w =
  do tyinit' <- transExp einit --w Tipo
     case typ of
       Nothing -> do b <- tiposIguales tyinit' TNil
                     if b then P.error "El tipo de la expresion no debe ser nil\n" 
                            else insertValV symb tyinit' w  
       Just s  -> do t' <- transTy (NameTy s) --w Tipo
                     b  <- tiposIguales tyinit' t'
                     if not b then P.error (show tyinit' ++ show t' ++ " Los tipos son distintos\n") 
                              else insertValV symb t' w 
trDec (TypeDec ts) w                       = addTypos ts w                    

insVar :: Manticore w => (Symbol, Bool, Ty) -> w a -> w a
insVar (symb, _, ty) w = do ty' <- transTy ty
                            insertValV symb ty' w 

-- insdec toma la tupla de una funcion y el entorno de ese momento. Devolvemos
-- el entorno con la funcion y sus parametros agregados.
insDec :: (Manticore w) => (Symbol, [Field], Maybe Symbol, Exp, Pos) -> w a -> w a
insDec (symb, params, result, body, pos) w = 
  do params' <- mapM (\(sym,esc,ty) -> transTy ty) params
     u       <- ugen
     case result of --dado que result es un Maybe, analizo que tipo debo ingresar en el entorno
          Nothing -> insertFunV symb (u, symb, params', TUnit, False) w
          Just s  -> do t <- transTy (NameTy s)  
                        insertFunV symb (u, symb, params', t, False) w
                          

transExp :: (Manticore w) => Exp -> w Tipo
transExp (VarExp v p)             = addpos (transVar v) p
transExp (UnitExp {})             = return TUnit
transExp (NilExp {})              = return TNil
transExp (IntExp {})              = return $ TInt RW
transExp (StringExp {})           = return TString
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
transExp(RecordExp flds rt p)     = 
  do let (sym, e) = unzip $ sortBy  order' flds
     e' <- mapM transExp e
     u <- ugen
     return  $ TRecord (zip3 sym e' [0..length e]) u 
        where order' (sym1, _) (sym2, _)= if sym1 < sym2 then LT     else if sym1 > sym2 then GT else EQ 
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
  do u     <- ugen
     sn'   <- getTipoT sn
     cant' <- transExp cant
     C.unlessM (tiposIguales cant' $ TInt RW) $ P.error "El índice debe ser un entero"
     init' <- transExp init
     C.unlessM (tiposIguales (unwrap sn') init') $ P.error "El tipo del init debe coincidir con el de la variable"
     return sn'
  where unwrap (TArray t _) = t
