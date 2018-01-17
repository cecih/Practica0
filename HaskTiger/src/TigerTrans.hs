{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module TigerTrans where

import qualified Control.Monad.State as ST
import           Prelude             hiding (EQ, GT, LT, error, exp, seq)
import qualified Prelude             as P (error)
import qualified TigerAbs            as Abs
import           TigerEnv
import           TigerErrores
import           TigerFrame          as F
import           TigerSymbol         as T
import           TigerTemp
import           TigerTree

import           Control.Monad
import qualified Data.Foldable       as Fold
import           Data.List           as List
import           Data.Ord            hiding (EQ, GT, LT)
import           Data.Text as TXT
import           Debug.Trace

type TransFrag = Frag -- Reexport Fragtype

data BExp = Ex Exp | Nx Stm | Cx ((Label, Label) -> Stm)

instance Show BExp where
  show (Ex e)  = "Ex " ++ show e
  show (Nx e)  = "Nx " ++ show e
  show (Cx _ ) = "Cx "

type Level = [(Frame, Int)]

getFrame :: Level -> Frame
getFrame ((f,_):_) = f

getNlvl :: Level -> Int
getNlvl ((_,i):_) = i

setFrame :: Frame -> Level -> Level
setFrame f ((_,l):xs) = (f,l) : xs

newLevel :: Level -> Symbol -> [Bool] -> Level
newLevel [] s bs              = [(newFrame s bs,0)]
newLevel ls@((pF,lvl):_) s bs = (newFrame s bs, lvl+1) : ls

getParent :: Level -> Level
getParent []     = P.error "No fuimos del outermost level"
getParent (_:xs) = xs

outermost :: Level
outermost = [(newFrame (pack "_undermain") [],-1) ]

class (Monad w, TLGenerator w, Daemon w) => MemM w where
  -- | Level management
  getActualLevel :: w Int
  upLvl :: w ()
  downLvl :: w ()
  -- | Salida management
  pushSalida :: Maybe Label -> w ()
  topSalida :: w (Maybe Label)
  popSalida :: w ()
  -- | Level management Cont.
  pushLevel :: Level -> w ()
  popLevel  :: w ()
  topLevel  :: w Level
  -- | Pedimos memoria para una variable local
  allocLocal :: Bool -> w Access
  allocLocal b = 
    do t <- topLevel
       popLevel
       (f, acc) <- F.allocLocal (getFrame t) b
       let nt = setFrame f t
       pushLevel nt
       return  acc
  -- | Pedimos memoria para un argumento
  allocArg :: Bool -> w Access
  allocArg b = 
    do t <- topLevel
       popLevel
       (f,a) <- F.allocArg (getFrame t) b
       pushLevel (setFrame f t)
       return a
  -- | Frag management
  -- Básicamente los fragmentos van a ser un efecto
  -- lateral de la computación.
  pushFrag  :: Frag -> w ()
  getFrags  :: w [Frag]


class IrGen w where
  procEntryExit :: Level -> BExp -> w ()
  unitExp :: w BExp
  nilExp :: w BExp
  intExp :: Int -> w BExp
  stringExp :: Symbol -> w BExp
  simpleVar :: Access -> Int -> w BExp
  varDec :: Access -> w BExp
  fieldVar :: BExp -> Int -> w BExp
  subscriptVar :: BExp -> BExp -> w BExp
  recordExp :: [(BExp,Int)]  -> w BExp
  callExp :: Label -> Bool -> Bool -> Level -> [BExp] -> w BExp
  letExp :: [BExp] -> BExp -> w BExp
  breakExp :: w BExp
  seqExp :: [BExp] -> w BExp
  preWhileforExp :: w ()
  posWhileforExp :: w ()
  whileExp :: BExp -> BExp -> w BExp
  forExp :: BExp -> BExp -> BExp -> BExp -> w BExp
  ifThenExp :: BExp -> BExp -> w BExp
  ifThenElseExp :: BExp -> BExp -> BExp -> w BExp
  ifThenElseExpUnit :: BExp -> BExp -> BExp -> w BExp
  assignExp :: BExp -> BExp -> w BExp
  preFunctionDec :: Level -> w ()
  posFunctionDec :: w ()
  functionDec :: BExp -> Level -> Bool -> w BExp
  binOpIntExp :: BExp -> Abs.Oper -> BExp -> w BExp
  binOpIntRelExp :: BExp -> Abs.Oper -> BExp -> w BExp
  binOpStrExp :: BExp -> Abs.Oper -> BExp -> w BExp
  arrayExp :: BExp -> BExp -> w BExp

-- | Función helper seq
seq :: [Stm] -> Stm
seq []     = ExpS $ Const 0
seq [s]    = s
seq (x:xs) = Seq x (seq xs)

-- | Des-empaquetador de expresiones
-- Es momadico ya que deberá crear labels, y temps
-- para des-empaquetar una condición.
unEx :: (Monad w, TLGenerator w) => BExp -> w Exp
unEx (Ex e)  = return e
unEx (Nx s)  = return $ Eseq s (Const 0)
unEx (Cx cf) = 
  do r <- newTemp
     t <- newLabel
     f <- newLabel
     return $ Eseq (seq [Move (Temp r) (Const 1)
                         , cf(t, f)
                         , Label f
                         , Move (Temp r) (Const 0)
                         , Label t])
                   (Temp r)


-- | Des-empaquetador de statements (cosas que no retornan valor)
unNx :: (Monad w,TLGenerator w) => BExp -> w Stm
unNx (Ex e)  = return $ ExpS e
unNx (Nx s)  = return s
unNx (Cx cf) = do t <- newLabel
                  return $ seq [cf(t,t),Label t]

-- | Des-empaquetador de condiciones
unCx :: (Monad w,TLGenerator w, Daemon w) => BExp -> w ((Label, Label) -> Stm)
unCx (Nx s)         = internal $ pack "unCx(Nx...)"
unCx (Cx cf)        = return cf
-- Pequeña optimización boluda
unCx (Ex (Const 0)) = return (\(_,f) -> Jump (Name f) f)
unCx (Ex (Const _)) = return (\(t,_) -> Jump (Name t) t)
unCx (Ex e)         = return (uncurry (CJump NE e (Const 0)))

instance (MemM w) => IrGen w where
  procEntryExit lvl bd =  
    do bd' <- unNx bd
       let res = Proc bd' (getFrame lvl)
       pushFrag res
  stringExp t = 
    do l <- newLabel
       let ln = T.append (pack ".long ")  (pack $ show $ TXT.length t)
       let str = T.append (T.append (pack ".string \"") t) (pack "\"")
       pushFrag $ AString l [ln,str]
       return $ Ex $ Name l
  preFunctionDec lvl = 
    do pushSalida Nothing  -- In case a break is called.
       upLvl
       pushLevel lvl
  posFunctionDec = popSalida >> downLvl
  -- functionDec :: BExp -> Level -> Bool -> w BExp
  functionDec bd lvl proc = 
    do body <- if proc then unNx bd
                 else do e <- unEx bd
                         return $ Move (Temp rv) e
       procEntryExit lvl (Nx body)
       return $ Ex $ Const 0
  --simpleVar :: Access -> Int -> w BExp
  simpleVar acc level 
    | deltaProf > 0 = do sl   <- genSl deltaProf
                         tmp1 <- newTemp
                         tmp2 <- newTemp
                         return $ Ex $ Eseq (seq [Move (Temp tmp1) (Temp tmp2) -- ???
                                                  , Move (Temp tmp2) (Mem (BinOp Plus (Temp tmp1) (Const $ fromFrame acc)))])
                                            (Temp tmp1)  
    | otherwise     = internal $ pack "La variable no se encuentra definida"
  where deltaProf             = acc - level
        genSl 0               = []
        genSl n               = do temp <- newTemp
        fromFrame (InFrame f) = f
        fromFrame _           = P.error "No se" --FIXME 
  varDec acc = getActualLevel >>= simpleVar acc
  unitExp = return $ Ex (Const 0)
  nilExp = return $ Ex (Const 0)
  intExp i = return $ Ex (Const i)
  --fieldVar :: BExp -> Int -> w BExp
  fieldVar be i =
    do be' <- unEx be
       tmp <- newTemp       --TODO: chequear el return. Ver lo del wSz. 
       -- FIXME: lo puse para que tipara, hay que chequear si esta bien
       return $ Ex $ Eseq (Move (Temp tmp) be') 
                          (Mem (Binop Plus (Temp tmp) (Binop Mul (Const i) (Const wSz))))
  -- subscriptVar :: BExp -> BExp -> w BExp
  subscriptVar var ind = 
    do evar <- unEx var
       eind <- unEx ind
       tvar <- newTemp
       tind <- newTemp
       return $ Ex $ Eseq (seq [Move (Temp tvar) evar
                           , Move (Temp tind) eind
                           , ExpS $ externalCall "_checkIndex" [Temp tvar, Temp tind]])
                          (Mem $ Binop Plus (Temp tvar) (Binop Mul (Temp tind) (Const wSz)))
  -- recordExp :: [(BExp,Int)]  -> w BExp
  -- FIXME: el primer argumento de Eseq debe ser Stm y aca es una Exp
  recordExp flds = P.error "Nada"
    {-do flds' <- mapM (\(x, y) -> unEx x) flds -- FIXME: hecho para tipar, ver si esta bien
         tmp   <- newTemp
         return $ Ex $ Eseq (seq [externalCall "_initRecord" [Const (Prelude.length flds), flds']
                                  , Move (Temp tmp) (Temp rv)]) (Temp tmp)
    -}
  -- callExp :: Label -> Bool -> Bool -> Level -> [BExp] -> w BExp
  callExp name external isproc lvl args = P.error "COMPLETAR"
  -- letExp :: [BExp] -> BExp -> w BExp
  letExp [] e = -- Puede parecer al dope, pero no...
    do e' <- unEx e
       return $ Ex e'
  letExp bs body = 
    do bes <- mapM unNx bs
       be <- unEx body
       return $ Ex $ Eseq (seq bes) be
  -- breakExp :: w BExp
  breakExp = 
    do salida <- topSalida                      
       case salida of
         Just s -> return $ Nx (Jump (Name s) s) 
         _      -> internal $ pack "Dangling break"
  -- seqExp :: [BExp] -> w BExp
  seqExp [] = return $ Nx $ ExpS $ Const 0
  seqExp bes = 
    do let ret = Prelude.last bes
       case ret of
         Nx e' -> 
           do bes' <- mapM unNx bes
              return $ Nx $ seq bes'
         Ex e' -> 
           do let bfront = Prelude.init bes
              ess <- mapM unNx bfront
              return $ Ex $ Eseq (seq ess) e'
         _ -> internal $ pack "WAT!123"   --TODO: agregar caso Cx
  -- preWhileforExp :: w ()
  preWhileforExp = 
    do l <- newLabel
       pushSalida (Just l)
  -- posWhileforExp :: w ()
  posWhileforExp = popSalida
  -- whileExp :: BExp -> BExp -> Level -> w BExp
  whileExp cond body = 
    do test <- unCx cond
       cody <- unNx body
       init <- newLabel
       bd <- newLabel
       lastM <- topSalida
       case lastM of
         Just last ->
           return $ Nx $ seq
                  [Label init      -- TODO: el init que define, no tendra confusion con la funcion init de listas definida??
                   , test (bd,last)
                   , Label bd
                   , cody
                   , Jump (Name init) init
                   , Label last]
         _ -> internal $ pack "no label in salida"
  -- forExp :: BExp -> BExp -> BExp -> BExp -> w BExp
  forExp lo hi var body = 
    do sigue  <- newLabel                   
       sigue1 <- newLabel
       salida <- topSalida
       var'   <- unEx var 
       lo'    <- unEx lo
       hi'    <- unEx hi
       body'  <- unNx body
       tmp    <- newTemp
       case salida of
         Just s -> 
           return $ Nx (seq [Move var' lo' 
                             , Move (Temp tmp) hi' 
                             , CJump LE var' (Temp tmp) sigue s 
                             , Label sigue 
                             , body'
                             , CJump EQ var' (Temp tmp) s sigue1
                             , Label sigue1 
                             , Move var' (Binop Plus var' (Const 1))
                             , Jump (Name sigue) sigue 
                             , Label s])    
         _     -> internal $ pack "No se puede hacer el for"     --TODO: revisar esta ultima parte, sobre todo
  -- ifThenExp :: BExp -> BExp -> w BExp
  ifThenExp cond bod = 
    do t <- newLabel                             
       f <- newLabel
       cond' <- unCx cond
       bod'  <- unNx bod
       return $ Nx (seq [cond'(t,f)
                         , Label t
                         , bod'
                         , Label f])
  -- ifThenElseExp :: BExp -> BExp -> BExp -> w BExp  
  ifThenElseExp cond bod els = 
    do lt <- newLabel
       lf <- newLabel
       ls <- newLabel
       cond' <- unCx cond
       bod'  <- unEx bod
       els'  <- unEx els
       tmp   <- newTemp 
       return $ Ex $ Eseq (seq [cond' (lt, lf)
                                , Label lt             
                                , Move (Temp tmp) bod'
                                , Jump (Name ls) ls
                                , Label lf 
                                , Move (Temp tmp) els'
                                , Label ls]) 
                          (Temp tmp) 
  -- ifThenElseExpUnit :: BExp -> BExp -> BExp -> w BExp
  ifThenElseExpUnit cond bod els = 
    do lt <- newLabel                            
       lf <- newLabel
       ls <- newLabel
       cond' <- unCx cond
       bod'  <- unNx bod
       els'  <- unNx els
       return $ Nx (seq [cond' (lt, lf)
                         , Label lt
                         , bod'
                         , Jump (Name ls) ls
                         , Label lf 
                         , els'
                         , Label ls]) 
  -- assignExp :: BExp -> BExp -> w BExp
  assignExp cvar cinit = 
    do cvara <- unEx cvar
       cin <- unEx cinit
       case cvara of
         Mem v' -> 
           do t <- newTemp
              return $ Nx $ seq [Move (Temp t) cin
                                 , Move cvara (Temp t)]
         _ -> return $ Nx $ Move cvara cin
  -- binOpIntExp :: BExp -> Abs.Oper -> BExp -> w BExp
  binOpIntExp le op re =
    do le' <- unEx le
       re' <- unEx re
       return $ Ex $ Binop getOp le' re'
      where getOp =  case op of
                       Abs.PlusOp   -> Plus  
                       Abs.MinusOp  -> Minus 
                       Abs.TimesOp  -> Mul 
                       Abs.DivideOp -> Div
                       _        -> P.error "No es un operador binario aritmetico"
  -- binOpStrExp :: BExp -> Abs.Oper -> BExp -> w BExp
  binOpStrExp strl op strr =
    do strl' <- unEx strl
       strr' <- unEx strr
       case op of
         Abs.EqOp -> return $ Cx (\(lt, lf) -> CJump EQ strl' strr' lt lf)
         _        -> P.error "No es posible comparar las strings"
  -- binOpIntRelExp :: BExp -> Abs.Oper -> BExp -> w BExp
  binOpIntRelExp strl op strr = 
    do strl' <- unEx strl
       strr' <- unEx strr
       return $ Cx (\(lt, lf) -> CJump (getOp op) strl' strr' lt lf)
      where getOp op = case op of
                         Abs.EqOp  -> EQ 
                         Abs.NeqOp -> NE
                         Abs.LtOp  -> LT
                         Abs.LeOp  -> LE
                         Abs.GtOp  -> GT
                         Abs.GeOp  -> GE
                         _     -> P.error "No es un operador de relacion"
  -- arrayExp :: BExp -> BExp -> w BExp
  arrayExp size init = do
    do sz <- unEx size
       ini <- unEx init
       t <- newTemp
       return $ Ex $ Eseq (seq [ExpS $ externalCall "_allocArray" [sz,ini]
                                , Move (Temp t) (Temp rv)]) 
                          (Temp t)
