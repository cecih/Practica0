{-# LANGUAGE FlexibleContexts #-}

module TigerAssem where

import qualified TigerTemp as Temp
import qualified TigerTree as Tree
import qualified TigerFrame as Frame

import Control.Monad.ST
import Data.STRef as Ref

type Reg = String
type Tem = Temp.Temp
type Lab = Temp.Label

-- ¿Qué es la opción del jump?
data Instr = Oper {assem :: String,
                   dsto :: [Tem],
                   srco :: [Tem],
                   jump :: Maybe [Temp.Label]}
             | Labe {assem :: String,
                     labe :: Lab}
             | Move {assem :: String,
                     dstm :: Tem, 
                     srcm :: Tem}
          deriving (Eq, Show)

-- Función auxiliar para que programemos pa el cambio equisde equisde xd
printJump :: String
printJump = "j"

format :: (Temp.Temp -> String) -> Instr -> String
{-format f (Oper op) = (assem op) ++ map f (dst op) ++ map f (src op) ++ 
                     case (jump op) of
                       Nothing -> "" 
                       Just l  -> 
format f (Labe l) = printJump ++  (assem l)-}
format f (Move {assem = name, dstm = dst, srcm = src}) 
  | dst == src = ""
  | otherwise    = name ++ f dst ++ f src

-------------------------------------
-- --- Generación de assembler --- --
-------------------------------------

-- Completar
codeGen :: Frame.Frame -> Tree.Stm -> [Instr] 
codeGen fr stm = []
  -- Pasar x a los munchs
  -- x = newSTRef []
  --where instrs = runST x 

-- Corregir para que funcione con la monada
emit :: Instr -> STRef s [Instr] -> ST s ()
emit x ref = 
  do linstr <- readSTRef ref
     writeSTRef ref (x:linstr)

-------------------------------------
-- --- Maximal munch algorithm --- --
-------------------------------------

-- La referencia en munchExp es para que emit pueda ir
-- concatenando los resultados
-- munchExp :: Tree.Exp -> w Tem
munchExp (Tree.Const i) ref =
  do nt <- Temp.newTemp
     emit (Oper {assem = "ADDI ´d0 , r0 , " ++ show i ++ "\n",
                 dsto = [nt],
                 srco = [],
                 jump = Nothing}) ref
     return nt
-- FIJAR SI PODEMOS USAR LI
munchExp (Tree.Name l) ref =
  do nt <- newTemp
     emit (Oper {assem = "li ´d0 , " ++ unpack l ++ "\n",
                 dsto = [nt],
                 srco = [],
                 jump = Nothing}) ref
     return nt
munchExp (Tree.Binop Tree.Plus e1 e2) ref = 
  do nt <- Temp.newTemp
     ne1 <- munchExp e1 ref
     ne2 <- munchExp e2 ref
     emit (Oper {assem = "ADD ´d0 , ´s0 , ´s1 \n", 
                 dsto = [nt], 
                 srco = [ne1, ne2], 
                 jump = Nothing}) ref  
     return nt
munchExp (Tree.Binop Tree.Plus (Const i) e2) ref =
  do nt <- Temp.newTemp
     ne2 <- munchExp e2
     emit (Oper {assem = "ADDI ´d0 , ´s0 , " ++ show i ++ "\n"}),
                 dsto= [nt],
                 srco = [ne2],
                 jump = Nothing}) ref
     return nt
munchExp (Tree.Binop Tree.Plus e1 (Const i)) ref =
  do nt <- Temp.newTemp
     ne2 <- munchExp e1
     emit (Oper {assem = "ADDI ´d0 , ´s0 , " ++ show i ++ "\n"}),
                 dsto= [nt],
                 srco = [ne1],
                 jump = Nothing}) ref
     return nt
-- munchStm :: Tree.Stm -> ()
