module TigerAssem where

import qualified TigerTemp as Temp
import qualified TigerTree as Tree

type Reg = String
type Tem = Temp.Temp
type Lab = Temp.Label

-- ¿Qué es la opción del jump?
data Instr = Oper {assem :: String,
                   dst :: [Tem],
                   src :: [Tem],
                   jump :: [Label] ???}
             | Labe {assem :: String,
                     labe :: Lab}
             | Move {assem :: String,
                     dst :: Tem, 
                     src :: Tem}
          deriving (Eq, Show)

-------------------------------------
-- --- Maximal munch algorithm --- --
-------------------------------------

-- munchExp :: Tree.Exp -> Temp.Temp

-- munchStm :: Tree.Stm -> ()
