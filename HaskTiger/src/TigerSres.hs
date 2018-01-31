module TigerSres where

import TigerFrame
import TigerTemp
import TigerTips
import TigerTrans

type FunEntry = (Level, Label, [Tipo], Tipo, Bool)
type ValEntry = (Tipo, Access, Int) -- Tipo, en memoria o registro, nivel

data EnvEntry = 
    Var ValEntry | Func FunEntry
    deriving Show
