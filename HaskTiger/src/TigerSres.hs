module TigerSres where

import TigerTips
import TigerTemp
import TigerFrame

type FunEntry = (Unique, Label, [Tipo], Tipo, Bool)
type ValEntry = (Tipo, Access, Int) -- Tipo, en memoria o registro, nivel

data EnvEntry = 
    Var ValEntry | Func FunEntry
    deriving Show
