module PrintEnv where

import Data.Text
import Text.PrettyPrint.HughesPJ as PJ
import TigerSres
import TigerTips

-- >> ¿Los tipos son para tiger, digamos en minúsculas?
-- >> ¿Qué es RW y RO? Los RW son ints "normales", los RO son para los índices del for
-- >> ¿Unique lo ponemos como otro tipo distinto a Int?
-- >> ¿Formato de los arrays, alguna sugerencia?
-- >> ¿Para qué es el Unique del Record? Para diferenciar tipos por nombre
-- >> ¿Qué es un RefRecord? 
-- >> ¿Qué es un TTipo?
renderEnv :: EnvEntry -> String
renderEnv = render . printEnv

printEnv :: EnvEntry -> Doc
printEnv (Var ve)                = printTipo ve
-- El tipo de ++ sería por ejemplo: string -> string -> string
printEnv (Func (_, _, lt, t, _)) = parens (hcat (Prelude.map (\x -> printTipo x <> text " -> ") lt)) <>
                                   printTipo t

printTipo :: Tipo -> Doc
printTipo TUnit         = text "unit"
printTipo TNil          = text "nil"
printTipo (TInt r)      =
    case r of
        RW -> text "int RW"
        RO -> text "int RO"
printTipo TString       = text "string"
printTipo (TArray t _)  = printTipo t <> text "int"
printTipo (TRecord l _) = braces (fieldsRecord l)
--printTipo (RefRecord t) =
--printTipo (TTipo t)     =

fieldsRecord :: [(Text, Tipo, Int)] -> Doc
fieldsRecord []     = PJ.empty
fieldsRecord [x]    = fR x   
fieldsRecord (x:xs) = fR x <>
                      text ", "

fR (te, ti, i) = text (unpack te) <>
                 text ":" <>
                 printTipo ti <>
                 text "int" 



