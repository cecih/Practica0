import TigerAbs
import TigerSymbol

{-# LANGUAGE OverloadedStrings #-}

-- Versión básica ¿Se puede mejorar, quizás con mónadas?
-- Es decir, en realidad está devolviendo 0 sin saber si la función se ha llamado con 0 argumentos
-- o directamente no ha sido llamada.

-- La tigerabs.exp -> Nombre de la función llamante -> Cantidad máxima
maxargs :: Exp -> Symbol -> Int
maxargs (UnitExp _) _             = 0
maxargs (BreakExp _) _            = 0
maxargs (NilExp _) _              = 0
maxargs (IntExp _ _) _            = 0
maxargs (StringExp _ _) _         = 0
maxargs (VarExp v _) f            = 
  case v of
    SubscriptVar _ e -> maxargs e f 
    _                -> 0
maxargs (CallExp name le _) f 
  | f == name = max (length le) rest   
  | otherwise = rest
  where rest  = maximum (map (\x -> maxargs x f) le)
maxargs (OpExp e1 _ e2 _) f       = max (maxargs e1 f) (maxargs e2 f)
maxargs (RecordExp lr _ _) f      = maximum (map (\x -> maxargs (snd x) f) lr) 
maxargs (SeqExp le _) f           = maximum (map (\x -> maxargs x f) le)
maxargs (AssignExp _ e _) f       = maxargs e f
maxargs (IfExp e1 e2 me _) f      =
  case me of
    Nothing -> max res1 res2
    Just e  -> maximum [maxargs e f, res1, res2]
  where res1 = maxargs e1 f
        res2 = maxargs e2 f 
maxargs (WhileExp e1 e2 _) f   = max (maxargs e1 f) (maxargs e2 f)
maxargs (ForExp _ _ e1 e2 e3 _) f = maximum [maxargs e1 f, maxargs e2 f, maxargs e3 f]
maxargs (LetExp ld e _) f         = max (maximum (map maxargsDec ld)) (maxargs e f)
  where maxargsDec (FunctionDec ld')    = maximum (map (\(_, _, _, d, _) -> maxargs d f) ld')
        maxargsDec (VarDec _ _ _ exp _) = maxargs exp f
        maxargsDec _                    = 0
maxargs (ArrayExp _ e1 e2 _) f    = max (maxargs e1 f) (maxargs e2 f)

-- La tigerabs.exp -> Cantidad de veces que se usa '+'
cantplus :: Exp -> Int
cantplus (UnitExp _)             = 0
cantplus (BreakExp _)            = 0
cantplus (NilExp _)              = 0
cantplus (IntExp _ _)            = 0
cantplus (StringExp _ _)         = 0
cantplus (VarExp v _)            = 
  case v of
    SubscriptVar _ e -> cantplus e  
    _                -> 0
cantplus (OpExp e1 o e2 _)
    | isPlus o    = 1 + res 
    | otherwise   = res
    where res           = cantplus e1 + cantplus e2
          isPlus PlusOp = True
          isPlus _      = False 
cantplus (RecordExp lr _ _)      = sum (map (\x -> cantplus (snd x)) lr) 
cantplus (SeqExp le _)           = sum (map cantplus le)
cantplus (AssignExp _ e _)       = cantplus e
cantplus (IfExp e1 e2 me _)      =
  case me of
    Nothing -> res1 + res2
    Just e  -> maximum [cantplus e, res1, res2]
  where res1 = cantplus e1 
        res2 = cantplus e2  
cantplus (WhileExp e1 e2 _)      = cantplus e1 + cantplus e2
cantplus (ForExp _ _ e1 e2 e3 _) = sum [cantplus e1, cantplus e2, cantplus e3]
cantplus (LetExp ld e _)         = sum (map maxargsDec ld) + cantplus e
  where maxargsDec (FunctionDec ld')    = sum (map (\(_, _, _, d, _) -> cantplus d) ld')
        maxargsDec (VarDec _ _ _ exp _) = cantplus exp 
        maxargsDec _                    = 0
cantplus (ArrayExp _ e1 e2 _)    = cantplus e1 + cantplus e2
 
