module TigerErrores where

import           TigerSymbol

-- Acompañado de un tipo de errores
data SEErrores = ENotFound Symbol | EDiffVal Symbol | EInternal Symbol | EUser Symbol
    deriving Show

class Daemon w where
  derror :: SEErrores -> w a
  adder :: w a -> Symbol -> w a
  -- adder w s = handle w (derror . append s)
  notfound :: Symbol -> w a
  diffval :: Symbol -> w a
  internal :: Symbol -> w a
  user :: Symbol -> w a
