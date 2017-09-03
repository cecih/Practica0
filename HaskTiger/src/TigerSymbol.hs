module TigerSymbol (Symbol, pack, unpack, addStr, append) where

import Data.Text as T

-- | Symbol es como representamos las cadenas a lo largo del compilador...
type Symbol = T.Text

addStr :: String -> Symbol -> Symbol
addStr str = pack . (++) str . unpack
