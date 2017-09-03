# HaskTiger

Bienvenido!

El proyecto utiliza a [Stack](https://docs.haskellstack.org/en/stable/README/) que vendría a ser
un cabal mejorado.

Para hacer build basta con ejecutar `stack build`. Como resultado tendrás a *HaskTiger* como ejecutable con main `./app/TigerMain.hs`
y podrás ejecutarlo con `stack exec HaskTiger`.

## Testing

Utilizando *Stack* podemos generar una testsuit en `./test` y para ejecutarlos actualmene están activadas las siguiente banderas
+ `stack test :Parser`
+ `stack test :Escap`


## HaskTiger.cabal

Explorar `HaskTiger.cabal` que es donde está definido todo lo que dije arriba.

Saludos!
