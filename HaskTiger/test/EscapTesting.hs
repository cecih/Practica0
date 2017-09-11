import           System.Directory
import           TigerAbs
import           TigerEscap
import           TigerParser
import           TigerSymbol
import           Text.Parsec

main :: IO ()
main =
  putStrLn "\n======= Test ESCAPES in progress =======" >>
  either (const $ print "Fail") (const $ print "Good") (calcularEEsc ejemplo1) >>
  either (const $ print "Good Fail") (const $ print "Bad Good") (calcularEEsc ejemplo2) >>
  ( test "./test/test_code" (const $ print "Good Fail") (const $ print "Bad Good") "escapa.tig") >>
  (listDirectory good_loc >>= mapM_ testGood ) >>
  putStrLn "\n======= Test FIN ======="

good_loc = "./test/test_code/good"

testGood = test good_loc print (const $ putStrLn "BIEN")

test loc bad good s = readFile (loc ++ '/' : s) >>=
        either (fail "asd") (either bad good  . calcularEEsc) . runParser expression () s

ejemplo1 :: Exp -- La variable a escapa.
ejemplo1 = LetExp
            [ VarDec (pack "a") False Nothing (IntExp 1 (Simple 1 1)) (Simple 1 2)
            , FunctionDec
                    [ (pack "f1"
                      ,[( pack "a1", False , NameTy $ pack "int")]
                      ,Just $ pack "int"
                      ,VarExp (SimpleVar $ pack "a") (Simple 5 5)
                      , Simple 5 2)]
            ]
            (IntExp 42 (Simple 8 1))
            (Simple 1 0)

ejemplo2 :: Exp -- La variable b no está definida.
ejemplo2 = LetExp
            [ VarDec (pack "a") False Nothing (IntExp 1 (Simple 1 2)) (Simple 1 2)
            -- , VarDec "b" Nothing Nothing (IntExp 2 1) 2
            -- , VarDec "c" Nothing Nothing (IntExp 3 1) 3
            , FunctionDec
                    [ (pack "f1"
                      ,[(pack "a1", False , NameTy $ pack "int")]
                      , Just $ pack "int",VarExp (SimpleVar $ pack "b") (Simple 5 5)
                      ,(Simple 5 6))]
            ]
            (IntExp 42 (Simple 8 1))
            (Simple 1 0)
