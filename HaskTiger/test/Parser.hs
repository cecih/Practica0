import           System.Console.ANSI
import           System.Directory
import           Text.Parsec
import           TigerParser

main :: IO ()
main =
  putStrLn "\n======= Test PARSER in progress =======" >>
  putStrLn "Good:">>
  (listDirectory good_loc >>=
    mapM_ testGood)
  >>
  putStrLn "Bad:" >>
  (listDirectory bad_loc >>=
    mapM_ testBad)
  >>
  putStrLn "\n======= Test FIN ======="


good_loc = "./test/test_code/good"

-- | These ones should fail
bad_loc = "./test/test_code/syntax"

setRed = setSGR [SetColor Foreground Vivid Red]
setBlue = setSGR [SetColor Foreground Vivid Blue]
reset = setSGR []

colorPrint c s = c >> putStrLn s >> reset

goodRes :: String -> IO ()
goodRes = colorPrint setBlue

badRes :: String -> IO ()
badRes = colorPrint setRed

badResult:: String -> ParseError -> IO ()
badResult nm err = badRes nm >> print err

test loc bad good s =
	readFile (loc ++ '/' : s) >>=
	(either
        bad
		good       .
		(runParser expression () s))

testGood s = test good_loc (badResult s) (const $ goodRes s) s

testBad s = test bad_loc (const $ goodRes s) (const $ badRes s) s
