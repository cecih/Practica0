import TigerAbs
import TigerParser
import TigerSeman
import Tools

import System.Directory
import Text.Parsec

main :: IO ()
main =
  putStrLn "\n======= Test ESCAPES in progress =======" >>
  --(test "./test/test_code" (const $ bluefail) (const $ rednice) tester "escapa.tig") >>
  --(test "./test/test_code" (const $ bluefail) (const $ rednice) tester "intro.tig") >>
  --testDir good_loc (testSTDGood tester) >>
  --putStrLn "Type:" >>
  testDir type_loc (testGood type_loc tester) >>
  putStrLn "\n======= Test FIN ======="

tester s = either (fail "Iokese, no soi 100tifiko xD") runLion $ runParser expression () s s
