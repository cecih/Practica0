import TigerAbs
import TigerParser
import TigerSeman
import Tools

import System.Directory
import Text.Parsec

our_loc = "./test/test_code/ourtests"

main :: IO ()
main =
  --putStrLn "\n======= Test TYPES in progress =======" >>
  --testDir our_loc (testGood our_loc tester) >>
  --putStrLn "======= End of OURTESTS =======" >>
  putStrLn "\n======= Test TYPES in progress =======" >>
  --(test "./test/test_code" (const $ bluefail) (const $ rednice) tester "escapa.tig") >>
  --(test "./test/test_code" (const $ bluefail) (const $ rednice) tester "intro.tig") >>
  --testDir good_loc (testSTDGood tester) >>
  --putStrLn "Type:" >>
  --(test "./test/test_code/good" (const $ bluefail) (const $ rednice) tester "test06.tig") >>
  testDir good_loc (testGood good_loc tester) >>
  putStrLn "\n======= End of GOOD =======" >>
  testDir type_loc (testGood type_loc tester) >>
  putStrLn "\n======= Test FIN ======="

tester s = either (fail "Iokese, no soi 100tifiko xD") runLion $ runParser expression () s s
