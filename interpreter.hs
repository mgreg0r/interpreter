import System.IO
import System.Environment
import LexGrammar
import ParGrammar
import SkelGrammar
import PrintGrammar
import AbsGrammar
import ErrM

import Exec
import StaticCheck

run s = case pStmt program of
          Ok tree -> 
            case staticCheck tree of
              (Fail e) -> hPutStrLn stderr e
              OK -> exec tree
          Bad e -> hPutStrLn stderr e
        where program = myLexer s

main :: IO ()
main = do
  target <- getArgs
  case target of
    [] -> hPutStrLn stderr "invalid target"
    f:_ -> do
      s <- readFile f
      run s
      return ()
