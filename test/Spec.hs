import Test.Hspec

import qualified AstTest as Ast
import qualified UnificationTest as Unification
import qualified SolverTest as Solver
import qualified DebuggerTest as Debugger

main :: IO ()
main = hspec $ do
  Ast.test
  Unification.test
  Solver.test
  Debugger.test
