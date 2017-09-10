import Test.Hspec

import qualified AstTest as Ast
import qualified UnificationTest as Unification
import qualified SolverTest as Solver
import qualified DebuggerTest as Debugger
import qualified HsplTest as Hspl
import qualified ExamplesTest as Examples
import qualified TupleTest as Tuple
import qualified UITest as UI
import qualified VarMapTest as VarMap
import qualified LogicTest as Logic
import qualified ListTest as List

main :: IO ()
main = hspec $ do
  Ast.test
  Unification.test
  Solver.test
  Debugger.test
  Hspl.test
  Examples.test
  Tuple.test
  UI.test
  VarMap.test
  Logic.test
  List.test
