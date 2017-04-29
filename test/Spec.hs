import Test.Hspec

import qualified AstTest as Ast
import qualified UnificationTest as Unification

main :: IO ()
main = hspec $ do
  Ast.test
  Unification.test
