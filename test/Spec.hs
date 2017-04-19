import Test.Hspec

import Control.Hspl

main :: IO ()
main = hspec $ do
  describe "stub" $ do
    it "should return true" $ do
      stub `shouldBe` True
