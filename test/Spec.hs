import Test.HUnit
import Lib
import qualified Data.IntMap as I

test1 = TestCase (assertEqual "\\f g b -> (g (f b))" (Just t) (inferType I.empty func))
  where func :: Expr
        func = EAnn (ELam 0 (ELam 1 (ELam 2 (EApp (EVar 1) (EApp (EVar 0) (EVar 2)))))) t
        t :: EType
        t = TApp (TApp TBool TBool) (TApp (TApp TBool TBool) (TApp TBool TBool))

-- pattern matching lambda to make this work?
-- YL: see Xie's paper: Let arguments go first
test2 = TestCase (assertEqual "(\\x -> x) true" Nothing (inferType I.empty f))
  where f :: Expr
        f = (EApp (ELam 0 (EVar 0)) ETrue)

tests = TestList [test1, test2]

main :: IO ()
main = runTestTT tests >> return ()
