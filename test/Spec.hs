import qualified ArgFirst as A
import qualified Data.IntMap as I
import Data.Maybe
import qualified Lib as S
import Test.HUnit

test1 =
  TestCase
    (assertEqual "\\f g b -> (g (f b))" (Just t) (S.inferType I.empty func))
  where
    func :: S.Expr
    func =
      S.EAnn
        (S.ELam
           0
           (S.ELam
              1
              (S.ELam 2 (S.EApp (S.EVar 1) (S.EApp (S.EVar 0) (S.EVar 2))))))
        t
    t :: S.EType
    t =
      S.TApp
        (S.TApp S.TBool S.TBool)
        (S.TApp (S.TApp S.TBool S.TBool) (S.TApp S.TBool S.TBool))

-- pattern matching lambda to make this work?
-- YL: see Xie's paper: Let arguments go first
test2 = TestCase (assertEqual "(\\x -> x) true" Nothing (S.inferType I.empty f))
  where
    f :: S.Expr
    f = (S.EApp (S.ELam 0 (S.EVar 0)) S.ETrue)

-- test3 = TestCase (assertEqual "unify-0" True (isJust $ ()))
--   where t0 = A.TApp (A.TApp (A.TVar 0) (A.TVar 1)) (A.TVar 2)
--         t1 = A.TApp (A.TApp A.TInt A.TInt) (A.TApp A.TInt (A.TVar 3))
--         s = [(0, A.MTVar 0), (1, A.MTVar 1), (2, A.MTVar 2), (3, A.MTVar 3)]
tests = TestList [test1, test2]

main :: IO ()
main = runTestTT tests >> return ()
