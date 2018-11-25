{-#LANGUAGE TypeOperators #-}
{-#LANGUAGE DataKinds #-}
{-#LANGUAGE GADTs #-}
{-#LANGUAGE TypeApplications #-}
module Transformations where
import Types
import Rewrite
import TraverseChild
import Control.Monad (guard)
import Control.Applicative ((<|>))

flattenComp1 :: Rewrite Expr
flattenComp1 = rewriting @(Comprehension 'NonEmpty) topdown $ do
    Bind (Comp c) i :- r <- cur
    r' <- at r $ inline (compExpr c) i
    pure $ c `compAppend` r'

dropUnused :: Rewrite Expr
dropUnused = rewriting bottomup (pLeft <|> pRight)
  where
    pLeft, pRight :: Rewrite (Comprehension 'NonEmpty)
    pLeft = do
     Bind _ i :- (l :- r) <- cur
     guard $ not $ i `elem` freeVars (l :- r)
     return (l :- r)
    pRight = do
     l :- (Bind _ i :- r) <- cur
     guard $ not $ i `elem` freeVars r
     return (l :- r)

    _test1,_test2 :: Expr
    _test1 = Comp (Bind (Lit (Table "foo")) 0 :-  Bind (Lit (Table "foo")) 1  :- CEnd (UVar 1))
    _test2 = Comp (Bind (Lit (Table "foo")) 0 :-  Bind (Lit (Table "foo")) 1  :- CEnd (UVar 0))

distGuardAnd :: Rewrite Expr
distGuardAnd = rewriting @(Comprehension 'NonEmpty) topdown $ do
    Guard (BinOp And l r) :- rest <- cur
    pure $ Guard l :- Guard r :- rest
  where

    _test :: Expr
    _test = Comp (Bind (Comp (Bind (Lit (Table "foo")) 1 :- Guard (BinOp Eql (UVar 0) (Lit (LitInt 1))) :- CEnd (UVar 1))) 0 :- CEnd (UVar 0))

