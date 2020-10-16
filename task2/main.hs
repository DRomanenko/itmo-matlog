module Main where

import           Parser
import           Tokenizer

import           Data.List
import qualified Data.Map   as M
import           Data.Maybe
import qualified Data.Set   as S


main = do
  input <- getContents
  let inputToLines = lines input
  let Head (hypo, state) = parse $ alexScanTokens $ head $ inputToLines
  let minimized = minimize 0 (M.empty, M.empty) (hypo, state, map (line . parse . alexScanTokens) $ tail $ inputToLines)
  let minToString = case (minimized) of
        Nothing -> ["Proof is incorrect"]
        Just curExpr -> case (findIndex (\expr -> getExpr expr == state) curExpr) of
              Nothing -> ["Proof is incorrect"]
              Just n -> [toStringHead hypo state, toStringTail] where
                ind = getInd (take (n + 1) curExpr)
                toStringTail = unlines (map (\(n, signedExpr) -> "[" ++ show (1 + ind M.! n) ++ ". " ++ showSignedExpr signedExpr ind ++ "] " ++ show (getExpr signedExpr))
                                (filter ((`M.member` ind) . fst) (zip [0..] curExpr)))
  putStrLn $ unlines minToString

getInd signedExpr = M.fromList (map (\(a, b) -> (b, a)) (zip [0..] (filter (`S.member` (S.insert (length signedExpr - 1) usedIndexes)) [0.. length signedExpr - 1]))) where
  usedIndexes = foldr inserter (S.insert (length signedExpr - 1) S.empty) (zip [0..] signedExpr) where
    inserter (n, (MP _ i q)) a | S.member n a = S.insert i (S.insert q a)
    inserter _ a               = a

minimize _ (_, _) (_, _, []) = Just []
minimize n (heaD, taiL) (hypo, state, (expr : exprs)) =
  let signedExpr = case elemIndex expr hypo of
            Nothing -> if (isAxiom expr /= 0)
              then Just (Axiom expr (isAxiom expr))
              else case M.lookup expr taiL of
                Nothing -> Nothing
                Just exprs' -> case find (\(a, _) -> isJust $ M.lookup a heaD) exprs' of
                  Nothing     -> Nothing
                  Just (a, b) -> Just (MP expr b (heaD M.! a))
            Just n -> Just (Hypothesis expr (n + 1))
    in
      case signedExpr of
        Nothing -> Nothing
        Just signedExpr -> case affterCheck n (heaD, taiL) (hypo, state, (expr : exprs)) of
                Nothing -> Nothing
                Just signedExprs -> if (state /= expr && exprs == [])
                    then Nothing
                    else Just (if M.member expr heaD then signedExprs else (signedExpr : signedExprs))

toStringHead [] state = "|- " ++ show state
toStringHead hypo state = addAllFrom hypo ++ " " ++ toStringHead [] state where
  addAllFrom []             = []
  addAllFrom [expr]         = show expr
  addAllFrom (expr : exprs) = show expr ++ ", " ++ addAllFrom exprs

affterCheck n (heaD, taiL) (hypo, state, (expr : exprs)) =
  if M.member expr heaD
    then minimize n (heaD, taiL) (hypo, state, exprs)
    else minimize (n + 1) ((M.insert expr n heaD), (insT expr taiL n)) (hypo, state, exprs) where
      insT (Apply Impl a b) taiL n = case M.lookup b taiL of
          Nothing     -> M.insert b [(a, n)] taiL
          Just exprs' -> M.insert b ((a, n) : exprs') taiL
      insT _ taiL _ = taiL

isAxiom expr =
  case expr of
    (Apply Impl a1 (Apply Impl b a2)) | a1 == a2 -> 1
    (Apply Impl (Apply Impl a1 b1) (Apply Impl (Apply Impl a2 (Apply Impl b2 c1)) (Apply Impl a3 c2))) | a1 == a2 && a2 == a3 && b1 == b2 && c1 == c2 -> 2
    (Apply Impl a1 (Apply Impl b1 (Apply And a2 b2))) | a1 == a2 && b1 == b2 -> 3
    (Apply Impl (Apply And a1 b) a2) | a1 == a2 -> 4
    (Apply Impl (Apply And a b1) b2) | b1 == b2 -> 5
    (Apply Impl a1 (Apply Or a2 b)) | a1 == a2 -> 6
    (Apply Impl b1 (Apply Or a b2)) | b1 == b2 -> 7
    (Apply Impl (Apply Impl a1 c1) (Apply Impl (Apply Impl b1 c2) (Apply Impl (Apply Or a2 b2) c3))) | a1 == a2 && b1 == b2 && c1 == c2 && c2 == c3 -> 8
    (Apply Impl (Apply Impl a1 b1) (Apply Impl (Apply Impl a2 (Not b2)) (Not a3))) | a1 == a2 && a2 == a3 && b1 == b2 -> 9
    (Apply Impl (Not (Not a1)) a2) | a1 == a2 -> 10
    _ -> 0
