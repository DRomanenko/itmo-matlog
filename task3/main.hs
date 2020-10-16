module Main where

import           Parser
import           Tokenizer

import           Data.Either
import           Data.List
import qualified Data.Map    as M
import           Data.Maybe
import qualified Data.Set    as S

main = do
  input <- getContents
  let inputToLines = lines input
  let Head state = parse $ alexScanTokens $ head $ inputToLines
  let proof = check 0 (M.empty, M.empty) (state, map (line . parse . alexScanTokens) $ tail $ inputToLines)
  let proofToString = [show (Head state)] ++ (map (\(n, signedExpr) -> case signedExpr of
          Left expr -> "Expression " ++ show n ++ (if expr == "is not proved" then " " else ": ") ++ expr ++ "."
          Right expr -> "[" ++ show n ++ showSignedExpr expr) (zip [1..] proof))
  putStrLn $ unlines (proofToString ++ if checkRight (last proof) state then [] else ["The proof proves different expression."])

check _ (_, _) (_, []) = []
check n (heaD, taiL) (state, (expr : exprs)) =
  let signedExpr = case isAxiomSch expr of
        Left ind -> if (isAxiom expr /= 0) then Right (Axiom expr (isAxiom expr))
          else if isAxiom9Sch expr then Right (AxiomSch expr "A9")
            else let tryMP expr heaD taiL = case M.lookup expr taiL of
                      Nothing -> Nothing
                      Just exprs' -> case sortBy (\(a, b) (c, d) -> flip compare (heaD M.! a, b) (heaD M.! c, d))
                        (filter (isJust . (`M.lookup` heaD) . fst) exprs') of
                        ((a, b) : exprs'') -> Just $ MP expr (heaD M.! a) b
                        []                 -> Nothing
              in case tryMP expr heaD taiL of
                Nothing -> let
                  resForall = case expr of
                    (Apply Impl expr1 (Apply1 Forall term expr2)) -> checkForEx expr1 (Apply Impl expr1 expr2) term heaD expr
                    _ -> Left "is not proved"
                  resExists = case expr of
                    (Apply Impl (Apply1 Exist term expr1) expr2) -> checkForEx expr2 (Apply Impl expr1 expr2) term heaD expr
                    _ -> Left "is not proved"
                  in case (if isRight resExists || isLeft resForall && resExists /= Left "is not proved" then resExists else resForall) of
                    Left resToString -> Left (if resToString == "is not proved" then ind else resToString)
                    Right a -> Right a
                Just mpExpr -> Right mpExpr
        Right ind -> Right (AxiomSch expr (show ind))
  in affterCheck n (heaD, taiL) (state, (expr : exprs)) signedExpr

findMatch expr1 expr2 term s1 s2 = case (expr1, expr2) of
  (Not e, Not e') -> findMatch e e' term s1 s2
  (Expr pred, Expr pred') -> case (pred, pred') of
    (Ravno a b, Ravno c d) -> recCheck a c && recCheck b d where
      recCheck term1 term2 = case (term1, term2) of
        (Zero, Zero) -> True
        (Term a, currTerm) -> if (Term a) == term && currTerm /= term then (S.member term s1) || (S.null $ S.intersection s1 s2) else True
        (Quote a1, Quote a2) -> recCheck a1 a2
        (Apply2 op a1 b1, Apply2 op1 a2 b2) | op == op1 -> recCheck a1 a2 && recCheck b1 b2
    _ -> True
  (Apply op a1 b1, Apply op1 a2 b2) | op == op1 -> findMatch a1 a2 term s1 s2 && findMatch b1 b2 term s1 s2
  (Apply1 op a b1, Apply1 op1 _ b2) | op == op1 -> findMatch b1 b2 term (S.insert a s1) s2

findPlace fun (a1, b1) (a2, b2) term flag = let
  fun1 = fun a1 a2 term flag
  fun2 = fun b1 b2 term flag
  in if isJust fun1 && isJust fun2
    then if isJust $ fromJust fun1
      then if (isNothing (fromJust fun2) || fromJust fun1 == fromJust fun2) then fun1 else Nothing
      else fun2
    else Nothing

fp expr1 expr2 term flag = case (expr1, expr2) of
  (Not e, Not e') -> fp e e' term flag
  (Expr pred, Expr pred')-> case (pred, pred') of
    (Ravno a b, Ravno c d) -> findPlace (swapTerm) (a, b) (c, d) term flag where
      swapTerm term1 term2 term flag = case (term1, term2) of
        (Zero, Zero) -> Just Nothing
        (Term a, currTerm) -> if (Term a == term && currTerm == term && not flag) || (Term a == currTerm && Term a /= term) then Just Nothing
          else if Term a == term && flag then Just $ Just currTerm else Nothing
        (Quote a, Quote b) -> swapTerm a b term flag
        (Apply2 op a b, Apply2 op1 a1 b2) | op == op1 -> findPlace (swapTerm) (a, b) (a1, b2) term flag
        _ -> Nothing
    (Predicate p, Predicate p') -> if p == p' then Just Nothing else Nothing
    _ -> Nothing
  (Apply op a b, Apply op1 c d) | op == op1 -> findPlace (fp) (a, b) (c, d) term flag
  (Apply1 op a b, Apply1 op1 c d) | op == op1 -> (if a /= c then Nothing else fp b d term (flag && (a /= term)))
  _ -> Nothing

checkRight (Left expr) _      = True
checkRight (Right expr) state = (getExpr expr == state)

affterCheck n (heaD, taiL) (state, (expr : exprs)) signedExpr =
  case signedExpr of
    Left a -> [signedExpr]
    Right a -> signedExpr : (check (n + 1) (M.insert expr n heaD, insT expr taiL n) (state, exprs)) where
      insT (Apply Impl a b) taiL n = case M.lookup b taiL of
        Nothing     -> M.insert b [(a, n)] taiL
        Just exprs' -> M.insert b ((a, n) : exprs') taiL
      insT _ taiL _ = taiL

isAxiom expr =
  case expr of
    (Apply Impl (Expr (Ravno a1 b1)) (Apply Impl (Expr (Ravno a2 c1)) (Expr (Ravno b2 c2)))) | a1 == a2 && b1 == b2 && c1 == c2 && a1 == Term "a" && b1 == Term "b" && c1 == Term "c" -> 1
    (Apply Impl (Expr (Ravno a1 b1)) (Expr (Ravno (Quote a2) (Quote b2)))) | a1 == a2 && b1 == b2 && a1 == Term "a" && b1 == Term "b" -> 2
    (Apply Impl (Expr (Ravno (Quote a1) (Quote b2))) (Expr (Ravno a2 b1))) | a1 == a2 && b1 == b2 && a2 == Term "a" && b1 == Term "b"-> 3
    (Not (Expr (Ravno (Quote a) Zero))) | a == Term "a" -> 4
    (Expr (Ravno (Apply2 Plus a1 Zero) a2)) | a1 == a2 && a1 == Term "a"-> 5
    (Expr (Ravno (Apply2 Plus a1 (Quote b1)) (Quote (Apply2 Plus a2 b2)))) | a1 == a2 && b1 == b2 && a1 == Term "a" && b1 == Term "b"-> 6
    (Expr (Ravno (Apply2 Mul a Zero) Zero)) | a == Term "a" -> 7
    (Expr (Ravno (Apply2 Mul a1 (Quote b1)) (Apply2 Plus (Apply2 Mul a2 b2) a3))) | a1 == a2 && a2 == a3 && b1 == b2 && a1 == Term "a" && b1 == Term "b" -> 8
    _ -> 0

getForQueString term expr1 expr2 n = case fp expr1 expr2 term True of
  Nothing -> Left "is not proved"
  Just repTerm -> let
    termToSet currTerm = case currTerm of
      Zero            -> S.empty
      (Term a)        -> S.singleton (Term a)
      (Quote e)       -> termToSet e
      (Apply2 op a b) -> S.union (termToSet a) (termToSet b)
    res = termToSet (fromJust repTerm)
    in if isNothing repTerm || findMatch expr1 expr2 term (S.empty) res then Right n else Left $ "variable " ++ show term ++ " is not free for term " ++ show (fromJust repTerm) ++ " in ?@-axiom"

isAxiom9Sch expr = case expr of
  (Apply Impl (Apply And a (Apply1 Forall term (Apply Impl b1 c))) b2) | b1 == b2 -> let
    checkQuote = case fp b1 c term True of
      Nothing         -> False
      (Just Nothing)  -> True
      (Just (Just z)) -> (Quote term) == z
    checkZero = case fp b1 a term True of
      Nothing         -> False
      (Just Nothing)  -> True
      (Just (Just z)) -> Zero == z
    in checkQuote && checkZero
  _ -> False

checkForEx expr1 expr2 term heaD expr = if not (checkExpr expr1) && M.member expr2 heaD
  then Right $ Intro expr $ heaD M.! expr2
  else Left (if checkExpr expr1 && M.member expr2 heaD
    then "variable " ++ show term ++ " occurs free in ?@-rule" else "is not proved") where
    checkExpr expr = case expr of
      (Not e)  -> checkExpr e
      (Expr p) -> case p of
        (Ravno a b) -> recCheck a || recCheck b where
          recCheck term' = case term' of
            Zero            -> False
            (Term a)        -> (Term a) == term
            (Quote a)       -> recCheck a
            (Apply2 op a b) -> recCheck a || recCheck b
        (Predicate a) -> False
      (Apply op a b) -> checkExpr a || checkExpr b
      (Apply1 op a b) -> if term /= a then checkExpr b else False

isAxiomSch expr =
  case expr of
    (Apply Impl a1 (Apply Impl b a2)) | a1 == a2 -> Right 1
    (Apply Impl (Apply Impl a1 b1) (Apply Impl (Apply Impl a2 (Apply Impl b2 c1)) (Apply Impl a3 c2))) | a1 == a2 && a2 == a3 && b1 == b2 && c1 == c2 -> Right 2
    (Apply Impl (Apply And a1 b) a2) | a1 == a2 -> Right 3
    (Apply Impl (Apply And a b1) b2) | b1 == b2 -> Right 4
    (Apply Impl a1 (Apply Impl b1 (Apply And a2 b2))) | a1 == a2 && b1 == b2 -> Right 5
    (Apply Impl a1 (Apply Or a2 b)) | a1 == a2 -> Right 6
    (Apply Impl b1 (Apply Or a b2)) | b1 == b2 -> Right 7
    (Apply Impl (Apply Impl a1 c1) (Apply Impl (Apply Impl b1 c2) (Apply Impl (Apply Or a2 b2) c3))) | a1 == a2 && b1 == b2 && c1 == c2 && c2 == c3 -> Right 8
    (Apply Impl (Apply Impl a1 b1) (Apply Impl (Apply Impl a2 (Not b2)) (Not a3))) | a1 == a2 && a2 == a3 && b1 == b2 -> Right 9
    (Apply Impl (Not (Not a1)) a2) | a1 == a2 -> Right 10
    _ -> let
        isAxiom11Sch = case expr of
          (Apply Impl (Apply1 Forall term expr1) expr2) -> getForQueString term expr1 expr2 11
          _ -> Left "is not proved"
        isAxiom12Sch = case expr of
          (Apply Impl expr1 (Apply1 Exist term expr2)) -> getForQueString term expr2 expr1 12
          _ -> Left "is not proved"
        in if isRight isAxiom11Sch || isLeft isAxiom12Sch && isAxiom11Sch /= Left "is not proved" then isAxiom11Sch else isAxiom12Sch
