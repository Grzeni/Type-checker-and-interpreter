-- Wymagamy, by moduł zawierał tylko bezpieczne funkcje
{-# LANGUAGE Safe #-}
-- Definiujemy moduł zawierający rozwiązanie.

module GrzegorzWiniarski (typecheck, eval) where

-- Importujemy moduły z definicją języka oraz typami potrzebnymi w zadaniu
import AST
import DataTypes
import Data.Typeable()

-- Funkcja sprawdzająca typy
-- Dla wywołania typecheck fs vars e zakładamy, że zmienne występujące
-- w vars są już zdefiniowane i mają typ int, i oczekujemy by wyrażenia e
-- miało typ int
-- UWAGA: to nie jest jeszcze rozwiązanie; należy zmienić jej definicję.
typecheck :: [FunctionDef p] -> [Var] -> Expr p -> TypeCheckResult p
typecheck fs xs e = case helper fs fs ((var_list_to_env xs) ++ (converT fs)) e of
    MyError -> Error (getData e) ""
    MType TInt -> Ok
    _ -> Error (getData e) ""


data MyType = MType Type
    | MyError
    deriving (Show, Eq)

extract :: [(Var, MyType)] -> Var -> MyType
extract [] _ = MyError
extract ((x,y):t) v =
    if x == v
      then y
    else
      extract t v


match_to_MyType :: [(Var, MyType)] -> Expr p -> MyType
match_to_MyType xs ex = case ex of
      EVar p v -> extract xs v
      ENum p _ -> MType TInt
      EBool p _ -> MType TBool
      EUnit p -> MType TUnit
      EPair p e1 e2 -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
          (MyError, _) -> MyError
          (_, MyError) -> MyError
          (MType x, MType y) -> MType (TPair x y)
      EFst p e -> case (match_to_MyType xs e) of
          MyError -> MyError
          MType (TPair x _) -> MType x
          _ -> MyError
      ESnd p e -> case (match_to_MyType xs e) of
          MyError -> MyError
          MType (TPair _ y) -> MType y
          _ -> MyError
      ENil p tau -> MType tau
      ECons p e1 e2 -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
          (MyError, _) -> MyError
          (_, MyError) -> MyError
          (MType x, MType (TList y)) -> MType (TList y)
          _ -> MyError
      EUnary p op e -> case op of
          UNot -> case (match_to_MyType xs e) of
            MType TBool -> MType TBool
            _      -> MyError
          UNeg -> case (match_to_MyType xs e) of
            MType TInt -> MType TInt
            _     -> MyError
      EBinary p op e1 e2 -> case op of
          BAnd -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
              (MType TBool, MType TBool) -> MType TBool
              _ -> MyError
          BOr -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
              (MType TBool, MType TBool) -> MType TBool
              _ -> MyError
          BEq -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
              (MType TInt, MType TInt) -> MType TBool
              _ -> MyError
          BNeq -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
              (MType TInt, MType TInt) -> MType TBool
              _ -> MyError
          BLt -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
              (MType TInt, MType TInt) -> MType TBool
              _ -> MyError
          BGt -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
              (MType TInt, MType TInt) -> MType TBool
              _ -> MyError
          BLe -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
              (MType TInt, MType TInt) -> MType TBool
              _ -> MyError
          BGe -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
              (MType TInt, MType TInt) -> MType TBool
              _ -> MyError
          BAdd -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
              (MType TInt, MType TInt) -> MType TInt
              _ -> MyError
          BSub -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
              (MType TInt, MType TInt) -> MType TInt
              _ -> MyError
          BMul -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
              (MType TInt, MType TInt) -> MType TInt
              _ -> MyError
          BDiv -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
              (MType TInt, MType TInt) -> MType TInt
              _ -> MyError
          BMod -> case (match_to_MyType xs e1, match_to_MyType xs e2) of
              (MType TInt, MType TInt) -> MType TInt
              _ -> MyError
      ELet p v e1 e2 -> case (match_to_MyType xs e1) of
          MyError -> MyError
          _ -> match_to_MyType ((v,match_to_MyType xs e1):xs) e2
      EIf p e1 e2 e3 -> case (match_to_MyType xs e1, match_to_MyType xs e2, match_to_MyType xs e3) of
          (MType TBool, MType t1, MType t2)|t1==t2 -> MType t1
          (_, _, MType TBool) -> MyError
          _ -> MyError
      EMatchL p e e1 (x1, x2, e2) -> case (match_to_MyType xs e, match_to_MyType xs e1) of
          (MyError, _) -> MyError
          (_, MyError) -> MyError
          (MType (TList x), MType y) -> case (match_to_MyType ((x2, MType (TList x)):(x1, MType x):xs) e2) of
              MyError -> MyError
              MType z -> if z == y
                then
                  MType z
                else
                  MyError
          _ -> MyError
      EApp p e1 e2 -> case match_to_MyType xs e1 of
          MyError -> MyError
          MType (TArrow t1 t2) -> case match_to_MyType xs e2 of
              MyError -> MyError
              MType t3 | t3 == t1 -> MType t2
              _ -> MyError
          _ -> MyError
      EFn p var typ e -> case match_to_MyType ((var, MType typ):xs) e of
          MyError -> MyError
          MType t -> MType (TArrow typ t)



helper :: [FunctionDef p] -> [FunctionDef p] -> [(Var, MyType)] -> Expr p-> MyType
helper fs [] xs e = match_to_MyType xs e
helper fs (x:xs) ys e = case match_to_MyType ((funcArg x, (MType (funcArgType x))):(converT fs)) (funcBody x) of
    MyError -> MyError
    MType t | t == funcResType x -> helper fs xs ys e
    MType t -> MyError
var_list_to_env :: [Var] -> [(Var, MyType)]
var_list_to_env [] = []
var_list_to_env (x:xs) = (x,MType TInt):t where t = var_list_to_env xs

converT :: [FunctionDef p] -> [(Var, MyType)]
converT [] = []
converT (x:xs) = (funcName x, MType (TArrow (funcArgType x) (funcResType x))):(converT xs)


-- Funkcja obliczająca wyrażenia
-- Dla wywołania eval fs input e przyjmujemy, że dla każdej pary (x, v)
-- znajdującej się w input, wartość zmiennej x wynosi v.
-- Możemy założyć, że definicje funkcji fs oraz wyrażenie e są dobrze
-- typowane, tzn. typecheck fs (map fst input) e = Ok
eval :: [FunctionDef p] -> [(Var,Integer)] -> Expr p -> EvalResult
eval fs xs e = case match_to_MyType2 ((var_list_to_env2 xs) ++ (converT_ fs fs)) e of
    MyInteger v -> Value v
    _ -> RuntimeError


data MyType2 p = MyInteger Integer
    |MyBoolean Bool
    |MyPair (MyType2 p) (MyType2 p)
    |MyList (MyType2 p) (MyType2 p)
    |MyUnit
    |MyEmpty
    |MyArrow (MyType2 p) (MyType2 p)
    |MyClosureG [FunctionDef p] (FunctionDef p)
    |MyClosureL [(Var, MyType2 p)] Var (Expr p)
    |MyRunError
    deriving (Show, Eq)


extract2 :: [(Var,MyType2 p)] -> Var -> MyType2 p
extract2 [] _ = MyRunError
extract2 ((x,y):t) v =
      if x == v
        then y
      else
        extract2 t v

match_to_MyType2 :: [(Var,MyType2 p)] -> Expr p -> MyType2 p
match_to_MyType2 xs exp = case exp of
    EVar p v -> extract2 xs v
    ENum p v -> MyInteger v
    EBool p v -> MyBoolean v
    EUnary p op e -> case op of
        UNot -> case (match_to_MyType2 xs e) of
            MyBoolean bool -> MyBoolean (not bool)
            _ -> MyRunError
        UNeg -> case (match_to_MyType2 xs e) of
            MyInteger int -> MyInteger (negate int)
            _ -> MyRunError
    EBinary p op e1 e2 -> case op of
        BAnd -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
            (MyBoolean b1, MyBoolean b2) -> MyBoolean (b1 && b2)
            _ -> MyRunError
        BOr -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
            (MyBoolean b1, MyBoolean b2) -> MyBoolean (b1 || b2)
            _ -> MyRunError
        BEq -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
            (MyInteger i1, MyInteger i2) -> MyBoolean (i1 == i2)
            _ -> MyRunError
        BNeq -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
            (MyInteger i1, MyInteger i2) -> MyBoolean (i1 /= i2)
            _ -> MyRunError
        BLt -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
            (MyInteger i1, MyInteger i2) -> MyBoolean (i1 < i2)
            _ -> MyRunError
        BGt -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
            (MyInteger i1, MyInteger i2) -> MyBoolean (i1 > i2)
            _ -> MyRunError
        BLe -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
            (MyInteger i1, MyInteger i2) -> MyBoolean (i1 <= i2)
            _ -> MyRunError
        BGe -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
            (MyInteger i1, MyInteger i2) -> MyBoolean (i1 >= i2)
            _ -> MyRunError
        BAdd -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
            (MyInteger i1, MyInteger i2) -> MyInteger (i1 + i2)
            _ -> MyRunError
        BSub -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
            (MyInteger i1, MyInteger i2) -> MyInteger (i1 - i2)
            _ -> MyRunError
        BMul -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
            (MyInteger i1, MyInteger i2) -> MyInteger (i1 * i2)
            _ -> MyRunError
        BDiv -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
            (MyInteger _, MyInteger 0) -> MyRunError
            (MyInteger i1, MyInteger i2) -> MyInteger (i1 `div` i2)
            _ -> MyRunError
        BMod -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
            (MyInteger _, MyInteger 0) -> MyRunError
            (MyInteger i1, MyInteger i2) -> MyInteger (i1 `mod` i2)
            _ -> MyRunError
    EIf p e1 e2 e3 -> case (match_to_MyType2 xs e1,match_to_MyType2 xs e2,match_to_MyType2 xs e3) of
            (MyBoolean x, t, _) | x == True -> t
            (MyBoolean y,_ , t) | y == False -> t
            (_, _, MyBoolean _) -> MyRunError
            _ -> MyRunError
    ELet p v e1 e2 -> case (match_to_MyType2 xs e1) of
            MyRunError -> MyRunError
            _ -> match_to_MyType2 ((v,match_to_MyType2 xs e1):xs) e2
    EUnit p -> MyUnit
    EPair p e1 e2 -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
          (MyRunError, _) -> MyRunError
          (_,MyRunError) -> MyRunError
          (x, y) -> MyPair x y
    EFst p e -> case match_to_MyType2 xs e of
          MyPair x _ -> x
          _ -> MyRunError
    ESnd p e -> case match_to_MyType2 xs e of
          MyPair _ y -> y
          _ -> MyRunError
    ENil p t -> MyEmpty
    ECons p e1 e2 -> case (match_to_MyType2 xs e1, match_to_MyType2 xs e2) of
          (MyRunError, _) -> MyRunError
          (_,MyRunError) -> MyRunError
          (x, y) -> MyList x y
    EMatchL p e e1 (x1, x2, e2) -> case match_to_MyType2 xs e of
          MyEmpty -> match_to_MyType2 xs e1
          MyList t1 t2 -> match_to_MyType2 ((x2, t2):(x1, t1):xs) e2
          _ -> MyRunError
    EApp p e1 e2 -> case match_to_MyType2 xs e1 of
        MyClosureG fl f -> match_to_MyType2 ((funcArg f, match_to_MyType2 xs e2):(convert fl fl)) (funcBody f)
        MyClosureL env var e -> match_to_MyType2 ((var, match_to_MyType2 xs e2):env) e
        MyRunError -> MyRunError
    EFn p var typ e -> MyClosureL xs var e


convert :: [FunctionDef p] -> [FunctionDef p] -> [(Var, MyType2 p)]
convert [] _ = []
convert (f:fl) fs = ((funcName f, MyClosureG fs f):(convert fl fs))


var_list_to_env2 :: [(Var,Integer)] -> [(Var, MyType2 p)]
var_list_to_env2 [] = []
var_list_to_env2 ((x,y):t) = ((x,MyInteger y):t1) where t1 = var_list_to_env2 t


converT_ ::[FunctionDef p] -> [FunctionDef p] -> [(Var, MyType2 p)]
converT_ [] _ = []
converT_ (f:fs) constFun =
  (funcName f, MyClosureG constFun f): converT_ fs constFun
