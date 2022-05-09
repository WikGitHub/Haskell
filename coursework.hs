------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys

variables :: [Var]
variables = [ [x] | x <- ['a'..'z'] ] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [ x | x <- xs , not (elem x ys) ]

fresh :: [Var] -> Var
fresh = head . removeAll variables



------------------------- Assignment 1: Simple types

data Type = Base  | Type :-> Type deriving(Eq)

nice :: Type -> String
nice Base = "o"
nice (Base :-> b) = "o -> " ++ nice b
nice    (a :-> b) = "(" ++ nice a ++ ") -> " ++ nice b

instance Show Type where
  show = nice

type1 :: Type
type1 =  Base :-> Base

type2 :: Type
type2 = (Base :-> Base) :-> (Base :-> Base)

-- - - - - - - - - - - -- Terms

type Var  = String
data Term = Variable Var
  | Lambda   Var Type Term
  | Apply    Term Term

pretty :: Term -> String
pretty = f 0
    where
      f i (Variable   x) = x
      f i (Lambda x t m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ": " ++ nice t ++ " . " ++ f 0 m 
      f i (Apply    n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

instance Show Term where
  show = pretty

-- - - - - - - - - - - -- Numerals

numeral :: Int -> Term
numeral i = Lambda "f" type1 (Lambda "x" Base (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))

sucterm :: Term
sucterm =
    Lambda "m" type2 (
    Lambda "f" type1 (
    Lambda "x" Base (
    Apply (Apply (Variable "m") (Variable "f"))
          (Apply (Variable "f") (Variable "x"))
    )))

addterm :: Term
addterm =
    Lambda "m" type2 (
    Lambda "n" type2 (
    Lambda "f" type1 (
    Lambda "x" Base (
    Apply (Apply (Variable "m") (Variable "f"))
          (Apply (Apply (Variable "n") (Variable "f")) (Variable "x"))
    ))))

multerm :: Term
multerm =
    Lambda "m" type2 (
    Lambda "n" type2 (
    Lambda "f" type1 (
    Apply (Variable "m") (Apply (Variable "n") (Variable "f")) 
    )))

suc :: Term -> Term
suc m = Apply sucterm m

add :: Term -> Term -> Term
add m n = Apply (Apply addterm m) n

mul :: Term -> Term -> Term
mul m n = Apply (Apply multerm m) n

example1 :: Term
example1 = suc (numeral 0)

example2 :: Term
example2 = numeral 2 `mul` (suc (numeral 2))

example3 :: Term
example3 = numeral 0 `mul` numeral 10

example4 :: Term
example4 = numeral 10 `mul` numeral 0

example5 :: Term
example5 = (numeral 2 `mul` numeral 3) `add` (numeral 5 `mul` numeral 7)

example6 :: Term
example6 = (numeral 2 `add` numeral 3) `mul` (numeral 3 `add` numeral 2)

example7 :: Term
example7 = numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` (numeral 2 `mul` numeral 2)))


-- - - - - - - - - - - -- Renaming, substitution, beta-reduction

used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x t n) = [x] `merge` used n
used (Apply  n m) = used n `merge` used m


rename :: Var -> Var -> Term -> Term
rename x y (Variable z)
    | z == x    = Variable y
    | otherwise = Variable z
rename x y (Lambda z t n)
    | z == x    = Lambda z t n
    | otherwise = Lambda z t (rename x y n)
rename x y (Apply n m) = Apply (rename x y n) (rename x y m)


substitute :: Var -> Term -> Term -> Term
substitute x n (Variable y)
    | x == y    = n
    | otherwise = Variable y
substitute x n (Lambda y t m)
    | x == y    = Lambda y t m
    | otherwise = Lambda z t (substitute x n (rename y z m))
    where z = fresh (used n `merge` used m `merge` [x,y])
substitute x n (Apply m p) = Apply (substitute x n m) (substitute x n p)


beta :: Term -> [Term]
beta (Apply (Lambda x t n) m) =
  [substitute x m n] ++
  [Apply (Lambda x t n') m  | n' <- beta n] ++
  [Apply (Lambda x t n)  m' | m' <- beta m]
beta (Apply n m) =
  [Apply n' m  | n' <- beta n] ++
  [Apply n  m' | m' <- beta m]
beta (Lambda x t n) = [Lambda x t n' | n' <- beta n]
beta (Variable _) = []

-- - - - - - - - - - - -- Normalize

something :: Int
something = 0

val :: String
val =  show something ++ " -- "

normalize :: Term -> IO ()
normalize m = do
  let upper      = bound m
  let upperBound = show upper ++ " -- "
  putStr upperBound 
  print m
  let ms   = beta m 
  if null ms 
  then do
    return ()
  else do
    normalize (head ms)




------------------------- Assignment 2: Type checking

type Context = [(Var, Type)]

inGamma :: Context -> Var -> Type
inGamma [] thisV = error $ "Variable " ++ thisV ++ " not found"
inGamma ((v, t):xs) thisV
  | thisV == v = t
  | otherwise = inGamma xs thisV


checkType :: Type -> Type -> Type
checkType term1 term2 =
  if term2 == Base then
    error "Expecting ARROW type, but given BASE type"
  else
    checkType' term1 term2
 
checkType' :: Type -> Type -> Type
checkType' input (expected :-> output)
  | input == expected = output
  | otherwise = error $ "Expecting type " ++ show expected ++ " , but given type " ++ show input


typeof :: Context -> Term -> Type
typeof xs (Variable x)   = inGamma xs x

typeof [] (Lambda x t m) = t :-> typeof [(x, t)] m
typeof xs (Lambda x t m) = t :-> typeof ((x, t):xs) m

typeof [] (Apply m' n)   = checkType (typeof [] n) (typeof [] m')
typeof xs (Apply m' n)   = checkType (typeof xs n) (typeof xs m')


example8 = Lambda "x" Base (Apply (Apply (Variable "f") (Variable "x")) (Variable "x"))




------------------------- Assignment 3: Functionals

data Functional =
    Num Int
  | Fun (Functional -> Functional)

instance Show Functional where
  show (Num i) = "Num " ++ show i
  show (Fun f) = "Fun ??"

fun :: Functional -> Functional -> Functional
fun (Fun f) = f

-- - - - - - - - - - - -- Examples

add' :: Functional -> Functional
add' (Num a) = Fun (addF (Num a))

addF :: Functional -> Functional ->Functional
addF (Num a) (Num b) = Num (a + b)

addsix :: Functional -> Functional
addsix (Num a) = Num (a + 6)

plus :: Functional
plus = Fun (add')

plussix :: Functional
plussix = Fun addsix

twice :: Functional
twice = Fun (twice')

twice' :: Functional -> Functional
twice' (Fun f) = Fun (twice'' (Fun f))

twice'' :: Functional-> Functional-> Functional
twice'' (Fun f) (Num a) = f (f (Num a))

-- - - - - - - - - - - -- Constructing functionals

count :: Type -> Functional -> Int
count (a :-> b) (Fun f) = count b (fun (Fun f) (dummy a))
count Base (Num base) = base

dummy :: Type -> Functional
dummy Base = Num 0
dummy (Base :-> b) = Fun (dummy' b)
dummy (a :-> b) = Fun (dummy' a)

dummy' :: Type -> Functional -> Functional
dummy' Base _ = Num 0
dummy' (a :-> b) (Fun f) = Fun f

increment :: Functional -> Int -> Functional
increment (Num a) b = Num (a + b)
increment (Fun f) b = Fun (increment' (Fun f) b)

increment' :: Functional -> Int -> Functional -> Functional
increment' (Fun f) a (Fun f') = Fun (increment' (fun (Fun f) (Fun f')) a)
increment' (Fun f) a (Num b) = fun (fun plus (fun (Fun f) (Num b))) (Num a)




------------------------- Assignment 4: Counting reduction steps

type Valuation = [(Var, Functional)]

interpret :: Context -> Valuation -> Term -> Functional
interpret context [] (Variable a)        = dummy (typeof context (Variable a))
interpret context val  (Variable a)      = head
  where head:xs = [f | (thisV, f) <- val, thisV == a]
interpret context val (Lambda a t term)  = Fun (interpret' context val (Lambda a t term))
interpret context val (Apply term term') = increment (fun f g) (1+count (typeof context term')g)
  where
    f = interpret context val term
    g = interpret context val term'

bound :: Term -> Int
bound t = count (typeof [] t) (interpret [] [] t)

interpret' :: Context -> Valuation -> Term -> Functional -> Functional
interpret' context val (Lambda a t term)g = interpret((a, t) :context) ((a, g) :val)term
