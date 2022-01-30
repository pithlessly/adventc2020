-- Solutions to every problem from <https://learn-idris.net/problems>.

module Main

import Data.Vect

%default total

-- prove that a value is equal to itself

eq_self : a = a
eq_self = Refl

-- equivalence between LEM and DNE

DNE : Type
DNE = (t : Type) -> Not (Not t) -> t

LEM : Type
LEM = (t : Type) -> Either t (Not t)

dne_implies_lem : DNE -> LEM
dne_implies_lem dne t = dne _ (\k => k (Right (k . Left)))

lem_implies_dne : LEM -> DNE
lem_implies_dne lem t nnt =
  case lem t of
       Left a => a
       Right b => absurd (nnt b)

-- validity of TNE

TNE : Type
TNE = (t : Type) -> Not (Not (Not t)) -> Not t

tne : TNE
tne _ nnnt t = nnnt (\nt => nt t)

-- 0 is a left identity of (+)

zero_left_id : (n : Nat) -> 0 + n = n
zero_left_id _ = Refl

-- 0 is a right identity of (+)

zero_right_id : (n : Nat) -> n + 0 = n
zero_right_id 0 = Refl
zero_right_id (S k) = cong S (zero_right_id k)

-- (+) is associative

plus_assoc : (a, b, c : Nat) -> (a + b) + c = a + (b + c)
plus_assoc 0 b c = Refl
plus_assoc (S k) b c = cong S (plus_assoc k b c)

-- (+) is commutative

plus_comm : (m, n : Nat) -> n + m = m + n
plus_comm 0 n = zero_right_id n
plus_comm (S k) n =
  let 
    pcs : (n : Nat) -> n + S k = S (n + k)
    pcs 0 = Refl
    pcs (S j) = rewrite pcs j in Refl
  in
  rewrite plus_comm n k in pcs n

-- implement List take

my_take : Nat -> List a -> List a
my_take (S k) (x :: xs) = x :: my_take k xs
my_take _ _ = []

-- implement replicate

replicate : (n : Nat) -> a -> Vect n a
replicate Z _ = []
replicate (S k) a = a :: Main.replicate k a

-- concatenating lists adds their lengths

len_succ : (x : a) -> (xs : List a) -> length (x :: xs) = S (length xs)
len_succ _ _ = Refl

len_add : (xs, ys : List a) -> length (xs ++ ys) = length xs + length ys
len_add [] ys = Refl
len_add (x :: xs) ys = rewrite len_succ x (xs ++ ys) in cong S (len_add xs ys)

-- map preserves list length

map_len : (f : a -> b) -> (xs : List a) -> length xs = length (map f xs)
map_len _ [] = Refl
map_len f (_ :: xs) = cong S (map_len f xs)

-- equality of natural numbers is decideable

s_ne_z : (n : Nat) -> Not (Z = S n)
s_ne_z n premise = case premise of {}

eq_nat : (a, b : Nat) -> Dec (a = b)
eq_nat 0     0     = Yes Refl
eq_nat 0     (S k) = No (s_ne_z k)
eq_nat (S k) 0     = No (\t => s_ne_z k (sym t))
eq_nat (S k) (S j) = case eq_nat k j of
                          Yes p => Yes (cong S p)
                          No p => No (\Refl => p Refl)

-- check that a list contains an element

data Contains : a -> List a -> Type where
  Here : (x : a) -> (xs : List a) -> Contains x (x :: xs)
  There : (x : a) -> Contains y xs -> Contains y (x :: xs)

not_present : Not (x = y) -> Not (Contains x xs) -> Not (Contains x (y :: xs))
-- neither here nor there
not_present head_neq _        (Here _ _)  = head_neq Refl
not_present _ tail_nocontains (There _ w) = tail_nocontains w

parameters (eq_fn : (x, y : a) -> Dec (x = y)) -- screw type classes
           (x : a)

  list_contains : (xs : List a) -> Dec (Contains x xs)
  list_contains [] = No (\premise => case premise of {})
  list_contains (y :: ys) =
    case eq_fn x y of
         Yes head_eq => Yes (rewrite head_eq in Here y ys)
         No head_neq =>
                case list_contains ys of
                     Yes tc => Yes (There _ tc)
                     No tnc => No (not_present head_neq tnc)
