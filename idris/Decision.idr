module Decision

-- A type is considered a 'proposition' if all of its elements are equal.

IsProp : Type -> Type
IsProp t = (a, b : t) -> a = b

-- uip
eqIsProp : IsProp (a ~=~ b)
eqIsProp Refl Refl = Refl

-- It would be cool to have the property that a proof of a proposition
-- can be promoted from erased to unerased, as in:
unerase : IsProp t -> (0 _ : t) -> t
-- Unfortunately I don't think this can be implemented.

-- `Corresponds x f p` asserts that the function `f` decides the predicate `p` for the value `x`.
Corresponds : a -> (a -> Bool) -> (a -> Type) -> Type
Corresponds x f p = (f x = True -> p x, f x = False -> Not (p x))

-- `Decides a f p` asserts that the function `f` decides the predicate `p` for all values of type `x`.
Decides : (a : Type) -> (a -> Bool) -> (a -> Type) -> Type
Decides a f p = (x : a) -> Corresponds x f p

isEq : (n, m : Nat) -> ((n == m) = True) -> (n = m)
isEq  0     0    _   = Refl
isEq (S n) (S m) prf = cong S $ isEq n m prf
isEq  0    (S _) _   impossible
isEq (S _)  0    _   impossible

isNeq : (n, m : Nat) -> ((n == m) = False) -> Not (n = m)
isNeq 0 0 _ _ impossible
isNeq (S n) (S n) neq Refl = isNeq n n neq Refl
isNeq 0 (S k) neq eq = case eq of {}
isNeq (S k) 0 neq eq = case eq of {}

obvEq : (n : Nat) -> Decides Nat (n ==) (\m => n = m)
obvEq n m = (isEq n m, isNeq n m)

obvEq2 : (n : Nat) -> Decides Nat (n ==) (\m => n = m)
obvEq2  0     0    = (\Refl => Refl,          \c => case c of {})
obvEq2  0    (S _) = (\eq => case eq of {},   \Refl, eq => case eq of {})
obvEq2 (S _)  0    = (\eq => case eq of {},   \Refl, eq => case eq of {})
obvEq2 (S a) (S b) = let (eq', neq') = obvEq2 a b in
                     (\eq => cong S (eq' eq), \neq, Refl => neq' neq Refl)
