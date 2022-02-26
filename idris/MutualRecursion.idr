module MutualRecursion

even : Nat -> Bool
odd  : Nat -> Bool

even 0 = True
even (S n) = odd n
odd 0 = False
odd (S n) = even n
