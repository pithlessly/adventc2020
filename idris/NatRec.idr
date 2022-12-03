-- Induction principle for natural numbers.
-- (This is the only place we use pattern matching.)

ind : (p : Nat -> Type) ->
      p Z ->
      ((n : Nat) -> p n -> p (S n)) ->
      (n : Nat) -> p n
ind p z _ Z = z
ind p z s (S n) = s n (ind p z s n)

-- Two slightly different formulations of the recursion principle
-- for natural numbers. With `iter`, a function `s` is applied to
-- `z`, a base value, `n` times. With `rec`, the `s` function is
-- passed `n` as an additional argument.

NatIter, NatRec : Type
NatIter = (a : Type) -> a -> (       a -> a) -> Nat -> a
NatRec  = (a : Type) -> a -> (Nat -> a -> a) -> Nat -> a

-- Specifications of both versions.

NatIterSpec : NatIter -> Type
NatIterSpec iter =
  (a : Type) -> (z : a) -> (s : a -> a) ->
    (             iter a z s  Z    = z,
     (n : Nat) -> iter a z s (S n) = s (iter a z s n)
    )

NatRecSpec : NatRec -> Type
NatRecSpec rec =
  (a : Type) -> (z : a) -> (s : Nat -> a -> a) ->
    (             rec a z s  Z    = z,
     (n : Nat) -> rec a z s (S n) = s n (rec a z s n)
    )

-- Exercise 1.4 from the HoTT book:
-- define `rec` in terms of `iter`, and use the induction principle
-- to prove that this definition satisfies its specification.

rec_from_iter : NatIter -> NatRec
rec_from_iter iter a z s n =
  snd (iter (Nat, a) (Z, z) (\p => step p) n) where
    step : (Nat, a) -> (Nat, a)
    step p = (S (fst p), s (fst p) (snd p))

spec_compliant : (iter : NatIter) ->
                 NatIterSpec iter ->
                 NatRecSpec (rec_from_iter iter)
spec_compliant iter spec_i a z s = (spec_z, spec_s) where

  step : (Nat, a) -> (Nat, a)
  step p = (S (fst p), s (fst p) (snd p))

  iter' : Nat -> (Nat, a)
  iter' = iter (Nat, a) (Z, z) step

  rec' : Nat -> a
  rec' n = snd (iter' n)
  -- rec' = (rec_from_iter iter) a z s

  spec' : (             iter'  Z    = (Z, z),
           (n : Nat) -> iter' (S n) = step (iter' n))
  spec' = spec_i (Nat, a) (Z, z) step

  LoopInvariant : (n : Nat) -> Type
  LoopInvariant n = fst (iter' n) = n

  loop_invariant : (n : Nat) -> LoopInvariant n
  loop_invariant = ind LoopInvariant li_z li_s where

    li_z : LoopInvariant 0
    li_z = rewrite fst spec' in Refl

    li_s : (n : Nat) -> LoopInvariant n -> LoopInvariant (S n)
    li_s n prev = rewrite (snd spec') n in rewrite prev in Refl

  spec_z : snd (iter' Z) = z
  spec_z = rewrite fst spec' in Refl

  spec_s : (n : Nat) -> rec' (S n) = s n (rec' n)
  spec_s n = rewrite (snd spec') n in rewrite loop_invariant n in Refl
