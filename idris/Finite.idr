module Finite

import Data.Nat
import Data.Fin
import Decidable.Equality

%default total

-- "a type t is finite iff:
-- any f : (t -> t) having a left inverse also has a right inverse"
IsFinite : Type -> Type
IsFinite t =
  (f, g : t -> t) ->
  ((x : t) -> f (g x) = x) ->
  ((y : t) -> (x : t ** g x = y))

f0 : IsFinite Void
f0 _ _ _ _ impossible

allUnit : (0 x : Unit) -> x = ()
allUnit () = Refl

f1 : IsFinite Unit
f1 f g inj () = (() ** allUnit (g ()))

nat : Not (IsFinite Nat)
nat premise =
  -- consider the injection g = succ and its left inverse f = pred.
  -- (we don't care about the behavior of f outside the image of g.)
  case premise pred S (\_ => Refl) Z of
       (_ ** _) impossible

leftInverseImpliesInjective :
  (0 f, g : a -> a) -> ((x : a) -> f (g x) = x) ->
  (x, y : a) -> g x = g y -> x = y
leftInverseImpliesInjective f g inv x y eq =
  rewrite sym $ inv x in
  rewrite sym $ inv y in
          cong f eq

-- Given a predicate on numbers in a range,
-- return either a number satisfying the predicate
-- or a proof that no numbers in the range satisfy it.
example : (n : Nat) ->
          (p : Fin n -> Type) ->
          ((i : Fin n) -> Dec (p i)) ->
          Dec (i : Fin n ** p i)
example 0 p f = No $ \(i ** _) => absurd i
example (S k) p f =
  case f 0 of
    Yes p_0 => Yes (0 ** p_0)
    No not_p_0 =>
      case example k (\i => p (FS i)) (\i => f (FS i)) of
        Yes (i ** p_i) => Yes (FS i ** p_i)
        No no_example => No $ \ex =>
          case ex of
            (0 ** p_0) => not_p_0 p_0
            (FS i ** p_i) => no_example (i ** p_i)

fin : (n : Nat) -> IsFinite (Fin n)
fin n f g inverse y =
  -- It's a little tricky to prove this. My current thought
  -- is that given a, we could continue to iterate g until
  -- we get back to a:
  --
  --      g      g          g      g
  --   a ---> b --->  ...  ---> z ---> a
  --
  -- The finitude of the type is what ensures that we eventually
  -- end up in a cycle. The injectivity of g ensures that we
  -- have to cycle back to a in particular. Then we can just
  -- return the last element z in the chain, since it has the
  -- property that g z = a.
  ?fixme

-- The problem with this characterization is that it doesn't
-- really compose well. For example, it's probably difficult
-- to implement:
--
--   (IsFinite a, IsFinite b) -> IsFinite (a, b)
--
-- because you end up dealing with functions from pairs to
-- pairs, but you're only given ways to work with functions
-- on the original components.
--
-- This is probably why the typical characterization of a
-- finite set is instead "bijective with Fin n for some n."
-- This lets you build these bijections compositionally
-- using arithmetic. But it also means you have to have a
-- notion of Fin and Nat, so it feels more complicated.
