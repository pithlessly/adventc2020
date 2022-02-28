module Compute

%default total

-- lemma to turn a `Maybe` value into a proof of which constructor it is
deconstruct : (x : Maybe a) -> Either (x = Nothing) (y : a ** x = Just y)
deconstruct Nothing  = Left Refl
deconstruct (Just x) = Right (x ** Refl)

fmapNothing : {x : Maybe a} -> {f : a -> b} -> {y : b} ->
              (x = Nothing) -> (f <$> x = Just y) -> Void
fmapNothing Refl Refl impossible

bindNothing : {x : Maybe a} -> {f : a -> Maybe b} -> {y : b} ->
              (x = Nothing) -> (x >>= f = Just y) -> Void
bindNothing Refl Refl impossible

bindJust : {m : Maybe a} -> {f : a -> Maybe b} -> {x : a} ->
           (m = Just x) -> m >>= f = f x
bindJust Refl = Refl

-- A monad for computations that either produce a value of type `a`
-- or diverge.

record Compute a where
  constructor MkCompute
  -- try to compute the answer given a limited number of steps
  f : Nat -> Maybe a
  -- giving more steps doesn't affect the answer
  finishes : (n : Nat) -> (x : a) -> f n = Just x -> f (S n) = Just x

namespace Compute

  diverge : Compute a
  diverge = MkCompute (\_ => Nothing) (\_, _, eq => eq)

  return : a -> Compute a
  return x = MkCompute (\_ => Just x) (\_, _, eq => eq)

  fmap : (a -> b) -> Compute a -> Compute b
  fmap g (MkCompute f finishes) = MkCompute f' finishes'
  where
    f' : Nat -> Maybe b
    f' = map g . f

    finishes' : (n : Nat) -> (x : b) ->
                f' n = Just x ->
                f' (S n) = Just x
    finishes' n x worked_last_time =
      let same_last_time : f n ~=~ f (S n)
          same_last_time = case deconstruct (f n) of
                Left is_nothing =>
                  -- a contradiction: we are given both
                  --        f n = Nothing
                  --  g <$> f n = Just _
                  absurd $ fmapNothing is_nothing worked_last_time
                Right (y ** f_n_eq_Just_y) =>
                  -- `finishes` tells us that `f n` and `f (S n)`
                  -- are both equal to `Just y`, and things that are
                  -- equal to the same are also equal to each other
                  rewrite finishes n y f_n_eq_Just_y in f_n_eq_Just_y
      in rewrite sym same_last_time in worked_last_time

  join : Compute (Compute a) -> Compute a
  join (MkCompute f f_finishes) = MkCompute f' finishes'
  where
    f' : Nat -> Maybe a
    f' n = f n >>= \(MkCompute g _) => g n

    finishes' : (n : Nat) -> (x : a) -> f' n = Just x -> f' (S n) = Just x
    finishes' n x worked_last_time =
      case deconstruct (f n) of
        Left is_nothing =>
          -- a contradiction: we are given both
          --   f n         = Nothing
          --   f n >>= ... = Just _
          absurd $ bindNothing is_nothing worked_last_time
        Right (MkCompute g g_finishes ** is_just) =>
          -- we know:
          --    f n     = Just <inner computation>
          --    f (S n) = Just <inner computation>  (by `f_finishes`)
          --    g n     = Just x
          --    g (S n) = Just x                    (by `g_finishes`)
          -- therefore
          --    f' (S n) = f (S n) >>= \(MkCompute g _) => g (S n)
          --             = f n     >>= \(MkCompute g _) => g n
          --             = f' n
          let g_n_eq_Just_x =
              trans (sym (bindJust is_just)) worked_last_time
          in
          rewrite f_finishes _ _ is_just in
                  g_finishes _ _ g_n_eq_Just_x
