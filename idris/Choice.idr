import Control.Function.FunExt

-- The axiom of choice, sort of

choice : (r : a -> b -> Type) ->
         ((x : a) -> (y : b ** r x y)) ->
         (f : a -> b **
              (x : a) -> r x (f x))
choice r pf =
  (\x => fst (pf x) ** \x =>
        -- very strange...
        -- removing this pattern match makes the type checker fail, but trying
        -- to use the variable (e.g. let MkDPair _ y = pf x in y) also fails
        let MkDPair _ _ = pf x in
            DPair.snd (pf x))

-- Propositional truncation

Truncate : Type -> Type
Truncate a = Not (Not a)

truncate : a -> Truncate a
truncate x = \k => k x

truncated : FunExt => (x, y : Truncate a) -> x = y
truncated x _ = funExt (\not_a => absurd (x not_a))

Functor Truncate where
  map a_to_b not_not_a not_b = not_not_a (not_b . a_to_b)

-- Now for some formulations of the axiom of choice

0 Choice2, Choice3 : Type

Choice2 = (a : Type) -> (b : a -> Type) -> (c : (x : a) -> b x -> Type) ->
          -- if a relation has an inhabitant with some y for any x,
          ((x : a) -> Truncate (y : b x ** c x y)) ->
          -- then there is a function providing such an inhabitant for any x
          Truncate (f : (x : a) -> b x ** (x : a) -> c x (f x))

Choice3 = (a : Type) -> (b : a -> Type) ->
          -- if a family of types is inhabited at every point,
          ((x : a) -> Truncate (b x)) ->
          -- then there is a function providing such an inhabitant for any point
          Truncate ((x : a) -> b x)

-- These are equivalent to each other

left : Choice2 -> Choice3
left c2 a b pointwise =
  map {f=Truncate} (.fst) $
    c2 a b (\_, _ => Unit) $ \x =>
      map {f=Truncate} (\y => (y ** ()))
        (pointwise x)

right : Choice3 -> Choice2
right c3 a b c pointwise =
  map {f=Truncate} (\f => (\x => (f x).fst ** \x => (f x).snd)) $
    c3 a (\x => (y ** c x y)) pointwise
