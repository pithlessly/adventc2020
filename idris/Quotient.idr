-- An attempt at defining a quotient type

Quotient : (a : Type) -> (a -> a -> Type) -> Type
Quotient a r =
  (q : Type) ->
    (inj : a -> q) ->
    (ext : (b : Type) ->
           (f : a -> b) ->
           ((x, y : a) -> r x y -> f x = f y) ->
           (elim : q -> b **
                   (x : a) -> f x = elim (inj x)))
  -> q

-- probably can't be defined unfortunately
q_everything : Quotient a (\_, _ => ())
