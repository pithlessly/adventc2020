ind2 : (C : Bool -> Type) ->
       C True -> C False ->
       (x : Bool) -> C x
ind2 _ t _ True = t
ind2 _ _ f False = f

rec2 : (C : Type) -> C -> C -> Bool -> C
rec2 c = ind2 (\_ => c)

FunExt : Type
FunExt = (a : Type) -> (b : a -> Type) ->
         (f, g : (x : a) -> b x) ->
         ((x : a) -> f x = g x) ->
         f = g

-- Exercise 1.6 from the HoTT book:
-- assuming function extensionality, prove that this
-- definition of the non-dependent product type can
-- be proven to have the necessary induction principle

parameters (A, B : Type)
  Product : Type
  Product = (i : Bool) -> rec2 Type A B i

  pair : A -> B -> Product
  pair x y = ind2 (rec2 Type A B) x y

  parameters (funext : FunExt)
    product_ind : (C : Product -> Type) ->
                  ((a : A) -> (b : B) -> C (pair a b)) ->
                  (p : Product) -> C p
    product_ind c g p =
      let
        p' : Product
        p' = pair (p True) (p False)

        uniq : p' = p
        uniq = funext Bool (rec2 Type A B) p' p
                 (ind2 (\i => p' i = p i) Refl Refl)

        pairwise : c p'
        pairwise = g (p True) (p False)
      in
        rewrite sym uniq in pairwise

    -- The book only demands that this equality hold
    -- propositionally, so I'm not sure why it's possible
    -- to just use `Refl` here?
    -- It might be Idris assuming more about (=) than HoTT does

    spec : (C : Product -> Type) ->
           (g : (a : A) -> (b : B) -> C (pair a b)) ->
           (a : A) -> (b : B) ->
           product_ind C g (pair a b) = g a b
    spec c g a b = Refl
