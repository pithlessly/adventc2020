infixr 9 :*:
infixr 8 :+:
infixr 7 ~>

(:+:), (:*:) : (Type -> Type) -> (Type -> Type) -> (Type -> Type)
(f :+: g) x = Either (f x) (g x)
(f :*: g) x = Pair (f x) (g x)

(~>) : (Type -> Type) -> (Type -> Type) -> Type
f ~> g = {a : Type} -> f a -> g a

Id : Type -> Type
Id = id

data Zipper : (Type -> Type) -> (Type -> Type) where
  Var     :                                      Zipper Id a
  Sum     :       Zipper f :+: Zipper g       ~> Zipper (f :+: g)
  Product : f :*: Zipper g :+: Zipper f :*: g ~> Zipper (f :*: g)
  Chain   :       Zipper g :*: Zipper f . g   ~> Zipper (f . g)

fill : Zipper f a -> a -> f a
fill Var x = x
fill (Sum (Left  df)) x = Left  (fill df x)
fill (Sum (Right dg)) x = Right (fill dg x)
fill (Product (Left  (f, dg))) x = (f, fill dg x)
fill (Product (Right (df, g))) x = (fill df x, g)
fill (Chain (dg, df_g)) x = fill df_g $ fill dg x
