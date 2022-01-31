module Iso

import Language.Reflection

%default total
%language ElabReflection

-- taken from Data.List in Idris1 (not present in Idris2)
parameters (f : b -> c,
            g : a -> b)
  ||| Prove that mapping two functions is the same as mapping their composition.
  mapFusion : (l : List a) -> map f (map g l) = map (f . g) l
  mapFusion [] = Refl
  mapFusion (_ :: xs) = rewrite mapFusion xs in Refl

||| A witness that two types are isomorphic.
-- taken from Control.Isomorphism in Idris1 (not present in Idris2)
record Iso a b where
  constructor MkIso
  to : a -> b
  from : b -> a
  toFrom : (y : b) -> to (from y) = y
  fromTo : (x : a) -> from (to x) = x

||| A function that can decide equality for elements of type `t`.
DecEqFn : Type -> Type
DecEqFn t = (x, y : t) -> Dec (x = y)

||| Use an isomorphism between two types to convert an equality decision function on the former to one on the latter.
decEqFromIso : Iso t u -> DecEqFn t -> DecEqFn u
decEqFromIso iso eq_t x y =
  case eq_t (iso.from x) (iso.from y) of
       Yes prf => Yes $
                 rewrite sym $ iso.toFrom y in
                 rewrite sym $ iso.toFrom x in
                 cong iso.to prf
       No  prf => No $ \premise => prf $ cong iso.from premise

||| The sum of a list of types.
Sum     : List Type -> Type
Sum     = foldr Either Void
||| The product of a list of types.
Product : List Type -> Type
Product = foldr Pair ()

parameters {p, q : a -> Type} (f : (x : a) -> p x -> q x)
  ||| A generic way to map between two heterogenous products:
  ||| if the input and output both consist of some common structure (`p` or `q`),
  ||| then you can convert one into the other using a function that can convert
  ||| between these structures
  dependentMap : {ts : List a} -> Product (p <$> ts) -> Product (q <$> ts)
  dependentMap {ts = []}   ()     = ()
  dependentMap {ts = _::_} (h, t) = (f _ h, dependentMap t)

||| Decide whether two pairs are equal, given decisions about their elements.
decideProductEq : Dec (x1 = x2) -> Dec (y1 = y2) -> Dec ((x1, y1) = (x2, y2))
decideProductEq (Yes Refl) (Yes Refl) = Yes Refl
decideProductEq (No neq) _ = No $ \premise => neq (cong fst premise)
decideProductEq _ (No neq) = No $ \premise => neq (cong snd premise)

||| Construct an equality decision function on products, given
||| an equality decision function for each of the component types
deriveProductDecEq : (ts : _) -> Product (DecEqFn <$> ts) -> DecEqFn (Product ts)
deriveProductDecEq []     ()        ()       ()       = Yes Refl
deriveProductDecEq (_::_) (eq, eqs) (h1, t1) (h2, t2) =
  decideProductEq (eq h1 h2) (deriveProductDecEq _ eqs t1 t2)

||| Construct an equality decision function on `Either a b`, given
||| equality decision functions for both component types
decideSumEq : DecEqFn a -> DecEqFn b -> DecEqFn (Either a b)
decideSumEq eq_a _ (Left x) (Left y) =
  case eq_a x y of
       Yes prf => Yes $ cong Left prf
       No  prf => No $ \Refl => prf Refl
decideSumEq _ eq_b (Right x) (Right y) =
  case eq_b x y of
       Yes prf => Yes $ cong Right prf
       No  prf => No $ \Refl => prf Refl
decideSumEq _ _ (Left _) (Right _) = No absurd
decideSumEq _ _ (Right _) (Left _) = No absurd

||| Construct an equality decision function on sums, given
||| an equality decision function for each of the component types
deriveSumDecEq : (ts : _) -> Product (DecEqFn <$> ts) -> DecEqFn (Sum ts)
deriveSumDecEq (_::_) (eq, eqs) x y = decideSumEq eq (deriveSumDecEq _ eqs) x y

||| A sum of products of types.
SOPImpl : List (List Type) -> Type
SOPImpl ps = Sum (Product <$> ps)

||| A nested list of equality decision functions:
||| one for each type in a sum of products.
SOPDecEqFns : List (List Type) -> Type
SOPDecEqFns = Product . map (Product . map DecEqFn)

||| Construct an equality decision function on sums of products, given
||| equality decision functions for each of the component types
deriveSOPDecEq : (ps : List (List Type)) -> SOPDecEqFns ps -> DecEqFn (SOPImpl ps)
deriveSOPDecEq ps eqs = deriveSumDecEq (Product <$> ps) $
                        rewrite mapFusion DecEqFn Product ps in
                                dependentMap deriveProductDecEq eqs

||| A newtype for sums of products
data SOP : List (List Type) -> Type where
  MkSOP : SOPImpl ps -> SOP ps

||| Construct an equality decision function on the SOP wrapper type, given
||| equality decision functions for each of the component types
deriveDecEq : {ps : _} -> SOPDecEqFns ps -> DecEqFn (SOP ps)
deriveDecEq eqs (MkSOP x) (MkSOP y) =
  case eq x y of
       Yes p => Yes $ cong MkSOP p
       No  p => No $ \Refl => p Refl
  where
    eq : DecEqFn (SOPImpl ps)
    eq = deriveSOPDecEq ps eqs
