module CustomEq

-- Definition and basic properties of a custom definition of equality

Equal : (a : Type) -> a -> a -> Type
Equal a x y = (p : a -> Type) -> p x -> p y

refl : (a : Type) -> (x : a) -> Equal a x x
refl a x p px = px

sym : (a : Type) -> (x, y : a) -> Equal a x y -> Equal a y x
sym a x y eq = \p => eq (\t => p t -> p x) (\px => px)
{- alternatively:
sym a x y eq = eq (\t => Equal a t x) (refl a x)
-}

trans : (a : Type) -> (x, y, z : a) ->
        Equal a x y ->
        Equal a y z ->
        Equal a x z
trans a x y z xy yz = \p => yz p . xy p

cong : (a, b : Type) -> (f : a -> b) -> (x, y : a) ->
       Equal a x y -> Equal b (f x) (f y)
cong a b f x y eq = \p => eq (p . f)

-- Properties of equality that are independent of intensional type theory

AxiomK, UIPVariant, UIP : Type

AxiomK     = (a : Type) -> (x    : a) -> (p    : Equal a x x -> Type) -> p (refl a x) -> (h : Equal a x x) -> p h
UIPVariant = (a : Type) -> (x    : a) -> (e, f : Equal a x x) -> Equal (Equal a x x) e f
UIP        = (a : Type) -> (x, y : a) -> (e, f : Equal a x y) -> Equal (Equal a x y) e f

k_implies_uip_variant : AxiomK -> UIPVariant
k_implies_uip_variant axiom_k a x = \e, f => trans _ _ _ _ (only_refl e) (sym _ _ _ (only_refl f))
  where
    only_refl : (eq : Equal a x x) -> Equal _ eq (refl a x)
    only_refl = axiom_k a x (\t => Equal _ t (refl _ x)) (refl _ (refl _ x))

uip_variant_implies_uip : UIPVariant -> UIP
uip_variant_implies_uip uip_variant a x y e f =
  -- feels awkward... the first 'e' here could also be 'f'
  e (\t => (e, f : Equal a x t) -> Equal (Equal a x t) e f)
    (uip_variant a x)
    e f

uip_implies_k : UIP -> AxiomK
uip_implies_k uip a x p p_refl h = uip a x x (refl a x) h p p_refl

-- Conversions to/from Idris's usual definition of equality

toBuiltinEqual : (a : Type) -> (x, y : a) -> Equal a x y -> (x = y)
toBuiltinEqual a x y eq = eq (\t => x = t) Refl

fromBuiltinEqual : (a : Type) -> (x, y : a) -> (x = y) -> Equal a x y
fromBuiltinEqual a x x Refl = refl a x

-- Implementation of heterogenous equality

HEqual : (a : Type) -> (b : Type) -> a -> b -> Type
HEqual a b x y =
  (same_type : Equal Type a b **
   Equal b y (same_type id x))
