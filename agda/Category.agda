{-# OPTIONS --type-in-type #-}

open import Data.Nat.Base hiding (_⊔_)
open import Data.Fin.Base
open import Relation.Binary.PropositionalEquality
-- open import Axiom.Extensionality.Propositional

module Limit where

-- a → b   is sugar for (_ : a) → b
-- ∀ a → b is sugar for (a : _) → b

record category : Set where
  constructor mk-category
  field
    obj : Set
    hom : obj → obj → Set
    id  : ∀{a} → hom a a
    ∘   : ∀{a b c} → hom b c → hom a b → hom a c
    id-l    : ∀{a b} (f : hom a b) → (∘ id f) ≡ f
    id-r    : ∀{a b} (f : hom a b) → f ≡ (∘ id f)
    ∘-assoc : ∀{a b c d} (f : hom c d) (g : hom b c) (h : hom a b) → (∘ (∘ f g) h) ≡ (∘ f (∘ g h))
open category

discrete : Set → category
discrete A .obj         = A
discrete A .hom a b     = a ≡ b
discrete A .id          = refl
discrete A .∘ refl refl = refl
discrete A .id-l refl              = refl
discrete A .id-r refl              = refl
discrete A .∘-assoc refl refl refl = refl

set : category
set .obj     = Set
set .hom a b = (a → b)
set .id      = λ x → x
set .∘ f g   = λ x → f (g x)
set .id-l f        = refl
set .id-r f        = refl
set .∘-assoc f g h = refl

_[_,_] : (C : category) → C .obj → C .obj → Set
_[_,_] = hom

record functor (C D : category) : Set where
  field
    F₀ : C .obj → D .obj
    F₁ : ∀{a b} → C [ a , b ] → D [ F₀ a , F₀ b ]
    F-id : ∀{a} → F₁ (C .id {a}) ≡ D .id {F₀ a}
    F-∘  : ∀{a b c} (f : C [ b , c ]) (g : C [ a , b ]) →
           (F₁ (C .∘ f g)) ≡ (D .∘ (F₁ f) (F₁ g))
open functor

F1 : {C : category} → functor C C
F1 .F₀   = λ a → a
F1 .F₁   = λ f → f
F1 .F-id = refl
F1 .F-∘  = λ f g → refl

functor-∘ : {A B C : category} → (f : functor B C) → (g : functor A B) → functor A C
functor-∘ f g .F₀   = λ a → f .F₀ (g .F₀ a)
functor-∘ f g .F₁   = λ m → f .F₁ (g .F₁ m)
functor-∘ f g .F-id = trans (cong (f .F₁) (g .F-id)) (f .F-id)
functor-∘ f g .F-∘  = λ m₁ m₂ → trans (cong (f .F₁) (g .F-∘ m₁ m₂)) (f .F-∘ (g .F₁ m₁) (g .F₁ m₂))

cat : category
cat .obj = category
cat .hom = λ c d → functor c d
cat .id  = F1
cat .∘   = λ f g → functor-∘ f g
-- feels like these should be provable by eta on functors, but isn't?
cat .id-l f = {!!}
cat .id-r f = {!!}
cat .∘-assoc = {!!}
