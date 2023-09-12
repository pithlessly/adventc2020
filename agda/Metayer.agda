open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty

_≡[_]≡_ : ∀ {A} {B} → A → (A ≡ B) → B → Set
a ≡[ refl ]≡ b = a ≡ b

record is-quotient (A : Set) (r : A → A → Set) (A/r : Set) : Set₁ where
  field
    [_] : A → A/r
    relate : ∀ {a₀} {a₁} → r a₀ a₁ → [ a₀ ] ≡ [ a₁ ]
    induct : (Q     : A/r → Set)
             (Q[_]  : (a : A) → Q [ a ]) →
             (Q[_]≡ : ∀ {a₀} {a₁} → (p : r a₀ a₁) → Q[ a₀ ] ≡[ cong Q (relate p) ]≡ Q[ a₁ ]) →
             (q : A/r) → Q q

Set-has-all-quotients : Set₁
Set-has-all-quotients =
  ∀ A (r : A → A → Set) → Σ Set (is-quotient A r)

-- countable chains
record CC : Set₁ where
  field
    F₀ : ℕ → Set₀
    F₁ : (n : ℕ) → F₀ n → F₀ (suc n)
open CC

-- get from one position in a chain to another
step : ∀ {Δ} → (n m : ℕ) → n ≤′ m → Δ .F₀ n → Δ .F₀ m
step n n ≤′-refl F₀n = F₀n
step {Δ} n (suc m) (≤′-step c) F₀n = Δ .F₁ m (step {Δ} n m c F₀n)

record cocone-ω (Δ : CC) : Set₁ where
  constructor cocone
  field
    A : Set
    δ : (n : ℕ) → Δ .F₀ n → A
open cocone-ω

is-colim : ∀ {Δ} → cocone-ω Δ → Set₁
is-colim {Δ} (cocone A δ) =
  ((cocone A' δ') : cocone-ω Δ) → (A → A') -- omitting the coherences

Functor : (Set → Set) → Set₁
Functor F₀ = ∀ {a} {b} → (a → b) → (F₀ a → F₀ b)

precompose : (F₀ : Set → Set) (F₁ : Functor F₀) → CC → CC
precompose F₀ F₁ Δ .F₀ n = F₀ (CC.F₀ Δ n)
precompose F₀ F₁ Δ .F₁ n = F₁ (CC.F₁ Δ n)

Set-is-ω-category : Set₁
Set-is-ω-category = ∀ {Δ} → Σ (cocone-ω Δ) is-colim

S÷→Sω : Set-has-all-quotients → Set-is-ω-category
S÷→Sω S÷ {Δ} = co , co-is-colim where
  base : Set
  base = Σ ℕ (Δ .F₀)

  converge : base → base → Set
  converge (n₀ , o₀) (n₁ , o₁) = Σ ℕ λ n₂ →
    Σ (n₀ ≤′ n₂) λ n₀≤n₂ →
    Σ (n₁ ≤′ n₂) λ n₁≤n₂ →
      step {Δ} n₀ n₂ n₀≤n₂ o₀ ≡ step {Δ} n₁ n₂ n₁≤n₂ o₁

  label : Set
  label-q : is-quotient base converge label
  label   = S÷ base converge .fst
  label-q = S÷ base converge .snd

  open is-quotient label-q

  co : cocone-ω Δ
  co = cocone label (λ n o → [ n , o ])

  postulate
    -- this can't be proven without stating the coherence conditions in is-colim
    co-is-colim : is-colim co

ω-continuous : (F₀ : Set → Set) (F₁ : Functor F₀) → Set₁
ω-continuous F₀ F₁ =
  ∀ {Δ : CC} → (c : cocone-ω Δ) → is-colim c →
    Σ (cocone-ω (precompose F₀ F₁ Δ)) is-colim

module _ (sω : Set-is-ω-category) (F₀ : Set → Set) (F₁ : Functor F₀) where
  iterF₀ : ℕ → Set
  iterF₀ zero    = ⊥
  iterF₀ (suc n) = F₀ (iterF₀ n)

  iterF₁ : (n : ℕ) → iterF₀ n → iterF₀ (suc n)
  iterF₁ zero = ⊥-elim
  iterF₁ (suc n) = F₁ (iterF₁ n)

  Δ : CC
  CC.F₀ Δ = iterF₀
  CC.F₁ Δ = iterF₁

  ω-fixpoint-cocone : cocone-ω Δ
  ω-fixpoint-cocone = sω .fst

  ω-fixpoint : Set
  ω-fixpoint = ω-fixpoint-cocone .A

  ω-fixpoint-δ : Σ ℕ iterF₀ → ω-fixpoint
  ω-fixpoint-δ (n , o) = ω-fixpoint-cocone .δ n o

  ω-fixpoint-is-colim : (A' : Set) → (Σ ℕ iterF₀ → A') → (ω-fixpoint → A')
  ω-fixpoint-is-colim A' δ' = sω .snd (cocone A' (λ n o → δ' (n , o)))

  to : ω-fixpoint → F₀ ω-fixpoint
  to ωf with ω-fixpoint-is-colim (Σ ℕ iterF₀) (λ p → p) ωf
  to _ | zero , o = ⊥-elim o
  to _ | suc n , o = F₁ (λ o → ω-fixpoint-δ (n , o)) o

  postulate
    from : F₀ ω-fixpoint → ω-fixpoint
