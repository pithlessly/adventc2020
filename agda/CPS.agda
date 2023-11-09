open import Data.List
open import Data.Nat

module CPS where

module _ {a : Set} where

  data _∈_ : a → List a → Set where
    here  : ∀ {x   xs} → x ∈ (x ∷ xs)
    there : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

  data _⊆_ : List a → List a → Set where
    id   : ∀ {xs} → xs ⊆ xs
    keep : ∀ {x xs ys} → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)
    skip : ∀ {x xs ys} → xs ⊆ ys →      xs  ⊆ (x ∷ ys)

  ∈-⊆ : ∀ {x xs ys} → x ∈ xs → xs ⊆ ys → x ∈ ys
  ∈-⊆ loc id = loc
  ∈-⊆ loc (skip rest) = there (∈-⊆ loc rest)
  ∈-⊆ (there loc) (keep rest) = there (∈-⊆ loc rest)
  ∈-⊆ here (keep _) = here

∈-map : ∀ {a b x xs} → (f : a → b) → x ∈ xs → f x ∈ map f xs
∈-map f here = here
∈-map f (there x) = there (∈-map f x)

module F1 where

  data ty : Set where
    nat  : ty
    arr  : ty → ty → ty
    prod : ty → ty → ty
  
  data term : List ty → ty → Set where
    vv   : ∀ {Γ a}   → a ∈ Γ → term Γ a
    lit  : ∀ {Γ}     → ℕ → term Γ nat
    lam  : ∀ {Γ a b} → term (a ∷ Γ) b → term Γ (arr a b)
    ap   : ∀ {Γ a b} → term Γ (arr a b) → term Γ a → term Γ b
    prod : ∀ {Γ a b} → term Γ a → term Γ b → term Γ (prod a b)
    fst  : ∀ {Γ a b} → term Γ (prod a b) → term Γ a
    snd  : ∀ {Γ a b} → term Γ (prod a b) → term Γ b
  
  data cps-ty : Set where
    nat  : cps-ty
    neg  : cps-ty → cps-ty
    prod : cps-ty → cps-ty → cps-ty
  
  mutual
    data cps-value : List cps-ty → cps-ty → Set where
      vv   : ∀ {Γ a}   → a ∈ Γ → cps-value Γ a
      lit  : ∀ {Γ}     → ℕ → cps-value Γ nat
      lam  : ∀ {Γ a}   → cps-expr (a ∷ Γ) → cps-value Γ (neg a)
      prod : ∀ {Γ a b} → cps-value Γ a → cps-value Γ b → cps-value Γ (prod a b)
      fst  : ∀ {Γ a b} → cps-value Γ (prod a b) → cps-value Γ a
      snd  : ∀ {Γ a b} → cps-value Γ (prod a b) → cps-value Γ b
  
    data cps-expr : List cps-ty → Set where
      ap   : ∀ {Γ a} → cps-value Γ (neg a) → cps-value Γ a → cps-expr Γ
  
  mutual
    weaken-v : ∀ {Γ₁ Γ₂ a} → Γ₁ ⊆ Γ₂ → cps-value Γ₁ a → cps-value Γ₂ a
    weaken-v subs (vv   loc  ) = vv (∈-⊆ loc subs)
    weaken-v subs (lit  n    ) = lit n
    weaken-v subs (lam  e    ) = lam (weaken-e (keep subs) e)
    weaken-v subs (prod v₁ v₂) = prod (weaken-v subs v₁) (weaken-v subs v₂)
    weaken-v subs (fst  v    ) = fst (weaken-v subs v)
    weaken-v subs (snd  v    ) = snd (weaken-v subs v)
  
    weaken-e : ∀ {Γ₁ Γ₂} → Γ₁ ⊆ Γ₂ → cps-expr Γ₁ → cps-expr Γ₂
    weaken-e subs (ap k x) = ap (weaken-v subs k) (weaken-v subs x)
  
  cps-let : ∀ {Γ a} → cps-value Γ a → cps-expr (a ∷ Γ) → cps-expr Γ
  cps-let v e = ap (lam e) v

  v₀ : ∀ {Γ a}     → cps-value (a ∷ Γ) a
  v₁ : ∀ {Γ a b}   → cps-value (b ∷ a ∷ Γ) a
  v₂ : ∀ {Γ a b c} → cps-value (c ∷ b ∷ a ∷ Γ) a
  v₀ = vv here
  v₁ = vv (there here)
  v₂ = vv (there (there here))

  cps-pure : ∀ {Γ a} → cps-value Γ a → cps-expr (neg a ∷ Γ)
  cps-pure v = ap v₀ (weaken-v (skip id) v)

  cps-bind : ∀ {Γ a b} → cps-expr (neg a ∷ Γ) → cps-expr (a ∷ b ∷ Γ) → cps-expr (b ∷ Γ)
  cps-bind e₁ e₂ = cps-let (lam e₂) (weaken-e (keep (skip id)) e₁)

  ⟦_⟧t : ty → cps-ty
  ⟦ nat      ⟧t = nat
  ⟦ prod a b ⟧t = prod ⟦ a ⟧t ⟦ b ⟧t
  ⟦ arr  a b ⟧t = neg (prod ⟦ a ⟧t (neg ⟦ b ⟧t))

  ⟦_⟧c : List ty → List cps-ty
  ⟦_⟧c = map ⟦_⟧t

  ⟦_⟧e : ∀ {Γ a} → term Γ a → cps-expr (neg ⟦ a ⟧t ∷ ⟦ Γ ⟧c)
  ⟦ vv  n ⟧e = cps-pure (vv (∈-map ⟦_⟧t n))
  ⟦ lit n ⟧e = cps-pure (lit n)
  ⟦ lam e ⟧e = cps-pure (lam
                          (cps-let (fst v₀)
                            (cps-let (snd v₁)
                              (weaken-e (keep (keep (skip id))) ⟦ e ⟧e))))
  ⟦ ap e₁ e₂ ⟧e =
    cps-bind ⟦ e₁ ⟧e
      (cps-bind (weaken-e (keep (skip id)) ⟦ e₂ ⟧e)
        (ap v₁ (prod v₀ v₂)))
  ⟦ prod e₁ e₂ ⟧e =
    cps-bind ⟦ e₁ ⟧e
      (cps-bind (weaken-e (keep (skip id)) ⟦ e₂ ⟧e)
        (ap v₂ (prod v₁ v₀)))
  ⟦ fst e ⟧e = cps-bind ⟦ e ⟧e (ap v₁ (fst v₀))
  ⟦ snd e ⟧e = cps-bind ⟦ e ⟧e (ap v₁ (snd v₀))

module F1-Delim where

  data ty : Set where
    nat  : ty
    arr  : ty → ty → ty → ty
    prod : ty → ty → ty

  mutual
    data value : List ty → ty → Set where
      vv   : ∀ {Γ a}     → a ∈ Γ → value Γ a
      lit  : ∀ {Γ}       → ℕ → value Γ nat
      lam  : ∀ {Γ e a b} → expr (a ∷ Γ) e b → value Γ (arr e a b)
      prod : ∀ {Γ a b}   → value Γ a → value Γ b → value Γ (prod a b)
      fst  : ∀ {Γ a b}   → value Γ (prod a b) → value Γ a
      snd  : ∀ {Γ a b}   → value Γ (prod a b) → value Γ b

    data expr : List ty → ty → ty → Set where
      pure    : ∀ {Γ e a}      → value Γ a → expr Γ e a
      bind    : ∀ {Γ e a b}    → expr Γ e a → expr (a ∷ Γ) e b → expr Γ e b
      ap      : ∀ {Γ e a b}    → value Γ (arr e a b) → value Γ a → expr Γ e b
      prompt  : ∀ {Γ e e′}     → expr Γ e′ e′ → expr Γ e e′
      control : ∀ {Γ e a}      → expr (arr e a e ∷ Γ) e e → expr Γ e a

  open F1 using (cps-ty; cps-value; cps-expr; v₀; v₁; v₂; weaken-v; weaken-e; cps-let; cps-bind)
  open cps-ty
  open cps-value
  open cps-expr

  cont-record : cps-ty → cps-ty → cps-ty
  cont-record e b = prod
    -- continuation beyond the innermost `prompt`
    (neg e)
    -- continuation between the innermost `prompt` and the current term
    (neg (prod b (neg e)))

  ⟦_⟧t : ty → cps-ty
  ⟦ nat        ⟧t = nat
  ⟦ prod   a b ⟧t = prod ⟦ a ⟧t ⟦ b ⟧t
  ⟦ arr  e a b ⟧t = neg (prod ⟦ a ⟧t (cont-record ⟦ e ⟧t ⟦ b ⟧t))

  ⟦_⟧c : List ty → List cps-ty
  ⟦_⟧c = map ⟦_⟧t

  cps-throw : ∀ {Γ e a} → cps-value Γ (cont-record e a) → cps-value Γ a → cps-expr Γ
  cps-throw vk vx = ap (snd vk) (prod vx (fst vk))

  cps-newrecord : ∀ {Γ e} → cps-value Γ (neg e) → cps-value Γ (cont-record e e)
  cps-newrecord k = prod k (lam (ap (snd v₀) (fst v₀)))

  mutual
    ⟦_⟧v : ∀ {Γ a} → value Γ a → cps-value ⟦ Γ ⟧c ⟦ a ⟧t
    ⟦ vv   n     ⟧v = vv (∈-map ⟦_⟧t n)
    ⟦ lit  n     ⟧v = lit n
    ⟦ lam  e     ⟧v = lam (cps-let (fst v₀)
                            (cps-let (snd v₁)
                              (weaken-e (keep (keep (skip id))) ⟦ e ⟧e)))
    ⟦ prod v₁ v₂ ⟧v = prod ⟦ v₁ ⟧v ⟦ v₂ ⟧v
    ⟦ fst  v     ⟧v = fst ⟦ v ⟧v
    ⟦ snd  v     ⟧v = snd ⟦ v ⟧v

    ⟦_⟧e : ∀ {Γ a e} → expr Γ e a → cps-expr (cont-record ⟦ e ⟧t ⟦ a ⟧t ∷ ⟦ Γ ⟧c)
    ⟦ pure    v     ⟧e =
      cps-throw v₀ (weaken-v (skip id) ⟦ v ⟧v)
    ⟦ bind    e₁ e₂ ⟧e =
      cps-let (prod (fst v₀)
                    (lam (cps-let (fst v₀)
                           (cps-let (prod (snd v₁) (snd v₂))
                             (weaken-e (keep (keep (skip (skip id)))) ⟦ e₂ ⟧e)))))
        (weaken-e (keep (skip id)) ⟦ e₁ ⟧e)
    ⟦ ap      vf vx ⟧e =
      ap (weaken-v (skip id) ⟦ vf ⟧v)
         (prod (weaken-v (skip id) ⟦ vx ⟧v) v₀)
    ⟦ prompt  e     ⟧e =
      cps-let (cps-newrecord (lam (cps-throw v₁ v₀)))
        (weaken-e (keep (skip id)) ⟦ e ⟧e)
    ⟦ control e     ⟧e =
      cps-let (lam               -- allocate a new continuation lambda capturing the current cont-record:
                (ap (snd v₁)       -- call the "shallow" part of the captured record...
                    (prod (fst v₀) --   with the argument to the lambda
                                   -- once that is finished, return to the caller:
                      (lam (cps-throw (snd v₁) v₀)))))
        (cps-let (cps-newrecord (fst v₁))
          (weaken-e (keep (keep (skip id))) ⟦ e ⟧e))
