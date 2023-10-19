module TransitiveClosure where

Rel : Set → Set₁
Rel a = a → a → Set

-- the reflexive transitive closure of `r` is the type of finite chains as follows:
data RTC1 {a : Set} (r : Rel a) : Rel a where
  refl : ∀ {x} → RTC1 r x x
  _::_ : ∀ {x y z} → r x y → RTC1 r y z → RTC1 r x z

_rtc1-∘_ : ∀ {a} {r : Rel a} {x y z : _} → RTC1 r x y → RTC1 r y z → RTC1 r x z
refl      rtc1-∘ c = c
(r :: c') rtc1-∘ c = r :: (c' rtc1-∘ c)

-- an alternative definition: the reflexive transitive closure of `r` is
-- the intersection of all reflexive transitive relations containing `r`
data RTC2 {a : Set} (r : Rel a) : a → a → Set₁ where
  all-rs : ∀ x y →
           (∀ (r' : Rel a) →
              (∀ x → r' x x) →
              (∀ x y z → r' x y → r' y z → r' x z) →
              (∀ x y → r x y → r' x y) →
              r' x y) →
           RTC2 r x y

-- these definitions are equivalent, but RTC2 is impredicative and therefore probably worse

RTC1→RTC2 : ∀ {a r} {x y : a} → RTC2 r x y → RTC1 r x y
RTC1→RTC2 {a} {r} (all-rs x y p) = p (RTC1 r) (λ _ → refl) (λ _ _ _ → _rtc1-∘_) (λ _ _ rxy → rxy :: refl)

RTC2→RTC1 : ∀ {a r} {x y : a} → RTC1 r x y → RTC2 r x y
RTC2→RTC1 {a} {r} {x} {y} chain = all-rs x y (walk chain) where
  walk : ∀ {x y} → RTC1 r x y →
         (r' : Rel a) →
         ((x₁ : a) → r' x₁ x₁) →
         ((x₁ y₁ z : a) → r' x₁ y₁ → r' y₁ z → r' x₁ z) →
         ((x₁ y₁ : a) → r x₁ y₁ → r' x₁ y₁) → r' x y
  walk refl         r' r'-refl _        r→r' = r'-refl _
  walk (p :: chain) r' r'-refl r'-trans r→r' = r'-trans _ _ _ (r→r' _ _ p)
                                                              (walk chain r' r'-refl r'-trans r→r')
