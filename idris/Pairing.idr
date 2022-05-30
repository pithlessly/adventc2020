import Data.Nat as Nat

lteRefl : (n : Nat) -> LTE n n
lteRefl 0 = LTEZero
lteRefl (S n) = LTESucc (lteRefl n)

data Even : Nat -> Type where
  ZEven : Even 0
  SSEven : Even n -> Even (2+n)

Odd : Nat -> Type
Odd = Not . Even

odd1 : Odd 1
odd1 x impossible

x2even : (n : Nat) -> Even (n*2)
x2even 0 = ZEven
x2even (S n) = SSEven $ x2even n

x3even : (n : Nat) -> Even (n*3) -> Even n
x3even 0 ZEven = ZEven
x3even 1 (SSEven x) = x
x3even (S (S n)) (SSEven (SSEven (SSEven e))) = SSEven (x3even n e)

x3odd : (n : Nat) -> Odd n -> Odd (n*3)
x3odd n o premise = o $ x3even n premise

-- values that become equal when multiplied by nonzero
-- were equal in the first place
multCancel : (a, b, b' : Nat) -> b * S a = b' * S a -> b = b'
multCancel a 0 0 _ = Refl
multCancel a 0 (S b') prf = absurd $ SIsNotZ $ sym prf
multCancel a (S b) 0 prf = absurd $ SIsNotZ prf
multCancel a (S b) (S b') prf =
  cong S $ multCancel _ _ _ $
  plusLeftCancel _ _ _ $ succInjective _ _ prf

multCancel' : (a : Nat) -> NonZero a ->
              (b, b' : Nat) -> (a * b = a * b') -> b = b'
multCancel' (S a) SIsNonZero b b' prf =
  multCancel a b b' $
  rewrite multCommutative b (S a) in
  rewrite multCommutative b' (S a) in prf

-- multiplying two nonzero values yields a nonzero value
multPos : {a, b : Nat} -> NonZero a -> NonZero b -> NonZero (a * b)
multPos {a=S _, b=S _} _ _ = SIsNonZero

-- the lower bound of the product is the product of the lower bounds
multMonotone : {a, a', b, b' : Nat} ->
               LTE a a' -> LTE b b' -> LTE (a * b) (a' * b')
multMonotone {a=0} LTEZero _ = LTEZero
multMonotone {a=S a} (LTESucc s) b_lt = plusLteMonotone b_lt $ multMonotone s b_lt

-- decompose (a, b) into (min + da, min + db) where da * db = 0
decompose : (a, b : Nat) ->
            (min : Nat ** da : Nat ** db : Nat **
               (a = min + da, b = min + db, Either (da = 0) (db = 0)))
decompose 0 b = (0 ** 0 ** b ** (Refl, Refl, Left Refl))
decompose a 0 = (0 ** a ** 0 ** (Refl, Refl, Right Refl))
decompose (S a) (S b) =
  let (min ** da ** db ** (mka, mkb, t)) = decompose a b in
      (S min ** da ** db ** (cong S mka, cong S mkb, t))

infix 10 ^

(^) : Nat -> Nat -> Nat
(^) = power

-- b^n is nonzero if b is nonzero
powerPos : (b, n : Nat) -> NonZero b -> NonZero (b^n)
powerPos (S _) 0 _ = SIsNonZero
powerPos b (S k) bnz = multPos bnz $ powerPos _ _ bnz

-- (b^) is a semigroup homomorphism
powerAdd : (b, n, m : Nat) -> b^n * b^m = b^(n + m)
powerAdd b 0 m = plusZeroRightNeutral _
powerAdd b (S k) m =
  rewrite sym $ multAssociative b (b^k) (b^m) in
  rewrite powerAdd b k m in Refl

nz_lte1 : NonZero x -> LTE 1 x
nz_lte1 SIsNonZero = LTESucc LTEZero

-- (b^) is injective for 2≤b
powerInjective : (b, n, n' : Nat) -> LTE 2 b ->
                 b^n = b^n' -> n = n'
powerInjective _ 0 0 _ _ = Refl
powerInjective b 0 (S n') g2 prf =
  let lemma = multMonotone g2 $ nz_lte1 $
              powerPos b n' $ case b of S _ => SIsNonZero
  in case (prf, lemma) of (Refl, LTEZero) impossible
powerInjective _ _ 0 g2 prf =
  sym $ powerInjective _ 0 _ g2 $ sym prf
powerInjective b@(S b') (S n) (S n') g2 prf =
  cong S $ powerInjective _ _ _ g2 $ multCancel b' _ _ $
    rewrite multCommutative (b^n) b in
    rewrite multCommutative (b^n') b in prf

f : Nat -> Nat -> Nat
f x y = (3^x) * (2^y)

fAdd : (x1, y1, x2, y2 : Nat) ->
       f x1 y1 * f x2 y2 = f (x1 + x2) (y1 + y2)
fAdd x1 y1 x2 y2 =
  rewrite sym $ powerAdd 3 x1 x2 in
  rewrite sym $ powerAdd 2 y1 y2 in
  -- incredibly boring reordering of terms...
  rewrite sym $ multAssociative (3^x1) (2^y1) (3^x2 * 2^y2) in
  rewrite       multAssociative (2^y1) (3^x2) (2^y2) in
  rewrite       multCommutative (2^y1) (3^x2) in
  rewrite sym $ multAssociative (3^x2) (2^y1) (2^y2) in
  rewrite       multAssociative (3^x1) (3^x2) (2^y1 * 2^y2) in
  Refl

fInjectiveWeak1 : (x, y : Nat) -> f 0 0 = f x y -> (x = 0, y = 0)
fInjectiveWeak1 0 0 Refl = (Refl, Refl)
fInjectiveWeak1 x y@(S y') prf =
  let lowb : LTE 2 (f x y)
      lowb = multMonotone (nz_lte1 $ powerPos 3 x SIsNonZero)
                          (multMonotone (lteRefl 2) $
                           nz_lte1 $ powerPos 2 y' SIsNonZero)
  in
  case (prf, lowb) of (Refl, LTEZero) impossible
fInjectiveWeak1 x@(S x') y prf =
  let lowb : LTE 3 (f x y)
      lowb = multMonotone (multMonotone (lteRefl 3) $
                           nz_lte1 $ powerPos 3 x' SIsNonZero)
                          (nz_lte1 $ powerPos 2 y SIsNonZero)
  in
  case (prf, lowb) of (Refl, LTEZero) impossible

fInjectiveWeak2 : (x, y : Nat) -> f x 0 = f 0 y -> (x = 0, y = 0)
fInjectiveWeak2 0 0 Refl = (Refl, Refl)
fInjectiveWeak2 x@(S x') 0 prf =
  -- prf : 3^(S x) * 1 = 1
  let lowb : LTE 3 (f x 0)
      lowb = multMonotone (multMonotone (lteRefl 3) $
                           nz_lte1 $ powerPos 3 x' SIsNonZero)
                          (lteRefl 1)
  in case (prf, lowb) of (Refl, LTEZero) impossible
fInjectiveWeak2 x y@(S y') lhs_eq_rhs =
  let pow3_odd : (n : Nat) -> Odd (3^n)
      pow3_odd 0 = odd1
      pow3_odd (S n) = rewrite multCommutative 3 (3^n) in
                               x3odd (3^n) $ pow3_odd n
      lhs_odd : Odd (f x 0)
      lhs_odd = rewrite multOneRightNeutral (3^x) in pow3_odd x

      rhs_even : Even (f 0 y)
      rhs_even =
        rewrite plusZeroRightNeutral (2 * 2^y') in
        rewrite multCommutative 2 (2^y') in
        x2even (2^y')
  in absurd $
      lhs_odd $ rewrite lhs_eq_rhs in rhs_even

fInjectiveWeak : (x1, x2, y1, y2 : Nat) ->
                 f x1 y1 = f x2 y2 ->
                 Either (x1 = 0) (x2 = 0) ->
                 Either (y1 = 0) (y2 = 0) ->
                 (x1 = x2, y1 = y2)
fInjectiveWeak 0 x 0 y eq (Left Refl) (Left Refl) =
  let (x0, y0) = fInjectiveWeak1 x y eq in (sym x0, sym y0)
fInjectiveWeak 0 x y 0 eq (Left Refl) (Right Refl) =
  let (x0, y0) = fInjectiveWeak2 x y $ sym eq in (sym x0, y0)
fInjectiveWeak x _ 0 y eq (Right refl) (Left Refl) =
  case refl of Refl => let (x0, y0) = fInjectiveWeak2 x y eq in (x0, sym y0)
fInjectiveWeak x _ y _ eq (Right refl) (Right refl') =
  case (refl, refl') of
       (Refl, Refl) =>
         let (x0, y0) = fInjectiveWeak1 x y $ sym eq in (x0, y0)

fInjective : (x1, x2, y1, y2 : Nat) ->
             f x1 y1 = f x2 y2 ->
             (x1 = x2, y1 = y2)
fInjective x1 x2 y1 y2 eq =
  let (xmin ** xda ** xdb ** (x1e, x2e, xd0)) = decompose x1 x2
      (ymin ** yda ** ydb ** (y1e, y2e, yd0)) = decompose y1 y2
      divisor : Nat
      divisor = f xmin ymin
      divisorNZ : NonZero divisor
      divisorNZ = multPos (powerPos 3 _ SIsNonZero) (powerPos 2 _ SIsNonZero)
      deltasEq : (f xda yda = f xdb ydb)
      deltasEq = multCancel' divisor divisorNZ (f xda yda) (f xdb ydb) $
        rewrite fAdd xmin ymin xda yda in
        rewrite fAdd xmin ymin xdb ydb in
        rewrite sym x1e in
        rewrite sym y1e in
        rewrite sym x2e in
        rewrite sym y2e in
        eq
  in
  let (xde, yde) = fInjectiveWeak xda xdb yda ydb deltasEq xd0 yd0 in
  (rewrite x1e in rewrite x2e in cong (xmin +) xde,
   rewrite y1e in rewrite y2e in cong (ymin +) yde)
