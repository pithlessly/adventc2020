module Iso

import Decidable.Equality

%default total

-- taken from Control.Isomorphism, which
-- doesn't seem to be supported in Idris 2
record Iso a b where
  constructor MkIso
  to : a -> b
  from : b -> a
  toFrom : (y : b) -> to (from y) = y
  fromTo : (x : a) -> from (to x) = x

decEqFromIso : Iso t u ->
               ((x, y : t) -> Dec (x = y)) ->
               ((x, y : u) -> Dec (x = y))
decEqFromIso iso eq_t x y =
  case eq_t (iso.from x) (iso.from y) of
       Yes prf => Yes $
                 rewrite sym $ iso.toFrom y in
                 rewrite sym $ iso.toFrom x in
                 cong iso.to prf
       No prf  => No $ \premise => prf $ cong iso.from premise
