%default total

Top1 : Type
Top1 = ()

data Top2 = MkTop2

eta1 : (x : Top1) -> x = ()
-- eta1 x = Refl -- works in Agda due to definitional eta, but not Idris
eta1 () = Refl
