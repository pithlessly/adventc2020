-- Data type to represent that a thunk should have a particular value
-- without computing it.

-- I don't think this is really useful, because with the Chez
-- backend it seems like thunk values aren't actually cached-
-- instead they are just functions Unit -> a.

data Thunk : a -> Type where
  MkThunk : (0 x : a) -> (t : Lazy a) -> (0 _ : x = t) -> Thunk x

lz : (x : a) -> (f : a -> b) -> (x : a ** Thunk (f x))
lz x f = (x ** MkThunk (f x) (f x) Refl)

force : Thunk x -> (x' : _ ** x = x')
force (MkThunk (Force x) x Refl) = (Force x ** Refl)

-- dummy main to make it easier to view the compiled version
main : IO ()
main = pure ()
