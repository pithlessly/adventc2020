module DList

import Data.List as List

data DList : Type -> Type where
  MkDList : (f : List a -> List a) ->
            {0 repr : List a} ->
            {1 isDList : (suffix : List a) -> (f suffix = repr ++ suffix)} ->
            DList a

fromList : List a -> DList a
fromList xs = MkDList (xs ++) {isDList = \_ => Refl}

toList : DList a -> List a
toList (MkDList f) = f []

isoLeft : (a : List t) -> toList (fromList a) = a
isoLeft a = List.appendNilRightNeutral a

-- Without function extensionality, we don't have
--  isoRight : (a : DList t) -> fromList (toList a) = a

(::) : a -> DList a -> DList a
x :: MkDList f {repr} {isDList} =
  MkDList ((x ::) . f)
  {repr = x::repr}
  {isDList = \suffix => rewrite isDList suffix in Refl}

(++) : DList a -> DList a -> DList a
(++) (MkDList f {repr=r1} {isDList=pf1})
     (MkDList g {repr=r2} {isDList=pf2}) =
  MkDList (f . g)
    {repr = r1 ++ r2}
    {isDList = \suffix =>
        rewrite sym $ List.appendAssociative r1 r2 suffix in
        rewrite pf1 (g suffix) in
        rewrite pf2 suffix in
                Refl}

appendIso : (a, b : DList _) -> toList (a ++ b) = toList a ++ toList b
appendIso (MkDList f {repr=r1} {isDList=pf1})
          (MkDList g {repr=r2} {isDList=pf2}) =
  rewrite pf2 [] in
  rewrite List.appendNilRightNeutral r2 in
  rewrite pf1 r2 in
  rewrite pf1 [] in
  rewrite List.appendAssociative r1 [] r2 in
          Refl
