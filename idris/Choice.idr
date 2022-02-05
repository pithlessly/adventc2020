-- The axiom of choice, sort of

choice : (r : a -> b -> Type) ->
         ((x : a) -> (y : b ** r x y)) ->
         (f : a -> b **
              (x : a) -> r x (f x))
choice r pf =
  (\x => fst (pf x) ** \x =>
        -- very strange...
        -- removing this pattern match makes the type checker fail, but trying
        -- to use the variable (e.g. let MkDPair _ y = pf x in y) also fails
        let MkDPair _ _ = pf x in
            DPair.snd (pf x))
