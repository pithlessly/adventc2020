%default total

-- A type of trees.
-- `t` is the type of data stored in a node.
-- `n` is the number of child nodes as a function of the data.

data W : (t : Type) -> (n : t -> Type) -> Type where
  MakeW : (tag : t) -> (children : n tag -> W t n) -> W t n

w_induction :
  (0 c : W t n -> Type) ->
  (f : (tag : t) -> (children : n tag -> W t n) ->
       (results : (i : n tag) -> c (children i)) ->
       c (MakeW tag children)) ->
  (w : W t n) -> c w

w_induction c f (MakeW tag children) =
  f tag children (\i => w_induction c f (children i))

w_recursion : ((tag : t) -> (n tag -> (W t n, c)) -> c) -> W t n -> c
w_recursion f =
  w_induction (\_ => c)
    (\tag, children, results =>
      f tag (\i => (children i, results i)))

w_recursion_spec :
  (f : (tag : t) -> (n tag -> (W t n, c)) -> c) ->
  (tag : t) -> (children : n tag -> W t n) ->
  w_recursion f (MakeW tag children) =
    f tag (\i => (children i, w_recursion f (children i)))
w_recursion_spec f tag children = Refl

WVoid : Type
WVoid = W Unit (\() => Unit)

w_absurd : WVoid -> Void
w_absurd = w_recursion (\(), tup => snd (tup ()))

WList : Type -> Type
WList t = W (Either () t) (\tag => case tag of
                                     Left () => Void
                                     Right _ => ())

roll : Either () (t, WList t) -> WList t
roll (Left ()) = MakeW (Left ()) absurd
roll (Right (t, ts)) = MakeW (Right t) (\_ => ts)

unroll : WList t -> Either () (t, WList t)
unroll = w_recursion $
  \tag => case tag of Left () => \_ => Left ()
                      Right t => \tup => Right (t, fst (tup ()))
