%default total

-- =========================================================== --
-- A type of trees:                                            --
-- `t` is the type of data stored in a node.                   --
-- `n` is the number of child nodes as a function of the data. --
-- =========================================================== --

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

-- ============================================================= --
-- Implementations of some common inductive types in terms of W. --
-- ============================================================= --

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

-- =================================================== --
-- W lets us construct inductive types. We now attempt --
-- to generalize W to support inductive families.      --
-- =================================================== --

-- This dependent version of W ends up parameterized by a lot of data,
-- so we package it into a record (called DPF for "dependent polynomial
-- functor", which I think is vaguely what this represents).
record DPF where
  constructor MkDPF
  -- The context by which the family is indexed.
  Ctx : Type
  -- The type of data stored in a tree node,
  -- as a function of the context.
  Tag : Ctx -> Type
  -- The number of child nodes, as a function of:
  -- * The context
  -- * This node's data
  Deg : (ctx : Ctx) -> Tag ctx -> Type
  -- The context provided to a child node, as a function of:
  -- * The context of the this node
  -- * The number of child nodes
  -- * Which child node we are talking about
  child_ctx :
    (ctx : Ctx) -> (tag : Tag ctx) -> Deg ctx tag -> Ctx

data WD : (f : DPF) -> f.Ctx -> Type where
  MakeWD : (tag : f.Tag ctx) ->
           (children : (i : f.Deg ctx tag) -> WD f (f.child_ctx ctx tag i)) ->
           WD f ctx

-- ============================================================= --
-- It might seem that W is insufficient to represent inductive   --
-- families. But here we demonstrate an alternative construction --
-- of WD in terms of W. It is possible that this is dependent on --
-- Idris's handling of a specific feature (universes, totality   --
-- checking, large elimination, etc.) which would prevent it     --
-- from working in a real type theory.                           --
-- ============================================================= --

parameters (f : DPF)

  -- In this representation, each tree node contains the intended context as a field.
  UncheckedTree : Type
  UncheckedTree = W (ctx : f.Ctx ** f.Tag ctx) (\(ctx ** tag) => f.Deg ctx tag)

  -- Then, for a tree to be considered valid for a context ctx', we require that:
  Valid : f.Ctx -> UncheckedTree -> Type
  Valid ctx' (MakeW (ctx ** tag) children) =
    -- * the context associated with the root node is actually ctx';
    (ctx' = ctx,
    -- * each child node is valid for the context it should have (as given by child_ctx).
    (i : f.Deg ctx tag) -> Valid (f.child_ctx ctx tag i) (children i))

  -- An element of WD' is a tree paired with a guarantee that it is valid.
  WD' : f.Ctx -> Type
  WD' ctx = (t : UncheckedTree ** Valid ctx t)

  parameters (ctx : f.Ctx)
    -- A constructor with the same signature as WD:
    makeWD' : (tag : f.Tag ctx) ->
              (children : (i : f.Deg ctx tag) -> WD' (f.child_ctx ctx tag i)) ->
              WD' ctx
    makeWD' tag children =
      (MakeW (ctx ** tag) (\i => (children i).fst) ** (Refl, \i => (children i).snd))

-- =========================================================== --
-- Implementation of a common inductive family in terms of WD. --
-- =========================================================== --

WFinF : DPF
WFinF =
  let
    Ctx : Type
    Ctx = Nat

    Tag : Nat -> Type
    Tag Z = Void
    Tag (S _) = Bool

    Deg : (n : Nat) -> Tag n -> Type
    Deg Z _ impossible
    Deg (S _) True = Void
    Deg (S _) False = Unit

    child_ctx : (n : Nat) -> (tag : Tag n) -> Deg n tag -> Nat
    child_ctx Z _ _ impossible
    child_ctx (S _) True _ impossible
    child_ctx (S n) False () = n
  in MkDPF Ctx Tag Deg child_ctx

WFin : Nat -> Type
WFin = WD WFinF

w_fz : (k : Nat) -> WFin (S k)
w_fz k = MakeWD True (\v => absurd v)

w_fs : (k : Nat) -> WFin k -> WFin (S k)
w_fs k x = MakeWD False (\() => x)
