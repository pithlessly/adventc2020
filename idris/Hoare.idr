module Hoare

import Data.List -- filter
import Decidable.Equality -- negEqSym

DecEqFn : Type -> Type
DecEqFn t = (x, y : t) -> Dec (x = y)

isYes : Dec p -> Bool
isYes (Yes _) = True
isYes (No _) = False

%default total

record Inputs where
  constructor MkInputs
  addr, reg, scalar : Type
  addr_eq    : DecEqFn addr
  reg_eq     : DecEqFn reg
  scalar_eq  : DecEqFn scalar
  scalar_add : scalar -> scalar -> scalar

namespace Hoare
  parameters (i : Inputs)
    public export
    data Location = Address i.addr | Register i.reg
    public export
    data Value = Pointer i.addr | Scalar i.scalar
    public export
    data Condition = Valid Location
                   | Contains Location Value

    -- pointers can be distinguished from other pointers,
    -- and scalars can be distinguished from other scalars,
    -- but we assume that pointers cannot be reliably distinguished from scalars
    couldBeSame : Value -> Value -> Bool
    couldBeSame (Pointer p) (Pointer p') = isYes (i.addr_eq p p')
    couldBeSame (Scalar n) (Scalar n') = isYes (i.scalar_eq n n')
    couldBeSame _ _ = True

    loc_eq : (x, y : Location) -> Dec (x = y)
    loc_eq (Address x) (Address y) =
      case i.addr_eq x y of
           Yes p => Yes (cong Address p)
           No p => No $ \Refl => p Refl
    loc_eq (Register x) (Register y) =
      case i.reg_eq x y of
           Yes p => Yes (cong Register p)
           No p => No $ \Refl => p Refl
    loc_eq (Address x) (Register y) = No $ \v => case v of {}
    loc_eq (Register x) (Address y) = No $ \v => case v of {}

    invalidate : Location -> List Condition -> List Condition
    invalidate loc = filter (not . delete) where
      delete : Condition -> Bool
      delete (Contains loc' _) = isYes $ loc_eq loc loc'
      delete _ = False

    notEqual : Location -> Value -> List Condition -> List Condition
    notEqual loc val = filter (not . delete) where
      delete : Condition -> Bool
      delete (Contains loc' val') = isYes (loc_eq loc loc') && couldBeSame val val'
      delete _ = False

    public export
    data Command : (pre, post : List Condition) -> Type where
      -- rearrange, duplicate, or drop conditions
      Shuffle : (0 f : forall a. List a -> List a) -> Command pre (f pre)
      -- registers are always valid
      RegValid : (0 r : _) -> Command conds (Valid (Register r) :: conds)
      -- if a location contains a value then it is valid
      ContainsValid : (0 loc : _) -> Command (Contains loc v :: conds)
                                             (Valid loc :: cons)
      -- load a constant into a valid location
      Const : (loc : _) -> (v : _) ->
              Command (Valid loc :: conds)
                      (Contains loc val :: invalidate loc conds)
      -- copy a value from one location to another
      Move : (src, dst : _) ->
             Command (Contains src v :: Valid dst :: conds)
                     (Contains dst v :: invalidate dst conds)
      -- load a pointer in one location
      Load : (src, dst : _) ->
             Command (Contains src (Pointer a) ::
                      Contains (Address a) v ::
                      Valid dst :: conds)
                     (Contains dst v :: invalidate dst conds)
      -- add the values at two locations
      Add : (a, b, dst : _) ->
            Command (Contains a (Scalar v1) ::
                     Contains b (Scalar v2) ::
                     Valid dst :: conds)

                    (Contains dst (Scalar $ i.scalar_add v1 v2) ::
                     invalidate dst conds)
      -- a sequence of two commands
      Seq : Command a b -> Command b c -> Command a c
      -- repeat a command until a location has a given value
      -- (this ought to have a more detailed type)
      LoopUntil : (loc : _) -> (v : Value) ->
             Command (notEqual loc v invariant) invariant ->
             Command (Valid loc :: invariant) (Contains loc v :: invariant)

namespace Example
  data Reg = RA | RB | RC

  reg_eq : DecEqFn Reg
  reg_eq RA RA = Yes Refl
  reg_eq RA RB = No $ \r => case r of {}
  reg_eq RA RC = No $ \r => case r of {}
  reg_eq RB RA = No $ \r => case r of {}
  reg_eq RB RB = Yes Refl
  reg_eq RB RC = No $ \r => case r of {}
  reg_eq RC RA = No $ \r => case r of {}
  reg_eq RC RB = No $ \r => case r of {}
  reg_eq RC RC = Yes Refl

  parameters (addr : Type, addr_eq : DecEqFn addr)

    inputs : Inputs
    inputs = MkInputs {
        addr = addr,
        reg = Reg,
        scalar = Int,
        addr_eq = addr_eq,
        reg_eq = reg_eq,
        scalar_eq = decEq,
        scalar_add = (+)
      }

    -- I wanted to write the following function:

    --    mem : (a : addr) -> Int -> Condition inputs
    --    mem a x = Contains _ (Address _ a) (Scalar _ x)

    --    reg : Reg -> Int -> Condition inputs
    --    reg r x = Contains _ (Register _ r) (Scalar _ x)

    --    -- repeatedly load from `addr` until it contains zero
    --    stupid_spinlock : (a : addr) ->
    --                      Command _ [mem a 10]
    --                                [reg RA 0, mem a 10]

    -- but I'm getting an error that inputs.addr does not unify with addr.
    -- Also, I think the way I'm going about this is entirely broken.
