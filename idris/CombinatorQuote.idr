%default total

-- Represents a term in untyped combinatory logic with S and K.
data Term = TS | TK | TApp Term Term

{- Given such term t, consider the encoding [t] of this term
   in the untyped lambda calculus:

     [TS]       = λf → S
     [TK]       = λf → K
     [TApp a b] = λf → f ([a] f) ([b] f)

     (where S and K are the literal S and K combinators.)

   Given a proper choice of f, it is possible to perform
   arbitrary manipulations in this encoding. But doing this
   is tricky, because you need to make sure f knows how to
   accept and distinguish different kinds of inputs:

   - An input of the S combinator;
   - An input of the K combinator;
   - An input which was the result of another call to f.

   The question is whether it's possible to come up with a
   static type for this encoding function. Perhaps it can
   be encoded with the help of dependent types, and then
   we can use QTT to ensure that this plumbing is erased?
 -}

-- 'Pi0 a b' is just (0 x : a) -> b x, which Idris seems to
-- have problems with manipulating directly
data Pi0 : (a : Type) -> (b : a -> Type) -> Type where
  MkPi0 : ((0 x : a) -> b x) -> Pi0 a b

runPi0 : Pi0 _ b -> b x
runPi0 (MkPi0 f) = f x

{- For our first attempt at implementing this, we have the user supply
   a family 'p a b', which describes the return type of f when called
   to encode 'TApp a b'. The key here is that p has the potential to
   inspect the terms syntactically to determine what type f should
   return, but f does not itself have access to this.
  
   This attempt gives a definition of 'encode' that looks correct,
   but it actually doesn't work:
  
   * The return type is dependent on the term, which might be OK.

   * It is actually impossible to supply a valid f (I think), because
     the function is not given any way to know what the type of its
     argument is, and so it can't do anything to inspect it.
     What it seems like we would need is some way to do an 'erased
     pattern match': we would write an expression which appears to
     match on an erased argument, but upon closer inspection every
     case is revealed to be identical (upon erasing types). So
     the pattern match only exists to verify that each branch
     type checks, and the function can be compiled to a uniform
     body that doesn't match on the erased argument.

     This is also similar to how you might type-check an elimination
     of an untagged union type (a ∨ b): check that the continuation
     has type ((a -> c) ∧ (b -> c)), i.e. it is valid as an element
     both of (a -> c) and of (b -> c) without any semantic change.
 -}

namespace V1

  TypeOfS, TypeOfK : Type
  TypeOfS = Pi0 Type $ \a => Pi0 Type $ \b => Pi0 Type $ \c =>
              (a -> b -> c) -> (a -> b) -> (a -> c)
  TypeOfK = Pi0 Type $ \a => Pi0 Type $ \b => a -> b -> a

  K : TypeOfK
  K = MkPi0 $ \_ => MkPi0 $ \_ => \x, y => x

  S : TypeOfS
  S = MkPi0 $ \_ => MkPi0 $ \_ => MkPi0 $ \_ => \x, y, z => x z (y z)

  Encoded : (Term -> Term -> Type) -> Term -> Type
  Encoded p TS = TypeOfS
  Encoded p TK = TypeOfK
  Encoded p (TApp a b) = p a b

  encode : (1 t : Term) -> ({0 a, b : _} -> Encoded p a -> Encoded p b -> p a b) -> Encoded p t
  encode TS f = S
  encode TK f = K
  encode (TApp x y) f = f (encode x f) (encode y f)

{- Let's simplify the problem to focus on the issue of "uniform
   pattern matching" in more detail. Suppose we have some other pair
   of combinators:
 -}

namespace V2

  Erase : Bool -> Type
  Erase True = (a, b : Type) -> a -> b -> a
  Erase False = (a, b : Type) -> a -> b -> b

  P1 : Erase True
  P1 _ _ x _ = x

  P2 : Erase False
  P2 _ _ _ y = y

  erase : (b : Bool) -> Erase b
  erase True = P1
  erase False = P2

  -- Now, is it possible to write a function
  recover : {0 b : _} -> Erase b -> Bool
  -- such that recover (erase b) = b? I'm not sure. But let's try it.

  -- The crucial thing we will use is this helper,
  -- which recovers an erased equation:
  equation : (0 _ : x = y) -> x = y
  equation Refl = Refl

  recover erased =
    let
      -- We start out knowing nothing about the 'Erased b' value. But we will
      -- prove that it's actually a function, and that it takes two polymorphic
      -- arguments and returns some type 'F' depending on the argument types.
      0 F : Type -> Type -> Type
      F t u = (case b of { True => t; False => u })

      -- We can do this by case analysis on 'b', because we're returning an
      -- identity type and so we know we will get Refl either way.
      erased_is_function : (Erase b = ((t, u : Type) -> t -> u -> F t u))
      erased_is_function = equation (case b of { True => Refl; False => Refl })

      -- We can now cast 'erased' to a function and specialize it to Bool.
      erased_as_function : Bool -> Bool -> F Bool Bool
      erased_as_function = (replace {p=id} erased_is_function erased) Bool Bool

      -- We can prove that the result must be a boolean, again by case analysis.
      f_bool_bool_is_bool : F Bool Bool = Bool
      f_bool_bool_is_bool = equation (case b of { True => Refl; False => Refl })

      -- We have our result!
      result : Bool
      result = replace {p=id} f_bool_bool_is_bool (erased_as_function True False)
    in
      result

  -- Proving that it round-trips is simple:
  recovers : (b : Bool) -> recover {b} (erase b) = b
  recovers False = Refl
  recovers True = Refl

{- In light of this, it seems pretty likely that it will
   actually be possible to write a usable 'encode' function.
   However, we need to be a little careful about what types
   we are using here. For example, the implementation of
   'recover' only worked because we were able to pass two
   arguments. This means that every type we might want to
   distinguish needs to have the same calling convention.
   Technically, V1's definitions of S and K don't fit this,
   because they take different numbers of erased arguments.
   In fact, after inspecting the Scheme backend, it looks
   like these erased arguments aren't even fully erased
   after all, in the sense that a function
     (\0 x => ...)
   is still represented as a function
     (lambda (p) ...)
   where p is never used. So, type theory aside, we can be
   confident that this will never work unless we make sure
   the calling convention is consistent between cases.
 -}

namespace V3

  -- This is all the same as in V1, except that K takes three
  -- erased type arguments, ignoring the last one.

  TypeOfS, TypeOfK : Type
  TypeOfS = Pi0 Type $ \a => Pi0 Type $ \b => Pi0 Type $ \c =>
              (a -> b -> c) -> (a -> b) -> (a -> c)
  TypeOfK = Pi0 Type $ \a => Pi0 Type $ \b => Pi0 Type $ \c =>
              a -> b -> a

  K : TypeOfK
  K = MkPi0 $ \_ => MkPi0 $ \_ => MkPi0 $ \_ => \x, y => x

  S : TypeOfS
  S = MkPi0 $ \_ => MkPi0 $ \_ => MkPi0 $ \_ => \x, y, z => x z (y z)

  Encoded : (Term -> Term -> Type) -> Term -> Type
  Encoded p TS = TypeOfS
  Encoded p TK = TypeOfK
  Encoded p (TApp a b) = p a b

  encode' : (1 t : Term) -> ({0 a, b : _} -> Encoded p a -> Encoded p b -> p a b) -> Encoded p t
  encode' TS f = S
  encode' TK f = K
  encode' (TApp x y) f = f (encode' x f) (encode' y f)

  record Encoding where
    constructor MkEncoding
    0 t : Term
    elim : {0 p : Term -> Term -> Type} ->
           ({0 a, b : _} -> Encoded p a -> Encoded p b -> p a b) ->
           Encoded p t

  encode : Term -> Encoding
  encode t = MkEncoding t (encode' t)

  {- Now we can implement a suitable 'f'. Type-erased, its implementation is:
       read  =  λ term → term (λ () x → x) (λ () _ → TS) () TK
       f     =  λ x y  → λ _ _ _ _ → TApp (read x) (read y)
    
     We can check the following:
       read ([TS] f)       = TS
       read ([TK] f)       = TK
       read ([TApp a b] f) = TApp (read ([a] f)) (read ([b] f))

     First, we define a suitable type for the return value of f. As it turns
     out, it doesn't even need to vary based on the argument terms.
   -}

  P : Term -> Term -> Type
  P _ _ = Pi0 Type $ \a => Pi0 Type $ \b => Pi0 Type $ \c =>
            a -> (Unit -> Term -> Term) -> Unit -> Term -> Term

  -- Now for read, where we do the bulk of the work. Everything but the
  -- last line is for type coercion, and should ideally be completely erased.

  read : Encoded P t -> Term
  read encoded =
    let
      0 F : Type -> Type -> Type -> Type
      F a b c = case t of TS => (a -> b -> c) -> (a -> b) -> (a -> c)
                          TK => a -> b -> a
                          TApp t u => a -> (Unit -> Term -> Term) -> Unit -> Term -> Term

      0 A, B, C : Type
      C = case t of TS => Term -> Term
                    TK => Term -- ignored by K, but we reuse it
                    TApp _ _ => Void -- ignored
      B = case t of TS => Term -> Term
                    TK => Unit -> Term -> Term
                    TApp _ _ => Void -- ignored
      A = case t of TS => Unit
                    TK => Unit -> Term -> Term
                    TApp _ _ => Unit -> Void -> Void

      0 encoded_is_pi0 : (Encoded P t =
                           (Pi0 Type $ \a => Pi0 Type $ \b => Pi0 Type $ \c => F a b c))
      encoded_is_pi0 = case t of TS => Refl; TK => Refl; TApp _ _ => Refl

      encoded' : F A B C
      encoded' = runPi0 $ runPi0 $ runPi0 $
                 replace {p=id} encoded_is_pi0 $
                 the (Encoded P t) encoded

      0 Encoded'' : Type
      Encoded'' = (Unit -> C -> C) -> (Unit -> Term -> Term) -> Unit -> Term -> Term

      0 encoded'_is_function : (F A B C = Encoded'')
      encoded'_is_function = case t of TS => Refl; TK => Refl; TApp _ _ => Refl

      encoded'' : Encoded''
      encoded'' = replace {p=id} encoded'_is_function encoded'
    in
      encoded'' (\(), c => c) (\(), _ => TS) () TK

  f' : (a, b : Term) -> P a b
  f' a b = MkPi0 $ \_ => MkPi0 $ \_ => MkPi0 $ \_ =>
             \_, _, _, _ => TApp a b

  f : Encoded P a -> Encoded P b -> P a b
  f x y = f' (read x) (read y)

  decode : Encoding -> Term
  decode (MkEncoding t elim) = read (elim f)

  -- Proving that the encoding is reversable is more complicated
  -- than it should be, but it's just a matter of substitution:

  roundTrip : Term -> Term
  roundTrip t = read (encode' t f)

  recovers' : (t : Term) -> t = roundTrip t
  recovers' TS = Refl
  recovers' TK = Refl
  recovers' (t @ (TApp a b)) =
    replace {p = \x => t = read {t} (f' x (roundTrip b))} (recovers' a) $
    replace {p = \x => t = read {t} (f' a x            )} (recovers' b) $
      Refl

  recovers : (t : Term) -> decode (encode t) = t
  recovers t = sym $ recovers' t
