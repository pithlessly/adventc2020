module type Ty = sig
  type t
end

module type ModuleTy = sig
  module type T
end

module type Bool =
  functor (T : ModuleTy)
          (_ : T.T)
          (_ : T.T) -> T.T

module True  (T : ModuleTy) (X : T.T) (_ : T.T) = X
module False (T : ModuleTy) (_ : T.T) (Y : T.T) = Y

module BoolInd
  (M : functor (_ : Bool) -> ModuleTy)
  (CaseT : M (True).T)
  (CaseF : M (False).T)
  (B : Bool)
  : functor () -> M (B).T
  = B (struct module type T = functor () -> M (B).T end)
      (functor () -> (val Obj.magic (module CaseT : M (True).T) : M (B).T))
      (functor () -> (val Obj.magic (module CaseF : M (False).T) : M (B).T))

module type Applicative = sig
  module F (_ : Ty) : Ty
  module Pure (A : Ty) : sig
    val pure : A.t -> F(A).t
  end
  module Ap (A : Ty) (B : Ty) (A_to_B : Ty with type t = A.t -> B.t) : sig
    val ap : F(A_to_B).t -> F(A).t -> F(B).t
  end
end

module LiftA2 (F : Applicative) (A : Ty) (B : Ty) (C : Ty) : sig
  val liftA2 : (A.t -> B.t -> C.t) ->
               F.F (A).t -> F.F (B).t -> F.F (C).t
end = struct
  module A_to_B_to_C = struct type t = A.t -> B.t -> C.t end
  module B_to_C = struct type t = B.t -> C.t end
  module Ap1 = F.Ap (B) (C) (B_to_C)
  module Ap2 = F.Ap (A) (B_to_C) (A_to_B_to_C)
  module Pure = F.Pure (A_to_B_to_C)
  let liftA2 f x y = Ap1.ap (Ap2.ap (Pure.pure f) x) y
end

module type Language = sig
  module type N
  module Root : N
  module MakeConstructs
    (Deps : functor (_ : N) -> Ty)
          : functor (_ : N) -> Ty

  module Traverse
    (F : Applicative)
    (A : functor (_ : N) -> Ty)
    (B : functor (_ : N) -> Ty)
    (Step : functor (I : N)    -> sig val step     :                  A (I).t -> F.F (                 B (I)).t end)
          : functor (I : N) () -> sig val traverse : MakeConstructs (A) (I).t -> F.F (MakeConstructs (B) (I)).t end
end

module X86 = struct
  module type N = Bool
  module Register : N = True
  module Instruction : N = False

  type register = [`Eax | `Ebx]
  type 'r instruction = [ `Add of 'r * 'r
                        | `Ret ]

  module RegisterT = struct type t = Register end

  module MakeConstructs (Deps : functor (_ : N) -> Ty) (I : N) : Ty =
    I (struct module type T = Ty end)
      (* register: *)
      (RegisterT)
      (* instruction: *)
      (struct type t = Deps (Register).t instruction end)

  (*
   * I hoped this would type check, but it doesn't!
  module Traverse
    (F : Applicative)
    (A : functor (_ : N) -> Ty)
    (B : functor (_ : N) -> Ty)
    (Step : functor (I : N) -> sig val step : A (I).t -> F.F (B (I)).t end)
    (I : N)
  =
    BoolInd
      (functor (I : Bool) ->
        struct module type T = sig
          val traverse : MakeConstructs (A) (I).t -> F.F (MakeConstructs (B) (I)).t end
        end)
      (
        struct
          module MyPure : sig val pure : RegisterT.t -> F.F (RegisterT).t end
                        = F.Pure (RegisterT)
          let traverse reg = MyPure.pure reg
        end
      )
      (
        struct
          module MyInstruction = struct type t = B (Register).t instruction end
          module MyPure : sig val pure : MyInstruction.t -> F.F (MyInstruction).t end
                        = F.Pure (MyInstruction)
          module MyLiftA2 = LiftA2 (F) (B (Register)) (B (Register)) (MyInstruction)
          let traverse = function
            | `Ret -> MyPure.pure `Ret
            | `Add (r1, r2) ->
                MyLiftA2.liftA2 (fun r1 r2 -> `Add (r1, r2)) r1 r2
        end
      )
      (I)
  *)
end
