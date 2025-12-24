import HeytingLean.Core.Types
import HeytingLean.LambdaIR.Syntax

namespace HeytingLean
namespace LambdaIR
namespace Nat2FunFragment

open HeytingLean.Core

/-- Primitive nat expressions over two parameters supported by the LambdaIR → MiniC 2-arg compiler. -/
inductive IsNatExpr₂ : Term [Ty.nat, Ty.nat] Ty.nat → Prop
  | constNat (n : Nat) :
      IsNatExpr₂ (Term.constNat n)
  | varFirst :
      -- Older parameter (outer lambda, index succ vz)
      IsNatExpr₂ (Term.var (Var.vs Var.vz))
  | varSecond :
      -- Newest parameter (inner lambda, index vz)
      IsNatExpr₂ (Term.var Var.vz)
  | add {f t : Term [Ty.nat, Ty.nat] Ty.nat}
      (hf : IsNatExpr₂ f) (ht : IsNatExpr₂ t) :
      IsNatExpr₂ (Term.app (Term.app Term.primAddNat f) t)

/-- Primitive boolean expressions over two nat parameters. -/
inductive IsBoolExpr₂ : Term [Ty.nat, Ty.nat] Ty.bool → Prop
  | constBool (b : Bool) :
      IsBoolExpr₂ (Term.constBool b)
  | eqNat {t₁ t₂ : Term [Ty.nat, Ty.nat] Ty.nat}
      (h₁ : IsNatExpr₂ t₁) (h₂ : IsNatExpr₂ t₂) :
      IsBoolExpr₂ (Term.app (Term.app Term.primEqNat t₁) t₂)

/-- Bodies for two-argument nat functions (allowing expressions and conditionals). -/
inductive IsNatBody₂ : Term [Ty.nat, Ty.nat] Ty.nat → Prop
  | expr {t : Term [Ty.nat, Ty.nat] Ty.nat}
      (ht : IsNatExpr₂ t) : IsNatBody₂ t
  | if_ {c : Term [Ty.nat, Ty.nat] Ty.bool}
        {t e : Term [Ty.nat, Ty.nat] Ty.nat}
        (hc : IsBoolExpr₂ c)
        (ht : IsNatBody₂ t)
        (he : IsNatBody₂ e) :
      IsNatBody₂ (Term.if_ c t e)

/-- Fragment predicate for curried `Nat → Nat → Nat` LambdaIR terms. -/
def IsNat2Fun
    (t : Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))) : Prop :=
  ∃ body, t = Term.lam (Term.lam body) ∧ IsNatBody₂ body

end Nat2FunFragment

open Nat2FunFragment
export Nat2FunFragment (IsNatExpr₂ IsBoolExpr₂ IsNatBody₂ IsNat2Fun)

end LambdaIR
end HeytingLean
