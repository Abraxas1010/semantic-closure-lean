import HeytingLean.Core.Types
import HeytingLean.LambdaIR.Syntax

namespace HeytingLean
namespace LambdaIR
namespace NatFunFragment

open HeytingLean.Core

/-- Primitive nat expressions supported by the LambdaIR → MiniC compiler. -/
inductive IsNatExpr : Term [Ty.nat] Ty.nat → Prop
  | constNat (n : Nat) : IsNatExpr (Term.constNat n)
  | var : IsNatExpr (Term.var Var.vz)
  | add {f t : Term [Ty.nat] Ty.nat}
      (hf : IsNatExpr f) (ht : IsNatExpr t) :
      IsNatExpr (Term.app (Term.app Term.primAddNat f) t)

/-- Primitive boolean expressions supported by the compiler. -/
inductive IsBoolExpr : Term [Ty.nat] Ty.bool → Prop
  | constBool (b : Bool) : IsBoolExpr (Term.constBool b)
  | eqNat {t₁ t₂ : Term [Ty.nat] Ty.nat}
      (h₁ : IsNatExpr t₁) (h₂ : IsNatExpr t₂) :
      IsBoolExpr (Term.app (Term.app Term.primEqNat t₁) t₂)

/-- Nat bodies allow primitive expressions and conditionals. -/
inductive IsNatBody : Term [Ty.nat] Ty.nat → Prop
  | expr {t : Term [Ty.nat] Ty.nat}
      (ht : IsNatExpr t) : IsNatBody t
  | if_ {c : Term [Ty.nat] Ty.bool} {t e : Term [Ty.nat] Ty.nat}
      (hc : IsBoolExpr c) (ht : IsNatBody t) (he : IsNatBody e) :
      IsNatBody (Term.if_ c t e)

/-- Fragment predicate used by the compiler correctness proof. -/
def IsNatFun (t : Term [] (Ty.arrow Ty.nat Ty.nat)) : Prop :=
  ∃ body, t = Term.lam body ∧ IsNatBody body

end NatFunFragment

open NatFunFragment
export NatFunFragment (IsNatExpr IsBoolExpr IsNatBody IsNatFun)

end LambdaIR
end HeytingLean
