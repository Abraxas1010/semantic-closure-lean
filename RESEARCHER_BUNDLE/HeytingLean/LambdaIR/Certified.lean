/-
  Certified wrappers for LambdaIR terms.

  Note: HeytingLean's LambdaIR is already intrinsically typed:
  `Term : Ctx → Ty → Type`. This module adds MLTT-style packaging
  that pairs runtime syntax with erased proof obligations.
-/

import HeytingLean.Certified.Basic
import HeytingLean.LambdaIR.Syntax

namespace HeytingLean
namespace LambdaIR

universe u

/-- Pack the indices of an intrinsically-typed term for storage/transport. -/
structure TypedTerm where
  Γ : Ctx
  τ : Ty
  term : Term Γ τ

namespace TypedTerm

/-- Extract the underlying term (indices retained by the structure fields). -/
@[inline] def extract (t : TypedTerm) : Term t.Γ t.τ := t.term

end TypedTerm

/-- A certified LambdaIR term: a term with an erased `Prop`-valued spec. -/
abbrev CertifiedTerm {Γ : Ctx} {τ : Ty} (Spec : Term Γ τ → Prop) : Type :=
  HeytingLean.Certified.Certified (Term Γ τ) Spec

/-- A certified packaged term. -/
abbrev CertifiedTypedTerm (Spec : TypedTerm → Prop) : Type :=
  HeytingLean.Certified.Certified TypedTerm Spec

@[simp] theorem CertifiedTerm.extract_eq {Γ : Ctx} {τ : Ty} {Spec : Term Γ τ → Prop}
    (ct : CertifiedTerm (Γ := Γ) (τ := τ) Spec) :
    ct.extract = ct.val := rfl

end LambdaIR
end HeytingLean

