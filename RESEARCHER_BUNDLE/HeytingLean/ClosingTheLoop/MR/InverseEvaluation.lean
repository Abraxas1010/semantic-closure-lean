import HeytingLean.ClosingTheLoop.MR.Basic

/-!
# Closing the Loop: evaluation hypotheses at `b` (Tier 1)

This file separates two hypotheses about the evaluation map `evalAt S b : Selector S → H(A,B)`:

1. `InjectiveEvalAt S b` (paper-shaped): evaluation at `b` is injective, i.e. `Φ b = Ψ b → Φ = Ψ`.
2. `RightInverseAt S b` (section-shaped): there is a chosen `β` with `evalAt S b (β g) = g`.

Assumptions:
- Fixed `S : MRSystem` and `b : S.B`.
- The two conditions are logically independent in general (injective vs surjective/section).
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace MR

universe u v

variable {S : MRSystem.{u, v}} (b : S.B)

/-- Paper-shaped hypothesis: evaluation at `b` is injective on admissible selectors. -/
structure InjectiveEvalAt (S : MRSystem.{u, v}) (b : S.B) : Prop where
  inj : Function.Injective (evalAt S b)

namespace InjectiveEvalAt

variable {b}

/-- If two admissible selectors agree at `b`, then they are equal.

Agenda mapping:
- This is the exact Lean form of the paper’s “uniqueness at `b`” condition. -/
theorem eq_of_eval_eq (Hinj : InjectiveEvalAt S b) {Φ Ψ : Selector S} :
    Φ b = Ψ b → Φ = Ψ := by
  intro h
  rcases Hinj with ⟨hInj⟩
  apply hInj
  simpa using h

end InjectiveEvalAt

/-- Section-shaped hypothesis: evaluation at `b` has a chosen right inverse `β`. -/
structure InverseEvaluation (S : MRSystem.{u, v}) (b : S.B) where
  β : AdmissibleMap S → Selector S
  right_inv : Function.RightInverse β (evalAt S b)

abbrev RightInverseAt (S : MRSystem.{u, v}) (b : S.B) : Type (max u v) :=
  InverseEvaluation S b

namespace InverseEvaluation

variable {b}

@[simp] lemma evalAt_beta (RI : InverseEvaluation S b) (g : AdmissibleMap S) :
    evalAt S b (RI.β g) = g :=
  RI.right_inv g

/-- A chosen right inverse makes `β` injective.

Agenda mapping:
- Exposes the extra constructive content of choosing a section. -/
theorem beta_injective (RI : InverseEvaluation S b) : Function.Injective RI.β := by
  intro x y hxy
  have hEval : evalAt S b (RI.β x) = evalAt S b (RI.β y) :=
    congrArg (evalAt S b) hxy
  -- Rewrite both sides via the right-inverse law.
  calc
    x = evalAt S b (RI.β x) := (evalAt_beta (S := S) (b := b) RI x).symm
    _ = evalAt S b (RI.β y) := hEval
    _ = y := evalAt_beta (S := S) (b := b) RI y

/-- A chosen right inverse makes `evalAt` surjective. -/
theorem evalAt_surjective (RI : InverseEvaluation S b) : Function.Surjective (evalAt S b) := by
  intro g
  exact ⟨RI.β g, evalAt_beta (S := S) (b := b) RI g⟩

end InverseEvaluation

/-! ## Deriving inverse evaluation from principled hypotheses -/

namespace InverseEvaluation

variable {b}

/-- If evaluation at `b` is surjective, we can (noncomputably) pick an inverse evaluation map `β`
using choice. This upgrades the existence-only hypothesis `Surjective` into section data. -/
noncomputable def of_evalAt_surjective (hsurj : Function.Surjective (evalAt S b)) :
    InverseEvaluation S b := by
  classical
  refine ⟨fun g => Classical.choose (hsurj g), ?_⟩
  intro g
  exact (Classical.choose_spec (hsurj g))

/-- Under the paper’s injectivity hypothesis, any right inverse of `evalAt` is also a left inverse. -/
theorem beta_leftInverse_of_injective (Hinj : InjectiveEvalAt S b) (RI : InverseEvaluation S b) :
    Function.LeftInverse RI.β (evalAt S b) := by
  intro Φ
  apply Hinj.inj
  simpa using (RI.right_inv (evalAt S b Φ))

end InverseEvaluation

namespace RightInverseAt

variable {b}

@[simp] lemma evalAt_beta (RI : RightInverseAt S b) (g : AdmissibleMap S) :
    evalAt S b (RI.β g) = g :=
  InverseEvaluation.evalAt_beta (S := S) (b := b) RI g

theorem beta_injective (RI : RightInverseAt S b) : Function.Injective RI.β :=
  InverseEvaluation.beta_injective (S := S) (b := b) RI

theorem evalAt_surjective (RI : RightInverseAt S b) : Function.Surjective (evalAt S b) :=
  InverseEvaluation.evalAt_surjective (S := S) (b := b) RI

end RightInverseAt

/-- A witness-carrying version of the image of `evalAt S b` (choice-free). -/
structure EvalImage (S : MRSystem.{u, v}) (b : S.B) : Type (max u v) where
  g : AdmissibleMap S
  Φ : Selector S
  eval_eq : evalAt S b Φ = g

namespace EvalImage

variable {b}

/-- Project the witness selector.

Agenda mapping:
- This packages “inverse evaluation on the image” without any choice principle:
  the witness `Φ` is carried as data. -/
def betaOnImage (x : EvalImage S b) : Selector S :=
  x.Φ

@[simp] lemma evalAt_betaOnImage (x : EvalImage S b) :
    evalAt S b (betaOnImage (S := S) (b := b) x) = x.g :=
  x.eval_eq

/-- The canonical map from selectors into their evaluation image. -/
def ofSelector (Φ : Selector S) : EvalImage S b :=
  ⟨Φ b, Φ, rfl⟩

@[simp] lemma betaOnImage_ofSelector (Φ : Selector S) :
    betaOnImage (S := S) (b := b) (ofSelector (S := S) (b := b) Φ) = Φ :=
  rfl

/-- Forget the witness, landing in the set-theoretic range of `evalAt`. -/
def toRange (x : EvalImage S b) : Set.range (evalAt S b) :=
  ⟨x.g, ⟨x.Φ, x.eval_eq⟩⟩

end EvalImage

end MR
end ClosingTheLoop
end HeytingLean
