import HeytingLean.ClosingTheLoop.MR.ClosureOperator

/-!
# Closing the Loop: mapping hypotheses to the paper (Tier 1)

This file records, in one place, the exact logical relationship between the two
evaluation hypotheses used in the development:

- `InjectiveEvalAt`: the paper-shaped uniqueness hypothesis (injective evaluation at `b`);
- `RightInverseAt`: the existence of a chosen section `β` (a right inverse of evaluation).

Assumptions:
- Fixed `S : MRSystem` and `b : S.B`.
- No additional assumptions or choice principles are introduced here.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace MR

universe u v

variable {S : MRSystem.{u, v}} {b : S.B}

/-- Paper condition: agreement at `b` forces selector equality. -/
theorem paper_uniqueness (Hinj : InjectiveEvalAt S b) {Φ Ψ : Selector S} :
    Φ b = Ψ b → Φ = Ψ :=
  Hinj.eq_of_eval_eq (S := S) (b := b)

/-- A chosen right inverse of evaluation makes `evalAt` surjective, hence provides
existence of selectors realizing any admissible map at `b`.

This is different from (and does not imply) the paper uniqueness hypothesis. -/
theorem rightInverse_implies_surjective (RI : RightInverseAt S b) :
    Function.Surjective (evalAt S b) :=
  RI.evalAt_surjective (S := S) (b := b)

end MR
end ClosingTheLoop
end HeytingLean
