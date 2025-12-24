import HeytingLean.ClosingTheLoop.MR.InverseEvaluation

/-!
# Closing the Loop: selector closure operator (Tier 1)

Given a chosen right inverse `β` for evaluation at a configuration `b : B`,
define the loop-closing operator on admissible selectors:

`closeSelector Φ := β (Φ b)`.

This operator is idempotent and its fixed points are the “closed” selectors at `b`.

Assumptions:
- Idempotence uses `RightInverseAt S b` (a chosen section for evaluation).
- The paper-shaped uniqueness hypothesis `InjectiveEvalAt S b` does *not* imply this closure
  construction by itself.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace MR

universe u v

variable {S : MRSystem.{u, v}} {b : S.B}

/-- The loop-closing operator on selectors induced by a chosen section at `b`. -/
def closeSelector (S : MRSystem.{u, v}) (b : S.B) (RI : RightInverseAt S b) :
    Selector S → Selector S :=
  fun Φ => RI.β (Φ b)

namespace closeSelector

variable (RI : RightInverseAt S b)

@[simp] lemma evalAt_close (Φ : Selector S) :
    evalAt S b (closeSelector S b RI Φ) = Φ b := by
  simpa [closeSelector] using RI.right_inv (Φ b)

@[simp] lemma close_apply_at (Φ : Selector S) :
    closeSelector S b RI Φ b = Φ b := by
  simpa [evalAt] using (evalAt_close (S := S) (b := b) (RI := RI) Φ)

/-- Closing twice does nothing (idempotence). -/
theorem idem (Φ : Selector S) :
    closeSelector S b RI (closeSelector S b RI Φ) = closeSelector S b RI Φ := by
  -- The operator depends only on the `b`-value, which is fixed by `closeSelector`.
  dsimp [closeSelector]
  congr
  simpa [evalAt] using (RI.right_inv (Φ b))

end closeSelector

/-! ## Noncomputable derivation: closure from surjectivity at `b` -/

namespace closeSelector

open Classical

variable {S : MRSystem.{u, v}} {b : S.B}

/-- If `evalAt S b` is surjective, we can (noncomputably) build an inverse evaluation map and
thus a loop-closing operator, without assuming `RightInverseAt` as data. -/
noncomputable def of_evalAt_surjective (S : MRSystem.{u, v}) (b : S.B)
    (hsurj : Function.Surjective (evalAt S b)) : Selector S → Selector S :=
  closeSelector S b (InverseEvaluation.of_evalAt_surjective (S := S) (b := b) hsurj)

theorem of_evalAt_surjective_idem (hsurj : Function.Surjective (evalAt S b)) (Φ : Selector S) :
    of_evalAt_surjective S b hsurj (of_evalAt_surjective S b hsurj Φ) =
      of_evalAt_surjective S b hsurj Φ := by
  -- Reduce to idempotence of `closeSelector` under the derived section.
  let RI : RightInverseAt S b :=
    InverseEvaluation.of_evalAt_surjective (S := S) (b := b) hsurj
  simpa [of_evalAt_surjective, RI] using (closeSelector.idem (S := S) (b := b) (RI := RI) Φ)

/-- If evaluation is injective at `b`, then any right inverse (in particular, one derived from
surjectivity) is a left inverse, so closing is the identity. -/
theorem of_evalAt_surjective_eq_id (Hinj : InjectiveEvalAt S b)
    (hsurj : Function.Surjective (evalAt S b)) (Φ : Selector S) :
    of_evalAt_surjective S b hsurj Φ = Φ := by
  let RI : RightInverseAt S b :=
    InverseEvaluation.of_evalAt_surjective (S := S) (b := b) hsurj
  have hLeft : Function.LeftInverse RI.β (evalAt S b) :=
    InverseEvaluation.beta_leftInverse_of_injective (S := S) (b := b) Hinj RI
  -- `closeSelector` uses only the evaluation at `b`.
  simpa [of_evalAt_surjective, closeSelector, evalAt] using (hLeft Φ)

end closeSelector

/-- A selector is closed (at `b`) if applying `closeSelector` leaves it unchanged. -/
def IsClosed (S : MRSystem.{u, v}) (b : S.B) (RI : RightInverseAt S b) (Φ : Selector S) : Prop :=
  closeSelector S b RI Φ = Φ

namespace IsClosed

variable (RI : RightInverseAt S b)

lemma iff_eq (Φ : Selector S) :
    IsClosed S b RI Φ ↔ Φ = RI.β (Φ b) := by
  -- `IsClosed` unfolds to `RI.β (Φ b) = Φ`.
  simp [IsClosed, closeSelector, eq_comm]

lemma exists_eq_beta_iff (Φ : Selector S) :
    IsClosed S b RI Φ ↔ ∃ g : AdmissibleMap S, RI.β g = Φ := by
  constructor
  · intro h
    refine ⟨Φ b, ?_⟩
    -- Closed means `β (Φ b) = Φ`.
    simpa [IsClosed, closeSelector] using h
  · rintro ⟨g, rfl⟩
    -- Elements in the image of `β` are fixed points.
    -- `closeSelector (β g) = β ((β g) b) = β g`.
    have hb : RI.β g b = g := by
      simpa [evalAt] using (RightInverseAt.evalAt_beta (S := S) (b := b) RI g)
    -- rewrite the defining equation using `hb`
    simp [IsClosed, closeSelector, hb]

lemma close_isClosed (Φ : Selector S) :
    IsClosed S b RI (closeSelector S b RI Φ) := by
  -- `IsClosed` is exactly idempotence.
  simpa [IsClosed] using (closeSelector.idem (S := S) (b := b) (RI := RI) Φ)

end IsClosed

end MR
end ClosingTheLoop
end HeytingLean
