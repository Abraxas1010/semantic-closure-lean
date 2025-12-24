import HeytingLean.ClosingTheLoop.MR.PaperMapping
import HeytingLean.ClosingTheLoop.Cat.ClosureOperator
import HeytingLean.ClosingTheLoop.Semantics.NucleusFixedPoints

/-!
# Closing the Loop: main theorems (paper-facing + category-facing)

This module collects the central, explicitly-scoped theorems used by the “Closing the Loop”
formalization.

Assumptions:
- Set-level uniqueness is stated under `MR.InjectiveEvalAt S b`.
- Set-level idempotent loop-closing uses `MR.RightInverseAt S b`.
- Category-level idempotent loop-closing uses exponentials (cartesian-closed), a point
  `b : 𝟙 ⟶ B`, and `Cat.RightInverseAt b`.
-/

namespace HeytingLean
namespace ClosingTheLoop

namespace SetLevel

open MR

universe u v

variable {S : MRSystem.{u, v}} {b : S.B}

/-- Paper-facing uniqueness: agreeing at `b` forces equality of admissible selectors.

Agenda mapping:
- This is the exact Lean statement of the paper’s “evaluation is injective at `b`” condition. -/
theorem selector_eq_of_eval_eq (Hinj : InjectiveEvalAt S b) {Φ Ψ : Selector S} :
    Φ b = Ψ b → Φ = Ψ :=
  InjectiveEvalAt.eq_of_eval_eq (S := S) (b := b) Hinj

/-- Constructive closure: a chosen section `β` induces an idempotent loop-closing operator.

Agenda mapping:
- Makes the stronger/extra assumption explicit: we require `RightInverseAt`, not just uniqueness. -/
theorem closeSelector_idem (RI : RightInverseAt S b) (Φ : Selector S) :
    closeSelector S b RI (closeSelector S b RI Φ) = closeSelector S b RI Φ :=
  closeSelector.idem (S := S) (b := b) (RI := RI) Φ

end SetLevel

namespace CatLevel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Cat

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {B H : C} [CategoryTheory.Exponentiable B] {b : 𝟙_ C ⟶ B}

/-- Category-facing closure: under exponentials + a point + a section, the closure endomorphism is idempotent.

Agenda mapping:
- Exhibits the minimum categorical prerequisites to state and prove idempotence of “closing the loop”. -/
theorem close_idem (ri : Cat.RightInverseAt (C := C) (B := B) (H := H) b) :
    Cat.close (C := C) (B := B) (H := H) b ri ≫ Cat.close (C := C) (B := B) (H := H) b ri =
      Cat.close (C := C) (B := B) (H := H) b ri :=
  Cat.close.idem (C := C) (B := B) (H := H) (b := b) ri

end CatLevel

end ClosingTheLoop
end HeytingLean
