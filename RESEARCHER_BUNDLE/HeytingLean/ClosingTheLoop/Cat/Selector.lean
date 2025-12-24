import Mathlib.CategoryTheory.Closed.Cartesian

/-!
# Closing the Loop: categorical selector object and evaluation-at-a-point (Tier 2)

This file starts the “structure ladder” requested by the research agenda.

Assumptions:
- A category `C` with a cartesian monoidal structure and cartesian-closed structure.
- Objects `B H : C`.
- A chosen global element `b : 𝟙_ C ⟶ B` (a point of `B`).

Agenda mapping:
- Makes explicit the minimum categorical structure needed to *state* “selectors” as an
  exponential object and “evaluation at `b`” as a morphism.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Cat

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable (B H : C) [CategoryTheory.Exponentiable B]

/-- The selector object `H^B` (internal hom / exponential). -/
abbrev SelectorObj : C :=
  B ⟹ H

/-- Evaluation at a chosen global element `b : 𝟙 ⟶ B`. -/
def evalAt (b : 𝟙_ C ⟶ B) : SelectorObj (C := C) B H ⟶ H :=
  (λ_ (B ⟹ H)).inv ≫ (b ⊗ₘ 𝟙 (B ⟹ H)) ≫ (CategoryTheory.exp.ev B).app H

lemma evalAt_def (b : 𝟙_ C ⟶ B) :
    evalAt (C := C) (B := B) (H := H) b =
      (λ_ (B ⟹ H)).inv ≫ (b ⊗ₘ 𝟙 (B ⟹ H)) ≫ (CategoryTheory.exp.ev B).app H :=
  rfl

end Cat
end ClosingTheLoop
end HeytingLean
