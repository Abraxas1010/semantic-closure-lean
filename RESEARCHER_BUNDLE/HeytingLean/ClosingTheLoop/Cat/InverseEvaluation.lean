import HeytingLean.ClosingTheLoop.Cat.Selector

/-!
# Closing the Loop: categorical injectivity vs right-inverse (Tier 2)

Assumptions:
- `C` cartesian monoidal and cartesian closed.
- `B H : C` and a chosen point `b : 𝟙_ C ⟶ B`.

Agenda mapping:
- Uses `Mono` as the categorical analogue of “injective”.
- Uses split epi/mono data as the categorical analogue of “chosen right inverse”.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Cat

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {B H : C} [CategoryTheory.Exponentiable B] (b : 𝟙_ C ⟶ B)

/-- Categorical analogue of injective evaluation: `evalAt b` is a monomorphism. -/
structure InjectiveEvalAt : Prop where
  mono : Mono (evalAt (C := C) (B := B) (H := H) b)

/-- Categorical analogue of a chosen right inverse: a section `β` of `evalAt b`. -/
structure InverseEvaluationAt where
  β : H ⟶ SelectorObj (C := C) B H
  right_inv : β ≫ evalAt (C := C) (B := B) (H := H) b = 𝟙 H

abbrev RightInverseAt {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {B H : C} [CategoryTheory.Exponentiable B] (b : 𝟙_ C ⟶ B) : Type _ :=
  InverseEvaluationAt (C := C) (B := B) (H := H) b

namespace InverseEvaluationAt

variable {b}

/-- If `evalAt b` is an isomorphism, its inverse is a canonical inverse evaluation map. -/
noncomputable def of_isIso_evalAt [IsIso (evalAt (C := C) (B := B) (H := H) b)] :
    InverseEvaluationAt (C := C) (B := B) (H := H) b where
  β := inv (evalAt (C := C) (B := B) (H := H) b)
  right_inv := by
    simp

/-- A split epi structure on `evalAt b` is exactly the data needed to build `InverseEvaluationAt`. -/
def of_splitEpi_evalAt (s : SplitEpi (evalAt (C := C) (B := B) (H := H) b)) :
    InverseEvaluationAt (C := C) (B := B) (H := H) b where
  β := s.section_
  right_inv := s.id

/-- `evalAt b` is a split epimorphism under `RightInverseAt`. -/
def evalAt_splitEpi (ri : InverseEvaluationAt (C := C) (B := B) (H := H) b) :
    SplitEpi (evalAt (C := C) (B := B) (H := H) b) where
  section_ := ri.β
  id := ri.right_inv

/-- The section `β` is a split monomorphism. -/
def beta_splitMono (ri : InverseEvaluationAt (C := C) (B := B) (H := H) b) : SplitMono ri.β where
  retraction := evalAt (C := C) (B := B) (H := H) b
  id := ri.right_inv

/-- Every split epi is an epi. -/
theorem evalAt_epi (ri : InverseEvaluationAt (C := C) (B := B) (H := H) b) :
    Epi (evalAt (C := C) (B := B) (H := H) b) :=
  (evalAt_splitEpi (C := C) (B := B) (H := H) (b := b) ri).epi

/-- Every split mono is a mono. -/
theorem beta_mono (ri : InverseEvaluationAt (C := C) (B := B) (H := H) b) : Mono ri.β :=
  (beta_splitMono (C := C) (B := B) (H := H) (b := b) ri).mono

end InverseEvaluationAt

namespace RightInverseAt

variable {b}

def evalAt_splitEpi (ri : RightInverseAt (C := C) (B := B) (H := H) b) :
    SplitEpi (evalAt (C := C) (B := B) (H := H) b) :=
  InverseEvaluationAt.evalAt_splitEpi (C := C) (B := B) (H := H) (b := b) ri

def beta_splitMono (ri : RightInverseAt (C := C) (B := B) (H := H) b) : SplitMono ri.β :=
  InverseEvaluationAt.beta_splitMono (C := C) (B := B) (H := H) (b := b) ri

theorem evalAt_epi (ri : RightInverseAt (C := C) (B := B) (H := H) b) :
    Epi (evalAt (C := C) (B := B) (H := H) b) :=
  InverseEvaluationAt.evalAt_epi (C := C) (B := B) (H := H) (b := b) ri

theorem beta_mono (ri : RightInverseAt (C := C) (B := B) (H := H) b) : Mono ri.β :=
  InverseEvaluationAt.beta_mono (C := C) (B := B) (H := H) (b := b) ri

end RightInverseAt

end Cat
end ClosingTheLoop
end HeytingLean
