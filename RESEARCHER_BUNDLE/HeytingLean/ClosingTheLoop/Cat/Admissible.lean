import Mathlib.CategoryTheory.Subobject.Basic
import HeytingLean.ClosingTheLoop.Cat.Selector

/-!
# Closing the Loop: admissible morphisms as a subobject of an exponential (Tier 2)

This file implements the paper’s idea that the admissible maps form a *proper subset*

`H(A,B) ⊊ Hom(A,B)`

in a categorical way: as a subobject of the full exponential `A ⟹ B`.

Design choice (objective):
- We model admissibility as an **internal object** `Hsub ↪ (A ⟹ B)` rather than as a mere predicate on arrows.
  This matches the paper’s notation `H(A,B)` as an object and keeps the selector construction literally
  `B ⟹ H(A,B)`.

What this gives (without extra assumptions):
- An inclusion morphism `ι : (Hsub : C) ⟶ (A ⟹ B)` which is mono.
- A selector object `B ⟹ (Hsub : C)` and evaluation-at-a-point `evalAt b : (B ⟹ Hsub) ⟶ Hsub`.

What it does *not* give automatically:
- A general way to decide if an arbitrary morphism `A ⟶ B` is admissible (that would amount to extra structure,
  e.g. a classifier, a reflection, or a realizability predicate).
- A full (M,R) system: metabolims/repair/replication require additional data layered on top of this subobject.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Cat

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

namespace Admissible

variable {A B : C} [CategoryTheory.Exponentiable A]

/-- The admissible hom-object `H(A,B)` presented as a subobject of the full exponential `A ⟹ B`. -/
abbrev Hom : Type _ :=
  Subobject (A ⟹ B)

namespace Hom

variable (Hsub : Hom (C := C) (A := A) (B := B))

/-- The underlying object of admissible maps. -/
abbrev Obj : C :=
  (Hsub : C)

/-- The inclusion `ι : H(A,B) ↪ (A ⟹ B)`. -/
abbrev ι : Obj (C := C) (A := A) (B := B) Hsub ⟶ (A ⟹ B) :=
  Hsub.arrow

instance : Mono (ι (C := C) (A := A) (B := B) Hsub) := by
  dsimp [ι]
  infer_instance

end Hom

section Selectors

variable {A B : C} [CategoryTheory.Exponentiable A] [CategoryTheory.Exponentiable B]
variable (Hsub : Hom (C := C) (A := A) (B := B))

/-- Selector object for admissible maps: `B ⟹ H(A,B)`. -/
abbrev SelectorObj : C :=
  Cat.SelectorObj (C := C) (B := B) (H := (Hsub : C))

/-- Admissible selectors as a subobject `H(B, H(A,B)) ↪ (B ⟹ H(A,B))`. -/
abbrev SelectorSub : Type _ :=
  Subobject (SelectorObj (C := C) (A := A) (B := B) Hsub)

/-- Evaluation at a point `b : 𝟙 ⟶ B` for selectors into the admissible hom-object. -/
def evalAt (b : 𝟙_ C ⟶ B) : SelectorObj (C := C) (A := A) (B := B) Hsub ⟶ (Hsub : C) :=
  Cat.evalAt (C := C) (B := B) (H := (Hsub : C)) b

/-- Evaluation at `b` restricted to admissible selectors (via the inclusion of the subobject). -/
def evalAtSub (b : 𝟙_ C ⟶ B) (SelSub : SelectorSub (C := C) (A := A) (B := B) Hsub) :
    (SelSub : C) ⟶ (Hsub : C) :=
  SelSub.arrow ≫ evalAt (C := C) (A := A) (B := B) Hsub b

end Selectors

end Admissible

end

end Cat
end ClosingTheLoop
end HeytingLean
