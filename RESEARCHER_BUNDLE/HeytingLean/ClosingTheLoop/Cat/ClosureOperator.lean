import HeytingLean.ClosingTheLoop.Cat.InverseEvaluation

/-!
# Closing the Loop: categorical closure endomorphism (Tier 2)

Assumptions:
- `C` cartesian monoidal and cartesian closed.
- `B H : C`, point `b : 𝟙 ⟶ B`, and `RightInverseAt b` supplying a section `β`.

Agenda mapping:
- Mirrors the Set-level closure operator proof, but makes explicit the categorical prerequisites:
  exponentials (selectors), a global element (evaluation at a point), and a section `β`.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Cat

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {B H : C} [CategoryTheory.Exponentiable B] (b : 𝟙_ C ⟶ B)

/-- The categorical loop-closing endomorphism on the selector object `H^B`. -/
def close (ri : RightInverseAt (C := C) (B := B) (H := H) b) :
    SelectorObj (C := C) B H ⟶ SelectorObj (C := C) B H :=
  evalAt (C := C) (B := B) (H := H) b ≫ ri.β

namespace close

variable {b} (ri : RightInverseAt (C := C) (B := B) (H := H) b)

/-- Closing twice does nothing: the categorical closure endomorphism is idempotent. -/
theorem idem :
    close (C := C) (B := B) (H := H) b ri ≫ close (C := C) (B := B) (H := H) b ri =
      close (C := C) (B := B) (H := H) b ri := by
  dsimp [close]
  calc
    (evalAt (C := C) (B := B) (H := H) b ≫ ri.β) ≫ (evalAt (C := C) (B := B) (H := H) b ≫ ri.β)
        = evalAt (C := C) (B := B) (H := H) b ≫
            (ri.β ≫ evalAt (C := C) (B := B) (H := H) b) ≫ ri.β := by
            simp [Category.assoc]
    _ = evalAt (C := C) (B := B) (H := H) b ≫ 𝟙 H ≫ ri.β := by
            simp [ri.right_inv]
    _ = evalAt (C := C) (B := B) (H := H) b ≫ ri.β := by simp

end close

end Cat
end ClosingTheLoop
end HeytingLean
