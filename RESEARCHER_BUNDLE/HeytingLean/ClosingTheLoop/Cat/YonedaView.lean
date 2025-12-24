import HeytingLean.ClosingTheLoop.Cat.Selector

/-!
# Closing the Loop: currying / representability view (Tier 2)

Assumptions:
- `C` cartesian monoidal and cartesian closed.
- `B H X : C`.

Agenda mapping:
- The currying equivalence `Hom(B ⊗ X, H) ≃ Hom(X, H^B)` is the representability principle
  behind a Yoneda-friendly reconstruction story: “selectors” are the representing object for
  the functor `X ↦ Hom(B ⊗ X, H)`.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Cat

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {B H X : C} [CategoryTheory.Exponentiable B]

/-- Currying equivalence: `Hom(B ⊗ X, H) ≃ Hom(X, H^B)`. -/
def curryEquiv :
    (B ⊗ X ⟶ H) ≃ (X ⟶ SelectorObj (C := C) B H) where
  toFun := CategoryTheory.CartesianClosed.curry (A := B) (Y := X) (X := H)
  invFun := CategoryTheory.CartesianClosed.uncurry (A := B) (Y := X) (X := H)
  left_inv := by
    intro f
    simp
  right_inv := by
    intro f
    simp

end Cat
end ClosingTheLoop
end HeytingLean
