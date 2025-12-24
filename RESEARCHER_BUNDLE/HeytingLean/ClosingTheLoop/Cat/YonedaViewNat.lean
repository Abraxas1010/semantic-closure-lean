import HeytingLean.ClosingTheLoop.Cat.Selector

/-!
# Closing the Loop: functorial currying (Yoneda-style) (Tier 2)

This file upgrades the pointwise currying equivalence

`Hom(B ⊗ X, H) ≃ Hom(X, H^B)`

into a natural isomorphism of functors in `X`.

Agenda mapping:
- Addresses the research note that (M,R)-style selector reconstruction can be
  presented functorially via the Yoneda lemma / representability.
- The functor `X ↦ Hom(B ⊗ X, H)` is represented by the exponential object `H^B`.

We work contravariantly in `X` (functors `Cᵒᵖ ⥤ Type _`).
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Cat

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {B H : C} [CategoryTheory.Exponentiable B]

/-- The hom-functor `X ↦ Hom(B ⊗ X, H)` (contravariant in `X`). -/
def homTensorLeft (B H : C) : Cᵒᵖ ⥤ Type v where
  obj X := (B ⊗ (Opposite.unop X) ⟶ H)
  map {X Y} f g := (B ◁ f.unop) ≫ g
  map_id X := by
    ext g
    simp
  map_comp {X Y Z} f g := by
    ext h
    simp

/-- The hom-functor `X ↦ Hom(X, H^B)` (contravariant in `X`). -/
def homSelectorObj (B H : C) [CategoryTheory.Exponentiable B] : Cᵒᵖ ⥤ Type v where
  obj X := (Opposite.unop X ⟶ SelectorObj (C := C) B H)
  map {X Y} f g := f.unop ≫ g
  map_id X := by
    ext g
    simp
  map_comp {X Y Z} f g := by
    ext h
    simp

/-- The functorial currying isomorphism in `X`.

At each object `X`, the component is `CategoryTheory.CartesianClosed.curry`.
Naturality follows from `CategoryTheory.CartesianClosed.curry_natural_left`.
-/
def curryNatIso (B H : C) [CategoryTheory.Exponentiable B] :
    homTensorLeft (C := C) B H ≅ homSelectorObj (C := C) B H := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · refine (Equiv.toIso
      { toFun := CategoryTheory.CartesianClosed.curry (A := B) (Y := Opposite.unop X) (X := H)
        invFun := CategoryTheory.CartesianClosed.uncurry (A := B) (Y := Opposite.unop X) (X := H)
        left_inv := by
          intro f
          simp
        right_inv := by
          intro f
          simp })
  · intro X Y f
    ext g
    simpa [homTensorLeft, homSelectorObj] using
      (CategoryTheory.CartesianClosed.curry_natural_left (A := B) (X := Opposite.unop Y)
        (X' := Opposite.unop X) (Y := H) (f := f.unop) (g := g))

end Cat
end ClosingTheLoop
end HeytingLean
