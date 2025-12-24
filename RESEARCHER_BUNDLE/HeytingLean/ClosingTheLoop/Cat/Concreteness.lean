import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Yoneda
import HeytingLean.ClosingTheLoop.Cat.ClosureOperator

/-!
# Closing the Loop: a minimal “concreteness” bridge (Tier 2)

This file does not attempt a philosophical treatment of “concreteness”. It isolates two
mathematically precise mechanisms by which one can reason about morphisms using *functions*:

1. **External concreteness assumption**: a faithful functor `U : C ⥤ Type _` lets us reflect
   equalities of morphisms from equalities of the underlying functions.
2. **Canonical Yoneda embedding**: without any external assumption, every category embeds fully
   faithfully into presheaves via `yoneda : C ⥤ (Cᵒᵖ ⥤ Type _)`.

Assumptions:
- For (1): a faithful functor `U : C ⥤ Type _`.
- For (2): none beyond `Category C` (Yoneda is always fully faithful).

Agenda mapping:
- Clarifies that “faithful embedding into `Set`/`Type`” is an *assumption*, while the Yoneda
  embedding is canonical (into presheaves, not into `Type` itself).
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Cat

open CategoryTheory
open CategoryTheory.Functor

universe u v w

variable {C : Type u} [Category.{v} C]
variable (U : C ⥤ Type w) [Functor.Faithful U]

/-- If `U` is faithful, then idempotence of a mapped endomorphism implies idempotence upstairs. -/
theorem idem_of_map_idem {X : C} (f : X ⟶ X) (h : U.map f ≫ U.map f = U.map f) :
    f ≫ f = f := by
  apply (Functor.map_injective U)
  simpa [Functor.map_comp] using h

section Yoneda

open CategoryTheory

/-- Yoneda is faithful, so idempotence of `yoneda.map f` reflects to idempotence of `f`.

This is the “no concreteness needed” version of `idem_of_map_idem`: you can always work in the
canonical presheaf model. -/
theorem idem_of_yoneda_map_idem {X : C} (f : X ⟶ X)
    (h : (yoneda.map f) ≫ (yoneda.map f) = yoneda.map f) : f ≫ f = f := by
  apply (Functor.map_injective (yoneda : C ⥤ (Cᵒᵖ ⥤ Type v)))
  simpa [Functor.map_comp] using h

end Yoneda

/-! ## A scoped “structure preservation” bridge

To interpret the categorical selector object `H^B` as an *actual function space*
`U(B) → U(H)` (and evaluation at a point as evaluation of functions), one needs additional
data beyond mere faithfulness:

* an equivalence `U(H^B) ≃ (U(B) → U(H))`, and
* a compatibility statement that `U.map (evalAt b)` is evaluation at the induced point.

Rather than overclaiming “any faithful `U` preserves exponentials”, we package the exact
comparison needed for this construction.
-/

section StructurePreservation

open CategoryTheory.MonoidalCategory

variable [CartesianMonoidalCategory C]
variable {B H : C} [CategoryTheory.Exponentiable B] (b : 𝟙_ C ⟶ B)

variable (U₀ : C ⥤ Type w)

/-- A chosen point of `U₀.obj B` induced by a global element `b : 𝟙 ⟶ B`,
assuming `U₀.obj 𝟙` has been identified with the singleton type. -/
def pointUnder (unitEquiv : U₀.obj (𝟙_ C) ≃ PUnit) : U₀.obj B :=
  U₀.map b (unitEquiv.symm PUnit.unit)

/-- A minimal comparison package expressing that a functor `U₀ : C ⥤ Type` preserves just enough
structure to interpret the selector object as a function space and evaluation at `b` as
evaluation of functions.

This is intentionally *not* a global “preserves exponentials” typeclass: it records exactly the
comparison data and the single compatibility equation used in this project. -/
structure PreservesSelectorEval where
  /-- Identify `U₀(𝟙)` with the singleton type to extract points from global elements. -/
  unitEquiv : U₀.obj (𝟙_ C) ≃ PUnit
  /-- Identify `U₀(H^B)` with the function space `U₀(B) → U₀(H)`. -/
  expEquiv : U₀.obj (SelectorObj (C := C) B H) ≃ (U₀.obj B → U₀.obj H)
  /-- Compatibility: `U₀.map (evalAt b)` is evaluation at the induced point of `U₀(B)`. -/
  map_evalAt :
    U₀.map (evalAt (C := C) (B := B) (H := H) b) =
      fun x => expEquiv x (pointUnder (C := C) (B := B) (U₀ := U₀) b unitEquiv)

/-- If `U₀` identifies the selector object with a function space and sends `evalAt b` to
evaluation at the induced point, then `U₀.map (close b ri)` is exactly the expected
“close by sampling at `b`” operator on functions. -/
theorem map_close_eq (unitEquiv : U₀.obj (𝟙_ C) ≃ PUnit)
    (expEquiv : U₀.obj (SelectorObj (C := C) B H) ≃ (U₀.obj B → U₀.obj H))
    (h_eval :
      U₀.map (evalAt (C := C) (B := B) (H := H) b) =
        fun x => expEquiv x (pointUnder (C := C) (B := B) (U₀ := U₀) b unitEquiv))
    (ri : RightInverseAt (C := C) (B := B) (H := H) b)
    (f : U₀.obj B → U₀.obj H) :
    expEquiv (U₀.map (close (C := C) (B := B) (H := H) b ri) (expEquiv.symm f)) =
      expEquiv (U₀.map ri.β (f (pointUnder (C := C) (B := B) (U₀ := U₀) b unitEquiv))) := by
  have hEvalAt :
      U₀.map (evalAt (C := C) (B := B) (H := H) b) (expEquiv.symm f) =
        f (pointUnder (C := C) (B := B) (U₀ := U₀) b unitEquiv) := by
    -- Apply the compatibility hypothesis to the specific argument, then simplify via the equivalence laws.
    have := congrArg (fun g => g (expEquiv.symm f)) h_eval
    simpa [pointUnder] using this
  -- Expand `close` and map through `U₀`.
  dsimp [close]
  -- `U₀.map (f ≫ g) = U₀.map f ≫ U₀.map g` in `Type`, i.e. function composition.
  simp [hEvalAt]

/-- Same as `map_close_eq`, but bundled through `PreservesSelectorEval`. -/
theorem map_close_eq' (p : PreservesSelectorEval (C := C) (B := B) (H := H) (b := b) U₀)
    (ri : RightInverseAt (C := C) (B := B) (H := H) b)
    (f : U₀.obj B → U₀.obj H) :
    p.expEquiv (U₀.map (close (C := C) (B := B) (H := H) b ri) (p.expEquiv.symm f)) =
      p.expEquiv (U₀.map ri.β (f (pointUnder (C := C) (B := B) (U₀ := U₀) b p.unitEquiv))) := by
  simpa [p.map_evalAt] using
    (map_close_eq (C := C) (B := B) (H := H) (b := b) (U₀ := U₀)
      (unitEquiv := p.unitEquiv) (expEquiv := p.expEquiv) (h_eval := p.map_evalAt)
      ri f)

end StructurePreservation

end Cat
end ClosingTheLoop
end HeytingLean
