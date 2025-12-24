import Mathlib.CategoryTheory.Limits.Shapes.Images
import HeytingLean.ClosingTheLoop.Cat.Selector

/-!
# Closing the Loop: categorical inverse-on-image of evaluation (Tier 2)

In `Set`, an “inverse evaluation” can always be defined *on the range* of a function:
it is the choice-free, witness-carrying construction `MR.EvalImage`.

Categorically, the analogous object is the image `image (evalAt b)` of evaluation
`evalAt b : (B ⟹ H) ⟶ H`. Without extra assumptions one does **not** get a map
`H ⟶ (B ⟹ H)`; the best one can do is:

- a canonical morphism `image (evalAt b) ⟶ (B ⟹ H)` whenever `evalAt b` is a monomorphism,
  using `imageMonoIsoSource`.

This matches the paper’s “inverse evaluation” move *only on the image* unless an
additional section (split epi) is assumed.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Cat

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.Limits

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {B H : C} [CategoryTheory.Exponentiable B] (b : 𝟙_ C ⟶ B)

namespace EvalImage

/-- The categorical image object of evaluation at `b`. -/
abbrev Obj (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]
    (B H : C) [CategoryTheory.Exponentiable B] (b : 𝟙_ C ⟶ B)
    [HasImage (evalAt (C := C) (B := B) (H := H) b)] : C :=
  image (evalAt (C := C) (B := B) (H := H) b)

/-- The inclusion `image (evalAt b) ⟶ H`. -/
abbrev ι (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]
    (B H : C) [CategoryTheory.Exponentiable B] (b : 𝟙_ C ⟶ B)
    [HasImage (evalAt (C := C) (B := B) (H := H) b)] :
    Obj (C := C) (B := B) (H := H) b ⟶ H :=
  image.ι (evalAt (C := C) (B := B) (H := H) b)

/-- If `evalAt b` is mono, we get a canonical “inverse on the image”
`image (evalAt b) ⟶ (B ⟹ H)`. -/
def betaOnImage (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]
    (B H : C) [CategoryTheory.Exponentiable B] (b : 𝟙_ C ⟶ B)
    [Mono (evalAt (C := C) (B := B) (H := H) b)] :
    Obj (C := C) (B := B) (H := H) b ⟶ SelectorObj (C := C) B H :=
  (imageMonoIsoSource (evalAt (C := C) (B := B) (H := H) b)).hom

@[simp, reassoc]
  theorem betaOnImage_evalAt [Mono (evalAt (C := C) (B := B) (H := H) b)] :
      betaOnImage (C := C) (B := B) (H := H) b ≫ evalAt (C := C) (B := B) (H := H) b =
        ι (C := C) (B := B) (H := H) b := by
  simp [betaOnImage, ι]

/-- Under mono, the source factors through the image via the `imageMonoIsoSource` inverse. -/
theorem factorThruImage_eq_inv [Mono (evalAt (C := C) (B := B) (H := H) b)] :
    factorThruImage (evalAt (C := C) (B := B) (H := H) b) =
      (imageMonoIsoSource (evalAt (C := C) (B := B) (H := H) b)).inv := by
  -- Both maps compose with `image.ι` to give `evalAt`.
  apply (cancel_mono (ι (C := C) (B := B) (H := H) b)).1
  simp [ι]

end EvalImage

end

end Cat
end ClosingTheLoop
end HeytingLean
