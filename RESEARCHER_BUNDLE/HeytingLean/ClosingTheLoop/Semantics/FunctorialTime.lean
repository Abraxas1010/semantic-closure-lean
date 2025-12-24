import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Nucleus
import HeytingLean.ClosingTheLoop.Semantics.KernelLaws

/-!
# Closing the Loop: functorial time semantics (Tier 2)

`FA/Temporal` treats time as an arbitrary small category `T` and time-indexed state spaces
as functors `X : T ⥤ Type _`.

This file extends the preorder-time semantics seed to **general time categories** by replacing
the preorder reachability condition `t ≤ t'` with quantification over morphisms `t ⟶ t'`.

Core constructions:

* `futureKernel`: a contractive/idempotent/meet-preserving operator on time-indexed predicates,
  expressing “holds in all futures reachable by a morphism”.
* `reachabilityNucleus`: an inflationary nucleus (LoF convention) that treats states unreachable
  from a chosen base time `t₀` as vacuously admissible, defined without choosing a specific
  arrow `t₀ ⟶ t` (it unions over *all* arrows).
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Semantics

open CategoryTheory
open Set

universe u v w

namespace FunctorialTime

variable {T : Type u} [Category.{v} T]
variable (X : T ⥤ Type w)

/-- Functorial-time “future kernel” of a time-indexed predicate `S`:
`x : X t` is in the kernel iff for every arrow `f : t ⟶ t'`, transporting along `f`
lands in `S t'`. -/
def futureKernel (S : ∀ t : T, Set (X.obj t)) : ∀ t : T, Set (X.obj t) :=
  fun t =>
    {x | ∀ ⦃t' : T⦄, ∀ f : t ⟶ t', X.map f x ∈ S t'}

namespace futureKernel

variable {X}

lemma monotone : Monotone (futureKernel X) := by
  intro S₁ S₂ hS t x hx t' f
  exact hS _ (hx f)

lemma contractive (S : ∀ t : T, Set (X.obj t)) (t : T) :
    futureKernel X S t ⊆ S t := by
  intro x hx
  simpa using hx (𝟙 t)

lemma idem (S : ∀ t : T, Set (X.obj t)) :
    futureKernel X (futureKernel X S) = futureKernel X S := by
  funext t
  ext x
  constructor
  · intro hx t' f
    have hx' : X.map f x ∈ futureKernel X S t' := hx f
    exact (contractive (X := X) (S := S) t') hx'
  · intro hx t' f t'' g
    -- Use functoriality: `X.map g (X.map f x) = X.map (f ≫ g) x`.
    simpa using (hx (f ≫ g))

lemma meet (S₁ S₂ : ∀ t : T, Set (X.obj t)) :
    futureKernel X (fun t => S₁ t ∩ S₂ t) = fun t => futureKernel X S₁ t ∩ futureKernel X S₂ t := by
  funext t
  ext x
  constructor
  · intro hx
    refine And.intro ?_ ?_
    · intro t' f; exact (hx f).1
    · intro t' f; exact (hx f).2
  · rintro ⟨hx₁, hx₂⟩
    intro t' f
    exact And.intro (hx₁ f) (hx₂ f)

end futureKernel

/-- Package `futureKernel` as a generic `Semantics.Kernel` on time-indexed predicates. -/
def futureKernelKernel : Kernel (α := ∀ t : T, Set (X.obj t)) where
  toFun := futureKernel X
  monotone' := futureKernel.monotone (X := X)
  map_inf' S T := by
    -- `inf` on predicates is pointwise intersection.
    simpa [Pi.inf_apply, inf_eq_inter] using (futureKernel.meet (X := X) S T)
  idempotent' S := by
    funext t
    ext x
    simpa using congrArg (fun F => F t x) (futureKernel.idem (X := X) S)
  apply_le' S := by
    intro t x hx
    exact futureKernel.contractive (X := X) (S := S) t hx

/-! ## Inflationary reachability nucleus (LoF convention) -/

variable {X}

/-- States at time `t` that are unreachable from the chosen base time `t₀`
(there is no arrow `t₀ ⟶ t` and base state mapping to them). -/
def unreachableFrom (t₀ : T) : ∀ t : T, Set (X.obj t) :=
  fun t =>
    {x | ¬ ∃ (f : t₀ ⟶ t) (x0 : X.obj t₀), X.map f x0 = x}

/-- A functorial-time `Nucleus` on predicates: close by unioning in unreachable states.

This uses the “union with an unreachable set” pattern from `PreorderTime`, but does not
require choosing any particular arrow `t₀ ⟶ t`. -/
def reachabilityNucleus (t₀ : T) : Nucleus (∀ t : T, Set (X.obj t)) where
  toFun S := fun t => S t ∪ unreachableFrom (X := X) t₀ t
  map_inf' S T := by
    funext t
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨Or.inl hx.1, Or.inl hx.2⟩
      · exact ⟨Or.inr hx, Or.inr hx⟩
    · rintro ⟨hxS, hxT⟩
      cases hxS with
      | inl hxS =>
          cases hxT with
          | inl hxT => exact Or.inl ⟨hxS, hxT⟩
          | inr hxU => exact Or.inr hxU
      | inr hxU =>
          exact Or.inr hxU
  idempotent' S := by
    intro t x hx
    rcases hx with hx | hx
    · exact hx
    · exact Or.inr hx
  le_apply' S := by
    intro t x hx
    exact Or.inl hx

@[simp] lemma reachabilityNucleus_apply (t₀ : T) (S : ∀ t : T, Set (X.obj t)) (t : T) :
    reachabilityNucleus (X := X) t₀ S t = S t ∪ unreachableFrom (X := X) t₀ t := rfl

end FunctorialTime

end Semantics
end ClosingTheLoop
end HeytingLean
