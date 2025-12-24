import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Nucleus

/-!
# Closing the Loop: preorder time semantics scaffolding (Tier 2)

We treat time as a **preorder** (a causal/temporal partial order). Mathlib provides a canonical
category structure on any preorder, so we can use functorial time-indexing `T ⥤ Type _`
from `ClosingTheLoop.FA.Temporal` with `T` specialized to a preorder.

This file adds a small, objective “semantic kernel” construction over preorder time:
given a time-indexed state functor `X : T ⥤ Type _` and a time-indexed predicate `S t : Set (X t)`,
define the subset of states at time `t` whose images at all future times satisfy `S`.

This operator is:
- monotone in `S`,
- idempotent,
- meet-preserving (intersection),

so its fixed points are exactly the “future-closed” safety properties over preorder time.

In addition, to match the repo’s default **inflationary nucleus** convention, we also provide
an explicit `Nucleus` on time-indexed predicates (relative to a chosen base time `t₀` with a
global reachability hypothesis `∀ t, t₀ ≤ t`), which adds all states that are unreachable from
that base time.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Semantics

open CategoryTheory

universe u v w

variable {T : Type u} [Preorder T]
variable (X : T ⥤ Type w)

/-- The “future kernel” of a time-indexed predicate `S`.

An element `x : X t` lies in `futureKernel X S t` iff for every future time `t' ≥ t`,
transporting along the unique morphism `t ⟶ t'` yields an element in `S t'`. -/
def futureKernel (S : ∀ t : T, Set (X.obj t)) : ∀ t : T, Set (X.obj t) :=
  fun t =>
    {x | ∀ t' : T, ∀ h : t ≤ t', X.map (CategoryTheory.homOfLE h) x ∈ S t'}

namespace futureKernel

variable {X}

lemma monotone :
    Monotone (futureKernel X) := by
  intro S₁ S₂ hS t x hx t' h
  exact hS _ (hx t' h)

lemma contractive (S : ∀ t : T, Set (X.obj t)) (t : T) :
    futureKernel X S t ⊆ S t := by
  intro x hx
  simpa using hx t (le_rfl)

lemma map_homOfLE_trans_apply {t t' t'' : T} (ht' : t ≤ t') (ht'' : t' ≤ t'')
    (x : X.obj t) :
    X.map (CategoryTheory.homOfLE (le_trans ht' ht'')) x =
      X.map (CategoryTheory.homOfLE ht'') (X.map (CategoryTheory.homOfLE ht') x) := by
  have hhom :
      (CategoryTheory.homOfLE (le_trans ht' ht'')) =
        (CategoryTheory.homOfLE ht' ≫ CategoryTheory.homOfLE ht'') := by
    rfl
  calc
    X.map (CategoryTheory.homOfLE (le_trans ht' ht'')) x
        = X.map (CategoryTheory.homOfLE ht' ≫ CategoryTheory.homOfLE ht'') x := by
          exact congrArg (fun f => f x) (congrArg X.map hhom)
    _ = (X.map (CategoryTheory.homOfLE ht') ≫ X.map (CategoryTheory.homOfLE ht'')) x := by
          simpa using
            congrArg (fun f => f x)
              (X.map_comp (CategoryTheory.homOfLE ht') (CategoryTheory.homOfLE ht''))
    _ = X.map (CategoryTheory.homOfLE ht'') (X.map (CategoryTheory.homOfLE ht') x) := rfl

lemma idem (S : ∀ t : T, Set (X.obj t)) :
    futureKernel X (futureKernel X S) = futureKernel X S := by
  funext t
  ext x
  constructor
  · intro hx t' ht'
    have hx' : X.map (CategoryTheory.homOfLE ht') x ∈ futureKernel X S t' :=
      hx t' ht'
    exact (contractive (X := X) (S := S) t') hx'
  · intro hx t' ht' t'' ht''
    -- Need: for any future `t'`, the transported state lies in `futureKernel X S t'`.
    -- Use `hx` at the composite future time.
    have hx'' : X.map (CategoryTheory.homOfLE (le_trans ht' ht'')) x ∈ S t'' :=
      hx t'' (le_trans ht' ht'')
    -- Convert single-step transport to composed transport (functoriality + `homOfLE_comp`).
    simpa [map_homOfLE_trans_apply (X := X) (ht' := ht') (ht'' := ht'') (x := x)] using hx''

lemma meet (S₁ S₂ : ∀ t : T, Set (X.obj t)) :
    futureKernel X (fun t => S₁ t ∩ S₂ t) = fun t => futureKernel X S₁ t ∩ futureKernel X S₂ t := by
  funext t
  ext x
  constructor
  · intro hx
    refine And.intro ?_ ?_
    · intro t' h
      exact (hx t' h).1
    · intro t' h
      exact (hx t' h).2
  · rintro ⟨hx₁, hx₂⟩
    intro t' h
    exact And.intro (hx₁ t' h) (hx₂ t' h)

end futureKernel

/-! ## Inflationary nucleus packaging (LoF convention) -/

section Nucleus

open Set

variable {X}
variable (t₀ : T) (hBase : ∀ t : T, t₀ ≤ t)

/-- States at time `t` that are unreachable from the chosen base time `t₀`. -/
def unreachableFrom : ∀ t : T, Set (X.obj t) :=
  fun t =>
    {x | ¬ ∃ x0 : X.obj t₀, X.map (CategoryTheory.homOfLE (hBase t)) x0 = x}

/-- A preorder-time `Nucleus` on time-indexed predicates: “treat unreachable states as vacuously
admissible” by unioning them into every predicate. -/
def reachabilityNucleus : Nucleus (∀ t : T, Set (X.obj t)) where
  toFun S := fun t => S t ∪ unreachableFrom (X := X) t₀ hBase t
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

@[simp] lemma reachabilityNucleus_apply (S : ∀ t : T, Set (X.obj t)) (t : T) :
    reachabilityNucleus (X := X) t₀ hBase S t = S t ∪ unreachableFrom (X := X) t₀ hBase t := rfl

section Bot

variable [OrderBot T]

/-- Special case: unreachable states from the canonical base time `⊥`. -/
abbrev unreachableFromBot : ∀ t : T, Set (X.obj t) :=
  unreachableFrom (X := X) (t₀ := ⊥) (hBase := fun t => (bot_le : ⊥ ≤ t))

/-- Special case: reachability nucleus from the canonical base time `⊥`. -/
abbrev reachabilityNucleusBot : Nucleus (∀ t : T, Set (X.obj t)) :=
  reachabilityNucleus (X := X) (t₀ := ⊥) (hBase := fun t => (bot_le : ⊥ ≤ t))

end Bot

end Nucleus

end Semantics
end ClosingTheLoop
end HeytingLean
