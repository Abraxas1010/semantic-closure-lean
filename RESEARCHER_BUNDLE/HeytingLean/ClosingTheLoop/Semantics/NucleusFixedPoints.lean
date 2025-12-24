import Mathlib.Order.Sublocale

/-!
# Closing the Loop: nuclei and closed fixed points (Tier 3)

This file makes the “nucleus ⇒ closed fixed-point Heyting core” step precise using mathlib’s
`Order.Nucleus` and `Order.Sublocale` development.

Assumptions:
- To construct a `Nucleus`, one needs an inflationary idempotent `inf`-preserving endomorphism.
- To talk about the Heyting structure on the closed part, we work in a frame (`Order.Frame`).

Agenda mapping:
- Separates what is proved from what is assumed: idempotence alone is not enough to claim a nucleus.
- Packages the fixed-point story as a reusable lemma and a constructor.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Semantics

open Set

universe u

section NucleusOfClosure

variable {α : Type u} [SemilatticeInf α]

/-- Build a `Nucleus` from an inflationary idempotent `inf`-preserving endomorphism.

Agenda mapping:
- This is the precise boundary between “idempotent closure” and “nucleus/Heyting” claims:
  the extra hypotheses are exactly `le_close` and `map_inf`. -/
def nucleusOfClosure (close : α → α)
    (le_close : ∀ x : α, x ≤ close x)
    (idem : ∀ x : α, close (close x) = close x)
    (map_inf : ∀ x y : α, close (x ⊓ y) = close x ⊓ close y) :
    Nucleus α where
  toFun := close
  map_inf' := map_inf
  idempotent' x := by
    simp [idem x]
  le_apply' x := le_close x

end NucleusOfClosure

section FixedPoints

variable {X : Type u} [Order.Frame X] (n : Nucleus X)

/-- The “closed part” of a nucleus, as a sublocale (carrier is `Set.range n`). -/
abbrev Ω : Sublocale X :=
  n.toSublocale

/-- Membership in the closed part is equivalent to being a fixed point. -/
theorem mem_Ω_iff_fixed {x : X} : x ∈ (n.toSublocale : Set X) ↔ n x = x := by
  constructor
  · intro hx
    rcases hx with ⟨y, rfl⟩
    simp
  · intro hx
    exact ⟨x, hx⟩

end FixedPoints

end Semantics
end ClosingTheLoop
end HeytingLean
