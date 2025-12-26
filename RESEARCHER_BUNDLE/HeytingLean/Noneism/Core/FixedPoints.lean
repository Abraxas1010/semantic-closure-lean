import Mathlib.Order.Sublocale

namespace HeytingLean
namespace Noneism
namespace Core

open Set

universe u

variable {X : Type u} [Order.Frame X] (n : Nucleus X)

/-- The fixed-point locus of a nucleus, as a sublocale. -/
abbrev Ω : Sublocale X :=
  n.toSublocale

theorem mem_Ω_iff_fixed {x : X} : x ∈ (n.toSublocale : Set X) ↔ n x = x := by
  constructor
  · intro hx
    rcases hx with ⟨y, rfl⟩
    simp
  · intro hx
    exact ⟨x, hx⟩

end Core
end Noneism
end HeytingLean

