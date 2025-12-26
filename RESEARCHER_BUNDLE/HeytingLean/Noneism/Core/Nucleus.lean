import Mathlib.Order.Nucleus
import HeytingLean.Noneism.Eigen.Dynamics

namespace HeytingLean
namespace Noneism

namespace Core

open HeytingLean.Noneism.Eigen

universe u

variable {α : Type u} [SemilatticeInf α]

/-- View an `Order.Nucleus` as a dynamics. -/
def nucleusDynamics (n : Nucleus α) : Dynamics α :=
  ⟨n⟩

/-- Fixed-point predicate for a nucleus. -/
def IsStable (n : Nucleus α) (x : α) : Prop :=
  n x = x

theorem stable_apply (n : Nucleus α) (x : α) : IsStable n (n x) := by
  simp [IsStable]

end Core

end Noneism
end HeytingLean

