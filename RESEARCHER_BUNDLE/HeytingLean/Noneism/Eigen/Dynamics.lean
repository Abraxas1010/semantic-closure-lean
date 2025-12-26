import HeytingLean.Noneism.Eigen.Basic

namespace HeytingLean
namespace Noneism
namespace Eigen

universe u

/-- A dynamics on a type. -/
structure Dynamics (α : Type u) where
  step : α → α

namespace Dynamics

variable {α : Type u} (d : Dynamics α)

/-- Iteration of a dynamics. -/
def iterate : Nat → α → α
  | 0, a => a
  | n + 1, a => d.step (iterate n a)

/-- Stability for a dynamics. -/
def IsStable (a : α) : Prop :=
  d.step a = a

/-- Unique stability for a dynamics. -/
def HasUniqueStable : Prop :=
  ∃! a, d.IsStable a

/-- Extract the unique stable point as an `Eigen` value. -/
noncomputable def stablePoint (h : d.HasUniqueStable) : Eigen α :=
  Eigen.cross d.step h

end Dynamics

end Eigen
end Noneism
end HeytingLean

