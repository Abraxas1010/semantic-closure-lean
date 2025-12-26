import HeytingLean.Noneism.Eigen.Basic

namespace HeytingLean
namespace Noneism
namespace Crossing

open HeytingLean.Noneism.Eigen

universe u

/-- The crossing constructor: package a unique fixed point of a dynamics as an `Eigen`. -/
noncomputable abbrev cross {α : Type u} (d : α → α) (h : ∃! a, d a = a) : Eigen α :=
  Eigen.cross d h

end Crossing
end Noneism
end HeytingLean

