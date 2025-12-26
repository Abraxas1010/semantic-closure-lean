import HeytingLean.Noneism.Eigen.Dynamics

namespace HeytingLean
namespace Noneism
namespace Eigen

universe u

/-- A type has eigenstructure if it comes with a distinguished dynamics and a proof that the
dynamics has a unique fixed point. -/
class HasEigenstructure (α : Type u) where
  dynamics : α → α
  has_unique_fixed : ∃! a, dynamics a = a

/-- The canonical eigenvalue for a type with eigenstructure. -/
noncomputable def eigenvalue {α : Type u} [h : HasEigenstructure α] : Eigen α :=
  Eigen.cross h.dynamics h.has_unique_fixed

theorem eigenvalue_stable {α : Type u} [h : HasEigenstructure α] :
    h.dynamics ((eigenvalue : Eigen α).val) = (eigenvalue : Eigen α).val :=
  (eigenvalue : Eigen α).isEigenform.stable

theorem eigenvalue_unique {α : Type u} [h : HasEigenstructure α] (a : α) (ha : h.dynamics a = a) :
    a = (eigenvalue : Eigen α).val :=
  (eigenvalue : Eigen α).isEigenform.unique a ha

end Eigen
end Noneism
end HeytingLean

