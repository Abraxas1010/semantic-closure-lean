import Mathlib.Logic.Function.Basic

namespace HeytingLean
namespace Noneism

universe u

/-- A value `a` is an eigenform of `d` if it is the unique fixed point of `d`. -/
structure IsEigenform {α : Type u} (d : α → α) (a : α) : Prop where
  stable : d a = a
  unique : ∀ b, d b = b → b = a

/-- An eigencomputable value: a value together with the dynamics that determines it and a proof
that it is the unique fixed point. -/
structure Eigen (α : Type u) where
  val : α
  dynamics : α → α
  isEigenform : IsEigenform dynamics val

namespace Eigen

instance {α : Type u} : Coe (Eigen α) α :=
  ⟨fun e => e.val⟩

theorem determined_by_dynamics {α : Type u} (e : Eigen α) (a : α) (ha : e.dynamics a = a) :
    a = e.val :=
  e.isEigenform.unique a ha

theorem val_unique_of_eq_dynamics {α : Type u} (e₁ e₂ : Eigen α) (h : e₁.dynamics = e₂.dynamics) :
    e₁.val = e₂.val := by
  apply e₂.isEigenform.unique
  simpa [h] using e₁.isEigenform.stable

/-- Build an `Eigen` value from a proof of unique existence of a fixed point. -/
noncomputable def ofExistsUniqueFixedPoint {α : Type u} (d : α → α) (h : ∃! a, d a = a) :
    Eigen α := by
  classical
  refine ⟨Classical.choose h, d, ?_⟩
  refine ⟨?_, ?_⟩
  · exact (Classical.choose_spec h).1
  · intro b hb
    exact (Classical.choose_spec h).2 b hb

/-- The crossing constructor: dynamics + a unique fixed point yields an `Eigen`. -/
noncomputable abbrev cross {α : Type u} (d : α → α) (h : ∃! a, d a = a) : Eigen α :=
  ofExistsUniqueFixedPoint d h

end Eigen

end Noneism
end HeytingLean
