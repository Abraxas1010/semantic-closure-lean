import HeytingLean.Noneism.Eigen.Basic
import HeytingLean.Noneism.Eigen.Attribute
import HeytingLean.Noneism.Bridge.SelectorDynamics

namespace HeytingLean
namespace Noneism
namespace Bridge

open HeytingLean.Noneism.Eigen

universe u v

variable (A : Type u) (B : Type v) (b : B)

abbrev SelectorAt (f : Metabolism (A := A) (B := B)) :=
  {Φ : Selector (A := A) (B := B) // evalAt (A := A) (B := B) b Φ = f}

theorem selectorDynamicsAt_unique_fixed (f : Metabolism (A := A) (B := B)) :
    ∃! x : SelectorAt (A := A) (B := B) b f,
      selectorDynamicsAt (A := A) (B := B) b f x = x := by
  refine ⟨⟨fun _ => f, by simp [evalAt]⟩, ?_, ?_⟩
  · ext b'
    simp [selectorDynamicsAt, selectorDynamics]
  · intro x hx
    have hx0 : selectorDynamics (A := A) (B := B) b x.1 = x.1 := by
      exact congrArg (fun y => y.1) hx
    have hconst : ∀ b', x.1 b' = x.1 b :=
      (selectorDynamics_stable_iff (A := A) (B := B) b x.1).1 hx0
    ext b' a
    have hb : x.1 b = f := by simpa [evalAt] using x.2
    have hb_a : x.1 b a = f a := congrArg (fun g => g a) hb
    have hb'_a : x.1 b' a = x.1 b a := congrArg (fun g => g a) (hconst b')
    exact hb'_a.trans hb_a

/-- The eigencomputable selector at `f`, as the unique fixed point of the fiber dynamics. -/
@[eigencomputable selectorDynamicsAt]
noncomputable def betaEigenAt (f : Metabolism (A := A) (B := B)) :
    Eigen (SelectorAt (A := A) (B := B) b f) :=
  Eigen.ofExistsUniqueFixedPoint
    (selectorDynamicsAt (A := A) (B := B) b f)
    (selectorDynamicsAt_unique_fixed (A := A) (B := B) b f)

/-- The underlying selector obtained from `betaEigenAt`. -/
noncomputable def beta (f : Metabolism (A := A) (B := B)) : Selector (A := A) (B := B) :=
  (betaEigenAt (A := A) (B := B) b f).val.1

theorem beta_right_inverse (f : Metabolism (A := A) (B := B)) :
    evalAt (A := A) (B := B) b (beta (A := A) (B := B) b f) = f :=
  (betaEigenAt (A := A) (B := B) b f).val.2

theorem beta_stable (f : Metabolism (A := A) (B := B)) :
    selectorDynamics (A := A) (B := B) b (beta (A := A) (B := B) b f) =
      beta (A := A) (B := B) b f := by
  have h :=
    (betaEigenAt (A := A) (B := B) b f).isEigenform.stable
  -- Project equality in the fiber.
  exact congrArg (fun x => x.1) h

end Bridge
end Noneism
end HeytingLean
