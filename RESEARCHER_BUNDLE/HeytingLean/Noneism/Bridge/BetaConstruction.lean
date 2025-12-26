import HeytingLean.Noneism.Bridge.BetaEigen

namespace HeytingLean
namespace Noneism
namespace Bridge

universe u v

variable (A : Type u) (B : Type v) (b : B)

/-- A choice-based right inverse of `evalAt`, given surjectivity. -/
noncomputable def betaRaw (hsurj : SurjectiveEvalAt (A := A) (B := B) b)
    (f : Metabolism (A := A) (B := B)) : Selector (A := A) (B := B) :=
  Classical.choose (hsurj f)

theorem betaRaw_right_inverse (hsurj : SurjectiveEvalAt (A := A) (B := B) b)
    (f : Metabolism (A := A) (B := B)) :
    evalAt (A := A) (B := B) b (betaRaw (A := A) (B := B) b hsurj f) = f :=
  Classical.choose_spec (hsurj f)

theorem beta_eq_const (f : Metabolism (A := A) (B := B)) :
    beta (A := A) (B := B) b f = (fun _ => f) := by
  classical
  let p : Selector (A := A) (B := B) → Prop :=
    fun Φ =>
      selectorDynamics (A := A) (B := B) b Φ = Φ ∧ evalAt (A := A) (B := B) b Φ = f
  have huniq : ∃! Φ : Selector (A := A) (B := B), p Φ := by
    simpa [p] using selectorDynamics_unique_stable (A := A) (B := B) b f
  have p_beta : p (beta (A := A) (B := B) b f) :=
    ⟨beta_stable (A := A) (B := B) b f, beta_right_inverse (A := A) (B := B) b f⟩
  have p_const : p (fun _ => f) := by
    constructor
    · funext b'
      simp [selectorDynamics]
    · simp [evalAt]
  exact ExistsUnique.unique huniq p_beta p_const

/-- If a choice-based right inverse is stable, it agrees with `beta`. -/
theorem beta_eq_betaRaw_of_stable (hsurj : SurjectiveEvalAt (A := A) (B := B) b)
    (f : Metabolism (A := A) (B := B)) (hstable :
      selectorDynamics (A := A) (B := B) b (betaRaw (A := A) (B := B) b hsurj f) =
        betaRaw (A := A) (B := B) b hsurj f) :
    beta (A := A) (B := B) b f = betaRaw (A := A) (B := B) b hsurj f := by
  let p : Selector (A := A) (B := B) → Prop :=
    fun Φ =>
      selectorDynamics (A := A) (B := B) b Φ = Φ ∧ evalAt (A := A) (B := B) b Φ = f
  have huniq : ∃! Φ : Selector (A := A) (B := B), p Φ := by
    simpa [p] using selectorDynamics_unique_stable (A := A) (B := B) b f
  have p_beta : p (beta (A := A) (B := B) b f) :=
    ⟨beta_stable (A := A) (B := B) b f, beta_right_inverse (A := A) (B := B) b f⟩
  have p_betaRaw : p (betaRaw (A := A) (B := B) b hsurj f) :=
    ⟨hstable, betaRaw_right_inverse (A := A) (B := B) b hsurj f⟩
  exact ExistsUnique.unique huniq p_beta p_betaRaw

end Bridge
end Noneism
end HeytingLean
