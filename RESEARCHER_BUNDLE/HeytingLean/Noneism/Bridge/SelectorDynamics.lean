import HeytingLean.Noneism.Bridge.EvaluationMap

namespace HeytingLean
namespace Noneism
namespace Bridge

universe u v

variable (A : Type u) (B : Type v) (b : B)

open scoped Classical

/-- The selector dynamics: re-close a selector through `b` by forgetting everything except `Φ b`. -/
def selectorDynamics : Selector (A := A) (B := B) → Selector (A := A) (B := B) :=
  fun Φ => fun _ => Φ b

theorem selectorDynamics_stable_iff (Φ : Selector (A := A) (B := B)) :
    selectorDynamics (A := A) (B := B) b Φ = Φ ↔ ∀ b', Φ b' = Φ b := by
  constructor
  · intro h b'
    have : selectorDynamics (A := A) (B := B) b Φ b' = Φ b' := congrFun h b'
    simpa [selectorDynamics] using this.symm
  · intro h
    funext b'
    simpa [selectorDynamics] using (h b').symm

/-- For each metabolism `f`, there is a unique stable selector whose evaluation at `b` is `f`. -/
theorem selectorDynamics_unique_stable (f : Metabolism (A := A) (B := B)) :
    ∃! Φ : Selector (A := A) (B := B),
      selectorDynamics (A := A) (B := B) b Φ = Φ ∧ evalAt (A := A) (B := B) b Φ = f := by
  refine ⟨fun _ => f, ?_, ?_⟩
  · constructor
    · funext b'
      simp [selectorDynamics]
    · simp [evalAt]
  · intro Φ' hΦ'
    funext b'
    funext a
    have hstable : selectorDynamics (A := A) (B := B) b Φ' = Φ' := hΦ'.1
    have heval : evalAt (A := A) (B := B) b Φ' = f := hΦ'.2
    have hb' : Φ' b' = Φ' b := (selectorDynamics_stable_iff (A := A) (B := B) b Φ').1 hstable b'
    have hb : Φ' b = f := by simpa [evalAt] using heval
    have hb'_a : Φ' b' a = Φ' b a := by
      simpa using congrArg (fun g => g a) hb'
    have hb_a : Φ' b a = f a := by
      simpa using congrArg (fun g => g a) hb
    exact hb'_a.trans hb_a

/-- Dynamics on the fiber of selectors evaluating to a fixed metabolism. -/
def selectorDynamicsAt (f : Metabolism (A := A) (B := B)) :
    {Φ : Selector (A := A) (B := B) // evalAt (A := A) (B := B) b Φ = f} →
      {Φ : Selector (A := A) (B := B) // evalAt (A := A) (B := B) b Φ = f} :=
  fun x =>
    ⟨selectorDynamics (A := A) (B := B) b x.1, by
      have hx : x.1 b = f := by simpa [evalAt] using x.2
      simp [evalAt, selectorDynamics, hx]⟩

end Bridge
end Noneism
end HeytingLean
