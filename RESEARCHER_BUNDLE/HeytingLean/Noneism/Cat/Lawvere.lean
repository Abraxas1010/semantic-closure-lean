import Mathlib.Logic.Function.Basic

namespace HeytingLean
namespace Noneism
namespace Cat

universe u v

/-- A Type-level fixed point theorem: a point-surjective `A → (A → B)` yields fixed points for all
endomaps `B → B`. -/
theorem fixedPoint_of_surjective_eval {A : Type u} {B : Type v} (e : A → (A → B))
    (hsurj : Function.Surjective e) (g : B → B) : ∃ b : B, g b = b := by
  classical
  let h : A → B := fun a => g ((e a) a)
  rcases hsurj h with ⟨a₀, ha₀⟩
  refine ⟨h a₀, ?_⟩
  have he : (e a₀) a₀ = h a₀ := by
    simpa using congrArg (fun f => f a₀) ha₀
  have hb : h a₀ = g (h a₀) := by
    calc
      h a₀ = g ((e a₀) a₀) := rfl
      _ = g (h a₀) := congrArg g he
  exact hb.symm

end Cat
end Noneism
end HeytingLean
