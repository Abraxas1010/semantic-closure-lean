import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic

/-!
# SDE IR (Phase 2)

This file introduces a **mathematical** SDE representation that we can translate TWA models into.

Notes:
- This is **not** the existing `LambdaIR.Term` calculus (which is nat/bool-only today). Instead,
  this module lives under `HeytingLean.LambdaIR` because it is intended to serve as the next
  compiler-facing "IR layer" for stochastic dynamics.
- We intentionally keep this IR *typed by finite index types* (`ι` for state coordinates, `κ` for
  noise coordinates). This gives strong shape guarantees without having to constantly juggle `Nat`
  bounds.
- Stochastic calculus theorems (Ito/Stratonovich convergence) are out of scope here; we focus on
  well-typedness and algebraic invariants we can already prove.
-/

noncomputable section

namespace HeytingLean
namespace LambdaIR
namespace SDE

universe u v

abbrev Vec (ι : Type u) : Type u := ι → ℝ
abbrev Mat (ι : Type u) (κ : Type v) : Type (max u v) := Matrix ι κ ℝ

/-- A (Stratonovich-style) SDE system with state index `ι` and noise index `κ`. -/
structure SDESystem (ι : Type u) (κ : Type v) [Fintype ι] [Fintype κ] where
  drift : Vec ι → Vec ι
  diffusion : Vec ι → Mat ι κ

namespace SDESystem

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]

/-- Zero SDE: no drift and no diffusion. -/
def zero : SDESystem ι κ :=
  { drift := fun _ => 0
    diffusion := fun _ => 0 }

end SDESystem

/-! ## Matrix-vector helper -/

section MulVec

variable {ι : Type u} {κ : Type v} [Fintype κ]

abbrev mulVec (B : Mat ι κ) (dW : Vec κ) : Vec ι :=
  B.mulVec dW

@[simp] lemma mulVec_zero_left (dW : Vec κ) : mulVec (ι := ι) (κ := κ) (0 : Mat ι κ) dW = 0 := by
  simp [mulVec]

@[simp] lemma mulVec_zero_right (B : Mat ι κ) : mulVec (ι := ι) (κ := κ) B (0 : Vec κ) = 0 := by
  simp [mulVec]

end MulVec

end SDE
end LambdaIR
end HeytingLean
