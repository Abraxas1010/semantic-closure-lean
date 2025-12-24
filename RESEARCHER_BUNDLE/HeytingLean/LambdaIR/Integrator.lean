import Mathlib.Tactic

import HeytingLean.LambdaIR.SDE

/-!
# SDE Integrators (Phase 2)

We implement two standard discrete-time stepping rules:

- Euler–Maruyama (Ito-style; also used as a predictor),
- Heun / stochastic trapezoid (used as a Stratonovich integrator).

These are defined purely as functions on `ι → ℝ` vectors and do not assume any stochastic
convergence theorem; they are meant as "compiler targets" with strong shape correctness.
-/

noncomputable section

namespace HeytingLean
namespace LambdaIR
namespace SDE

open SDESystem

section Steps

variable {ι : Type} {κ : Type} [Fintype ι] [Fintype κ]

/-- Single Euler–Maruyama step. -/
def eulerStep (S : SDESystem ι κ) (dt : ℝ) (dW : Vec κ) (x : Vec ι) : Vec ι :=
  x + dt • S.drift x + mulVec (S.diffusion x) dW

/-- Single Heun (predictor-corrector) step.

This is the common Stratonovich integrator obtained by applying the trapezoid rule to both the
drift and diffusion terms. -/
def stratonovichStep (S : SDESystem ι κ) (dt : ℝ) (dW : Vec κ) (x : Vec ι) : Vec ι :=
  let xPred : Vec ι := eulerStep S dt dW x
  x + (dt / 2) • (S.drift x + S.drift xPred)
    + (1 / 2) • mulVec (S.diffusion x + S.diffusion xPred) dW

@[simp] lemma eulerStep_zero (dt : ℝ) (dW : Vec κ) (x : Vec ι) :
    eulerStep (S := SDESystem.zero (ι := ι) (κ := κ)) dt dW x = x := by
  simp [eulerStep, SDESystem.zero]

@[simp] lemma stratonovichStep_zero (dt : ℝ) (dW : Vec κ) (x : Vec ι) :
    stratonovichStep (S := SDESystem.zero (ι := ι) (κ := κ)) dt dW x = x := by
  simp [stratonovichStep, SDESystem.zero]

end Steps

/-! ## Trajectories and Monte Carlo averages -/

section Trajectory

variable {ι : Type} {κ : Type} [Fintype ι] [Fintype κ]

/-- Run a trajectory given a fixed timestep `dt` and a list of noise increments `dW₀, …, dWₙ₋₁`.

Returns the list of states including the initial state. -/
def simulateTrajectory (S : SDESystem ι κ) (dt : ℝ) (x0 : Vec ι) (dWs : List (Vec κ)) :
    List (Vec ι) :=
  dWs.scanl (fun x dW => stratonovichStep S dt dW x) x0

@[simp] lemma simulateTrajectory_nil (S : SDESystem ι κ) (dt : ℝ) (x0 : Vec ι) :
    simulateTrajectory S dt x0 [] = [x0] := by
  simp [simulateTrajectory]

end Trajectory

section Mean

variable {ι : Type}

/-- Pointwise average of a list of states, returning `0` on the empty list. -/
def mean (xs : List (Vec ι)) : Vec ι :=
  match xs with
  | [] => 0
  | _ =>
      let n : ℝ := xs.length
      (1 / n) • xs.foldl (fun acc x => acc + x) 0

@[simp] lemma mean_nil : mean (ι := ι) ([] : List (Vec ι)) = 0 := rfl

end Mean

end SDE
end LambdaIR
end HeytingLean
