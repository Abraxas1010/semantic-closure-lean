import HeytingLean.Noneism
import Lean

namespace HeytingLean
namespace Noneism
namespace Tests

open HeytingLean.Noneism

section BetaSanity

open Bridge

def sampleF : Bridge.Metabolism (A := Nat) (B := Nat) :=
  fun x => x + 1

example : Bridge.evalAt (A := Nat) (B := Nat) (b := 0) (Bridge.beta (A := Nat) (B := Nat) 0 sampleF) = sampleF := by
  simpa using Bridge.beta_right_inverse (A := Nat) (B := Nat) (b := 0) sampleF

end BetaSanity

section AttributeSanity

open Lean
open HeytingLean.Noneism.Eigen.Attr

run_cmd do
  let env ← getEnv
  let some dyn := eigencomputableDynamicsName? env `HeytingLean.Noneism.Bridge.betaEigenAt
    | throwError "missing eigencomputable tag for betaEigenAt"
  let ok :=
    dyn == `selectorDynamicsAt ∨ dyn == `HeytingLean.Noneism.Bridge.selectorDynamicsAt
  unless ok do
    throwError "unexpected dynamics name: {dyn}"

end AttributeSanity

end Tests
end Noneism
end HeytingLean

