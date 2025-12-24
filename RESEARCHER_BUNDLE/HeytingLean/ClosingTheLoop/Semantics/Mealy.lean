import HeytingLean.ClosingTheLoop.MR.ClosureOperator

/-!
# Closing the Loop: Mealy / coalgebra bridge (Tier 2)

This file provides a minimal Mealy-machine definition (input/output automaton) and
instantiates it with the (M,R) loop-closing operator `MR.closeSelector`.

Agenda mapping (connections):
- **Mealy machines / coalgebras**: a Mealy machine is a coalgebra for the functor `X ↦ I → X × O`.
- **Semantic closure**: idempotent “closing” yields stabilization after one step, and the
  fixed points are exactly the closed organizations (`MR.IsClosed`).

We keep the claims strictly local and constructive: no terminal-coalgebra assumptions.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Semantics

universe u v w

/-- A (deterministic) Mealy machine with input alphabet `I`, output alphabet `O`, and state `S`. -/
structure Mealy (I : Type u) (O : Type v) (S : Type w) where
  step : S → I → S × O

namespace Mealy

variable {I : Type u} {O : Type v} {S : Type w}

/-- One-step state update. -/
@[simp] def stepState (m : Mealy I O S) (s : S) (i : I) : S := (m.step s i).1

/-- One-step output. -/
@[simp] def stepOut (m : Mealy I O S) (s : S) (i : I) : O := (m.step s i).2

end Mealy

/-! ## Coalgebra view -/

/-- Endofunctor for Mealy machines: `X ↦ I → X × O`. -/
def MealyF (I : Type u) (O : Type v) (X : Type w) :=
  I → X × O

/-- A minimal coalgebra (in `Type`), enough to phrase the Mealy connection. -/
structure Coalgebra (F : Type w → Type _) where
  carrier : Type w
  str : carrier → F carrier

namespace Coalgebra

variable {I : Type u} {O : Type v} {S : Type w}

/-- Any Mealy machine is a coalgebra for `MealyF I O`. -/
def ofMealy (m : Mealy I O S) : Coalgebra (MealyF (I := I) (O := O)) where
  carrier := S
  str := fun s => fun i => m.step s i

/-- Any coalgebra for `MealyF I O` is a Mealy machine. -/
def toMealy (c : Coalgebra (MealyF (I := I) (O := O))) :
    Mealy I O c.carrier where
  step := fun s i => c.str s i

end Coalgebra

/-! ## (M,R) as a Mealy dynamics (autonomous closure loop) -/

namespace MRBridge

open MR

universe u' v'

variable {S : MRSystem.{u', v'}} {b : S.B} (RI : RightInverseAt S b)

/-- The closure loop viewed as an (autonomous) Mealy machine:
one input step `⋆` updates the selector by `closeSelector`, and outputs the repaired map at `b`. -/
def closeMachine : Mealy PUnit (AdmissibleMap S) (Selector S) where
  step Φ _ :=
    let Φ' := closeSelector S b RI Φ
    (Φ', Φ' b)

@[simp] lemma closeMachine_step_fst (Φ : Selector S) :
    ((closeMachine (S := S) (b := b) RI).step Φ PUnit.unit).1 = closeSelector S b RI Φ := by
  simp [closeMachine]

@[simp] lemma closeMachine_step_snd (Φ : Selector S) :
    ((closeMachine (S := S) (b := b) RI).step Φ PUnit.unit).2 = Φ b := by
  simp [closeMachine, closeSelector.close_apply_at]

/-- After one step, the machine state is a closed selector (organizational closure). -/
theorem closeMachine_state_closed (Φ : Selector S) :
    MR.IsClosed S b RI ((closeMachine (S := S) (b := b) RI).step Φ PUnit.unit).1 := by
  -- `IsClosed` for the post-step state is exactly idempotence of `closeSelector`.
  simp [closeMachine, MR.IsClosed, closeSelector.idem]

/-- The closure loop stabilizes in one additional step (idempotence). -/
theorem closeMachine_step_idem (Φ : Selector S) :
    let m := closeMachine (S := S) (b := b) RI
    m.step (m.step Φ PUnit.unit).1 PUnit.unit = m.step Φ PUnit.unit := by
  intro m
  -- both components stabilize: state by idempotence, output by evaluation-at-`b` stability
  ext <;> simp [m, closeMachine, closeSelector.idem]

end MRBridge

end Semantics
end ClosingTheLoop
end HeytingLean
