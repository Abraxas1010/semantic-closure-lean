import HeytingLean.Process.Syntax
import HeytingLean.Process.Typing
import HeytingLean.Process.Semantics

/-!
Tiny payment→ack example to exercise the calculus.
- Channels: pay (Nat), ack (Unit)
- Client: send pay n ; recv ack ; nil
- Server: recv pay x ; send ack () ; nil
- System: Client | Server reduces via comms.
-/

namespace HeytingLean
namespace Process

open Classical

-- channels
def payC : ChanId := 0
def ackC : ChanId := 1

def natTy : ChanTy := ⟨ValTy.nat⟩
def unitTy : ChanTy := ⟨ValTy.unit⟩

-- context: pay:Nat, ack:Unit, others undefined
def Γ0 : ChanCtx := fun a => if a = payC then some natTy else if a = ackC then some unitTy else none

-- client for amount n
def Client (n : Nat) : Proc :=
  Proc.send payC (Val.nat n) <|
    Proc.recv ackC (fun _ => Proc.nil)

-- server: receive amount, then ack
def Server : Proc :=
  Proc.recv payC (fun v =>
    match v with
    | Val.nat _ => Proc.send ackC Val.unit Proc.nil
    | _ => Proc.nil)

def System (n : Nat) : Proc := Proc.parr (Client n) Server

namespace Typing

open WellTypedProc HasValType

private lemma ctx_pay : Γ0 payC = some natTy := by
  unfold Γ0 payC
  simp

private lemma ack_ne_pay : ackC ≠ payC := by decide

private lemma ctx_ack : Γ0 ackC = some unitTy := by
  unfold Γ0 ackC payC
  simp [ack_ne_pay]

lemma client_typed {n} : WellTypedProc Γ0 (Client n) := by
  -- send pay n; then wait for ack
  have hpay : Γ0 payC = some natTy := ctx_pay
  have hack : Γ0 ackC = some unitTy := ctx_ack
  refine WellTypedProc.send Γ0 payC natTy (Val.nat n) (Proc.recv ackC (fun _ => Proc.nil)) hpay (HasValType.nat n) ?hrecv
  refine WellTypedProc.recv Γ0 ackC unitTy (fun _ => Proc.nil) hack ?hk
  intro v hv; cases v with
  | unit => exact WellTypedProc.nil Γ0
  | _ => cases hv

/-- Typing derivation for the server process that waits for a `pay` and replies with `ack`. -/
lemma server_typed : WellTypedProc Γ0 Server := by
  -- recv pay, then send ack
  have hpay : Γ0 payC = some natTy := ctx_pay
  have hack : Γ0 ackC = some unitTy := ctx_ack
  refine WellTypedProc.recv Γ0 payC natTy (fun v => match v with | Val.nat _ => Proc.send ackC Val.unit Proc.nil | _ => Proc.nil) hpay ?hk
  intro v hv; cases v with
  | nat _ =>
      refine WellTypedProc.send Γ0 ackC unitTy Val.unit Proc.nil hack HasValType.unit (WellTypedProc.nil Γ0)
  | _ => cases hv

/-- The composed client/server system is well-typed for every payment amount `n`. -/
lemma system_typed {n} : WellTypedProc Γ0 (System n) :=
  WellTypedProc.par Γ0 (Client n) Server (client_typed) (server_typed)

end Typing

namespace Steps

open Reduces

/-- First reduction step: the client sends `pay n` which the server receives. -/
lemma step_pay (n : Nat) :
  System n ⟶ Proc.parr (Proc.recv ackC (fun _ => Proc.nil)) (Proc.send ackC Val.unit Proc.nil) := by
  -- top-level comm on payC
  change Proc.parr (Proc.send payC (Val.nat n) (Proc.recv ackC (fun _ => Proc.nil))) Server ⟶ _
  -- unfold Server to expose recv payC
  unfold Server
  -- apply comm rule; use symmetry by placing matching sides
  exact Reduces.comm payC (Val.nat n) (Proc.recv ackC (fun _ => Proc.nil)) (fun v => match v with | Val.nat _ => Proc.send ackC Val.unit Proc.nil | _ => Proc.nil)

/-- Second reduction step: the server responds with `ack`, completing the handshake. -/
lemma step_ack (n : Nat) :
  Proc.parr (Proc.recv ackC (fun _ => Proc.nil)) (Proc.send ackC Val.unit Proc.nil)
    ⟶ Proc.parr Proc.nil Proc.nil := by
  -- communicate on ackC
  change _ ⟶ Proc.parr _ _
  exact Reduces.comm_symm ackC Val.unit Proc.nil (fun _ => Proc.nil)

/-- Two-step reduction from the initial system to a pair of inactive processes. -/
lemma two_steps (n : Nat) : System n ⟶* Proc.parr Proc.nil Proc.nil :=
  ReducesStar.step (step_pay (n:=n)) (ReducesStar.step (step_ack (n:=n)) (ReducesStar.refl _))

end Steps

namespace Safety

open Process.Typing Reduces ReducesStar

/-- After the two communication steps, the resulting process remains well typed under `Γ0`. -/
theorem subject_reduction_two_steps (n : Nat) :
    WellTypedProc Γ0 (Proc.parr Proc.nil Proc.nil) := by
  have hTyped : WellTypedProc Γ0 (System n) :=
    Typing.system_typed (n := n)
  have hSteps : System n ⟶* Proc.parr Proc.nil Proc.nil :=
    Steps.two_steps (n := n)
  exact ReducesStar.subject_reduction hTyped hSteps

end Safety

end Process
end HeytingLean
