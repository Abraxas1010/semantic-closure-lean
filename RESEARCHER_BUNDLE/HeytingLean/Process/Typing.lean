import Mathlib.Data.Set.Lattice
import HeytingLean.Process.Syntax

/-!
Typing for the minimal process calculus.
 - Channel context and extension
 - Value typing
 - Process typing (WellTypedProc)
 - Weakening and simple inversion lemmas
-/

namespace HeytingLean
namespace Process

open Classical

abbrev ChanCtx := ChanId → Option ChanTy

def extend (Γ : ChanCtx) (a : ChanId) (τ : ChanTy) : ChanCtx :=
  fun x => if x = a then some τ else Γ x

inductive HasValType : Val → ValTy → Prop
| unit  : HasValType Val.unit ValTy.unit
| bool  : ∀ b, HasValType (Val.bool b) ValTy.bool
| int   : ∀ i, HasValType (Val.int i) ValTy.int
| nat   : ∀ n, HasValType (Val.nat n) ValTy.nat
| pair  : ∀ v₁ v₂ τ₁ τ₂,
    HasValType v₁ τ₁ →
    HasValType v₂ τ₂ →
    HasValType (Val.pair v₁ v₂) (ValTy.prod τ₁ τ₂)
| inl   : ∀ v τ₁ τ₂,
    HasValType v τ₁ →
    HasValType (Val.inl v) (ValTy.sum τ₁ τ₂)
| inr   : ∀ v τ₁ τ₂,
    HasValType v τ₂ →
    HasValType (Val.inr v) (ValTy.sum τ₁ τ₂)

-- no simp attribute needed here

inductive WellTypedProc : ChanCtx → Proc → Prop
| nil   : ∀ Γ, WellTypedProc Γ Proc.nil
| send  : ∀ Γ a τ v P,
    Γ a = some τ →
    HasValType v τ.payload →
    WellTypedProc Γ P →
    WellTypedProc Γ (Proc.send a v P)
| recv  : ∀ Γ a τ k,
    Γ a = some τ →
    (∀ v, HasValType v τ.payload → WellTypedProc Γ (k v)) →
    WellTypedProc Γ (Proc.recv a k)
| par   : ∀ Γ P Q,
    WellTypedProc Γ P →
    WellTypedProc Γ Q →
    WellTypedProc Γ (Proc.parr P Q)
| new   : ∀ Γ τ k,
    (∀ a, WellTypedProc (extend Γ a τ) (k a)) →
    WellTypedProc Γ (Proc.new τ k)
| choice : ∀ Γ P Q,
    WellTypedProc Γ P →
    WellTypedProc Γ Q →
    WellTypedProc Γ (Proc.choice P Q)
| cond   : ∀ Γ b P Q,
    HasValType b ValTy.bool →
    WellTypedProc Γ P →
    WellTypedProc Γ Q →
    WellTypedProc Γ (Proc.cond b P Q)
| rep    : ∀ Γ P,
    WellTypedProc Γ P →
    WellTypedProc Γ (Proc.rep P)

namespace WellTypedProc

-- Inversion helpers for core forms used in subject reduction
lemma inv_par {Γ P Q} (h : WellTypedProc Γ (Proc.parr P Q)) :
  WellTypedProc Γ P ∧ WellTypedProc Γ Q := by
  cases h with
  | par _ _ _ hP hQ => exact And.intro hP hQ

/-- Inversion lemma for a well-typed `send`: it yields the channel type, value typing, and continuation typing. -/
lemma inv_send {Γ a v P}
  (h : WellTypedProc Γ (Proc.send a v P)) :
  ∃ τ, Γ a = some τ ∧ HasValType v τ.payload ∧ WellTypedProc Γ P := by
  cases h with
  | send _ _ τ _ _ ha hv hP => exact ⟨τ, ha, hv, hP⟩

/-- Inversion lemma for a well-typed `recv`: it exposes the channel type and continuation typing premise. -/
lemma inv_recv {Γ a k}
  (h : WellTypedProc Γ (Proc.recv a k)) :
  ∃ τ, Γ a = some τ ∧ (∀ v, HasValType v τ.payload → WellTypedProc Γ (k v)) := by
  cases h with
  | recv _ _ τ _ ha hk => exact ⟨τ, ha, hk⟩

end WellTypedProc

end Process
end HeytingLean
