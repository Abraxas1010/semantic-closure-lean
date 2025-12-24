import HeytingLean.Process.Syntax
import HeytingLean.Process.Typing

/-!
Small-step semantics for the minimal process calculus and subject reduction.
- Reduces: communication, choice, cond, and parallel congruence
- ReducesStar: reflexive–transitive closure
- Subject reduction for the rules present here
-/

namespace HeytingLean
namespace Process

open Classical

inductive Reduces : Proc → Proc → Prop
| comm (a : ChanId) (v : Val) (P : Proc) (k : Val → Proc) :
    Reduces (Proc.parr (Proc.send a v P) (Proc.recv a k)) (Proc.parr P (k v))
| comm_symm (a : ChanId) (v : Val) (P : Proc) (k : Val → Proc) :
    Reduces (Proc.parr (Proc.recv a k) (Proc.send a v P)) (Proc.parr (k v) P)
| par_left  {P P' Q} : Reduces P P' → Reduces (Proc.parr P Q) (Proc.parr P' Q)
| par_right {P Q Q'} : Reduces Q Q' → Reduces (Proc.parr P Q) (Proc.parr P Q')
| choice_left  (P Q) : Reduces (Proc.choice P Q) P
| choice_right (P Q) : Reduces (Proc.choice P Q) Q
| cond_true  (P Q)   : Reduces (Proc.cond (Val.bool true) P Q) P
| cond_false (P Q)   : Reduces (Proc.cond (Val.bool false) P Q) Q
| rep_unfold (P)     : Reduces (Proc.rep P) (Proc.parr P (Proc.rep P))

infix:50 " ⟶ " => Reduces

inductive ReducesStar : Proc → Proc → Prop
| refl (P) : ReducesStar P P
| step {P Q R} : Reduces P Q → ReducesStar Q R → ReducesStar P R

infix:50 " ⟶* " => ReducesStar

namespace Reduces

open WellTypedProc

theorem subject_reduction
  {Γ P P'} (hP : WellTypedProc Γ P) (hstep : P ⟶ P') : WellTypedProc Γ P' := by
  induction hstep generalizing Γ with
  | @comm a v P k =>
      -- P = send a v P | recv a k
      cases hP with
      | par _ _ _ hL hR =>
          -- Invert typing of left and right
          rcases inv_send (Γ:=Γ) (a:=a) (v:=v) (P:=P) hL with ⟨τ, ha, hv, hP'⟩
          rcases inv_recv (Γ:=Γ) (a:=a) (k:=k) hR with ⟨τ', ha', hk⟩
          -- Channel type must agree; use some-injectivity to align payloads
          have ht : some τ = some τ' := by exact Eq.trans (Eq.symm ha) ha'
          have hτ : τ = τ' := by cases ht; rfl
          -- Build typed result
          have hkv : WellTypedProc Γ (k v) := by
            have hvτ' : HasValType v τ'.payload := by simpa [hτ] using hv
            exact hk v hvτ'
          exact WellTypedProc.par Γ P (k v) hP' hkv
  | @comm_symm a v P k =>
      -- P = recv a k | send a v P
      cases hP with
      | par _ _ _ hL hR =>
          rcases inv_recv (Γ:=Γ) (a:=a) (k:=k) hL with ⟨τ, haL, hk⟩
          rcases inv_send (Γ:=Γ) (a:=a) (v:=v) (P:=P) hR with ⟨τ', haR, hv, hP'⟩
          have ht : some τ = some τ' := by exact Eq.trans (Eq.symm haL) haR
          have hτ : τ = τ' := by cases ht; rfl
          have hkv : WellTypedProc Γ (k v) := by
            have hvτ : HasValType v τ.payload := by simpa [hτ] using hv
            exact hk v hvτ
          exact WellTypedProc.par Γ (k v) P hkv hP'
  | @par_left P P' Q h ih =>
      cases hP with
      | par _ _ _ hPL hPQ =>
          exact WellTypedProc.par Γ P' Q (ih hPL) hPQ
  | @par_right P Q Q' h ih =>
      cases hP with
      | par _ _ _ hPL hPQ =>
          exact WellTypedProc.par Γ P Q' hPL (ih hPQ)
  | @choice_left P Q =>
      cases hP with
      | choice _ _ _ hPt _ => exact hPt
  | @choice_right P Q =>
      cases hP with
      | choice _ _ _ _ hQt => exact hQt
  | @cond_true P Q =>
      cases hP with
      | cond _ _ _ _ _ hP' _ => exact hP'
  | @cond_false P Q =>
      cases hP with
      | cond _ _ _ _ _ _ hQ' => exact hQ'
  | @rep_unfold P =>
      cases hP with
      | rep _ _ hP' => exact WellTypedProc.par Γ P (Proc.rep P) hP' (WellTypedProc.rep Γ P hP')

end Reduces

namespace ReducesStar

open WellTypedProc

theorem trans {P Q R} : (P ⟶* Q) → (Q ⟶* R) → (P ⟶* R) := by
  intro hPQ hQR; induction hPQ with
  | refl P => simpa using hQR
  | step h hPR ih => exact ReducesStar.step h (ih hQR)

theorem subject_reduction
  {Γ P P'} (hP : WellTypedProc Γ P) (hsteps : ReducesStar P P') :
  WellTypedProc Γ P' := by
  induction hsteps generalizing Γ with
  | refl P =>
      simpa using hP
  | step h hPR ih =>
      -- First apply single-step subject reduction, then propagate along the tail.
      exact ih (Reduces.subject_reduction hP h)

end ReducesStar

end Process
end HeytingLean
