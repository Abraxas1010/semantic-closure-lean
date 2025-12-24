import HeytingLean.Process.Syntax
import HeytingLean.Process.Semantics

/-!
Simple readiness predicate and a tiny progress lemma for a ready pair
at the top level (not a full progress theorem).
-/

namespace HeytingLean
namespace Process

inductive Ready : Proc → Prop
| send (a v P) : Ready (Proc.send a v P)
| recv (a k)   : Ready (Proc.recv a k)

open Ready

def ReadyPair (P : Proc) : Prop :=
  ∃ a v P' k, P = Proc.parr (Proc.send a v P') (Proc.recv a k)

open Reduces

theorem ready_pair_steps {P} : ReadyPair P → ∃ Q, P ⟶ Q := by
  intro h; rcases h with ⟨a,v,P',k,hP⟩; subst hP; exact ⟨_, Reduces.comm a v P' k⟩

end Process
end HeytingLean

