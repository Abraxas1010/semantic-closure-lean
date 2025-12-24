import Mathlib.Data.Set.Basic

/-!
# Closing the Loop: Rosen-style (M,R) scaffold (Tier 1)

This module provides a minimal `Set`-based encoding of the (M,R) ingredients used
in `WIP/closure_paper.md`:

- types `A`, `B`,
- a set `H ⊆ (A → B)` of admissible maps,
- a distinguished metabolism `f ∈ H`,
- an admissible selector space `H(B, H(A,B)) ⊆ (B → H(A,B))`,
- evaluation at a configuration `b : B`.

Assumptions:
- None beyond working in `Set` (types and functions).
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace MR

universe u v

/-- A minimal Rosen (M,R) system in `Set`: admissible maps `H(A,B)`, together with `f ∈ H`. -/
structure MRSystem where
  A : Type u
  B : Type v
  /-- Admissible maps `H(A,B) ⊆ (A → B)`. -/
  H : Set (A → B)
  /-- A distinguished metabolism map. -/
  f : A → B
  hf : f ∈ H
  /-- Admissible selectors `H(B, H(A,B)) ⊆ (B → H(A,B))`. -/
  Sel : Set (B → {g : A → B // g ∈ H})
  /-- A distinguished selector / repair map (paper notation: `Φ_f`). -/
  Φf : B → {g : A → B // g ∈ H}
  hΦf : Φf ∈ Sel

/-- An admissible map bundled with its membership proof. -/
abbrev AdmissibleMap (S : MRSystem.{u, v}) : Type (max u v) :=
  {g : S.A → S.B // g ∈ S.H}

/-- Replacement/repair selectors: admissible maps `B → H(A,B)` with their admissibility proof. -/
abbrev Selector (S : MRSystem.{u, v}) : Type (max u v) :=
  {Φ : S.B → AdmissibleMap S // Φ ∈ S.Sel}

instance (S : MRSystem.{u, v}) : CoeFun (Selector S) (fun _ => S.B → AdmissibleMap S) where
  coe Φ := Φ.1

/-- Evaluation at a chosen configuration `b : B`. -/
def evalAt (S : MRSystem.{u, v}) (b : S.B) : Selector S → AdmissibleMap S :=
  fun Φ => Φ b

@[simp] lemma evalAt_apply (S : MRSystem.{u, v}) (b : S.B) (Φ : Selector S) :
    evalAt S b Φ = Φ b := rfl

/-- Paper-shaped uniqueness hypothesis: evaluation at `b` is injective on admissible selectors. -/
def EvalAtInjective (S : MRSystem.{u, v}) (b : S.B) : Prop :=
  Function.Injective (evalAt S b)

end MR
end ClosingTheLoop
end HeytingLean
