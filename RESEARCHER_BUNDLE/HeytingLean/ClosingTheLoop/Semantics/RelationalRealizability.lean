import Mathlib.Data.Set.Lattice
import HeytingLean.ClosingTheLoop.Semantics.KernelLaws
import HeytingLean.ClosingTheLoop.Semantics.Mealy
import HeytingLean.ClosingTheLoop.Semantics.LambdaIRBridge
import HeytingLean.ClosingTheLoop.Semantics.ProcessBridge
import HeytingLean.Process.Semantics

/-!
# Closing the Loop: relational realizability (Tier 2)

This file provides a single “relational realizability” theorem that unifies the
λ-calculus / process / Mealy hooks at the level of **reachability relations**.

Core idea:

*A computation model induces a reachability relation `Reach` on states.*

Given a relation `R` between two state spaces, if `R` is a simulation w.r.t. reachability,
then **invariants transport**: any future-closed predicate on the target yields a future-closed
predicate on the source via realizability (`∃`-witness).

This is the minimal, publication-grade statement capturing “limits of realizability of
relational models” without committing to a specific compilation/encoding between calculi.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Semantics

open Set

universe u v

/-- A reachability-based computation model: a state space equipped with a reflexive/transitive
reachability relation (think: multi-step reduction, time evolution, etc.). -/
structure ReachSystem where
  State : Type u
  Reach : State → State → Prop
  refl : ∀ x, Reach x x
  trans : ∀ {x y z}, Reach x y → Reach y z → Reach x z

namespace ReachSystem

variable (S : ReachSystem)

/-- Safety kernel induced by reachability: keep states whose every reachable future state lies in `P`. -/
def K (P : Set S.State) : Set S.State :=
  {x | ∀ y, S.Reach x y → y ∈ P}

lemma K_contract (P : Set S.State) : S.K P ⊆ P := by
  intro x hx
  simpa using hx x (S.refl x)

lemma K_monotone : Monotone S.K := by
  intro P Q hPQ x hx y hy
  exact hPQ (hx y hy)

lemma K_idem (P : Set S.State) : S.K (S.K P) = S.K P := by
  ext x
  constructor
  · intro hx y hy
    have hyK : y ∈ S.K P := hx y hy
    exact hyK y (S.refl y)
  · intro hx y hy z hz
    exact hx z (S.trans hy hz)

lemma K_meet (P Q : Set S.State) : S.K (P ∩ Q) = S.K P ∩ S.K Q := by
  ext x
  constructor
  · intro hx
    refine And.intro ?_ ?_
    · intro y hy; exact (hx y hy).1
    · intro y hy; exact (hx y hy).2
  · rintro ⟨hxP, hxQ⟩ y hy
    exact And.intro (hxP y hy) (hxQ y hy)

/-- `K` packaged as a generic `Semantics.Kernel` on `Set State`. -/
def kernel : Kernel (α := Set S.State) where
  toFun := S.K
  monotone' := S.K_monotone
  map_inf' P Q := by
    simpa [inf_eq_inter] using (S.K_meet P Q)
  idempotent' P := by
    simpa using (S.K_idem P)
  apply_le' P := by
    intro x hx
    exact S.K_contract P hx

/-- A predicate is future-closed if it is closed under reachability. -/
def IsInvariant (P : Set S.State) : Prop :=
  ∀ ⦃x y⦄, S.Reach x y → x ∈ P → y ∈ P

lemma K_eq_of_invariant (P : Set S.State) (hInv : S.IsInvariant P) : S.K P = P := by
  ext x
  constructor
  · intro hx; exact S.K_contract P hx
  · intro hx y hy
    exact hInv hy hx

end ReachSystem

/-! ## Relational realizability -/

namespace Realizability

variable {S₁ : ReachSystem} {S₂ : ReachSystem}

/-- A reachability simulation: every reachable future in `S₁` can be matched by a reachable
future in `S₂`, preserving the relation. -/
structure Simulation (R : S₁.State → S₂.State → Prop) : Prop where
  sim : ∀ {x x' y}, R x y → S₁.Reach x x' → ∃ y', S₂.Reach y y' ∧ R x' y'

/-- Existence-based realizability: `x` is realized by some `y ∈ Q` related to it. -/
def Realizable (R : S₁.State → S₂.State → Prop) (Q : Set S₂.State) : Set S₁.State :=
  {x | ∃ y, R x y ∧ y ∈ Q}

/-- If `Q` is invariant in the target system, then the realizable states form an invariant
predicate in the source system. -/
theorem realizable_invariant_of_simulation
    {R : S₁.State → S₂.State → Prop} (hSim : Simulation (S₁ := S₁) (S₂ := S₂) R)
    {Q : Set S₂.State} (hInv : S₂.IsInvariant Q) :
    S₁.IsInvariant (Realizable (S₁ := S₁) (S₂ := S₂) R Q) := by
  intro x x' hx ⟨y, hRxy, hyQ⟩
  rcases hSim.sim hRxy hx with ⟨y', hyReach, hRx'y'⟩
  refine ⟨y', hRx'y', ?_⟩
  exact hInv hyReach hyQ

end Realizability

/-! ## Concrete instances (hook layer) -/

namespace Instances

open HeytingLean.Process

/-- Process calculus reachability system (multi-step reduction). -/
def processSystem : ReachSystem where
  State := Proc
  Reach := ReducesStar
  refl := ReducesStar.refl
  trans := by
    intro x y z hxy hyz
    exact ReducesStar.trans hxy hyz

end Instances

end Semantics
end ClosingTheLoop
end HeytingLean
