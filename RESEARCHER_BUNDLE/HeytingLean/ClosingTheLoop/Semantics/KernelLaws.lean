import Mathlib.Data.Set.Lattice

/-!
# Closing the Loop: generic kernel laws (Tier 2)

Both the preorder-time `futureKernel` (contractive “interior” operator on predicates)
and the process-calculus `Kproc` operator share the same algebraic shape:

* monotone
* meet-preserving
* idempotent
* contractive (`K x ≤ x`)

This file packages those laws so `ClosingTheLoop` can connect:
- invariant-style semantics (kernels / safety properties), and
- fixed-point “semantic closure” talk (stable / closed parts),

without committing to a specific model of computation.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Semantics

universe u

section Kernel

variable {α : Type u} [SemilatticeInf α]

/-- A contractive, meet-preserving, idempotent endomorphism (an “interior/kernel” operator). -/
structure Kernel where
  toFun : α → α
  monotone' : Monotone toFun
  map_inf' : ∀ x y : α, toFun (x ⊓ y) = toFun x ⊓ toFun y
  idempotent' : ∀ x : α, toFun (toFun x) = toFun x
  apply_le' : ∀ x : α, toFun x ≤ x

namespace Kernel

instance : CoeFun (Kernel (α := α)) (fun _ => α → α) where
  coe k := k.toFun

@[simp] lemma toFun_eq_coe (k : Kernel (α := α)) : k.toFun = k := rfl

lemma monotone (k : Kernel (α := α)) : Monotone k := k.monotone'

@[simp] lemma map_inf (k : Kernel (α := α)) (x y : α) :
    k (x ⊓ y) = k x ⊓ k y := k.map_inf' x y

@[simp] lemma idempotent (k : Kernel (α := α)) (x : α) : k (k x) = k x := k.idempotent' x

lemma apply_le (k : Kernel (α := α)) (x : α) : k x ≤ x := k.apply_le' x

/-- Fixed-point predicate for a kernel operator. -/
def IsFixed (k : Kernel (α := α)) (x : α) : Prop := k x = x

lemma isFixed_iff (k : Kernel (α := α)) (x : α) : k.IsFixed x ↔ k x = x := Iff.rfl

/-- Every `k x` is a fixed point (idempotence). -/
lemma isFixed_apply (k : Kernel (α := α)) (x : α) : k.IsFixed (k x) := by
  simp [IsFixed]

end Kernel

end Kernel

end Semantics
end ClosingTheLoop
end HeytingLean

