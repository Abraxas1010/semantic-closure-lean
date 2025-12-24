import HeytingLean.Process.Syntax

/-!
Lightweight session-typing skeleton (compile-only):
- A tiny session type grammar and duality
- Not integrated into process typing yet; provided for future extension
-/

namespace HeytingLean
namespace Process

inductive STy : Type
| tEnd
| send (τ : ValTy) (next : STy)
| recv (τ : ValTy) (next : STy)
deriving DecidableEq

open STy

def dual : STy → STy
| STy.tEnd => STy.tEnd
| STy.send τ s => STy.recv τ (dual s)
| STy.recv τ s => STy.send τ (dual s)

@[simp] theorem dual_dual (s : STy) : dual (dual s) = s := by
  induction s with
  | tEnd => simp [dual]
  | send τ s ih => simp [dual, ih]
  | recv τ s ih => simp [dual, ih]

end Process
end HeytingLean
