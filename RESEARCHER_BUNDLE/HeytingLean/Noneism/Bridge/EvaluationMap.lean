import Mathlib.Logic.Function.Basic

namespace HeytingLean
namespace Noneism
namespace Bridge

universe u v

variable (A : Type u) (B : Type v)

/-- Metabolisms: maps `A → B`. -/
abbrev Metabolism :=
  A → B

/-- Selectors: maps `B → (A → B)`. -/
abbrev Selector :=
  B → Metabolism (A := A) (B := B)

/-- Evaluation at a configuration `b : B`: `Φ ↦ Φ b`. -/
def evalAt (b : B) : Selector (A := A) (B := B) → Metabolism (A := A) (B := B) :=
  fun Φ => Φ b

/-- Injectivity of evaluation at `b`. -/
def InjectiveEvalAt (b : B) : Prop :=
  Function.Injective (evalAt (A := A) (B := B) b)

/-- Surjectivity of evaluation at `b`. -/
def SurjectiveEvalAt (b : B) : Prop :=
  Function.Surjective (evalAt (A := A) (B := B) b)

/-- Bijectivity of evaluation at `b`. -/
def BijectiveEvalAt (b : B) : Prop :=
  Function.Bijective (evalAt (A := A) (B := B) b)

end Bridge
end Noneism
end HeytingLean

