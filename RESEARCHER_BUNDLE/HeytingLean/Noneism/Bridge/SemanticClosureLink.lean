import HeytingLean.Noneism.Bridge.EvaluationMap
import HeytingLean.ClosingTheLoop.MR.Basic

namespace HeytingLean
namespace Noneism
namespace Bridge

universe u v

/-- Forget admissibility proofs, viewing an admissible map as a plain metabolism. -/
abbrev toTypeMetabolism (S : HeytingLean.ClosingTheLoop.MR.MRSystem.{u, v})
    (g : HeytingLean.ClosingTheLoop.MR.AdmissibleMap S) : Metabolism (A := S.A) (B := S.B) :=
  g.1

/-- Forget admissibility proofs, viewing an admissible selector as a plain selector. -/
abbrev toTypeSelector (S : HeytingLean.ClosingTheLoop.MR.MRSystem.{u, v})
    (Φ : HeytingLean.ClosingTheLoop.MR.Selector S) : Selector (A := S.A) (B := S.B) :=
  fun b => (Φ b).1

theorem evalAt_toTypeSelector (S : HeytingLean.ClosingTheLoop.MR.MRSystem.{u, v}) (b : S.B)
    (Φ : HeytingLean.ClosingTheLoop.MR.Selector S) :
    evalAt (A := S.A) (B := S.B) b (toTypeSelector S Φ) =
      toTypeMetabolism S (HeytingLean.ClosingTheLoop.MR.evalAt S b Φ) := rfl

end Bridge
end Noneism
end HeytingLean
