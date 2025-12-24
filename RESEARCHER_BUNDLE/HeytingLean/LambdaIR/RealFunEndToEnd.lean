import HeytingLean.LambdaIR.RealFunMiniCProof
import HeytingLean.LambdaIR.Nat2FunFragment
import HeytingLean.LambdaIR.Nat2CompileFrag
import HeytingLean.LambdaIR.Nat2CompileFragCorrectness
import HeytingLean.LambdaIR.Semantics
import HeytingLean.EndToEnd.NatFunSpec
import HeytingLean.Theorems.Core

namespace HeytingLean
namespace LambdaIR
namespace RealFunEndToEnd

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Nat2FunFragment
open HeytingLean.LambdaIR.Nat2CompileFrag
open HeytingLean.EndToEnd
open HeytingLean.EndToEnd.NatFunSpec
open HeytingLean.LambdaIR.RealFunMiniCProof

/-- `termXorSumIR` lies in the nat→nat→nat fragment. -/
theorem termXorSum_isNat2Fun : IsNat2Fun termXorSumIR := by
  refine ⟨
    Term.if_
      (Term.app
        (Term.app Term.primEqNat (Term.var (Var.vs Var.vz)))
        (Term.var Var.vz))
      (Term.constNat 0)
      (Term.app
        (Term.app Term.primAddNat (Term.var (Var.vs Var.vz)))
        (Term.var Var.vz)),
    rfl,
    ?_⟩
  refine IsNatBody₂.if_
    (IsBoolExpr₂.eqNat IsNatExpr₂.varFirst IsNatExpr₂.varSecond)
    ?_ ?_
  · exact IsNatBody₂.expr (IsNatExpr₂.constNat 0)
  · exact IsNatBody₂.expr
      (IsNatExpr₂.add IsNatExpr₂.varFirst IsNatExpr₂.varSecond)

/-- LambdaIR semantics for `termXorSumIR` agree with `leanXorSum`. -/
theorem termXorSumIR_semantics :
  ∀ x y,
    LambdaIR.evalClosed
      (Term.app
        (Term.app termXorSumIR (Term.constNat x))
        (Term.constNat y)) = leanXorSum x y := by
  intro x y
  by_cases h : x = y
  · subst h
    simp [termXorSumIR, leanXorSum, LambdaIR.evalClosed,
          LambdaIR.eval, extendEnv]
  · simp [termXorSumIR, leanXorSum, LambdaIR.evalClosed,
          LambdaIR.eval, extendEnv, h]

/-- End-to-end correctness for the zero-or-sum example. -/
@[apmt_thm]
theorem xorSum_end_to_end :
  EndToEndNat2Spec leanXorSum "xorSum" "x" "y" termXorSumIR :=
by
  refine NatFunSpec.EndToEndNat2Spec_of_IsNat2Fun
    (ht := termXorSum_isNat2Fun) (hf := ?_)
  intro x y
  exact termXorSumIR_semantics x y

end RealFunEndToEnd
end LambdaIR
end HeytingLean
