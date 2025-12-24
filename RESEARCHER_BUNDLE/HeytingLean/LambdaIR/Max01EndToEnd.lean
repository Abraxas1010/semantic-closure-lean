import HeytingLean.LambdaIR.Max01MiniCProof
import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.LambdaIR.NatCompileFrag
import HeytingLean.LambdaIR.NatCompileFragCorrectness
import HeytingLean.LambdaIR.Semantics
import HeytingLean.EndToEnd.NatFunSpec
import HeytingLean.Theorems.Core

namespace HeytingLean
namespace LambdaIR
namespace Max01EndToEnd

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment
open HeytingLean.LambdaIR.NatCompileFrag
open HeytingLean.EndToEnd.NatFunSpec
open HeytingLean.LambdaIR.Max01MiniCProof

/-- `termMax01IR` lies in the nat→nat fragment. -/
theorem termMax01_isNatFun : IsNatFun termMax01IR := by
  refine ⟨
    Term.if_
      (Term.app
        (Term.app Term.primEqNat (Term.var Var.vz))
        (Term.constNat 0))
      (Term.constNat 1)
      (Term.var Var.vz),
    rfl,
    ?_⟩
  refine IsNatBody.if_
    (IsBoolExpr.eqNat IsNatExpr.var (IsNatExpr.constNat 0))
    ?_ ?_
  · exact IsNatBody.expr (IsNatExpr.constNat 1)
  · exact IsNatBody.expr IsNatExpr.var

/-- LambdaIR semantics for `termMax01IR` agree with `leanMax01`. -/
theorem termMax01IR_semantics :
  ∀ n,
    LambdaIR.evalClosed
      (Term.app termMax01IR (Term.constNat n)) = leanMax01 n :=
by
  intro n
  by_cases h : n = 0
  · subst h
    simp [termMax01IR, leanMax01, LambdaIR.evalClosed, LambdaIR.eval, extendEnv]
  · simp [termMax01IR, leanMax01, LambdaIR.evalClosed, LambdaIR.eval, extendEnv, h]

/-- End-to-end nat→nat correctness for max01. -/
@[apmt_thm]
theorem max01_end_to_end :
  EndToEndNatSpec leanMax01 "max01" "x" termMax01IR :=
by
  apply EndToEndNatSpec_of_IsNatFun
    (leanF := leanMax01)
    (funName := "max01")
    (paramName := "x")
    (t := termMax01IR)
  · exact termMax01_isNatFun
  · intro n
    exact termMax01IR_semantics n

end Max01EndToEnd
end LambdaIR
end HeytingLean
