import HeytingLean.LambdaIR.ClampMiniCProof
import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.LambdaIR.NatCompileFrag
import HeytingLean.LambdaIR.NatCompileFragCorrectness
import HeytingLean.LambdaIR.Semantics
import HeytingLean.EndToEnd.NatFunSpec
import HeytingLean.Theorems.Core

namespace HeytingLean
namespace LambdaIR
namespace ClampEndToEnd

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment
open HeytingLean.LambdaIR.NatCompileFrag
open HeytingLean.EndToEnd.NatFunSpec
open HeytingLean.LambdaIR.ClampMiniCProof

/-- `termClamp01IR` lies in the nat→nat fragment. -/
theorem termClamp01_isNatFun : IsNatFun termClamp01IR := by
  refine ⟨
    Term.if_
      (Term.app
        (Term.app Term.primEqNat (Term.var Var.vz))
        (Term.constNat 0))
      (Term.constNat 0)
      (Term.constNat 1),
    rfl,
    ?_⟩
  refine IsNatBody.if_
    (IsBoolExpr.eqNat IsNatExpr.var (IsNatExpr.constNat 0))
    ?_ ?_
  · exact IsNatBody.expr (IsNatExpr.constNat 0)
  · exact IsNatBody.expr (IsNatExpr.constNat 1)

/-- LambdaIR semantics for `termClamp01IR` agree with `leanClamp01`. -/
theorem termClamp01IR_semantics :
  ∀ n,
    LambdaIR.evalClosed
      (Term.app termClamp01IR (Term.constNat n)) = leanClamp01 n :=
by
  intro n
  by_cases h : n = 0
  · subst h
    simp [termClamp01IR, leanClamp01, LambdaIR.evalClosed, LambdaIR.eval, extendEnv]
  ·
    simp [termClamp01IR, leanClamp01, LambdaIR.evalClosed, LambdaIR.eval, extendEnv, h]

/-- End-to-end nat→nat correctness for clamp01 via the fragment compiler. -/
@[apmt_thm]
theorem clamp01_end_to_end :
  EndToEndNatSpec leanClamp01 "clamp01" "x" termClamp01IR :=
by
  apply EndToEndNatSpec_of_IsNatFun
    (leanF := leanClamp01)
    (funName := "clamp01")
    (paramName := "x")
    (t := termClamp01IR)
  · exact termClamp01_isNatFun
  · intro n
    exact termClamp01IR_semantics n

end ClampEndToEnd
end LambdaIR
end HeytingLean
