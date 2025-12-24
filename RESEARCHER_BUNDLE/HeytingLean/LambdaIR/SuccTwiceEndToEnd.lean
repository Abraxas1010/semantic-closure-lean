import HeytingLean.LambdaIR.SuccTwiceMiniCProof
import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.LambdaIR.NatCompileFrag
import HeytingLean.LambdaIR.NatCompileFragCorrectness
import HeytingLean.LambdaIR.Semantics
import HeytingLean.EndToEnd.NatFunSpec
import HeytingLean.Theorems.Core

namespace HeytingLean
namespace LambdaIR
namespace SuccTwiceEndToEnd

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment
open HeytingLean.LambdaIR.NatCompileFrag
open HeytingLean.EndToEnd.NatFunSpec
open HeytingLean.LambdaIR.SuccTwiceMiniCProof

/-- `termSuccTwiceIR` lies in the nat→nat fragment. -/
theorem termSuccTwice_isNatFun : IsNatFun termSuccTwiceIR := by
  refine ⟨
    Term.app
      (Term.app Term.primAddNat (Term.var Var.vz))
      (Term.constNat 2),
    rfl,
    ?_⟩
  exact IsNatBody.expr (IsNatExpr.add IsNatExpr.var (IsNatExpr.constNat 2))

/-- LambdaIR semantics for `termSuccTwiceIR` agree with `leanSuccTwice`. -/
theorem termSuccTwiceIR_semantics :
  ∀ n,
    LambdaIR.evalClosed
      (Term.app termSuccTwiceIR (Term.constNat n)) = leanSuccTwice n :=
by
  intro n
  simp [termSuccTwiceIR, leanSuccTwice, LambdaIR.evalClosed, LambdaIR.eval, extendEnv]

/-- End-to-end nat→nat correctness for succTwice. -/
@[apmt_thm]
theorem succTwice_end_to_end :
  EndToEndNatSpec leanSuccTwice "succ_twice" "x" termSuccTwiceIR :=
by
  apply EndToEndNatSpec_of_IsNatFun
    (leanF := leanSuccTwice)
    (funName := "succ_twice")
    (paramName := "x")
    (t := termSuccTwiceIR)
  · exact termSuccTwice_isNatFun
  · intro n
    exact termSuccTwiceIR_semantics n

end SuccTwiceEndToEnd
end LambdaIR
end HeytingLean
