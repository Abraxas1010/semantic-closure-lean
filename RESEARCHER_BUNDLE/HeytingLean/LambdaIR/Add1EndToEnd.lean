import HeytingLean.LambdaIR.Add1MiniCProof
import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.LambdaIR.NatCompileFrag
import HeytingLean.LambdaIR.NatCompileFragCorrectness
import HeytingLean.LambdaIR.Semantics
import HeytingLean.EndToEnd.NatFunSpec
import HeytingLean.Theorems.Core

namespace HeytingLean
namespace LambdaIR
namespace Add1EndToEnd

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment
open HeytingLean.LambdaIR.NatCompileFrag
open HeytingLean.EndToEnd
open HeytingLean.EndToEnd.NatFunSpec
open HeytingLean.LambdaIR.Add1MiniCProof  -- brings leanAdd1, termAdd1IR into scope

/-- `termAdd1IR` is a nat→nat function in the LambdaIR nat fragment. -/
theorem termAdd1_isNatFun : IsNatFun termAdd1IR := by
  refine ⟨
    Term.app
      (Term.app Term.primAddNat (Term.var Var.vz))
      (Term.constNat 1),
    rfl,
    ?_⟩
  exact IsNatBody.expr (IsNatExpr.add IsNatExpr.var (IsNatExpr.constNat 1))

/-- LambdaIR semantics for `termAdd1IR` agree with the Lean `leanAdd1`. -/
theorem termAdd1IR_semantics :
  ∀ n,
    LambdaIR.evalClosed
      (Term.app termAdd1IR (Term.constNat n)) = leanAdd1 n :=
by
  intro n
  simp [termAdd1IR, leanAdd1, LambdaIR.evalClosed, LambdaIR.eval, extendEnv]

/-- End-to-end correctness of add1 via the nat→nat fragment compiler. -/
@[apmt_thm]
theorem add1_end_to_end :
  EndToEndNatSpec leanAdd1 "add1" "x" termAdd1IR :=
by
  apply EndToEndNatSpec_of_IsNatFun
    (leanF := leanAdd1)
    (funName := "add1")
    (paramName := "x")
    (t := termAdd1IR)
  · exact termAdd1_isNatFun
  · intro n
    exact termAdd1IR_semantics n

end Add1EndToEnd
end LambdaIR
end HeytingLean
