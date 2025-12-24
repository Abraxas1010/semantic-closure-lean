import HeytingLean.LambdaIR.DoubleMiniCProof
import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.LambdaIR.NatCompileFrag
import HeytingLean.LambdaIR.NatCompileFragCorrectness
import HeytingLean.LambdaIR.Semantics
import HeytingLean.EndToEnd.NatFunSpec
import HeytingLean.Theorems.Core

namespace HeytingLean
namespace LambdaIR
namespace DoubleEndToEnd

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment
open HeytingLean.LambdaIR.NatCompileFrag
open HeytingLean.EndToEnd.NatFunSpec
open HeytingLean.LambdaIR.DoubleMiniCProof

/-- `termDoubleIR` lies in the nat→nat fragment. -/
theorem termDouble_isNatFun : IsNatFun termDoubleIR := by
  refine ⟨
    Term.app
      (Term.app Term.primAddNat (Term.var Var.vz))
      (Term.var Var.vz),
    rfl,
    ?_⟩
  exact IsNatBody.expr (IsNatExpr.add IsNatExpr.var IsNatExpr.var)

/-- LambdaIR semantics for `termDoubleIR` coincide with the Lean `leanDouble`. -/
theorem termDoubleIR_semantics :
  ∀ n,
    LambdaIR.evalClosed
      (Term.app termDoubleIR (Term.constNat n)) = leanDouble n :=
by
  intro n
  simp [termDoubleIR, leanDouble, LambdaIR.evalClosed, LambdaIR.eval, extendEnv]

/-- End-to-end nat→nat correctness for doubling. -/
@[apmt_thm]
theorem double_end_to_end :
  EndToEndNatSpec leanDouble "double" "x" termDoubleIR :=
by
  apply EndToEndNatSpec_of_IsNatFun
    (leanF := leanDouble)
    (funName := "double")
    (paramName := "x")
    (t := termDoubleIR)
  · exact termDouble_isNatFun
  · intro n
    exact termDoubleIR_semantics n

end DoubleEndToEnd
end LambdaIR
end HeytingLean
