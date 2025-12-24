import HeytingLean.LambdaIR.Add2MiniCProof
import HeytingLean.LambdaIR.Nat2FunFragment
import HeytingLean.LambdaIR.Nat2CompileFrag
import HeytingLean.LambdaIR.Nat2CompileFragCorrectness
import HeytingLean.LambdaIR.Semantics
import HeytingLean.EndToEnd.NatFunSpec
import HeytingLean.Theorems.Core

namespace HeytingLean
namespace LambdaIR
namespace Add2EndToEnd

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Nat2FunFragment
open HeytingLean.LambdaIR.Nat2CompileFrag
open HeytingLean.EndToEnd
open HeytingLean.EndToEnd.NatFunSpec
open HeytingLean.LambdaIR.Add2MiniCProof

/-- `termAdd2IR` lies in the nat→nat→nat fragment. -/
theorem termAdd2_isNat2Fun : IsNat2Fun termAdd2IR := by
  refine ⟨
    Term.app
      (Term.app Term.primAddNat (Term.var (Var.vs Var.vz)))
      (Term.var Var.vz),
    rfl,
    ?_⟩
  exact IsNatBody₂.expr
      (IsNatExpr₂.add IsNatExpr₂.varFirst IsNatExpr₂.varSecond)

/-- LambdaIR semantics for `termAdd2IR` agree with `leanAdd2`. -/
theorem termAdd2IR_semantics :
  ∀ x y,
    LambdaIR.evalClosed
      (Term.app
        (Term.app termAdd2IR (Term.constNat x))
        (Term.constNat y)) = leanAdd2 x y := by
  intro x y
  simp [termAdd2IR, leanAdd2, LambdaIR.evalClosed,
        LambdaIR.eval, extendEnv]

/-- End-to-end nat→nat→nat correctness for addition. -/
@[apmt_thm]
theorem add2_end_to_end :
  EndToEndNat2Spec leanAdd2 "add2" "x" "y" termAdd2IR :=
by
  refine NatFunSpec.EndToEndNat2Spec_of_IsNat2Fun
    (ht := termAdd2_isNat2Fun) (hf := ?_)
  intro x y
  exact termAdd2IR_semantics x y

end Add2EndToEnd
end LambdaIR
end HeytingLean
