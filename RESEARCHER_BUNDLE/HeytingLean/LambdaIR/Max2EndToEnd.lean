import HeytingLean.LambdaIR.Max2MiniCProof
import HeytingLean.LambdaIR.Nat2FunFragment
import HeytingLean.LambdaIR.Nat2CompileFrag
import HeytingLean.LambdaIR.Nat2CompileFragCorrectness
import HeytingLean.LambdaIR.Semantics
import HeytingLean.EndToEnd.NatFunSpec
import HeytingLean.Theorems.Core

namespace HeytingLean
namespace LambdaIR
namespace Max2EndToEnd

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Nat2FunFragment
open HeytingLean.LambdaIR.Nat2CompileFrag
open HeytingLean.EndToEnd
open HeytingLean.EndToEnd.NatFunSpec
open HeytingLean.LambdaIR.Max2MiniCProof

/-- `termMax2IR` lies in the nat→nat→nat fragment. -/
theorem termMax2_isNat2Fun : IsNat2Fun termMax2IR := by
  refine ⟨
    Term.if_
      (Term.app
        (Term.app Term.primEqNat (Term.var (Var.vs Var.vz)))
        (Term.var Var.vz))
      (Term.var Var.vz)
      (Term.var (Var.vs Var.vz)),
    rfl,
    ?_⟩
  refine IsNatBody₂.if_
    (IsBoolExpr₂.eqNat IsNatExpr₂.varFirst IsNatExpr₂.varSecond)
    ?_ ?_
  · exact IsNatBody₂.expr IsNatExpr₂.varSecond
  · exact IsNatBody₂.expr IsNatExpr₂.varFirst

/-- LambdaIR semantics for `termMax2IR` agree with `leanMax2`. -/
theorem termMax2IR_semantics :
  ∀ x y,
    LambdaIR.evalClosed
      (Term.app
        (Term.app termMax2IR (Term.constNat x))
        (Term.constNat y)) = leanMax2 x y := by
  intro x y
  by_cases h : x = y
  · subst h
    simp [termMax2IR, leanMax2, LambdaIR.evalClosed,
          LambdaIR.eval, extendEnv]
  · simp [termMax2IR, leanMax2, LambdaIR.evalClosed,
          LambdaIR.eval, extendEnv, h]

/-- End-to-end nat→nat→nat correctness for the max-like example. -/
@[apmt_thm]
theorem max2_end_to_end :
  EndToEndNat2Spec leanMax2 "max2" "x" "y" termMax2IR :=
by
  refine NatFunSpec.EndToEndNat2Spec_of_IsNat2Fun
    (ht := termMax2_isNat2Fun) (hf := ?_)
  intro x y
  exact termMax2IR_semantics x y

end Max2EndToEnd
end LambdaIR
end HeytingLean
