import HeytingLean.LambdaIR.Min2MiniCProof
import HeytingLean.LambdaIR.Nat2FunFragment
import HeytingLean.LambdaIR.Nat2CompileFrag
import HeytingLean.LambdaIR.Nat2CompileFragCorrectness
import HeytingLean.LambdaIR.Semantics
import HeytingLean.EndToEnd.NatFunSpec
import HeytingLean.Theorems.Core

namespace HeytingLean
namespace LambdaIR
namespace Min2EndToEnd

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Nat2FunFragment
open HeytingLean.LambdaIR.Nat2CompileFrag
open HeytingLean.EndToEnd
open HeytingLean.EndToEnd.NatFunSpec
open HeytingLean.LambdaIR.Min2MiniCProof

/-- `termMin2IR` lies in the nat→nat→nat fragment. -/
theorem termMin2_isNat2Fun : IsNat2Fun termMin2IR := by
  refine ⟨
    Term.if_
      (Term.app
        (Term.app Term.primEqNat (Term.var (Var.vs Var.vz)))
        (Term.var Var.vz))
      (Term.var (Var.vs Var.vz))
      (Term.var Var.vz),
    rfl,
    ?_⟩
  refine IsNatBody₂.if_
    (IsBoolExpr₂.eqNat IsNatExpr₂.varFirst IsNatExpr₂.varSecond)
    ?_ ?_
  · exact IsNatBody₂.expr IsNatExpr₂.varFirst
  · exact IsNatBody₂.expr IsNatExpr₂.varSecond

/-- LambdaIR semantics for `termMin2IR` agree with `leanMin2`. -/
theorem termMin2IR_semantics :
  ∀ x y,
    LambdaIR.evalClosed
      (Term.app
        (Term.app termMin2IR (Term.constNat x))
        (Term.constNat y)) = leanMin2 x y := by
  intro x y
  by_cases h : x = y
  · subst h
    simp [termMin2IR, leanMin2, LambdaIR.evalClosed,
          LambdaIR.eval, extendEnv]
  · simp [termMin2IR, leanMin2, LambdaIR.evalClosed,
          LambdaIR.eval, extendEnv, h]

/-- End-to-end nat→nat→nat correctness for the min-like example. -/
@[apmt_thm]
theorem min2_end_to_end :
  EndToEndNat2Spec leanMin2 "min2" "x" "y" termMin2IR :=
by
  refine NatFunSpec.EndToEndNat2Spec_of_IsNat2Fun
    (ht := termMin2_isNat2Fun) (hf := ?_)
  intro x y
  exact termMin2IR_semantics x y

end Min2EndToEnd
end LambdaIR
end HeytingLean
