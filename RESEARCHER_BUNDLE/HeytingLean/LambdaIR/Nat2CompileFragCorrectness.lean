import HeytingLean.Core.Types
import HeytingLean.Core.SemanticsBase
import HeytingLean.LambdaIR.Nat2FunFragment
import HeytingLean.LambdaIR.Nat2CompileFrag
import HeytingLean.LambdaIR.Semantics
import HeytingLean.LambdaIR.NatIntEqLemmas
import HeytingLean.MiniC.Semantics

namespace HeytingLean
namespace LambdaIR
namespace Nat2CompileFragCorrectness

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Nat2FunFragment
open HeytingLean.LambdaIR.Nat2CompileFrag
open HeytingLean.MiniC

@[simp] theorem asNat_natToVal (n : Nat) :
    Val.asNat? (natToVal n) = some n := by
  simp [Val.asNat?, natToVal]

/-- Fixed parameter names used for the 2-arg fragment. -/
def param1 : String := "x"
def param2 : String := "y"

@[simp] def arg2Store (x y : Nat) : Store :=
  fun name =>
    if name = param1 then
      some (natToVal x)
    else if name = param2 then
      some (natToVal y)
    else
      none

@[simp] def arg2Env (x y : Nat) :
    LambdaIR.Env [Ty.nat, Ty.nat] :=
  Core.extendEnv
    (Γ := [Ty.nat]) (α := Ty.nat)
    (Core.extendEnv (Γ := []) (α := Ty.nat)
      baseEnv (x := (x : InterpTy Ty.nat)))
    (x := (y : InterpTy Ty.nat))

@[simp] theorem compileNatBody₂Frag_of_expr
    {t : Term [Ty.nat, Ty.nat] Ty.nat}
    (ht : IsNatExpr₂ t) :
    compileNatBody₂Frag param1 param2 t
      = Stmt.return (compileNatExpr₂Frag param1 param2 t) := by
  cases ht with
  | constNat =>
      simp [compileNatBody₂Frag, compileNatBodyWith,
            compileNatExpr₂Frag, compileNatExprWith]
  | varFirst =>
      simp [compileNatBody₂Frag, compileNatBodyWith,
            compileNatExpr₂Frag, compileNatExprWith]
  | varSecond =>
      simp [compileNatBody₂Frag, compileNatBodyWith,
            compileNatExpr₂Frag, compileNatExprWith]
  | add _ _ =>
      simp [compileNatBody₂Frag, compileNatBodyWith,
            compileNatExpr₂Frag, compileNatExprWith]

theorem compileNatExpr₂Frag_correct
    {t : Term [Ty.nat, Ty.nat] Ty.nat}
    (ht : IsNatExpr₂ t) (x y : Nat) :
    evalExpr (compileNatExpr₂Frag param1 param2 t)
        (arg2Store x y)
      = some (natToVal (LambdaIR.eval t (arg2Env x y))) := by
  let env : LambdaIR.Env [Ty.nat, Ty.nat] := arg2Env x y
  change
      evalExpr (compileNatExpr₂Frag param1 param2 t)
          (arg2Store x y)
        = some (natToVal (LambdaIR.eval t env))
  induction ht with
  | constNat n =>
      simp [compileNatExpr₂Frag, compileNatExprWith,
            LambdaIR.eval, natToVal, evalExpr]
  | varFirst =>
      have : evalExpr (Expr.var param1) (arg2Store x y)
          = some (natToVal x) := by
        simp [arg2Store, evalExpr, lookup, natToVal, param1]
      simpa [compileNatExpr₂Frag, compileNatExprWith,
            LambdaIR.eval, env] using this
  | varSecond =>
      have : evalExpr (Expr.var param2) (arg2Store x y)
          = some (natToVal y) := by
        simp [arg2Store, evalExpr, lookup, natToVal, param1, param2]
      simpa [compileNatExpr₂Frag, compileNatExprWith,
            LambdaIR.eval, env] using this
  | add hf ht ihf iht =>
      have hf' := ihf
      have ht' := iht
      simp [compileNatExpr₂Frag] at hf' ht'
      simp [param1, param2] at hf' ht'
      simp [compileNatExpr₂Frag, compileNatExprWith,
            LambdaIR.eval, evalExpr, natToVal, env,
            arg2Env, hf', ht', param1, param2]

theorem compileBoolExpr₂Frag_correct
    {c : Term [Ty.nat, Ty.nat] Ty.bool}
    (hc : IsBoolExpr₂ c) (x y : Nat) :
    evalExpr (compileBoolExpr₂Frag param1 param2 c)
        (arg2Store x y)
      = some (Val.bool (LambdaIR.eval c (arg2Env x y))) := by
  revert x y
  cases hc with
  | constBool b =>
      intro x y
      simp [compileBoolExpr₂Frag, compileBoolExprWith,
            LambdaIR.eval, evalExpr]
  | eqNat hf ht =>
      intro x y
      let env : LambdaIR.Env [Ty.nat, Ty.nat] := arg2Env x y
      have hf' := compileNatExpr₂Frag_correct hf x y
      have ht' := compileNatExpr₂Frag_correct ht x y
      simp [compileNatExpr₂Frag] at hf' ht'
      simp [compileBoolExpr₂Frag, compileBoolExprWith,
            LambdaIR.eval, evalExpr, hf', ht']

theorem compileNatBody₂Frag_correct
    {body : Term [Ty.nat, Ty.nat] Ty.nat}
    (hb : IsNatBody₂ body)
    (x y : Nat) :
    execFrag (compileNatBody₂Frag param1 param2 body)
        (arg2Store x y)
      = some (ExecResult.returned
          (natToVal (LambdaIR.eval body (arg2Env x y)))) := by
  revert x y
  induction hb with
  | @expr t hexpr =>
      intro x y
      let env : LambdaIR.Env [Ty.nat, Ty.nat] := arg2Env x y
      have hEval :=
        compileNatExpr₂Frag_correct hexpr x y
      have hEval' :
          evalExpr (compileNatExpr₂Frag param1 param2 t) (arg2Store x y)
            = some (natToVal (LambdaIR.eval t env)) := by
        simpa [env] using hEval
      have hExec :
          execFrag (compileNatBody₂Frag param1 param2 t)
            (arg2Store x y)
            = some (ExecResult.returned (natToVal (LambdaIR.eval t env))) := by
        simp [compileNatBody₂Frag_of_expr hexpr, hEval', env]
      simpa [LambdaIR.eval, natToVal, env] using hExec
  | @if_ c t e hc ht he ih_t ih_e =>
      intro x y
      let env : LambdaIR.Env [Ty.nat, Ty.nat] := arg2Env x y
      have hCond :=
        compileBoolExpr₂Frag_correct hc x y
      have hCond' :
          evalExpr (compileBoolExpr₂Frag param1 param2 c)
            (arg2Store x y)
            = some (Val.bool (LambdaIR.eval c env)) := by
        simpa [env] using hCond
      cases h : LambdaIR.eval c env with
      | true =>
          have hCondTrue :
              evalExpr (compileBoolExpr₂Frag param1 param2 c)
                (arg2Store x y) = some (Val.bool true) := by
            simpa [h] using hCond'
          have hExec :
              execFrag (compileNatBody₂Frag param1 param2 (Term.if_ c t e))
                (arg2Store x y)
                = execFrag (compileNatBody₂Frag param1 param2 t)
                    (arg2Store x y) := by
            simpa [compileNatBody₂Frag, compileNatBodyWith,
                  compileBoolExpr₂Frag, compileBoolExprWith] using
              (execFrag_if_true
                (cond := compileBoolExpr₂Frag param1 param2 c)
                (then_ := compileNatBody₂Frag param1 param2 t)
                (else_ := compileNatBody₂Frag param1 param2 e)
                (σ := arg2Store x y)
                hCondTrue)
          have hThen :=
            ih_t x y
          have hThen' :
              execFrag (compileNatBody₂Frag param1 param2 t)
                  (arg2Store x y)
                = some (ExecResult.returned
                    (natToVal (LambdaIR.eval t env))) := by
            simpa [env] using hThen
          have hEvalIf :
              natToVal (LambdaIR.eval (Term.if_ c t e) env)
                = natToVal (LambdaIR.eval t env) := by
            simp [LambdaIR.eval, h]
          exact hEvalIf ▸ (hExec.trans hThen')
      | false =>
          have hCondFalse :
              evalExpr (compileBoolExpr₂Frag param1 param2 c)
                (arg2Store x y) = some (Val.bool false) := by
            simpa [h] using hCond'
          have hExec :
              execFrag (compileNatBody₂Frag param1 param2 (Term.if_ c t e))
                (arg2Store x y)
                = execFrag (compileNatBody₂Frag param1 param2 e)
                    (arg2Store x y) := by
            simpa [compileNatBody₂Frag, compileNatBodyWith,
                  compileBoolExpr₂Frag, compileBoolExprWith] using
              (execFrag_if_false
                (cond := compileBoolExpr₂Frag param1 param2 c)
                (then_ := compileNatBody₂Frag param1 param2 t)
                (else_ := compileNatBody₂Frag param1 param2 e)
                (σ := arg2Store x y)
                hCondFalse)
          have hElse :=
            ih_e x y
          have hElse' :
              execFrag (compileNatBody₂Frag param1 param2 e)
                  (arg2Store x y)
                = some (ExecResult.returned
                    (natToVal (LambdaIR.eval e env))) := by
            simpa [env] using hElse
          have hEvalIf :
              natToVal (LambdaIR.eval (Term.if_ c t e) env)
                = natToVal (LambdaIR.eval e env) := by
            simp [LambdaIR.eval, h]
          exact hEvalIf ▸ (hExec.trans hElse')

/-- General semantics preservation for the nat→nat→nat fragment compiler (fixed parameter names, arbitrary function name). -/
theorem compileNat2FunFrag_correct
    {funName : String}
    {t : Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))}
    (ht : IsNat2Fun t)
    (leanF : Nat → Nat → Nat)
    (hf :
      ∀ x y,
        LambdaIR.evalClosed
          (Term.app
            (Term.app t (Term.constNat x))
            (Term.constNat y)) = leanF x y) :
    Nat2FunSpec funName param1 param2 leanF t := by
  intro x y
  rcases ht with ⟨body, rfl, hBody⟩
  have hLeanEval :
      LambdaIR.eval body (arg2Env x y) = leanF x y := by
    have := hf x y
    simpa [LambdaIR.evalClosed, LambdaIR.eval, arg2Env] using this
  have hExecBody := compileNatBody₂Frag_correct hBody x y
  have hLeanEval_exp :
      LambdaIR.eval body
          (Core.extendEnv (Γ := [Ty.nat]) (α := Ty.nat)
            (Core.extendEnv (Γ := []) (α := Ty.nat)
              baseEnv (x := (x : InterpTy Ty.nat)))
            (x := (y : InterpTy Ty.nat))) = leanF x y := by
    simpa [arg2Env] using hLeanEval
  have hExecVal :
      execFrag (compileNatBody₂Frag param1 param2 body)
        (arg2Store x y) =
        some (ExecResult.returned (natToVal (leanF x y))) := by
    have h := hExecBody
    simpa [hLeanEval_exp, param1, param2] using h
  have hExecVal' :
      execFrag (compileNatBody₂Frag param1 param2 body)
        (fun name =>
          if name = param1 then some (natToVal x)
          else if name = param2 then some (natToVal y)
          else none) =
        some (ExecResult.returned (natToVal (leanF x y))) := by
    simpa [arg2Store, param1, param2] using hExecVal
  -- simplify the runner using the computed execution result
  have hParams :
      (compileNat2FunFrag funName "x" "y" (Term.lam (Term.lam body))).params
        = ["x", "y"] := rfl
  have hBody' :
      (compileNat2FunFrag funName "x" "y" (Term.lam (Term.lam body))).body
        = compileNatBody₂Frag "x" "y" body := rfl
  have hExecVal'' :
      execFrag (compileNatBody₂Frag "x" "y" body)
        (fun name =>
          if name = "x" then some (natToVal x)
          else if name = "y" then some (natToVal y)
          else none) =
        some (ExecResult.returned (natToVal (leanF x y))) := by
    simpa [param1, param2] using hExecVal'
  simp only [runNat2FunFrag, hParams, hBody', hExecVal'', param1, param2,
        asNat_natToVal, guard]
  simp

end Nat2CompileFragCorrectness
end LambdaIR
end HeytingLean
