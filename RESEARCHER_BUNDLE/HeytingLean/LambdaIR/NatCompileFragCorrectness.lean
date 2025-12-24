import HeytingLean.Core.Types
import HeytingLean.Core.SemanticsBase
import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.LambdaIR.NatCompileFrag
import HeytingLean.LambdaIR.Semantics
import HeytingLean.LambdaIR.NatIntEqLemmas
import HeytingLean.MiniC.Semantics

namespace HeytingLean
namespace LambdaIR
namespace NatCompileFrag

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment
open HeytingLean.MiniC

@[simp] theorem compileNatBodyFrag_of_expr
    (paramName : String) {t : Term [Ty.nat] Ty.nat}
    (ht : IsNatExpr t) :
    compileNatBodyFrag paramName t
      = Stmt.return (compileNatExprFrag paramName t) := by
  cases ht with
  | constNat =>
      simp [compileNatBodyFrag, compileNatExprFrag]
  | var =>
      simp [compileNatBodyFrag, compileNatExprFrag]
  | add hf ht =>
      simp [compileNatBodyFrag, compileNatExprFrag]

@[simp] def argStore (paramName : String) (n : Nat) : Store :=
  fun x => if x = paramName then some (natToVal n) else none

theorem compileNatExprFrag_correct
    {t : Term [Ty.nat] Ty.nat}
    (ht : IsNatExpr t)
    (paramName : String) (n : Nat) :
    evalExpr (compileNatExprFrag paramName t) (argStore paramName n)
      = some (natToVal (LambdaIR.eval t
          (Core.extendEnv (Γ := []) (α := Ty.nat)
            baseEnv (x := (n : InterpTy Ty.nat))))) :=
by
  let env : Env [Ty.nat] :=
    Core.extendEnv (Γ := []) (α := Ty.nat)
      baseEnv (x := (n : InterpTy Ty.nat))
  change
      evalExpr (compileNatExprFrag paramName t) (argStore paramName n)
        = some (natToVal (LambdaIR.eval t env))
  induction ht with
  | constNat m =>
      simp [compileNatExprFrag, LambdaIR.eval, natToVal, evalExpr]
  | var =>
      simp [compileNatExprFrag, LambdaIR.eval, argStore,
            natToVal, evalExpr, lookup, env]
  | add hf ht ihf iht =>
      simp [compileNatExprFrag, LambdaIR.eval, ihf, iht, natToVal,
            evalExpr, Int.natCast_add]

theorem compileBoolExprFrag_correct
    {c : Term [Ty.nat] Ty.bool}
    (hc : IsBoolExpr c)
    (paramName : String) (n : Nat) :
    evalExpr (compileBoolExprFrag paramName c) (argStore paramName n)
      = some (Val.bool (LambdaIR.eval c
          (Core.extendEnv (Γ := []) (α := Ty.nat)
            Core.baseEnv (x := (n : InterpTy Ty.nat))))) :=
by
  let env : Env [Ty.nat] :=
    Core.extendEnv (Γ := []) (α := Ty.nat)
      Core.baseEnv (x := (n : InterpTy Ty.nat))
  change
      evalExpr (compileBoolExprFrag paramName c) (argStore paramName n)
        = some (Val.bool (LambdaIR.eval c env))
  cases hc with
  | constBool b =>
      simp [compileBoolExprFrag, LambdaIR.eval, evalExpr]
  | eqNat hf ht =>
      have hf' := compileNatExprFrag_correct hf paramName n
      have ht' := compileNatExprFrag_correct ht paramName n
      simp [compileBoolExprFrag, LambdaIR.eval, hf', ht', natToVal,
            evalExpr, env]

theorem compileNatBodyFrag_correct
    {body : Term [Ty.nat] Ty.nat}
    (hb : IsNatBody body)
    (paramName : String) (n : Nat) :
    execFrag (compileNatBodyFrag paramName body) (argStore paramName n)
      = some (ExecResult.returned (natToVal (LambdaIR.eval body
          (Core.extendEnv (Γ := []) (α := Ty.nat)
            Core.baseEnv (x := (n : InterpTy Ty.nat)))))) :=
by
  revert paramName n
  induction hb with
  | @expr t hexpr =>
      intro paramName n
      let env : Env [Ty.nat] :=
        Core.extendEnv (Γ := []) (α := Ty.nat)
          Core.baseEnv (x := (n : InterpTy Ty.nat))
      change
          execFrag (compileNatBodyFrag paramName t) (argStore paramName n)
            = some (ExecResult.returned (natToVal (LambdaIR.eval t env)))
      have hExpr := compileNatExprFrag_correct hexpr paramName n
      have hExpr' :
          evalExpr (compileNatExprFrag paramName t) (argStore paramName n)
            = some (natToVal (LambdaIR.eval t env)) := by
        simpa [env] using hExpr
      simpa [compileNatBodyFrag_of_expr paramName hexpr,
            LambdaIR.eval, natToVal, env] using
        (execFrag_return_of_eval
          (σ := argStore paramName n)
          (e := compileNatExprFrag paramName t)
          (v := natToVal (LambdaIR.eval t env))
          hExpr')
  | @if_ c t e hc ht he ih_t ih_e =>
      intro paramName n
      let env : Env [Ty.nat] :=
        Core.extendEnv (Γ := []) (α := Ty.nat)
          Core.baseEnv (x := (n : InterpTy Ty.nat))
      change
          execFrag (compileNatBodyFrag paramName (Term.if_ c t e))
              (argStore paramName n)
            = some (ExecResult.returned (natToVal (LambdaIR.eval (Term.if_ c t e) env)))
      have hcond := compileBoolExprFrag_correct hc paramName n
      have hcond' :
          evalExpr (compileBoolExprFrag paramName c) (argStore paramName n)
            = some (Val.bool (LambdaIR.eval c env)) := by
        simpa [env] using hcond
      cases h : LambdaIR.eval c env with
      | true =>
          have hcondTrue :
              evalExpr (compileBoolExprFrag paramName c) (argStore paramName n)
                = some (Val.bool true) := by
            simpa [h] using hcond'
          have hExec :
              execFrag (compileNatBodyFrag paramName (Term.if_ c t e)) (argStore paramName n)
                = execFrag (compileNatBodyFrag paramName t) (argStore paramName n) := by
            simpa [compileNatBodyFrag] using
              (execFrag_if_true
                (cond := compileBoolExprFrag paramName c)
                (then_ := compileNatBodyFrag paramName t)
                (else_ := compileNatBodyFrag paramName e)
                (σ := argStore paramName n)
                hcondTrue)
          have hThen := ih_t paramName n
          have hThen' :
              execFrag (compileNatBodyFrag paramName t) (argStore paramName n)
                = some (ExecResult.returned (natToVal (LambdaIR.eval t env))) := by
            simpa [env] using hThen
          have hCombined := hExec.trans hThen'
          have hGoal :
              some (ExecResult.returned
                  (natToVal (LambdaIR.eval (Term.if_ c t e) env)))
                = some (ExecResult.returned (natToVal (LambdaIR.eval t env))) := by
            simp [LambdaIR.eval, env, h, natToVal]
          exact hGoal.symm ▸ hCombined
      | false =>
          have hcondFalse :
              evalExpr (compileBoolExprFrag paramName c) (argStore paramName n)
                = some (Val.bool false) := by
            simpa [h] using hcond'
          have hExec :
              execFrag (compileNatBodyFrag paramName (Term.if_ c t e)) (argStore paramName n)
                = execFrag (compileNatBodyFrag paramName e) (argStore paramName n) := by
            simpa [compileNatBodyFrag] using
              (execFrag_if_false
                (cond := compileBoolExprFrag paramName c)
                (then_ := compileNatBodyFrag paramName t)
                (else_ := compileNatBodyFrag paramName e)
                (σ := argStore paramName n)
                hcondFalse)
          have hElse := ih_e paramName n
          have hElse' :
              execFrag (compileNatBodyFrag paramName e) (argStore paramName n)
                = some (ExecResult.returned (natToVal (LambdaIR.eval e env))) := by
            simpa [env] using hElse
          have hCombined := hExec.trans hElse'
          have hGoal :
              some (ExecResult.returned
                  (natToVal (LambdaIR.eval (Term.if_ c t e) env)))
                = some (ExecResult.returned (natToVal (LambdaIR.eval e env))) := by
            simp [LambdaIR.eval, env, h, natToVal]
          exact hGoal.symm ▸ hCombined

@[simp] theorem asNat_natToVal (n : Nat) :
    Val.asNat? (natToVal n) = some n := by
  simp [Val.asNat?, natToVal]

@[simp] theorem evalClosed_lam_app
    (body : Term [Ty.nat] Ty.nat) (n : Nat) :
    LambdaIR.evalClosed
      (LambdaIR.Term.app (LambdaIR.Term.lam body) (LambdaIR.Term.constNat n))
      = LambdaIR.eval body
          (Core.extendEnv (Γ := []) (α := Ty.nat)
            Core.baseEnv (x := (n : InterpTy Ty.nat))) :=
by
  unfold LambdaIR.evalClosed
  simp [LambdaIR.eval]

/-- General semantics preservation for the nat→nat fragment compiler. -/
theorem compileNatFunFrag_correct
    {funName paramName : String}
    {t : Term [] (Ty.arrow Ty.nat Ty.nat)}
    (ht : IsNatFun t) :
    NatFunSpecFrag funName paramName t :=
by
  intro n
  rcases ht with ⟨body, rfl, hbody⟩
  let env : Env [Ty.nat] :=
    Core.extendEnv (Γ := []) (α := Ty.nat)
      Core.baseEnv (x := (n : InterpTy Ty.nat))
  have hExec := compileNatBodyFrag_correct hbody paramName n
  have hExec' :
      execFrag (compileNatBodyFrag paramName body) (argStore paramName n)
        = some (ExecResult.returned (natToVal (LambdaIR.eval body env))) := by
    simpa [env] using hExec
  have hExec'' :
      execFrag (compileNatBodyFrag paramName body)
          (fun x => if x = paramName then some (Val.int ↑n) else none)
        = some (ExecResult.returned (natToVal (LambdaIR.eval body env))) := by
    simpa [argStore, natToVal] using hExec'
  dsimp [NatFunSpecFrag, runNatFunFrag, compileNatFunFrag, argStore] at ⊢
  have hMatch :
      (match execFrag (compileNatBodyFrag paramName body)
            (fun x => if x = paramName then some (Val.int ↑n) else none) with
        | some (ExecResult.returned v) => Val.asNat? v
        | _ => none)
        = Val.asNat? (natToVal (LambdaIR.eval body env)) := by
    simp [hExec'', natToVal]
  have hGoal :
      Val.asNat? (natToVal (LambdaIR.eval body env))
        = some (LambdaIR.eval body env) :=
    asNat_natToVal (LambdaIR.eval body env)
  have hInner :
      (match execFrag (compileNatBodyFrag paramName body)
            (fun x => if x = paramName then some (Val.int ↑n) else none) with
        | some (ExecResult.returned v) => Val.asNat? v
        | _ => none)
        = some (LambdaIR.eval body env) :=
    hMatch.trans hGoal
  have hClosed :=
    evalClosed_lam_app body n
  simpa [guard, env, hClosed, hInner]

end NatCompileFrag
end LambdaIR
end HeytingLean
