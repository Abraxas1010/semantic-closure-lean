import HeytingLean.Core.Types
import HeytingLean.Core.SemanticsBase
import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.LambdaIR.ToMiniC
import HeytingLean.LambdaIR.Semantics
import HeytingLean.LambdaIR.NatIntEqLemmas
import HeytingLean.MiniC.Semantics

namespace HeytingLean
namespace LambdaIR
namespace ToMiniC

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment
open HeytingLean.MiniC

@[simp] def baseEnv : Env [] := by
  intro τ v; cases v

@[simp] def argEnv (n : Nat) : Env [Ty.nat] :=
  fun {τ} v =>
    match v with
    | Var.vz => n
    | Var.vs v' => baseEnv v'

@[simp] def argStore (paramName : String) (n : Nat) : Store :=
  fun x => if x = paramName then some (natToVal n) else none

theorem compileNatExpr_correct
    {t : Term [Ty.nat] Ty.nat}
    (ht : IsNatExpr t)
    (paramName : String) (n : Nat) :
    evalExpr (compileNatExprFrag paramName t) (argStore paramName n)
      = some (natToVal (LambdaIR.eval t (argEnv n))) :=
by
  induction ht with
  | constNat m =>
      simp [compileNatExprFrag, LambdaIR.eval, natToVal, evalExpr]
  | var =>
      simp [compileNatExprFrag, LambdaIR.eval, argEnv, argStore,
            natToVal, evalExpr, lookup]
  | add hf ht ihf iht =>
      simp [compileNatExprFrag, LambdaIR.eval, ihf, iht, natToVal,
            evalExpr, Int.natCast_add, argEnv]

theorem compileBoolExpr_correct
    {c : Term [Ty.nat] Ty.bool}
    (hc : IsBoolExpr c)
    (paramName : String) (n : Nat) :
    evalExpr (compileBoolExprFrag paramName c) (argStore paramName n)
      = some (Val.bool (LambdaIR.eval c (argEnv n))) :=
by
  cases hc with
  | constBool b =>
      simp [compileBoolExprFrag, LambdaIR.eval, evalExpr]
  | eqNat hf ht =>
      have hf' := compileNatExpr_correct hf paramName n
      have ht' := compileNatExpr_correct ht paramName n
      simp [compileBoolExprFrag, LambdaIR.eval, hf', ht', natToVal,
            evalExpr]

theorem compileNatBody_correct
    {body : Term [Ty.nat] Ty.nat}
    (hb : IsNatBody body)
    (paramName : String) (n : Nat) :
    execFrag (compileNatBody paramName body) (argStore paramName n)
      = some (ExecResult.returned (natToVal (LambdaIR.eval body (argEnv n)))) :=
by
  induction hb with
  | @expr t hexpr =>
      have hExpr := compileNatExpr_correct (t := t) hexpr paramName n
      simpa [compileNatBody] using
        (execFrag_return_of_eval
          (σ := argStore paramName n)
          (e := compileNatExprFrag paramName t)
          (v := natToVal (LambdaIR.eval t (argEnv n)))
          hExpr)
  | @if_ c t e hc ht he ih_t ih_e =>
      have hcond := compileBoolExpr_correct hc paramName n
      cases h : LambdaIR.eval c (argEnv n) with
      | true =>
          have hcondTrue :
              evalExpr (compileBoolExprFrag paramName c) (argStore paramName n)
                = some (Val.bool true) := by
            simpa [LambdaIR.eval, h] using hcond
          simp [compileNatBody, execFrag, LambdaIR.eval, h,
                hcondTrue, ih_t]
      | false =>
          have hcondFalse :
              evalExpr (compileBoolExprFrag paramName c) (argStore paramName n)
                = some (Val.bool false) := by
            simpa [LambdaIR.eval, h] using hcond
          simp [compileNatBody, execFrag, LambdaIR.eval, h,
                hcondFalse, ih_e]

@[simp] theorem asNat_natToVal (n : Nat) :
    Val.asNat? (natToVal n) = some n := by
  simp [Val.asNat?, natToVal]

@[simp] theorem evalClosed_lam_app
    (body : Term [Ty.nat] Ty.nat) (n : Nat) :
    LambdaIR.evalClosed
      (LambdaIR.Term.app (LambdaIR.Term.lam body) (LambdaIR.Term.constNat n))
      = LambdaIR.eval body (argEnv n) :=
by
  simp [LambdaIR.evalClosed, LambdaIR.eval, argEnv]

/-- General semantics preservation for the nat→nat fragment. -/
theorem compileNatFun_correct
    {funName paramName : String}
    {t : Term [] (Ty.arrow Ty.nat Ty.nat)}
    (ht : IsNatFun t) :
    NatFunSpec funName paramName t :=
by
  intro fn hCompile n
  rcases ht with ⟨body, rfl, hbody⟩
  simp [compileNatFun] at hCompile
  cases hCompile
  have hExec := compileNatBody_correct hbody paramName n
  simp [NatFunSpec, compileNatFun, runNatFunFrag, hExec,
        argStore, asNat_natToVal, evalClosed_lam_app]

end ToMiniC
end LambdaIR
end HeytingLean
