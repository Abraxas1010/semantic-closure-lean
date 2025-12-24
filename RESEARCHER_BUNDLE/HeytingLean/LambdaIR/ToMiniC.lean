import HeytingLean.Core.Types
import HeytingLean.LambdaIR.Syntax
import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.LambdaIR.Semantics
import HeytingLean.MiniC.Syntax
import HeytingLean.MiniC.Semantics

namespace HeytingLean
namespace LambdaIR
namespace ToMiniC

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.MiniC

/-- Compile a LambdaIR nat expression (with one nat parameter) to a MiniC expression. -/
def compileNatExpr (paramName : String) : Term [Ty.nat] Ty.nat → Expr
  | Term.constNat n => Expr.intLit (Int.ofNat n)
  | Term.var Var.vz => Expr.var paramName
  | Term.app (Term.app Term.primAddNat f) t =>
      Expr.add (compileNatExpr paramName f) (compileNatExpr paramName t)
  | _ => Expr.intLit 0

/-- Compile a LambdaIR bool expression (with one nat parameter) to a MiniC expression. -/
def compileBoolExpr (paramName : String) : Term [Ty.nat] Ty.bool → Expr
  | Term.constBool b => Expr.boolLit b
  | Term.app (Term.app Term.primEqNat t₁) t₂ =>
      Expr.eq (compileNatExpr paramName t₁) (compileNatExpr paramName t₂)
  | _ => Expr.boolLit false

@[simp] def compileNatExprFrag (paramName : String) : Term [Ty.nat] Ty.nat → Expr
  | Term.constNat m => Expr.intLit (Int.ofNat m)
  | Term.var Var.vz => Expr.var paramName
  | Term.app (Term.app Term.primAddNat f) s =>
      Expr.add (compileNatExprFrag paramName f) (compileNatExprFrag paramName s)
  | _ => Expr.intLit 0

@[simp] def compileBoolExprFrag (paramName : String) : Term [Ty.nat] Ty.bool → Expr
  | Term.constBool b => Expr.boolLit b
  | Term.app (Term.app Term.primEqNat t₁) t₂ =>
      Expr.eq (compileNatExprFrag paramName t₁) (compileNatExprFrag paramName t₂)
  | _ => Expr.boolLit false

/-- Compile a LambdaIR nat body (with one nat parameter) to a MiniC statement. -/
def compileNatBody (paramName : String) : Term [Ty.nat] Ty.nat → Stmt
  | Term.if_ c t e =>
      Stmt.if_ (compileBoolExprFrag paramName c)
        (compileNatBody paramName t)
        (compileNatBody paramName e)
  | term => Stmt.return (compileNatExprFrag paramName term)

/-- Compile a closed `nat → nat` LambdaIR term into a MiniC function. -/
def compileNatFun (funName paramName : String)
    (t : LambdaIR.Term [] (Ty.arrow Ty.nat Ty.nat)) : Except String Fun :=
  match t with
  | .lam body =>
      .ok
        { name := funName
          params := [paramName]
          body := compileNatBody paramName body }
  | _ => .error "expected lambda"

/-- Specification connecting LambdaIR semantics with the compiled MiniC function. -/
def NatFunSpec (funName paramName : String)
    (t : LambdaIR.Term [] (Ty.arrow Ty.nat Ty.nat)) : Prop :=
  ∀ fn, compileNatFun funName paramName t = Except.ok fn →
    ∀ n,
      runNatFunFrag fn paramName n =
        some (LambdaIR.evalClosed
          (LambdaIR.Term.app t (LambdaIR.Term.constNat n)))

/-- Run the compiled MiniC function if compilation succeeds. -/
def runCompiledNatFun (funName paramName : String)
    (t : LambdaIR.Term [] (Ty.arrow Ty.nat Ty.nat)) (n : Nat) : Option Nat :=
  match compileNatFun funName paramName t with
  | Except.ok fn => runNatFun fn n
  | Except.error _ => none

/-- Run the compiled nat→nat function via the fragment semantics. -/
def runCompiledNatFunFrag (funName paramName : String)
    (t : LambdaIR.Term [] (Ty.arrow Ty.nat Ty.nat)) (n : Nat) : Option Nat :=
  match compileNatFun funName paramName t with
  | Except.ok fn => runNatFunFrag fn paramName n
  | Except.error _ => none

end ToMiniC
end LambdaIR
end HeytingLean
