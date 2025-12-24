import HeytingLean.Core.Types
import HeytingLean.LambdaIR.Syntax
import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.LambdaIR.Semantics
import HeytingLean.MiniC.Syntax
import HeytingLean.MiniC.Semantics

namespace HeytingLean
namespace LambdaIR
namespace NatCompileFrag

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment
open HeytingLean.MiniC

/-- Fragment-only nat expression compiler: total and fully reducible. -/
def compileNatExprFrag (paramName : String) :
    Term [Ty.nat] Ty.nat → Expr
  | Term.constNat m => Expr.intLit (Int.ofNat m)
  | Term.var Var.vz => Expr.var paramName
  | Term.app (Term.app Term.primAddNat f) g =>
      Expr.add (compileNatExprFrag paramName f)
        (compileNatExprFrag paramName g)
  | _ => Expr.intLit 0

/-- Fragment-only bool expression compiler. -/
def compileBoolExprFrag (paramName : String) :
    Term [Ty.nat] Ty.bool → Expr
  | Term.constBool b => Expr.boolLit b
  | Term.app (Term.app Term.primEqNat t₁) t₂ =>
      Expr.eq (compileNatExprFrag paramName t₁)
        (compileNatExprFrag paramName t₂)
  | _ => Expr.boolLit false

/-- Fragment-only nat body compiler. -/
def compileNatBodyFrag (paramName : String) :
    Term [Ty.nat] Ty.nat → Stmt
  | Term.if_ c t e =>
      Stmt.if_ (compileBoolExprFrag paramName c)
        (compileNatBodyFrag paramName t)
        (compileNatBodyFrag paramName e)
  | term => Stmt.return (compileNatExprFrag paramName term)

/-- Nat→nat fragment compiler that always succeeds. -/
def compileNatFunFrag (funName paramName : String)
    (t : Term [] (Ty.arrow Ty.nat Ty.nat)) : Fun :=
  match t with
  | Term.lam body =>
      { name := funName
        params := [paramName]
        body := compileNatBodyFrag paramName body }
  | _ =>
      { name := funName
        params := [paramName]
        body := Stmt.return (Expr.intLit 0) }

/-- Fragment-only spec that relates compilation with LambdaIR semantics. -/
def NatFunSpecFrag (funName paramName : String)
    (t : Term [] (Ty.arrow Ty.nat Ty.nat)) : Prop :=
  ∀ n,
    runNatFunFrag (compileNatFunFrag funName paramName t) paramName n
      = some (LambdaIR.evalClosed
          (LambdaIR.Term.app t (LambdaIR.Term.constNat n)))

/-- Convenience runner that invokes the fragment compiler before execFrag. -/
def runCompiledNatFunFrag (funName paramName : String)
    (t : Term [] (Ty.arrow Ty.nat Ty.nat)) (n : Nat) : Option Nat :=
  runNatFunFrag (compileNatFunFrag funName paramName t) paramName n

end NatCompileFrag
end LambdaIR
end HeytingLean
