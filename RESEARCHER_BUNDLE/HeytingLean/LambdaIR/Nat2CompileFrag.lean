import HeytingLean.Core.Types
import HeytingLean.LambdaIR.Syntax
import HeytingLean.LambdaIR.Nat2FunFragment
import HeytingLean.LambdaIR.Semantics
import HeytingLean.MiniC.Syntax
import HeytingLean.MiniC.Semantics

namespace HeytingLean
namespace LambdaIR
namespace Nat2CompileFrag

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Nat2FunFragment
open HeytingLean.MiniC

/-- Generic compiler for nat expressions given a variable mapping into MiniC. -/
def compileNatExprWith :
    ∀ {Γ}, (Var Γ Ty.nat → Expr) →
      Term Γ Ty.nat → Expr
  | _, _, Term.constNat m => Expr.intLit (Int.ofNat m)
  | _, varMap, Term.var v => varMap v
  | _, varMap, Term.app (Term.app Term.primAddNat f) g =>
      Expr.add (compileNatExprWith varMap f)
        (compileNatExprWith varMap g)
  | _, _, _ => Expr.intLit 0

/-- Generic compiler for boolean expressions given a variable mapping into MiniC. -/
def compileBoolExprWith :
    ∀ {Γ}, (Var Γ Ty.nat → Expr) →
      Term Γ Ty.bool → Expr
  | _, _, Term.constBool b => Expr.boolLit b
  | _, varMap, Term.app (Term.app Term.primEqNat t₁) t₂ =>
      Expr.eq (compileNatExprWith varMap t₁)
        (compileNatExprWith varMap t₂)
  | _, _, _ => Expr.boolLit false

/-- Generic compiler for nat bodies given a variable mapping into MiniC. -/
def compileNatBodyWith :
    ∀ {Γ}, (Var Γ Ty.nat → Expr) →
      Term Γ Ty.nat → Stmt
  | _, varMap, Term.if_ c t e =>
      Stmt.if_ (compileBoolExprWith varMap c)
        (compileNatBodyWith varMap t)
        (compileNatBodyWith varMap e)
  | _, varMap, term =>
      Stmt.return (compileNatExprWith varMap term)

/-- Variable map for the two nat parameters (outer first, inner second). -/
def varMap₂ (param1 param2 : String) :
    Var [Ty.nat, Ty.nat] Ty.nat → Expr
  | Var.vz => Expr.var param2
  | Var.vs Var.vz => Expr.var param1
  | _ => Expr.intLit 0

/-- Compile nat expressions with two nat parameters. -/
def compileNatExpr₂Frag (param1 param2 : String) :
    Term [Ty.nat, Ty.nat] Ty.nat → Expr :=
  compileNatExprWith (varMap₂ param1 param2)

/-- Compile boolean expressions with two nat parameters. -/
def compileBoolExpr₂Frag (param1 param2 : String) :
    Term [Ty.nat, Ty.nat] Ty.bool → Expr :=
  compileBoolExprWith (varMap₂ param1 param2)

/-- Compile bodies of nat→nat→nat fragment functions. -/
def compileNatBody₂Frag (param1 param2 : String) :
    Term [Ty.nat, Ty.nat] Ty.nat → Stmt :=
  compileNatBodyWith (varMap₂ param1 param2)

/-- Compiler for curried nat→nat→nat LambdaIR functions. -/
def compileNat2FunFrag (funName param1 param2 : String)
    (t : Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))) : Fun :=
  match t with
  | Term.lam (Term.lam body) =>
      { name := funName
        params := [param1, param2]
        body := compileNatBody₂Frag param1 param2 body }
  | _ =>
      { name := funName
        params := [param1, param2]
        body := Stmt.return (Expr.intLit 0) }

/-- Specification relating compiled nat→nat→nat fragment functions and LambdaIR semantics. -/
def Nat2FunSpec (funName param1 param2 : String)
    (leanF : Nat → Nat → Nat)
    (t :
      Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))) : Prop :=
  ∀ x y,
    runNat2FunFrag
        (compileNat2FunFrag funName param1 param2 t)
        param1 param2 x y
      = some (leanF x y)

/-- Convenience runner that invokes the fragment compiler before executing. -/
def runCompiledNat2FunFrag (funName param1 param2 : String)
    (t :
      Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat)))
    (x y : Nat) : Option Nat :=
  runNat2FunFrag
    (compileNat2FunFrag funName param1 param2 t)
    param1 param2 x y

end Nat2CompileFrag
end LambdaIR
end HeytingLean
