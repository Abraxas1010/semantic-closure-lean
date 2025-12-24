import HeytingLean.LambdaIR.Semantics

/-!
# Closing the Loop: λ-calculus bridge via `LambdaIR` (Tier 2)

`HeytingLean.LambdaIR` already provides a simply-typed λ-calculus (syntax + evaluation).
This file records the minimal semantic facts needed for the audit agenda item
“functional model of computation”:

* **β-law** for evaluation (`(λx. body) arg` evaluates by substitution into the environment),
* a small **curry/uncurry** alignment at the semantics level (functions-as-exponentials in `Type`).

These are the Type-level counterparts of the categorical currying story used in
`ClosingTheLoop.Cat` (selectors as exponentials).
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Semantics

namespace LambdaIRBridge

open HeytingLean.LambdaIR

/-- β-law: evaluating an application of a lambda reduces by extending the environment. -/
theorem eval_beta {Γ : LambdaIR.Ctx} {α β : LambdaIR.Ty}
    (body : Term (α :: Γ) β) (arg : Term Γ α) (ρ : LambdaIR.Env Γ) :
    LambdaIR.eval (Term.app (Term.lam body) arg) ρ =
      LambdaIR.eval body (LambdaIR.extendEnv ρ (LambdaIR.eval arg ρ)) := by
  rfl

/-- Semantics of `lam` is (definitionally) a curried function in the environment and argument. -/
theorem eval_lam_eq_curry {Γ : LambdaIR.Ctx} {α β : LambdaIR.Ty} (body : Term (α :: Γ) β) :
    (fun ρ : LambdaIR.Env Γ => LambdaIR.eval (Term.lam body) ρ) =
      Function.curry
        (fun p : LambdaIR.Env Γ × LambdaIR.InterpTy α =>
          LambdaIR.eval body (LambdaIR.extendEnv p.1 p.2)) := by
  funext ρ
  funext x
  rfl

/-- Uncurrying the semantic function of a `lam` yields the expected “pair semantics”. -/
theorem eval_lam_eq_uncurry {Γ : LambdaIR.Ctx} {α β : LambdaIR.Ty} (body : Term (α :: Γ) β) :
    Function.uncurry (fun ρ : LambdaIR.Env Γ => LambdaIR.eval (Term.lam body) ρ) =
      (fun p : LambdaIR.Env Γ × LambdaIR.InterpTy α =>
        LambdaIR.eval body (LambdaIR.extendEnv p.1 p.2)) := by
  funext p
  cases p with
  | mk ρ x => rfl

end LambdaIRBridge

end Semantics
end ClosingTheLoop
end HeytingLean
