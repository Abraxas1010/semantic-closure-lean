import HeytingLean.C.Syntax

namespace HeytingLean
namespace C

open HeytingLean.C

abbrev Store := Ident → Option Int

inductive ExecResult
  | normal (σ : Store)
  | returned (v : Int)

/-- Evaluate expressions in the tiny C subset. -/
def evalExpr : CExpr → Store → Option Int
  | CExpr.intLit n, _ => some n
  | CExpr.var x, σ => σ x
  | CExpr.add e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      pure (v₁ + v₂)
  | CExpr.sub e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      pure (v₁ - v₂)
  | CExpr.mul e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      pure (v₁ * v₂)
  | CExpr.eq e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      pure (if v₁ = v₂ then 1 else 0)
  | CExpr.le e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      pure (if v₁ ≤ v₂ then 1 else 0)

/-- Big-step execution for statements. -/
private def execFuel : Nat → CStmt → Store → Option ExecResult
  | 0, _, _ => none
  | fuel + 1, CStmt.return e, σ => do
      let v ← evalExpr e σ
      pure (ExecResult.returned v)
  | fuel + 1, CStmt.assign x e, σ => do
      let v ← evalExpr e σ
      pure (ExecResult.normal (fun y => if y = x then some v else σ y))
  | fuel + 1, CStmt.seq s₁ s₂, σ => do
      match execFuel fuel s₁ σ with
      | some (ExecResult.normal σ') => execFuel fuel s₂ σ'
      | some (ExecResult.returned v) => pure (ExecResult.returned v)
      | none => none
  | fuel + 1, CStmt.if_ cond then_ else_, σ => do
      let v ← evalExpr cond σ
      if v = 0 then
        execFuel fuel else_ σ
      else
        execFuel fuel then_ σ
  | fuel + 1, CStmt.while cond body, σ => do
      let v ← evalExpr cond σ
      if v = 0 then
        pure (ExecResult.normal σ)
      else
        match execFuel fuel body σ with
        | some (ExecResult.normal σ') => execFuel fuel (CStmt.while cond body) σ'
        | some (ExecResult.returned v) => pure (ExecResult.returned v)
        | none => none

def exec (s : CStmt) (σ : Store) (fuel : Nat := 10000) : Option ExecResult :=
  execFuel fuel s σ

/-- Bind parameters to argument values. -/
def bindParams : List Ident → List Int → Option Store
  | [], [] => some (fun _ => none)
  | p :: ps, a :: as => do
      let σ ← bindParams ps as
      pure (fun x => if x = p then some a else σ x)
  | _, _ => none

/-- Run a C function on a list of arguments. -/
def runCFun (f : CFun) (args : List Int) : Option Int := do
  let σ ← bindParams f.params args
  match ← exec f.body σ with
  | ExecResult.returned v => pure v
  | ExecResult.normal _   => none

/-! # Fragment-level, structurally recursive semantics

These definitions mirror `exec`/`runCFun` but are restricted to the
while-free fragment (the subset emitted by the MiniC fragment compiler).
They avoid opacity issues with the `partial def exec`. -/

/-- Evaluate fragment statements (return/if only) in the tiny C subset. -/
def execFragC : CStmt → Store → Option ExecResult
  | CStmt.return e, σ => (evalExpr e σ).map ExecResult.returned
  | CStmt.if_ cond t e, σ => do
      let v ← evalExpr cond σ
      if v = 0 then execFragC e σ else execFragC t σ
  | _, _ => none

@[simp] theorem execFragC_return (e : CExpr) (σ : Store) :
    execFragC (CStmt.return e) σ
      = (evalExpr e σ).map ExecResult.returned := rfl

@[simp] theorem execFragC_if_true
    (cond : CExpr) (t e : CStmt) (σ : Store)
    (h : evalExpr cond σ = some v) (hnz : v ≠ 0) :
    execFragC (CStmt.if_ cond t e) σ = execFragC t σ := by
  simp [execFragC, h, hnz]

@[simp] theorem execFragC_if_false
    (cond : CExpr) (t e : CStmt) (σ : Store)
    (h : evalExpr cond σ = some v) (hz : v = 0) :
    execFragC (CStmt.if_ cond t e) σ = execFragC e σ := by
  simp [execFragC, h, hz]

/-- Run a fragment C function on a list of arguments (fails on non-fragment constructs). -/
def runCFunFrag (f : CFun) (args : List Int) : Option Int := do
  let σ ← bindParams f.params args
  match execFragC f.body σ with
  | some (ExecResult.returned v) => some v
  | _ => none

end C
end HeytingLean
