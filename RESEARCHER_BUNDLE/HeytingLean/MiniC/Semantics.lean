import HeytingLean.MiniC.Syntax

namespace HeytingLean
namespace MiniC

/-- Runtime values for MiniC. -/
inductive Val
  | int (n : Int)
  | bool (b : Bool)
  deriving Repr, DecidableEq

/-- Encode a natural number as a MiniC value. -/
@[simp] def natToVal (n : Nat) : Val := Val.int (Int.ofNat n)

@[simp] def Val.asNat? : Val → Option Nat
  | Val.int n =>
      if n ≥ 0 then
        some (Int.toNat n)
      else
        none
  | _ => none

/-- Stores map variable names to optional values. -/
abbrev Store := String → Option Val

/-- Empty store with no bindings. -/
@[simp] def emptyStore : Store := fun _ => none

/-- Lookup a variable in the store. -/
@[simp] def lookup (σ : Store) (name : String) : Option Val := σ name

/-- Update a variable in the store. -/
@[simp] def update (σ : Store) (name : String) (v : Val) : Store :=
  fun y => if y = name then some v else σ y

/-- Results of executing a statement. -/
inductive ExecResult
  | normal (σ : Store)
  | returned (v : Val)

/-- Evaluate an expression under the store. -/
def evalExpr : Expr → Store → Option Val
  | Expr.var x, σ => lookup σ x
  | Expr.intLit n, _ => some (Val.int n)
  | Expr.boolLit b, _ => some (Val.bool b)
  | Expr.add e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.int n₁, Val.int n₂ => pure (Val.int (n₁ + n₂))
      | _, _ => none
  | Expr.sub e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.int n₁, Val.int n₂ => pure (Val.int (n₁ - n₂))
      | _, _ => none
  | Expr.mul e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.int n₁, Val.int n₂ => pure (Val.int (n₁ * n₂))
      | _, _ => none
  | Expr.le e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.int n₁, Val.int n₂ => pure (Val.bool (decide (n₁ ≤ n₂)))
      | _, _ => none
  | Expr.eq e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.int n₁, Val.int n₂ => pure (Val.bool (decide (n₁ = n₂)))
      | Val.bool b₁, Val.bool b₂ => pure (Val.bool (decide (b₁ = b₂)))
      | _, _ => none
  | Expr.not e, σ => do
      let v ← evalExpr e σ
      match v with
      | Val.bool b => pure (Val.bool (!b))
      | _ => none
  | Expr.and e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.bool b₁, Val.bool b₂ => pure (Val.bool (b₁ && b₂))
      | _, _ => none
  | Expr.or e₁ e₂, σ => do
      let v₁ ← evalExpr e₁ σ
      let v₂ ← evalExpr e₂ σ
      match v₁, v₂ with
      | Val.bool b₁, Val.bool b₂ => pure (Val.bool (b₁ || b₂))
      | _, _ => none

/-- Partial big-step executor for MiniC statements. -/
private def execFuel : Nat → Stmt → Store → Option ExecResult
  | 0, _, _ => none
  | _ + 1, Stmt.skip, σ => some (ExecResult.normal σ)
  | _ + 1, Stmt.assign x rhs, σ => do
      let v ← evalExpr rhs σ
      pure (ExecResult.normal (update σ x v))
  | fuel + 1, Stmt.seq s₁ s₂, σ => do
      match execFuel fuel s₁ σ with
      | some (ExecResult.normal σ') => execFuel fuel s₂ σ'
      | some (ExecResult.returned v) => pure (ExecResult.returned v)
      | none => none
  | fuel + 1, Stmt.if_ cond then_ else_, σ => do
      let v ← evalExpr cond σ
      match v with
      | Val.bool true  => execFuel fuel then_ σ
      | Val.bool false => execFuel fuel else_ σ
      | _ => none
  | fuel + 1, Stmt.while cond body, σ => do
      let v ← evalExpr cond σ
      match v with
      | Val.bool true =>
          match execFuel fuel body σ with
          | some (ExecResult.normal σ') => execFuel fuel (Stmt.while cond body) σ'
          | some (ExecResult.returned w) => pure (ExecResult.returned w)
          | none => none
      | Val.bool false => pure (ExecResult.normal σ)
      | _ => none
  | _ + 1, Stmt.return e, σ => do
      let v ← evalExpr e σ
      pure (ExecResult.returned v)

def exec (s : Stmt) (σ : Store) (fuel : Nat := 10000) : Option ExecResult :=
  execFuel fuel s σ

/-- Bind parameters to arguments, returning an initial store. -/
@[simp] def bindParams : List String → List Val → Option Store
  | [], [] => some emptyStore
  | p :: ps, v :: vs => do
      let σ ← bindParams ps vs
      pure (update σ p v)
  | _, _ => none

/-- Execute a function with argument values. -/
def runFun (fn : Fun) (args : List Val) : Option Val := do
  let σ ← bindParams fn.params args
  match exec fn.body σ with
  | some (ExecResult.normal _) => none
  | some (ExecResult.returned v) => some v
  | none => none

/-- Run the main function of a program. -/
def runProgram (prog : Program) (args : List Val) : Option Val :=
  runFun prog.main args

/-- Specialised helper for single-argument nat→nat functions. -/
def runNatFun (fn : Fun) (n : Nat) : Option Nat := do
  let v ← runFun fn [natToVal n]
  Val.asNat? v

/-- Fragment-only semantics for the nat→nat subset emitted by the compiler. -/
def execFrag : Stmt → Store → Option ExecResult
  | Stmt.return e, σ => do
      let v ← evalExpr e σ
      pure (ExecResult.returned v)
  | Stmt.if_ cond then_ else_, σ => do
      let v ← evalExpr cond σ
      match v with
      | Val.bool true => execFrag then_ σ
      | Val.bool false => execFrag else_ σ
      | _ => none
  | _, _ => none

@[simp] theorem execFrag_return (e : Expr) (σ : Store) :
    execFrag (Stmt.return e) σ
      = (evalExpr e σ).map ExecResult.returned := by
  cases h : evalExpr e σ <;> simp [execFrag, h]

@[simp] theorem execFrag_return_of_eval {e : Expr} {σ : Store} {v : Val}
    (h : evalExpr e σ = some v) :
    execFrag (Stmt.return e) σ = some (ExecResult.returned v) := by
  dsimp [execFrag]
  simp [h]

@[simp] theorem execFrag_if_true
    (cond : Expr) (then_ else_ : Stmt) (σ : Store)
    (h : evalExpr cond σ = some (Val.bool true)) :
    execFrag (Stmt.if_ cond then_ else_) σ = execFrag then_ σ := by
  dsimp [execFrag]
  simp [h]

@[simp] theorem execFrag_if_false
    (cond : Expr) (then_ else_ : Stmt) (σ : Store)
    (h : evalExpr cond σ = some (Val.bool false)) :
    execFrag (Stmt.if_ cond then_ else_) σ = execFrag else_ σ := by
  dsimp [execFrag]
  simp [h]

/-- Fragment-only runner for nat→nat functions. -/
def runNatFunFrag (fn : Fun) (paramName : String) (n : Nat) : Option Nat := do
  guard (fn.params = [paramName])
  let σ : Store := fun x => if x = paramName then some (natToVal n) else none
  match execFrag fn.body σ with
  | some (ExecResult.returned v) => Val.asNat? v
  | _ => none

/-- Fragment-only runner for nat→nat→nat functions (curried as two parameters). -/
def runNat2FunFrag (fn : Fun) (param1 param2 : String)
    (x y : Nat) : Option Nat := do
  guard (fn.params = [param1, param2])
  let σ : Store :=
    fun name =>
      if name = param1 then
        some (natToVal x)
      else if name = param2 then
        some (natToVal y)
      else
        none
  match execFrag fn.body σ with
  | some (ExecResult.returned v) => Val.asNat? v
  | _ => none

end MiniC
end HeytingLean
