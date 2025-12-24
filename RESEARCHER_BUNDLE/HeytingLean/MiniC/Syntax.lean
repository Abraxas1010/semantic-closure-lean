namespace HeytingLean
namespace MiniC

/-- MiniC value-level types (v0). -/
inductive Ty
  | int
  | bool
  deriving DecidableEq, Repr

/-- Expressions are pure computations over the store. -/
inductive Expr
  | var (name : String)
  | intLit (n : Int)
  | boolLit (b : Bool)
  | add (e₁ e₂ : Expr)
  | sub (e₁ e₂ : Expr)
  | mul (e₁ e₂ : Expr)
  | le  (e₁ e₂ : Expr)
  | eq  (e₁ e₂ : Expr)
  | not (e : Expr)
  | and (e₁ e₂ : Expr)
  | or  (e₁ e₂ : Expr)
  deriving Repr, Inhabited

/-- Statements mutate the store or produce a return value. -/
inductive Stmt
  | skip
  | assign (name : String) (rhs : Expr)
  | seq (s₁ s₂ : Stmt)
  | if_ (cond : Expr) (then_ else_ : Stmt)
  | while (cond : Expr) (body : Stmt)
  | return (val : Expr)
  deriving Repr, Inhabited

structure Fun where
  name   : String
  params : List String
  body   : Stmt
  deriving Repr

structure Program where
  defs : List Fun
  main : Fun
  deriving Repr

end MiniC
end HeytingLean
