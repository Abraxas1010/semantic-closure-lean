namespace HeytingLean
namespace C

abbrev Ident := String

/- A tiny C-like type system (only integers for the nat fragment). -/
inductive CType
  | int

/- Expressions over integers and variables. -/
inductive CExpr
  | intLit (n : Int)
  | var    (x : Ident)
  | add    (e₁ e₂ : CExpr)
  | sub    (e₁ e₂ : CExpr)
  | mul    (e₁ e₂ : CExpr)
  | eq     (e₁ e₂ : CExpr)
  | le     (e₁ e₂ : CExpr)

/- Statements for the fragment. -/
inductive CStmt
  | return (e : CExpr)
  | assign (x : Ident) (e : CExpr)
  | seq    (s₁ s₂ : CStmt)
  | if_    (cond : CExpr) (then_ else_ : CStmt)
  | while  (cond : CExpr) (body : CStmt)

/-- Functions with a name, parameter list, and body. -/
structure CFun where
  name   : Ident
  params : List Ident
  body   : CStmt

end C
end HeytingLean
