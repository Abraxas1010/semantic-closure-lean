import HeytingLean.MiniC.Syntax
import HeytingLean.C.Syntax

namespace HeytingLean
namespace MiniC
namespace ToC

open HeytingLean.MiniC
open HeytingLean.C

/-- Translate MiniC expressions to the tiny C subset. -/
def compileExpr : Expr → CExpr
  | Expr.intLit n    => CExpr.intLit n
  | Expr.boolLit b   => CExpr.intLit (if b then 1 else 0)
  | Expr.var x       => CExpr.var x
  | Expr.add e₁ e₂   => CExpr.add (compileExpr e₁) (compileExpr e₂)
  | Expr.sub e₁ e₂   => CExpr.sub (compileExpr e₁) (compileExpr e₂)
  | Expr.mul e₁ e₂   => CExpr.mul (compileExpr e₁) (compileExpr e₂)
  | Expr.le e₁ e₂    => CExpr.le (compileExpr e₁) (compileExpr e₂)
  | Expr.eq e₁ e₂    => CExpr.eq (compileExpr e₁) (compileExpr e₂)
  | Expr.not e       => CExpr.eq (compileExpr e) (CExpr.intLit 0)    -- boolean not as equality to 0
  | Expr.and e₁ e₂   => CExpr.mul (compileExpr e₁) (compileExpr e₂)  -- 0/1 encoding
  | Expr.or e₁ e₂    =>
      -- return 1 when either operand is non-zero (assuming 0/1 encoding)
      CExpr.le (CExpr.intLit 1)
        (CExpr.add (compileExpr e₁) (compileExpr e₂))

/-- Translate MiniC statements to the tiny C subset. -/
def compileStmt : Stmt → CStmt
  | Stmt.return e        => CStmt.return (compileExpr e)
  | Stmt.assign x e      => CStmt.assign x (compileExpr e)
  | Stmt.if_ c t e       => CStmt.if_ (compileExpr c) (compileStmt t) (compileStmt e)
  | Stmt.seq s₁ s₂       => CStmt.seq (compileStmt s₁) (compileStmt s₂)
  | Stmt.skip            => CStmt.return (CExpr.intLit 0)
  | Stmt.while c b       => CStmt.while (compileExpr c) (compileStmt b)

/-- Translate a MiniC fragment function to the tiny C subset. -/
def compileFun (fn : Fun) : CFun :=
  { name := fn.name
    params := fn.params
    body := compileStmt fn.body }

end ToC
end MiniC
end HeytingLean
