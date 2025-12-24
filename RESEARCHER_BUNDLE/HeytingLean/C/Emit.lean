import HeytingLean.C.Syntax

/-!
# Emit tiny-C AST as C source code (Phase 4 utility)

This is a lightweight pretty-printer for the tiny `HeytingLean.C` fragment:
- integer expressions (plus comparisons encoded as `0/1`),
- assignments, sequencing, `if`, and `while`,
- functions returning a single integer (`long long`).

This is used by Phase 4 ("Quantum on a Laptop") to emit a repo-local `.c` file that can be compiled
and executed with the system toolchain, exercising the C back-end in a way the Lean type-checker
cannot.
-/

namespace HeytingLean
namespace C

open HeytingLean.C

namespace Emit

private def indent (n : Nat) : String :=
  String.mk (List.replicate (2 * n) ' ')

private def paren (s : String) : String := s!"({s})"

/-- Emit a `CExpr` as a C expression string (always parenthesized for safety). -/
def expr (e : CExpr) : String :=
  match e with
  | .intLit n => toString n
  | .var x => x
  | .add e₁ e₂ => paren s!"{expr e₁} + {expr e₂}"
  | .sub e₁ e₂ => paren s!"{expr e₁} - {expr e₂}"
  | .mul e₁ e₂ => paren s!"{expr e₁} * {expr e₂}"
  | .eq e₁ e₂  => paren s!"({expr e₁} == {expr e₂} ? 1 : 0)"
  | .le e₁ e₂  => paren s!"({expr e₁} <= {expr e₂} ? 1 : 0)"

private def assignedVars : CStmt → List Ident
  | .return _ => []
  | .assign x _ => [x]
  | .seq s₁ s₂ => assignedVars s₁ ++ assignedVars s₂
  | .if_ _ t e => assignedVars t ++ assignedVars e
  | .while _ b => assignedVars b

private def locals (params : List Ident) (body : CStmt) : List Ident :=
  (assignedVars body).eraseDups.filter (fun x => !(params.contains x))

private def stmtLines : Nat → CStmt → List String
  | n, .return e => [s!"{indent n}return {expr e};"]
  | n, .assign x e => [s!"{indent n}{x} = {expr e};"]
  | n, .seq s₁ s₂ => stmtLines n s₁ ++ stmtLines n s₂
  | n, .if_ cond t e =>
      let head := indent n ++ "if (" ++ expr cond ++ " != 0) {"
      let mid := indent n ++ "} else {"
      let tail := indent n ++ "}"
      [head] ++ stmtLines (n+1) t ++ [mid] ++ stmtLines (n+1) e ++ [tail]
  | n, .while cond body =>
      let head := indent n ++ "while (" ++ expr cond ++ " != 0) {"
      let tail := indent n ++ "}"
      [head] ++ stmtLines (n+1) body ++ [tail]

private def cType : String := "long long"

private def paramsDecl (ps : List Ident) : String :=
  String.intercalate ", " (ps.map (fun p => s!"{cType} {p}"))

/-- Emit a `CFun` to a C function definition string. -/
def funDef (f : CFun) : String :=
  let ls := locals f.params f.body
  let decls := ls.map (fun x => s!"{indent 1}{cType} {x} = 0;")
  let header := s!"{cType} {f.name}({paramsDecl f.params}) " ++ "{"
  let footer := "}"
  String.intercalate "\n" ([header] ++ decls ++ stmtLines 1 f.body ++ [footer])

/-- Emit multiple `CFun` definitions, separated by blank lines. -/
def funDefs (fs : List CFun) : String :=
  String.intercalate "\n\n" (fs.map funDef)

end Emit

end C
end HeytingLean
