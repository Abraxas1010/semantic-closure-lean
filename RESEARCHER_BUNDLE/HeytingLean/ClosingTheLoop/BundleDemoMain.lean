import HeytingLean.ClosingTheLoop
import HeytingLean.LambdaIR.NatCompileFrag
import HeytingLean.MiniC.ToC
import HeytingLean.C.Emit

/-!
# ClosingTheLoop verification bundle: demo executable

This `main` is *not* part of the paper’s mathematics. It exists to give external
researchers a concrete, reproducible artifact pipeline:

`LambdaIR term → MiniC AST → tiny-C AST → emitted C source`

The verifier script builds this executable (exercising Lean's C backend) and runs it to
write artifacts under `artifacts/compiler/`.
-/

namespace HeytingLean
namespace ClosingTheLoop

namespace BundleDemo

open HeytingLean.LambdaIR

private def varIndex : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Nat
  | _, _, .vz => 0
  | _, _, .vs v => varIndex v + 1

private partial def termToString : {Γ : Ctx} → {τ : Ty} → Term Γ τ → String
  | _, _, .var v => s!"(var {varIndex v})"
  | _, _, .lam body => s!"(lam {termToString body})"
  | _, _, .app f x => s!"(app {termToString f} {termToString x})"
  | _, _, .pair t₁ t₂ => s!"(pair {termToString t₁} {termToString t₂})"
  | _, _, .fst t => s!"(fst {termToString t})"
  | _, _, .snd t => s!"(snd {termToString t})"
  | _, _, .inl t => s!"(inl {termToString t})"
  | _, _, .inr t => s!"(inr {termToString t})"
  | _, _, .matchSum s k₁ k₂ => s!"(matchSum {termToString s} {termToString k₁} {termToString k₂})"
  | _, _, .if_ c t e => s!"(if {termToString c} {termToString t} {termToString e})"
  | _, _, .constNat n => s!"(nat {n})"
  | _, _, .constBool b => s!"(bool {b})"
  | _, _, .primAddNat => "(primAddNat)"
  | _, _, .primEqNat => "(primEqNat)"

private def add1Term : Term [] (HeytingLean.Core.Ty.arrow HeytingLean.Core.Ty.nat HeytingLean.Core.Ty.nat) :=
  Term.lam
    (Term.app (Term.app Term.primAddNat (Term.var HeytingLean.Core.Var.vz)) (Term.constNat 1))

private def writeFileSafely (path : System.FilePath) (contents : String) : IO Unit := do
  try
    match path.parent with
    | some dir => IO.FS.createDirAll dir
    | none => pure ()
    IO.FS.writeFile path contents
  catch e =>
    IO.eprintln s!"[closing_the_loop_bundle_demo] write failed: {path}: {e}"

private def driverC (funName : String) (x : Nat) : String :=
  String.intercalate "\n"
    [ ""
    , ""
    , "int main(void) {"
    , s!"  long long x = {x};"
    , s!"  printf(\"%lld\\n\", {funName}(x));"
    , "  return 0;"
    , "}"
    , ""
    ]

def main (_argv : List String) : IO UInt32 := do
  try
    IO.println "[closing_the_loop_bundle_demo] generating LambdaIR + C artifacts"

    let funName := "add1"
    let paramName := "x"
    let t := add1Term
    let compiledMiniC := LambdaIR.NatCompileFrag.compileNatFunFrag funName paramName t
    let cFun := HeytingLean.MiniC.ToC.compileFun compiledMiniC

    let sample : Nat := 41
    let outLean :=
      LambdaIR.evalClosed (LambdaIR.Term.app t (LambdaIR.Term.constNat sample))
    let outMiniC :=
      HeytingLean.MiniC.runNatFunFrag compiledMiniC paramName sample

    let outNat : Nat := outLean
    IO.println s!"[demo] evalClosed add1({sample}) = {outNat}"
    IO.println s!"[demo] runNatFunFrag add1({sample}) = {reprStr outMiniC}"

    -- “Lambda” artifact (human-readable LambdaIR AST)
    writeFileSafely
      "artifacts/compiler/ir/add1.lambdair.txt"
      (termToString t ++ "\n")

    -- MiniC artifact (repr)
    writeFileSafely
      "artifacts/compiler/ir/add1.minic.txt"
      (reprStr compiledMiniC ++ "\n")

    -- Emitted C artifact (compile via `cc` in the verifier script)
    let cProgram :=
      "#include <stdio.h>\n\n" ++ HeytingLean.C.Emit.funDef cFun ++ driverC funName sample
    writeFileSafely
      "artifacts/compiler/c/add1.c"
      cProgram

    IO.println "[closing_the_loop_bundle_demo] done"
    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"[closing_the_loop_bundle_demo] error: {e}"
    return (1 : UInt32)

end BundleDemo

end ClosingTheLoop
end HeytingLean

/-! Expose entry point for the Lake executable target. -/

def main (args : List String) : IO UInt32 :=
  HeytingLean.ClosingTheLoop.BundleDemo.main args
