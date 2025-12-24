import Mathlib.Data.FinEnum
import Mathlib.Tactic

import HeytingLean.MiniC.Syntax

/-!
# MiniC back-end for SDE integrators (Phase 3)

This module generates *imperative* MiniC code for SDE stepping.

Important caveat:
- The mathematical SDE IR in `HeytingLean.LambdaIR.SDE` is over `ℝ` and represents functions
  `Vec ι → Vec ι` and `Vec ι → Mat ι κ`. That is **not directly compilable** today.
- Phase 3 therefore introduces a *compilable SDE interface* where drift and diffusion are given as
  **MiniC expressions** over a fixed naming scheme for the current state variables.

This keeps the pipeline honest: no hidden axioms, and any discretization/approximation is exposed
at the interface boundary.
-/

namespace HeytingLean
namespace MiniC
namespace SDE

open HeytingLean.MiniC

/-! ## Utility: enumerate finite index types as lists -/

private def elemsList (α : Type) [FinEnum α] : List α :=
  FinEnum.toList α

/-! ## Naming scheme -/

/-- Codegen names for a state index type `ι` and noise index type `κ`. -/
structure Names (ι : Type) (κ : Type) [FinEnum ι] [FinEnum κ] where
  dt : String := "dt"
  x : ι → String
  dW : κ → String
  xPred : ι → String
  xNext : ι → String
  dWStep : Nat → κ → String

namespace Names

variable {ι : Type} {κ : Type} [FinEnum ι] [FinEnum κ]

private def idxι (i : ι) : Nat := ((FinEnum.equiv (α := ι)) i).val
private def idxκ (k : κ) : Nat := ((FinEnum.equiv (α := κ)) k).val

/-- Default deterministic variable naming: `x_0`, `x_1`, … and similarly for `dW`. -/
def default : Names ι κ :=
  { x := fun i => s!"x_{idxι i}"
    dW := fun k => s!"dW_{idxκ k}"
    xPred := fun i => s!"xPred_{idxι i}"
    xNext := fun i => s!"xNext_{idxι i}"
    dWStep := fun t k => s!"dW_{t}_{idxκ k}" }

/-- Parameter list for a state vector `x : ι → Int` (flattened). -/
def xParams (N : Names ι κ) : List String :=
  (elemsList ι).map N.x

/-- Parameter list for a single-step noise vector `dW : κ → Int` (flattened). -/
def dWParams (N : Names ι κ) : List String :=
  (elemsList κ).map N.dW

/-- Parameter list for a `steps`-long noise schedule (flattened by step then coordinate). -/
def dWParamsSteps (N : Names ι κ) (steps : Nat) : List String :=
  (List.range steps).foldr (fun t acc => (elemsList κ).map (fun k => N.dWStep t k) ++ acc) []

end Names

/-! ## Compilable SDE interface -/

/-- A compilable SDE interface: drift and diffusion provided as MiniC expressions.

The expressions are expected to reference state variables using the naming scheme `Names.x`.
They may also reference additional free variables (constants/parameters) if the caller includes
them in the final function parameter lists. -/
structure CompilableSDESystem (ι : Type) (κ : Type) [FinEnum ι] [FinEnum κ] where
  drift : Names ι κ → ι → Expr
  diffusion : Names ι κ → ι → κ → Expr

namespace Expr

/-- Rename variables in a MiniC expression. -/
def rename (ρ : String → String) : Expr → Expr
  | Expr.var x => Expr.var (ρ x)
  | Expr.intLit n => Expr.intLit n
  | Expr.boolLit b => Expr.boolLit b
  | Expr.add e₁ e₂ => Expr.add (rename ρ e₁) (rename ρ e₂)
  | Expr.sub e₁ e₂ => Expr.sub (rename ρ e₁) (rename ρ e₂)
  | Expr.mul e₁ e₂ => Expr.mul (rename ρ e₁) (rename ρ e₂)
  | Expr.le e₁ e₂ => Expr.le (rename ρ e₁) (rename ρ e₂)
  | Expr.eq e₁ e₂ => Expr.eq (rename ρ e₁) (rename ρ e₂)
  | Expr.not e => Expr.not (rename ρ e)
  | Expr.and e₁ e₂ => Expr.and (rename ρ e₁) (rename ρ e₂)
  | Expr.or e₁ e₂ => Expr.or (rename ρ e₁) (rename ρ e₂)

end Expr

/-! ## Code generation helpers -/

private def sumExpr {α : Type} (xs : List α) (f : α → Expr) : Expr :=
  xs.foldl (fun acc a => Expr.add acc (f a)) (Expr.intLit 0)

private def seq1 : List Stmt → Stmt
  | [] => Stmt.return (Expr.intLit 0)
  | s :: ss => ss.foldl (fun acc t => Stmt.seq acc t) s

private def listBind {α β : Type} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (fun a acc => f a ++ acc) []

private def renameXToXPred
    {ι : Type} {κ : Type} [FinEnum ι] [FinEnum κ]
    (N : Names ι κ) (name : String) : String :=
  (elemsList ι).foldl (fun acc i => if acc = N.x i then N.xPred i else acc) name

private def div2Stmt (inExpr : Expr) (outVar tmpVar qVar : String) : Stmt :=
  let initTmp : Stmt := Stmt.assign tmpVar inExpr
  let isNeg : Expr := Expr.le (Expr.var tmpVar) (Expr.intLit (-1))
  let loopCond : Expr := Expr.le (Expr.intLit 2) (Expr.var tmpVar)  -- 2 ≤ tmp
  let loopBody : Stmt :=
    Stmt.seq
      (Stmt.assign tmpVar (Expr.sub (Expr.var tmpVar) (Expr.intLit 2)))
      (Stmt.assign qVar (Expr.add (Expr.var qVar) (Expr.intLit 1)))
  let loop : Stmt := Stmt.while loopCond loopBody
  let negBranch : Stmt :=
    seq1
      [ Stmt.assign tmpVar (Expr.sub (Expr.intLit 0) (Expr.var tmpVar))
      , Stmt.assign qVar (Expr.intLit 0)
      , loop
      , Stmt.assign outVar (Expr.sub (Expr.intLit 0) (Expr.var qVar))
      ]
  let posBranch : Stmt :=
    seq1
      [ Stmt.assign qVar (Expr.intLit 0)
      , loop
      , Stmt.assign outVar (Expr.var qVar)
      ]
  Stmt.seq initTmp (Stmt.if_ isNeg negBranch posBranch)

/-! ## Euler and Stratonovich step codegen (per coordinate) -/

section StepCodegen

variable {ι : Type} {κ : Type} [FinEnum ι] [FinEnum κ]

private def diffusionMulSum
    (S : CompilableSDESystem ι κ) (N : Names ι κ) (dWName : κ → String) (i : ι) : Expr :=
  sumExpr (elemsList κ) (fun k => Expr.mul (S.diffusion N i k) (Expr.var (dWName k)))

private def eulerCoordExpr
    (S : CompilableSDESystem ι κ) (N : Names ι κ) (dWName : κ → String) (i : ι) : Expr :=
  Expr.add (Expr.var (N.x i))
    (Expr.add
      (Expr.mul (Expr.var N.dt) (S.drift N i))
      (diffusionMulSum (S := S) (N := N) dWName i))

private def driftPredExpr (S : CompilableSDESystem ι κ) (N : Names ι κ) (i : ι) : Expr :=
  Expr.rename (fun nm => renameXToXPred (N := N) nm) (S.drift N i)

private def diffusionPredExpr (S : CompilableSDESystem ι κ) (N : Names ι κ) (i : ι) (k : κ) : Expr :=
  Expr.rename (fun nm => renameXToXPred (N := N) nm) (S.diffusion N i k)

private def stratonovichCoordBody (S : CompilableSDESystem ι κ) (N : Names ι κ) (i : ι) : Stmt :=
  let xPredAssigns : List Stmt :=
    (elemsList ι).map (fun j => Stmt.assign (N.xPred j) (eulerCoordExpr (S := S) (N := N) N.dW j))
  let driftSum : Expr := Expr.add (S.drift N i) (driftPredExpr (S := S) (N := N) i)
  let driftTerm : Expr := Expr.mul (Expr.var N.dt) driftSum
  let diffTerm : Expr :=
    sumExpr (elemsList κ) (fun k =>
      Expr.mul (Expr.add (S.diffusion N i k) (diffusionPredExpr (S := S) (N := N) i k)) (Expr.var (N.dW k)))
  let idx : Nat := ((FinEnum.equiv (α := ι)) i).val
  let halfDrift : String := s!"halfDrift_{idx}"
  let halfDiff : String := s!"halfDiff_{idx}"
  let driftTmp : String := s!"tmpDrift_{idx}"
  let driftQ : String := s!"qDrift_{idx}"
  let diffTmp : String := s!"tmpDiff_{idx}"
  let diffQ : String := s!"qDiff_{idx}"
  let divDrift : Stmt := div2Stmt driftTerm halfDrift driftTmp driftQ
  let divDiff : Stmt := div2Stmt diffTerm halfDiff diffTmp diffQ
  let retExpr : Expr :=
    Expr.add (Expr.var (N.x i)) (Expr.add (Expr.var halfDrift) (Expr.var halfDiff))
  seq1 (xPredAssigns ++ [divDrift, divDiff, Stmt.return retExpr])

end StepCodegen

/-! ## Full translation to a MiniC program -/

section Translate

variable {ι : Type} {κ : Type} [FinEnum ι] [FinEnum κ]

private def funName (pfx : String) (n : Nat) : String :=
  s!"{pfx}_{n}"

private def funName2 (pfx : String) (n m : Nat) : String :=
  s!"{pfx}_{n}_{m}"

private def idxι (i : ι) : Nat := ((FinEnum.equiv (α := ι)) i).val
private def idxκ (k : κ) : Nat := ((FinEnum.equiv (α := κ)) k).val

private def driftFun (S : CompilableSDESystem ι κ) (N : Names ι κ) (i : ι) : Fun :=
  { name := funName "sde_drift" (idxι i)
    params := N.xParams
    body := Stmt.return (S.drift N i) }

private def diffusionFun (S : CompilableSDESystem ι κ) (N : Names ι κ) (i : ι) (k : κ) : Fun :=
  { name := funName2 "sde_diffusion" (idxι i) (idxκ k)
    params := N.xParams
    body := Stmt.return (S.diffusion N i k) }

private def eulerStepFun (S : CompilableSDESystem ι κ) (N : Names ι κ) (i : ι) : Fun :=
  { name := funName "sde_euler_step" (idxι i)
    params := N.dt :: (N.xParams ++ N.dWParams)
    body := Stmt.return (eulerCoordExpr (S := S) (N := N) N.dW i) }

private def stratonovichStepFun (S : CompilableSDESystem ι κ) (N : Names ι κ) (i : ι) : Fun :=
  { name := funName "sde_stratonovich_step" (idxι i)
    params := N.dt :: (N.xParams ++ N.dWParams)
    body := stratonovichCoordBody (S := S) (N := N) i }

private def simulateEulerCoordBody
    (S : CompilableSDESystem ι κ) (N : Names ι κ) (steps : Nat) (i : ι) : Stmt :=
  let xNextAssigns (t : Nat) : List Stmt :=
    (elemsList ι).map (fun j =>
      Stmt.assign (N.xNext j) (eulerCoordExpr (S := S) (N := N) (N.dWStep t) j))
  let commit : List Stmt :=
    (elemsList ι).map (fun j => Stmt.assign (N.x j) (Expr.var (N.xNext j)))
  let perStep (t : Nat) : List Stmt := xNextAssigns t ++ commit
  let stepsStmts : List Stmt := listBind (List.range steps) perStep
  seq1 (stepsStmts ++ [Stmt.return (Expr.var (N.x i))])

private def simulateEulerFun
    (S : CompilableSDESystem ι κ) (N : Names ι κ) (steps : Nat) (i : ι) : Fun :=
  { name := funName "sde_simulate_euler" (idxι i)
    params := N.dt :: (N.xParams ++ N.dWParamsSteps steps)
    body := simulateEulerCoordBody (S := S) (N := N) steps i }

private def simulateStratonovichStepCoord (S : CompilableSDESystem ι κ) (N : Names ι κ) (t : Nat)
    (i : ι) : List Stmt :=
  let xPredAssigns : List Stmt :=
    (elemsList ι).map (fun j =>
      Stmt.assign (N.xPred j) (eulerCoordExpr (S := S) (N := N) (N.dWStep t) j))
  let driftSum : Expr := Expr.add (S.drift N i) (driftPredExpr (S := S) (N := N) i)
  let driftTerm : Expr := Expr.mul (Expr.var N.dt) driftSum
  let diffTerm : Expr :=
    sumExpr (elemsList κ) (fun k =>
      Expr.mul (Expr.add (S.diffusion N i k) (diffusionPredExpr (S := S) (N := N) i k))
        (Expr.var (N.dWStep t k)))
  let halfDrift : String := s!"halfDrift_s{t}_{idxι i}"
  let halfDiff : String := s!"halfDiff_s{t}_{idxι i}"
  let driftTmp : String := s!"tmpDrift_s{t}_{idxι i}"
  let driftQ : String := s!"qDrift_s{t}_{idxι i}"
  let diffTmp : String := s!"tmpDiff_s{t}_{idxι i}"
  let diffQ : String := s!"qDiff_s{t}_{idxι i}"
  let divDrift : Stmt := div2Stmt driftTerm halfDrift driftTmp driftQ
  let divDiff : Stmt := div2Stmt diffTerm halfDiff diffTmp diffQ
  let xNextExpr : Expr :=
    Expr.add (Expr.var (N.x i)) (Expr.add (Expr.var halfDrift) (Expr.var halfDiff))
  xPredAssigns ++ [divDrift, divDiff, Stmt.assign (N.xNext i) xNextExpr]

private def simulateStratonovichCoordBody
    (S : CompilableSDESystem ι κ) (N : Names ι κ) (steps : Nat) (i : ι) : Stmt :=
  let stepBlock (t : Nat) : List Stmt :=
    let buildXNext : List Stmt :=
      listBind (elemsList ι) (fun j => simulateStratonovichStepCoord (S := S) (N := N) (t := t) j)
    let commit : List Stmt :=
      (elemsList ι).map (fun j => Stmt.assign (N.x j) (Expr.var (N.xNext j)))
    buildXNext ++ commit
  let bodyStmts : List Stmt := listBind (List.range steps) stepBlock
  seq1 (bodyStmts ++ [Stmt.return (Expr.var (N.x i))])

private def simulateStratonovichFun
    (S : CompilableSDESystem ι κ) (N : Names ι κ) (steps : Nat) (i : ι) : Fun :=
  { name := funName "sde_simulate_stratonovich" (idxι i)
    params := N.dt :: (N.xParams ++ N.dWParamsSteps steps)
    body := simulateStratonovichCoordBody (S := S) (N := N) steps i }

/-- Translate a compilable SDE system to a MiniC program.

The generated program contains:
- per-coordinate `drift` functions,
- per-entry `diffusion` functions,
- per-coordinate Euler and Stratonovich stepping functions,
- per-coordinate unrolled trajectory simulators for a fixed `steps` (Euler + Stratonovich).

Because MiniC has only scalar returns, the vector-valued maps are exposed as families of functions
indexed by coordinates. -/
def translateSDESystem (S : CompilableSDESystem ι κ) (steps : Nat := 0) : Program :=
  let N : Names ι κ := Names.default
  let is := elemsList ι
  let ks := elemsList κ
  let driftDefs := is.map (driftFun (S := S) (N := N))
  let diffDefs := listBind is (fun i => ks.map (fun k => diffusionFun (S := S) (N := N) i k))
  let eulerDefs := is.map (eulerStepFun (S := S) (N := N))
  let stratDefs := is.map (stratonovichStepFun (S := S) (N := N))
  let simEulerDefs := is.map (simulateEulerFun (S := S) (N := N) steps)
  let simStratDefs := is.map (simulateStratonovichFun (S := S) (N := N) steps)
  let main : Fun :=
    { name := "sde_main"
      params := []
      body := Stmt.return (Expr.intLit 0) }
  { defs := driftDefs ++ diffDefs ++ eulerDefs ++ stratDefs ++ simEulerDefs ++ simStratDefs
    main := main }

end Translate

end SDE
end MiniC
end HeytingLean
