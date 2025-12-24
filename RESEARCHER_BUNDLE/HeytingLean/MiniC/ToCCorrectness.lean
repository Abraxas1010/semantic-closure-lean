import HeytingLean.MiniC.Syntax
import HeytingLean.MiniC.Semantics
import HeytingLean.MiniC.ToC
import HeytingLean.C.Semantics

namespace HeytingLean
namespace MiniC
namespace ToC

open HeytingLean.C

/-- Map MiniC values to C integers (booleans become `1`/`0`). -/
def valToInt : MiniC.Val → Int
  | MiniC.Val.int i  => i
  | MiniC.Val.bool b => if b then 1 else 0

/-- Translate a MiniC store into a C store by re-encoding values as ints. -/
def storeToC (σ : MiniC.Store) : C.Store :=
  fun x => (σ x).map valToInt

@[simp] theorem valToInt_natToVal (n : Nat) :
    valToInt (MiniC.natToVal n) = Int.ofNat n := by
  simp [MiniC.natToVal, valToInt]

@[simp] theorem valToInt_bool_true : valToInt (MiniC.Val.bool true) = 1 := by
  simp [valToInt]

@[simp] theorem valToInt_bool_false : valToInt (MiniC.Val.bool false) = 0 := by
  simp [valToInt]

/-- If a MiniC expression evaluates to `v`, its compiled C expression evaluates to `valToInt v`. -/
theorem compileExpr_correct
    {e : MiniC.Expr} {σ : MiniC.Store} {v : MiniC.Val}
    (h : MiniC.evalExpr e σ = some v) :
    C.evalExpr (MiniC.ToC.compileExpr e) (storeToC σ) = some (valToInt v) := by
  revert σ v h
  induction e with
  | intLit i =>
      intro σ v h
      cases h
      simp [C.evalExpr, MiniC.ToC.compileExpr, valToInt]
  | boolLit b =>
      intro σ v h
      cases h
      cases b <;> simp [C.evalExpr, MiniC.ToC.compileExpr, valToInt]
  | var x =>
      intro σ v h
      have hx : σ x = some v := h
      simp [C.evalExpr, MiniC.ToC.compileExpr, storeToC, hx, valToInt]
  | add e₁ e₂ ih₁ ih₂ =>
      intro σ v h
      cases h₁ : MiniC.evalExpr e₁ σ with
      | none =>
          simp [MiniC.evalExpr, h₁] at h
      | some v₁ =>
          cases h₂ : MiniC.evalExpr e₂ σ with
          | none =>
              simp [MiniC.evalExpr, h₁, h₂] at h
          | some v₂ =>
              cases v₁ with
              | int n₁ =>
                  cases v₂ with
                  | int n₂ =>
                      have hv : v = MiniC.Val.int (n₁ + n₂) := by
                        have h' := h
                        simp [MiniC.evalExpr, h₁, h₂] at h'
                        cases h'
                        rfl
                      subst hv
                      have hv₁ := ih₁ h₁
                      have hv₂ := ih₂ h₂
                      simp [C.evalExpr, MiniC.ToC.compileExpr, hv₁, hv₂, valToInt]
                  | bool _ =>
                      simp [MiniC.evalExpr, h₁, h₂] at h
              | bool _ =>
                  simp [MiniC.evalExpr, h₁, h₂] at h
  | sub e₁ e₂ ih₁ ih₂ =>
      intro σ v h
      cases h₁ : MiniC.evalExpr e₁ σ with
      | none =>
          simp [MiniC.evalExpr, h₁] at h
      | some v₁ =>
          cases h₂ : MiniC.evalExpr e₂ σ with
          | none =>
              simp [MiniC.evalExpr, h₁, h₂] at h
          | some v₂ =>
              cases v₁ with
              | int n₁ =>
                  cases v₂ with
                  | int n₂ =>
                      have hv : v = MiniC.Val.int (n₁ - n₂) := by
                        have h' := h
                        simp [MiniC.evalExpr, h₁, h₂] at h'
                        cases h'
                        rfl
                      subst hv
                      have hv₁ := ih₁ h₁
                      have hv₂ := ih₂ h₂
                      simp [C.evalExpr, MiniC.ToC.compileExpr, hv₁, hv₂, valToInt]
                  | bool _ =>
                      simp [MiniC.evalExpr, h₁, h₂] at h
              | bool _ =>
                  simp [MiniC.evalExpr, h₁, h₂] at h
  | mul e₁ e₂ ih₁ ih₂ =>
      intro σ v h
      cases h₁ : MiniC.evalExpr e₁ σ with
      | none =>
          simp [MiniC.evalExpr, h₁] at h
      | some v₁ =>
          cases h₂ : MiniC.evalExpr e₂ σ with
          | none =>
              simp [MiniC.evalExpr, h₁, h₂] at h
          | some v₂ =>
              cases v₁ with
              | int n₁ =>
                  cases v₂ with
                  | int n₂ =>
                      have hv : v = MiniC.Val.int (n₁ * n₂) := by
                        have h' := h
                        simp [MiniC.evalExpr, h₁, h₂] at h'
                        cases h'
                        rfl
                      subst hv
                      have hv₁ := ih₁ h₁
                      have hv₂ := ih₂ h₂
                      simp [C.evalExpr, MiniC.ToC.compileExpr, hv₁, hv₂, valToInt]
                  | bool _ =>
                      simp [MiniC.evalExpr, h₁, h₂] at h
              | bool _ =>
                  simp [MiniC.evalExpr, h₁, h₂] at h
  | le e₁ e₂ ih₁ ih₂ =>
      intro σ v h
      cases h₁ : MiniC.evalExpr e₁ σ with
      | none =>
          simp [MiniC.evalExpr, h₁] at h
      | some v₁ =>
          cases h₂ : MiniC.evalExpr e₂ σ with
          | none =>
              simp [MiniC.evalExpr, h₁, h₂] at h
          | some v₂ =>
              cases v₁ with
              | int n₁ =>
                  cases v₂ with
                  | int n₂ =>
                      have hv : v = MiniC.Val.bool (decide (n₁ ≤ n₂)) := by
                        have h' := h
                        simp [MiniC.evalExpr, h₁, h₂] at h'
                        cases h'
                        rfl
                      subst hv
                      have hv₁ := ih₁ h₁
                      have hv₂ := ih₂ h₂
                      simp [C.evalExpr, MiniC.ToC.compileExpr, hv₁, hv₂, valToInt]
                  | bool _ =>
                      simp [MiniC.evalExpr, h₁, h₂] at h
              | bool _ =>
                  simp [MiniC.evalExpr, h₁, h₂] at h
  | eq e₁ e₂ ih₁ ih₂ =>
      intro σ v h
      cases h₁ : MiniC.evalExpr e₁ σ with
      | none =>
          simp [MiniC.evalExpr, h₁] at h
      | some v₁ =>
          cases h₂ : MiniC.evalExpr e₂ σ with
          | none =>
              simp [MiniC.evalExpr, h₁, h₂] at h
          | some v₂ =>
              cases v₁ with
              | int n₁ =>
                  cases v₂ with
                  | int n₂ =>
                      have hv : v = MiniC.Val.bool (decide (n₁ = n₂)) := by
                        have h' := h
                        simp [MiniC.evalExpr, h₁, h₂] at h'
                        cases h'
                        rfl
                      subst hv
                      have hv₁ := ih₁ h₁
                      have hv₂ := ih₂ h₂
                      simp [C.evalExpr, MiniC.ToC.compileExpr, hv₁, hv₂, valToInt]
                  | bool _ =>
                      simp [MiniC.evalExpr, h₁, h₂] at h
              | bool b₁ =>
                  cases v₂ with
                  | bool b₂ =>
                      have hv : v = MiniC.Val.bool (decide (b₁ = b₂)) := by
                        have h' := h
                        simp [MiniC.evalExpr, h₁, h₂] at h'
                        cases h'
                        rfl
                      subst hv
                      have hv₁ := ih₁ h₁
                      have hv₂ := ih₂ h₂
                      simp [C.evalExpr, MiniC.ToC.compileExpr, hv₁, hv₂, valToInt] at *
                      cases b₁ <;> cases b₂ <;> simp
                  | int _ =>
                      simp [MiniC.evalExpr, h₁, h₂] at h
  | not e ih =>
      intro σ v h
      cases hEval : MiniC.evalExpr e σ with
      | none =>
          simp [MiniC.evalExpr, hEval] at h
      | some v' =>
          cases v' with
          | bool b =>
              have hv : v = MiniC.Val.bool (!b) := by
                have h' := h
                simp [MiniC.evalExpr, hEval] at h'
                cases h'
                rfl
              subst hv
              have hv' := ih hEval
              simp [C.evalExpr, MiniC.ToC.compileExpr, hv', valToInt]
          | int _ =>
              simp [MiniC.evalExpr, hEval] at h
  | and e₁ e₂ ih₁ ih₂ =>
      intro σ v h
      cases h₁ : MiniC.evalExpr e₁ σ with
      | none =>
          simp [MiniC.evalExpr, h₁] at h
      | some v₁ =>
          cases h₂ : MiniC.evalExpr e₂ σ with
          | none =>
              simp [MiniC.evalExpr, h₁, h₂] at h
          | some v₂ =>
              cases v₁ with
              | bool b₁ =>
                  cases v₂ with
                  | bool b₂ =>
                      have hv : v = MiniC.Val.bool (b₁ && b₂) := by
                        have h' := h
                        simp [MiniC.evalExpr, h₁, h₂] at h'
                        cases h'
                        rfl
                      subst hv
                      have hv₁ := ih₁ h₁
                      have hv₂ := ih₂ h₂
                      simp [C.evalExpr, MiniC.ToC.compileExpr, hv₁, hv₂, valToInt] at *
                      cases b₁ <;> cases b₂ <;> simp
                  | int _ =>
                      simp [MiniC.evalExpr, h₁, h₂] at h
              | int _ =>
                  simp [MiniC.evalExpr, h₁, h₂] at h
  | or e₁ e₂ ih₁ ih₂ =>
      intro σ v h
      cases h₁ : MiniC.evalExpr e₁ σ with
      | none =>
          simp [MiniC.evalExpr, h₁] at h
      | some v₁ =>
          cases h₂ : MiniC.evalExpr e₂ σ with
          | none =>
              simp [MiniC.evalExpr, h₁, h₂] at h
          | some v₂ =>
              cases v₁ with
              | bool b₁ =>
                  cases v₂ with
                  | bool b₂ =>
                      have hv : v = MiniC.Val.bool (b₁ || b₂) := by
                        have h' := h
                        simp [MiniC.evalExpr, h₁, h₂] at h'
                        cases h'
                        rfl
                      subst hv
                      have hv₁ := ih₁ h₁
                      have hv₂ := ih₂ h₂
                      simp [C.evalExpr, MiniC.ToC.compileExpr, hv₁, hv₂, valToInt] at *
                      cases b₁ <;> cases b₂ <;> simp
                  | int _ =>
                      simp [MiniC.evalExpr, h₁, h₂] at h
              | int _ =>
                  simp [MiniC.evalExpr, h₁, h₂] at h

/-! ## Fragment statements + runners

The fragment compiler (`LambdaIR → MiniC`) emits only `return`/`if` statements.
This section connects the fragment semantics of MiniC (`execFrag`) to the fragment
semantics of the tiny C subset (`execFragC`/`runCFunFrag`).
-/

/-- Map a MiniC fragment execution result into the tiny C result type. -/
def execResultToC : MiniC.ExecResult → C.ExecResult
  | MiniC.ExecResult.normal σ => C.ExecResult.normal (storeToC σ)
  | MiniC.ExecResult.returned v => C.ExecResult.returned (valToInt v)

/-- If a MiniC value parses as a nat `n`, its C integer encoding is `Int.ofNat n`. -/
theorem valToInt_of_asNat? {v : MiniC.Val} {n : Nat} (h : MiniC.Val.asNat? v = some n) :
    valToInt v = Int.ofNat n := by
  cases v with
  | int i =>
      dsimp [MiniC.Val.asNat?] at h
      by_cases hi : i ≥ 0
      · have ht : Int.toNat i = n := by
          have h' : some (Int.toNat i) = some n := by
            simpa [hi] using h
          exact Option.some.inj h'
        calc
          valToInt (MiniC.Val.int i) = i := by simp [valToInt]
          _ = (Int.ofNat (Int.toNat i)) := by
            simpa using (Int.toNat_of_nonneg hi).symm
          _ = Int.ofNat n := by simpa [ht]
      · simp [hi] at h
  | bool b =>
      cases h

/-- Statement-level correctness for the while-free fragment: `execFrag` → `execFragC`. -/
theorem compileStmt_correct
    {s : MiniC.Stmt} {σ : MiniC.Store} {r : MiniC.ExecResult}
    (h : MiniC.execFrag s σ = some r) :
    C.execFragC (MiniC.ToC.compileStmt s) (storeToC σ) = some (execResultToC r) := by
  induction s generalizing σ r with
  | «return» e =>
      cases r with
      | normal σ' =>
          cases hv : MiniC.evalExpr e σ <;> simp [MiniC.execFrag, hv] at h
      | returned v =>
          have hEval : MiniC.evalExpr e σ = some v := by
            cases hv : MiniC.evalExpr e σ with
            | none =>
                have : False := by
                  simp [MiniC.execFrag, hv] at h
                cases this
            | some v' =>
                have hv' : v' = v := by
                  simpa [MiniC.execFrag, hv] using h
                simpa [hv'] using hv
          have hC := compileExpr_correct (σ := σ) (v := v) hEval
          simp [MiniC.ToC.compileStmt, C.execFragC, execResultToC, hC]
  | if_ cond then_ else_ ihT ihE =>
      cases hEval : MiniC.evalExpr cond σ with
      | none =>
          simp [MiniC.execFrag, hEval] at h
      | some v =>
          cases v with
          | int i =>
              simp [MiniC.execFrag, hEval] at h
          | bool b =>
              have hCCond := compileExpr_correct (σ := σ) (v := MiniC.Val.bool b) hEval
              cases b with
              | false =>
                  have hE : MiniC.execFrag else_ σ = some r := by
                    simpa [MiniC.execFrag, hEval] using h
                  have ih := ihE (σ := σ) (r := r) hE
                  have hC0 : C.evalExpr (MiniC.ToC.compileExpr cond) (storeToC σ) = some 0 := by
                    simpa [valToInt] using hCCond
                  simpa [MiniC.ToC.compileStmt, C.execFragC, hC0, execResultToC] using ih
              | true =>
                  have hT : MiniC.execFrag then_ σ = some r := by
                    simpa [MiniC.execFrag, hEval] using h
                  have ih := ihT (σ := σ) (r := r) hT
                  have hC1 : C.evalExpr (MiniC.ToC.compileExpr cond) (storeToC σ) = some 1 := by
                    simpa [valToInt] using hCCond
                  have hnz : (1 : Int) ≠ 0 := by decide
                  simpa [MiniC.ToC.compileStmt, C.execFragC, hC1, hnz, execResultToC] using ih
  | skip =>
      simp [MiniC.execFrag] at h
  | assign x rhs =>
      simp [MiniC.execFrag] at h
  | seq s₁ s₂ ih₁ ih₂ =>
      simp [MiniC.execFrag] at h
  | «while» cond body =>
      simp [MiniC.execFrag] at h

/-- Runner correctness: successful `MiniC.runNatFunFrag` implies successful `C.runCFunFrag`. -/
theorem runNatFunFrag_correct_toC
    (fn : MiniC.Fun) (paramName : String) (n out : Nat)
    (h : MiniC.runNatFunFrag fn paramName n = some out) :
    C.runCFunFrag (MiniC.ToC.compileFun fn) [Int.ofNat n] = some (Int.ofNat out) := by
  by_cases hParams : fn.params = [paramName]
  · let σ : MiniC.Store :=
      fun x => if x = paramName then some (MiniC.natToVal n) else none
    have hTail :
        (match MiniC.execFrag fn.body σ with
          | some (MiniC.ExecResult.returned v) => MiniC.Val.asNat? v
          | _ => none) = some out := by
      simpa [MiniC.runNatFunFrag, hParams, σ] using h
    cases hExec : MiniC.execFrag fn.body σ with
    | none =>
        simp [hExec] at hTail
    | some res =>
        cases res with
        | normal σ' =>
            simp [hExec] at hTail
        | returned v =>
            have hAsNat : MiniC.Val.asNat? v = some out := by
              simpa [hExec] using hTail
            have hVal : valToInt v = Int.ofNat out :=
              valToInt_of_asNat? (v := v) (n := out) hAsNat
            have hStmt :=
              compileStmt_correct (s := fn.body) (σ := σ) (r := MiniC.ExecResult.returned v) hExec
            have hCExec :
                C.execFragC (MiniC.ToC.compileStmt fn.body) (storeToC σ)
                  = some (C.ExecResult.returned (Int.ofNat out)) := by
              simpa [execResultToC, hVal] using hStmt
            -- run the compiled C function with the corresponding integer argument
            have hBind : C.bindParams fn.params [(n : Int)] = some (storeToC σ) := by
              -- reduce `bindParams` to the singleton-binding store, then identify it with `storeToC σ`
              simp [C.bindParams, hParams]
              ext x
              simp [σ, storeToC, valToInt, MiniC.natToVal]
            dsimp [C.runCFunFrag, MiniC.ToC.compileFun]
            simp [hBind]
            simp [hCExec]
  · have hGuard : (guard (fn.params = [paramName]) : Option Unit) = none := by
      simp [guard, hParams]
      rfl
    have hNone : MiniC.runNatFunFrag fn paramName n = none := by
      simp [MiniC.runNatFunFrag, hGuard]
    have : False := by
      simpa [hNone] using h
    cases this

end ToC
end MiniC
end HeytingLean
