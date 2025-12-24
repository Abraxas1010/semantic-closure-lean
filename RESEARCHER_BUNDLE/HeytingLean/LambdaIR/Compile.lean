/-
  Certified compilation helpers for existing LambdaIR fragment compilers.

  This file intentionally wraps *existing* fragment-correctness theorems
  (Nat¹ and Nat²) into MLTT-style `Certified` artifacts.
-/

import HeytingLean.Certified.Basic
import HeytingLean.LambdaIR.NatCompileFragCorrectness
import HeytingLean.LambdaIR.Nat2CompileFragCorrectness

namespace HeytingLean
namespace LambdaIR

open HeytingLean.Certified
open HeytingLean.Core

namespace CertifiedCompile

/-- Spec for a compiled Nat→Nat fragment function. -/
def Nat1CompiledSpec (funName paramName : String)
    (t : Term [] (Ty.arrow Ty.nat Ty.nat)) (f : HeytingLean.MiniC.Fun) : Prop :=
  f.name = funName ∧
    ∀ n,
      HeytingLean.MiniC.runNatFunFrag f paramName n =
        some (LambdaIR.evalClosed (LambdaIR.Term.app t (LambdaIR.Term.constNat n)))

/-- Compile a Nat→Nat fragment function, returning the compiler output with its proof. -/
def compileNat1Fun (funName paramName : String)
    {t : Term [] (Ty.arrow Ty.nat Ty.nat)}
    (ht : NatFunFragment.IsNatFun t) :
    Certified HeytingLean.MiniC.Fun (Nat1CompiledSpec funName paramName t) :=
  ⟨NatCompileFrag.compileNatFunFrag funName paramName t,
    by
      have hName : (NatCompileFrag.compileNatFunFrag funName paramName t).name = funName := by
        rcases ht with ⟨body, rfl, hBody⟩
        rfl
      refine ⟨hName, ?_⟩
      have h :=
        NatCompileFrag.compileNatFunFrag_correct
          (funName := funName) (paramName := paramName) (t := t) ht
      intro n
      exact h n⟩

/-- Spec for a compiled Nat→Nat→Nat (curried) fragment function. -/
def Nat2CompiledSpec (funName : String)
    (t : Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat)))
    (f : HeytingLean.MiniC.Fun) : Prop :=
  f.name = funName ∧
    f.params = [Nat2CompileFragCorrectness.param1, Nat2CompileFragCorrectness.param2] ∧
    ∀ x y,
      HeytingLean.MiniC.runNat2FunFrag
          f Nat2CompileFragCorrectness.param1 Nat2CompileFragCorrectness.param2 x y
        = some (LambdaIR.evalClosed
            (Term.app (Term.app t (Term.constNat x)) (Term.constNat y)))

/-- Compile a Nat→Nat→Nat fragment function (fixed param names `"x"`, `"y"`), with certificate. -/
def compileNat2Fun (funName : String)
    {t : Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))}
    (ht : Nat2FunFragment.IsNat2Fun t) :
    Certified HeytingLean.MiniC.Fun (Nat2CompiledSpec funName t) :=
  ⟨Nat2CompileFrag.compileNat2FunFrag funName
      Nat2CompileFragCorrectness.param1 Nat2CompileFragCorrectness.param2 t,
    by
      have hName :
          (Nat2CompileFrag.compileNat2FunFrag funName
              Nat2CompileFragCorrectness.param1 Nat2CompileFragCorrectness.param2 t).name
            = funName := by
        rcases ht with ⟨body, rfl, hBody⟩
        rfl
      have hParams :
          (Nat2CompileFrag.compileNat2FunFrag funName
              Nat2CompileFragCorrectness.param1 Nat2CompileFragCorrectness.param2 t).params
            = [Nat2CompileFragCorrectness.param1, Nat2CompileFragCorrectness.param2] := by
        rcases ht with ⟨body, rfl, hBody⟩
        rfl
      refine ⟨hName, hParams, ?_⟩
      let leanF : Nat → Nat → Nat := fun x y =>
        LambdaIR.evalClosed (Term.app (Term.app t (Term.constNat x)) (Term.constNat y))
      have hf :
          ∀ x y,
            LambdaIR.evalClosed
                (Term.app (Term.app t (Term.constNat x)) (Term.constNat y))
              = leanF x y := by
        intro x y
        rfl
      have h :=
        Nat2CompileFragCorrectness.compileNat2FunFrag_correct
          (funName := funName) (t := t) ht leanF hf
      intro x y
      simpa [Nat2CompiledSpec, leanF] using (h x y)⟩

end CertifiedCompile

end LambdaIR
end HeytingLean
