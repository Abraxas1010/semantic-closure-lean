import Mathlib.Data.Set.Insert
import HeytingLean.ClosingTheLoop.MR.PaperMapping

/-!
# Closing the Loop: assumption mismatch tests (Tier 1 tests)

This file provides tiny `Set` examples showing that:

- the paper-shaped uniqueness condition (`InjectiveEvalAt`) does not imply existence of a chosen
  right inverse (`RightInverseAt`), because evaluation need not be surjective on a restricted
  admissible selector space;
- conversely, `RightInverseAt` implies surjectivity (via the library lemma).
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Tests

open MR

private def selConstTrue : Bool → {g : Unit → Bool // g ∈ (Set.univ : Set (Unit → Bool))} :=
  fun _ => ⟨fun _ => true, by simp⟩

private def sysInjNotSurj : MRSystem where
  A := Unit
  B := Bool
  H := Set.univ
  f := fun _ => true
  hf := by simp
  Sel := {selConstTrue}
  Φf := selConstTrue
  hΦf := by simp

private def mapTrue : AdmissibleMap sysInjNotSurj :=
  sysInjNotSurj.Φf true

private def mapFalse : AdmissibleMap sysInjNotSurj :=
  ⟨fun _ => false, by simp [sysInjNotSurj]⟩

private theorem mapFalse_ne_mapTrue : mapFalse ≠ mapTrue := by
  intro h
  have hfun : (fun _ : Unit => false) = (fun _ : Unit => true) := by
    simpa [mapFalse, mapTrue] using congrArg Subtype.val h
  have : (false : Bool) = true := congrArg (fun f => f ()) hfun
  cases this

private instance : Subsingleton (Selector sysInjNotSurj) where
  allEq Φ Ψ := by
    rcases Φ with ⟨f, hf⟩
    rcases Ψ with ⟨g, hg⟩
    apply Subtype.ext
    have hf' : f = selConstTrue := by simpa [sysInjNotSurj] using hf
    have hg' : g = selConstTrue := by simpa [sysInjNotSurj] using hg
    simp [hf', hg']

private theorem evalAt_not_surjective : ¬ Function.Surjective (evalAt sysInjNotSurj true) := by
  intro hsurj
  rcases hsurj mapFalse with ⟨Φ, hΦ⟩
  -- Since the selector space is a singleton, every selector evaluates to `mapTrue` at `b = true`.
  have : evalAt sysInjNotSurj true Φ = mapTrue := by
    rcases Φ with ⟨f, hf⟩
    have hf' : f = selConstTrue := by simpa [sysInjNotSurj] using hf
    simp [MR.evalAt, mapTrue, sysInjNotSurj, hf']
  exact mapFalse_ne_mapTrue (hΦ.symm.trans this)

example : InjectiveEvalAt sysInjNotSurj true := by
  refine ⟨?_⟩
  simpa using (Function.injective_of_subsingleton (evalAt sysInjNotSurj true))

example : ¬ Nonempty (RightInverseAt sysInjNotSurj true) := by
  intro h
  rcases h with ⟨RI⟩
  have hsurj : Function.Surjective (evalAt sysInjNotSurj true) :=
    RightInverseAt.evalAt_surjective (S := sysInjNotSurj) (b := true) RI
  exact evalAt_not_surjective hsurj

example {S : MRSystem} {b : S.B} (RI : RightInverseAt S b) :
    Function.Surjective (evalAt S b) :=
  RightInverseAt.evalAt_surjective (S := S) (b := b) RI

end Tests
end ClosingTheLoop
end HeytingLean
