import HeytingLean.ClosingTheLoop.MR.ClosureOperator

/-!
# Closing the Loop: toy MR example (Tier 1 tests)

We build a tiny (M,R) system in `Set` and a concrete `RightInverseAt` section `β` to
exercise the `closeSelector` operator and its idempotence theorem.
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Tests

open MR

private def toyH : Set (Unit → Bool) := Set.univ

private def toySystem : MRSystem where
  A := Unit
  B := Bool
  H := toyH
  f := fun _ => true
  hf := by simp [toyH]
  Sel := Set.univ
  Φf := fun _ => ⟨fun _ => true, by simp [toyH]⟩
  hΦf := by simp

private def mapTrue : AdmissibleMap toySystem := ⟨fun _ => true, by simp [toySystem, toyH]⟩
private def mapFalse : AdmissibleMap toySystem := ⟨fun _ => false, by simp [toySystem, toyH]⟩

private def toySelector : Selector toySystem :=
  ⟨fun b =>
      match b with
      | true => mapFalse
      | false => mapTrue,
    by simp [toySystem]⟩

private def toyRI (b : toySystem.B) : RightInverseAt toySystem b where
  β := fun g => ⟨fun _ => g, by simp [toySystem]⟩
  right_inv := by
    intro g
    rfl

example :
    closeSelector toySystem true (toyRI true) toySelector true = toySelector true := by
  simp [toySelector, closeSelector, toyRI, toySystem]

example :
    closeSelector toySystem true (toyRI true) toySelector false = toySelector true := by
  -- Closing collapses all configurations to the one picked at `b = true`.
  simp [toySelector, closeSelector, toyRI, toySystem]

example :
    closeSelector toySystem true (toyRI true)
        (closeSelector toySystem true (toyRI true) toySelector) =
      closeSelector toySystem true (toyRI true) toySelector := by
  simpa using (closeSelector.idem (S := toySystem) (b := true) (RI := toyRI true) toySelector)

end Tests
end ClosingTheLoop
end HeytingLean
