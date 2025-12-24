import Mathlib.Order.Nucleus

/-!
# Closing the Loop: nucleus bridge (Tier 3)

`closeSelector` (Tier 1) is an idempotent *projection* on a selector space, i.e. it
encodes “closing the semantic loop” at the level of individual mechanisms.

To connect this to the existing *nucleus / Heyting core* story, we provide a small,
generic construction:

> A meet-preserving retraction `α ↔ β` induces a `Nucleus α` by `x ↦ dec (enc x)`.

This matches the “retraction-induced nucleus” reading in `WIP/closure_paper.md`,
while keeping the hypotheses explicit (meet preservation + section/retraction laws).
-/

namespace HeytingLean
namespace ClosingTheLoop
namespace Semantics

universe u v

section RetractionToNucleus

variable {α : Type u} {β : Type v} [SemilatticeInf α] [SemilatticeInf β]

/-- A meet-preserving section–retraction pair `α ↔ β`, suitable for inducing a nucleus on `α`. -/
structure MeetRetraction where
  enc : α → β
  dec : β → α
  /-- Section law: `enc (dec y) = y`. -/
  enc_dec : Function.LeftInverse enc dec
  /-- Inflationary law: `x ≤ dec (enc x)`. -/
  le_dec_enc : ∀ x : α, x ≤ dec (enc x)
  /-- `enc` preserves finite meets. -/
  enc_map_inf : ∀ x y : α, enc (x ⊓ y) = enc x ⊓ enc y
  /-- `dec` preserves finite meets. -/
  dec_map_inf : ∀ x y : β, dec (x ⊓ y) = dec x ⊓ dec y

namespace MeetRetraction

variable (r : MeetRetraction (α := α) (β := β))

/-- The induced nucleus on `α`: close by encoding then decoding. -/
def retractionNucleus : Nucleus α where
  toFun x := r.dec (r.enc x)
  map_inf' x y := by
    simp [r.enc_map_inf, r.dec_map_inf]
  idempotent' x := by
    -- `dec (enc (dec (enc x))) = dec (enc x)` by the section law.
    have : r.enc (r.dec (r.enc x)) = r.enc x := by
      simpa using (r.enc_dec (r.enc x))
    exact le_of_eq (by simpa using congrArg r.dec this)
  le_apply' x := r.le_dec_enc x

@[simp] lemma retractionNucleus_apply (x : α) :
    r.retractionNucleus x = r.dec (r.enc x) := rfl

@[simp] lemma retractionNucleus_idem (x : α) :
    r.retractionNucleus (r.retractionNucleus x) = r.retractionNucleus x :=
  (r.retractionNucleus).idempotent x

end MeetRetraction

end RetractionToNucleus

section SetDemo

open Set

variable {σ : Type u}

/-- A tiny bridge demo: on `Set σ`, nuclei include constant-union closure `S ↦ S ∪ U`. -/
def addClosureNucleus (U : Set σ) : Nucleus (Set σ) where
  toFun S := S ∪ U
  map_inf' S T := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨Or.inl hx.1, Or.inl hx.2⟩
      · exact ⟨Or.inr hx, Or.inr hx⟩
    · rintro ⟨hxS, hxT⟩
      cases hxS with
      | inl hxS =>
          cases hxT with
          | inl hxT => exact Or.inl ⟨hxS, hxT⟩
          | inr hxU => exact Or.inr hxU
      | inr hxU =>
          exact Or.inr hxU
  idempotent' S := by
    intro x hx
    rcases hx with hx | hx
    · exact hx
    · exact Or.inr hx
  le_apply' S := by
    intro x hx
    exact Or.inl hx

end SetDemo

end Semantics
end ClosingTheLoop
end HeytingLean
