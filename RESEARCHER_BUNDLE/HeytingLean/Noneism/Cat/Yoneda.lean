import Mathlib.CategoryTheory.Yoneda
import HeytingLean.Noneism.Cat.Presheaf

namespace HeytingLean
namespace Noneism
namespace Cat

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- The Yoneda embedding, viewed as the map from objects to their presheaf of probes. -/
abbrev potentialize (C : Type u) [Category.{v} C] : C ⥤ Presheaf C :=
  yoneda

/-- The Yoneda embedding is fully faithful. -/
def potentializeFullyFaithful : (potentialize (C := C)).FullyFaithful := by
  simpa [potentialize] using (CategoryTheory.Yoneda.fullyFaithful (C := C))

/-- Choose a representing object for a representable presheaf. -/
noncomputable def actualize (F : Presheaf C) [Functor.IsRepresentable F] : C := by
  classical
  exact Classical.choose (Functor.IsRepresentable.has_representation (F := F))

noncomputable def actualizeRepresentation (F : Presheaf C) [Functor.IsRepresentable F] :
    F.RepresentableBy (actualize (C := C) F) := by
  classical
  let h := Functor.IsRepresentable.has_representation (F := F)
  -- `h` gives a witness object and a representation structure.
  have hRep : Nonempty (F.RepresentableBy (Classical.choose h)) :=
    Classical.choose_spec h
  -- unfold `actualize` (it is the chosen object)
  simpa [actualize] using (Classical.choice hRep)

/-- Any representing object is isomorphic to `actualize F`. -/
noncomputable def actualizeIso (F : Presheaf C) [Functor.IsRepresentable F] {Y : C}
    (eY : F.RepresentableBy Y) : actualize (C := C) F ≅ Y :=
  Functor.RepresentableBy.uniqueUpToIso (actualizeRepresentation (C := C) F) eY

end Cat
end Noneism
end HeytingLean
