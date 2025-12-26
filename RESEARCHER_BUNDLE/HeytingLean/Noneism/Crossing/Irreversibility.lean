import HeytingLean.Noneism.Cat.Yoneda

namespace HeytingLean
namespace Noneism
namespace Crossing

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- Any two representing objects for a presheaf are isomorphic. -/
noncomputable def representable_uniqueUpToIso (F : Cat.Presheaf C) {Y Y' : C}
    (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y') : Y ≅ Y' :=
  Functor.RepresentableBy.uniqueUpToIso e e'

end Crossing
end Noneism
end HeytingLean

