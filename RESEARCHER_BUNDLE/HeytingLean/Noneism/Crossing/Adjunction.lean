import HeytingLean.Noneism.Cat.Yoneda

namespace HeytingLean
namespace Noneism
namespace Crossing

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- For a representable presheaf, `actualize` provides a representing object. -/
noncomputable def actualizeIsoYoneda (F : Cat.Presheaf C) [Functor.IsRepresentable F] :
    yoneda.obj (Cat.actualize (C := C) F) ≅ F :=
  (Cat.actualizeRepresentation (C := C) F).toIso

end Crossing
end Noneism
end HeytingLean

