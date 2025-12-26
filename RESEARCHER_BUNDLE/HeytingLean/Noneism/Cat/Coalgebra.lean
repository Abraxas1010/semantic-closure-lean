import Mathlib.CategoryTheory.Endofunctor.Algebra

namespace HeytingLean
namespace Noneism
namespace Cat

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- Coalgebras of an endofunctor, re-exported for the Noneism categorical layer. -/
abbrev Coalgebra (F : C ⥤ C) :=
  CategoryTheory.Endofunctor.Coalgebra F

end Cat
end Noneism
end HeytingLean
