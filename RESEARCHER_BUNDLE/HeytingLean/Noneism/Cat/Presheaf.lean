import Mathlib.CategoryTheory.Yoneda

namespace HeytingLean
namespace Noneism
namespace Cat

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]

/-- Presheaves on `C`. -/
abbrev Presheaf (C : Type u) [Category.{v} C] := Cᵒᵖ ⥤ Type w

end Cat
end Noneism
end HeytingLean
