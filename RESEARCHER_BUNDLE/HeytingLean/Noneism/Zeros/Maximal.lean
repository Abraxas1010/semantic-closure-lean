import HeytingLean.Noneism.Cat.Presheaf

namespace HeytingLean
namespace Noneism
namespace Zeros

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- Maximal zero as the presheaf category on `C`. -/
abbrev MaximalZero :=
  Cat.Presheaf C

end Zeros
end Noneism
end HeytingLean

