import Mathlib.CategoryTheory.Endofunctor.Algebra

namespace HeytingLean
namespace Noneism
namespace Cat

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

namespace Endofunctor

variable {F : C ⥤ C}

/-- Lambek-style statement: the structure map of an initial algebra is an isomorphism. -/
theorem initialAlgebra_str_isIso {A : CategoryTheory.Endofunctor.Algebra F} (h : Limits.IsInitial A) :
    IsIso A.str :=
  CategoryTheory.Endofunctor.Algebra.Initial.str_isIso (A := A) h

/-- Dual Lambek-style statement: the structure map of a terminal coalgebra is an isomorphism. -/
theorem terminalCoalgebra_str_isIso {A : CategoryTheory.Endofunctor.Coalgebra F} (h : Limits.IsTerminal A) :
    IsIso A.str :=
  CategoryTheory.Endofunctor.Coalgebra.Terminal.str_isIso (A := A) h

end Endofunctor

end Cat
end Noneism
end HeytingLean
