import Mathlib.CategoryTheory.Monad.Basic

namespace HeytingLean
namespace Noneism
namespace Cat

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- A lightweight predicate recording that a monad multiplication is pointwise an isomorphism. -/
def IsIdempotentMonad (T : Monad C) : Prop :=
  ∀ X, IsIso (T.μ.app X)

end Cat
end Noneism
end HeytingLean

