import HeytingLean.Noneism.Zeros.Minimal
import HeytingLean.Noneism.Zeros.Maximal
import HeytingLean.Noneism.Zeros.Recursive

namespace HeytingLean
namespace Noneism
namespace Zeros

universe u v w

/-- A lightweight record of the three layers used in the Noneism story. -/
structure ZeroHierarchy where
  Minimal : Type u
  Maximal : Type v
  Recursive : Type w

open HeytingLean.Noneism.Core
open CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {α : Type v} [SemilatticeInf α] (n : Nucleus α)

/-- Package the three layers for a chosen category `C` and nucleus `n`. -/
def mk (C : Type u) [Category.{v} C] (n : Nucleus α) : ZeroHierarchy :=
  { Minimal := MinimalZero
    Maximal := MaximalZero (C := C)
    Recursive := RecursiveZero (α := α) n }

end Zeros
end Noneism
end HeytingLean
