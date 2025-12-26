import HeytingLean.Noneism.Core.Nucleus

namespace HeytingLean
namespace Noneism
namespace Zeros

open HeytingLean.Noneism.Core

universe u

variable {α : Type u} [SemilatticeInf α]

/-- Recursive zero as the fixed-point locus of a nucleus. -/
abbrev RecursiveZero (n : Nucleus α) :=
  {x : α // IsStable (α := α) n x}

end Zeros
end Noneism
end HeytingLean

