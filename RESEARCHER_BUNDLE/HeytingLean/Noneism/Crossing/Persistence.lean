import HeytingLean.Noneism.Core.Nucleus

namespace HeytingLean
namespace Noneism
namespace Crossing

open HeytingLean.Noneism.Core

universe u

variable {α : Type u} [SemilatticeInf α]

theorem stable_apply (n : Nucleus α) (x : α) : IsStable (α := α) n (n x) :=
  Core.stable_apply (α := α) n x

end Crossing
end Noneism
end HeytingLean

