import HeytingLean.Noneism.Core.FixedPoints

namespace HeytingLean
namespace Noneism
namespace Core

universe u

variable {X : Type u} [Order.Frame X] (n : Nucleus X)

/-- The Heyting core of a nucleus, as a sublocale. -/
abbrev HeytingCore : Sublocale X :=
  n.toSublocale

instance : HeytingAlgebra (↥(n.toSublocale)) :=
  by infer_instance

instance : Order.Frame (↥(n.toSublocale)) :=
  by infer_instance

end Core
end Noneism
end HeytingLean
