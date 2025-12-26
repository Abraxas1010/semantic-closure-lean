import HeytingLean.Noneism.Eigen.Attribute
import HeytingLean.Noneism.Bridge.BetaConstruction

namespace HeytingLean
namespace Noneism
namespace Bridge

open Lean
open HeytingLean.Noneism.Eigen.Attr

/-- Collect all declarations tagged with `@[eigencomputable ...]` in this environment. -/
def eigencomputableDecls (env : Environment) : Array (Name × Name) :=
  env.constants.fold (init := #[]) fun acc n _ =>
    match eigencomputableDynamicsName? env n with
    | some dyn => acc.push (n, dyn)
    | none => acc

end Bridge
end Noneism
end HeytingLean

