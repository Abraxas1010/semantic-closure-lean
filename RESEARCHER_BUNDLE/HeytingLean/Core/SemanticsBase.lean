import HeytingLean.Core.Types

namespace HeytingLean
namespace Core

open Ty

/-- Interpretation of types into Lean's `Type`. -/
@[simp] def interpTy : Ty → Type
  | Ty.nat        => Nat
  | Ty.bool       => Bool
  | Ty.prod α β   => interpTy α × interpTy β
  | Ty.sum α β    => Sum (interpTy α) (interpTy β)
  | Ty.arrow α β  => interpTy α → interpTy β

/-- Intrinsically typed environments. -/
@[simp] def Env (Γ : Ctx) := ∀ {τ}, Var Γ τ → interpTy τ

@[simp] def baseEnv : Env [] := by
  intro τ v; cases v

/-- Extend an environment with a new head binding. -/
@[simp] def extendEnv {Γ α} (ρ : Env Γ) (x : interpTy α) : Env (α :: Γ) := by
  intro τ v
  cases v with
  | vz => exact x
  | vs v' => exact ρ v'

end Core
end HeytingLean
