namespace HeytingLean
namespace Core

/-- Shared type grammar for LeanCore-style calculi. -/
inductive Ty : Type where
  | nat
  | bool
  | prod (α β : Ty)
  | sum  (α β : Ty)
  | arrow (α β : Ty)
  deriving DecidableEq, Repr

/-- Contexts are lists of types. -/
abbrev Ctx := List Ty

/-- Shared de Bruijn variables. -/
inductive Var : Ctx → Ty → Type where
  | vz  {Γ τ} : Var (τ :: Γ) τ
  | vs  {Γ τ τ'} : Var Γ τ → Var (τ' :: Γ) τ
  deriving Repr

end Core
end HeytingLean
