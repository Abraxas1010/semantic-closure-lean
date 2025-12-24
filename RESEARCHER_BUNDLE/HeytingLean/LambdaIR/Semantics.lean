import HeytingLean.Core.SemanticsBase
import HeytingLean.LambdaIR.Syntax

namespace HeytingLean
namespace LambdaIR

open HeytingLean.Core

abbrev InterpTy := Core.interpTy
abbrev Env := Core.Env

@[simp] def extendEnv {Γ α} (ρ : Env Γ) (x : InterpTy α) :
    Env (α :: Γ) :=
  Core.extendEnv ρ x

@[simp] def eval : ∀ {Γ τ}, Term Γ τ → Env Γ → InterpTy τ
  | _, _, Term.var v,        ρ => ρ v
  | _, _, Term.lam body,     ρ => fun x => eval body (extendEnv ρ x)
  | _, _, Term.app f x,      ρ => (eval f ρ) (eval x ρ)
  | _, _, Term.pair t₁ t₂,   ρ => (eval t₁ ρ, eval t₂ ρ)
  | _, _, Term.fst t,        ρ => (eval t ρ).fst
  | _, _, Term.snd t,        ρ => (eval t ρ).snd
  | _, _, Term.inl t,        ρ => Sum.inl (eval t ρ)
  | _, _, Term.inr t,        ρ => Sum.inr (eval t ρ)
  | _, _, Term.matchSum s k₁ k₂, ρ =>
      match eval s ρ with
      | Sum.inl a => eval k₁ (extendEnv ρ a)
      | Sum.inr b => eval k₂ (extendEnv ρ b)
  | _, _, Term.if_ c t₁ t₂,  ρ =>
      match eval c ρ with
      | true  => eval t₁ ρ
      | false => eval t₂ ρ
  | _, _, Term.constNat n,   _ => n
  | _, _, Term.constBool b,  _ => b
  | _, _, Term.primAddNat,   _ => fun x y => Nat.add x y
  | _, _, Term.primEqNat,    _ => fun (x : Nat) (y : Nat) =>
      decide ((x : Int) = (y : Int))

@[simp] def evalClosed {τ} (t : Term [] τ) : InterpTy τ :=
  eval t baseEnv

end LambdaIR
end HeytingLean
