import Mathlib.Data.Set.Lattice

/-!
Minimal typed process calculus syntax.
- Values and value types
- Channels and channel types
- Processes with send/recv/parallel/new/choice/cond
-/

namespace HeytingLean
namespace Process

/- Value types ------------------------------------------------------------- -/

inductive ValTy : Type
| unit
| bool
| int
| nat
| prod (τ₁ τ₂ : ValTy)
| sum  (τ₁ τ₂ : ValTy)
deriving DecidableEq

/-- Values for communication. -/
inductive Val : Type
| unit  : Val
| bool  : Bool → Val
| int   : Int → Val
| nat   : Nat → Val
| pair  : Val → Val → Val
| inl   : Val → Val
| inr   : Val → Val

-- (no automatic simp attributes for constructors here)

/-- Simple channel type: a channel carries a single payload type. -/
structure ChanTy : Type where
  payload : ValTy
deriving DecidableEq

/-- Channel identifiers; a simple numeric namespace suffices for now. -/
abbrev ChanId := Nat

/- Processes ------------------------------------------------------------- -/

inductive Proc : Type
| nil : Proc
| send  (a : ChanId) (v : Val) (P : Proc) : Proc       -- a!v ; P
| recv  (a : ChanId) (k : Val → Proc) : Proc           -- a?(x). k x
| parr  (P Q : Proc) : Proc                            -- P | Q
| new   (τ : ChanTy) (k : ChanId → Proc) : Proc        -- ν a:τ. k a
| choice (P Q : Proc) : Proc                           -- P + Q
| cond   (b : Val) (Pt Pf : Proc) : Proc               -- if b then Pt else Pf
| rep    (P : Proc) : Proc                             -- !P (replication)

-- No global `|` notation to avoid clashes with inductive syntax.

end Process
end HeytingLean
