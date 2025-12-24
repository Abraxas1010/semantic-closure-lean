import HeytingLean.LambdaIR.NatFunFragment

namespace HeytingLean
namespace LambdaIR
namespace ClampMiniCProof

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment

/-- Lean-level clamp function returning 0 for input 0 and 1 otherwise. -/
def leanClamp01 (n : Nat) : Nat :=
  if n = 0 then 0 else 1

/-- LambdaIR term implementing `leanClamp01`. -/
def termClamp01IR : Term [] (Ty.arrow Ty.nat Ty.nat) :=
  Term.lam
    (Term.if_
      (Term.app
        (Term.app Term.primEqNat (Term.var Var.vz))
        (Term.constNat 0))
      (Term.constNat 0)
      (Term.constNat 1))

end ClampMiniCProof
end LambdaIR
end HeytingLean
