import HeytingLean.LambdaIR.NatFunFragment

namespace HeytingLean
namespace LambdaIR
namespace Max01MiniCProof

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment

/-- Lean-level function returning `1` when the input is `0`, otherwise the input. -/
def leanMax01 (n : Nat) : Nat :=
  if n = 0 then 1 else n

/-- LambdaIR term implementing `leanMax01`. -/
def termMax01IR : Term [] (Ty.arrow Ty.nat Ty.nat) :=
  Term.lam
    (Term.if_
      (Term.app
        (Term.app Term.primEqNat (Term.var Var.vz))
        (Term.constNat 0))
      (Term.constNat 1)
      (Term.var Var.vz))

end Max01MiniCProof
end LambdaIR
end HeytingLean
