import HeytingLean.LambdaIR.NatFunFragment

namespace HeytingLean
namespace LambdaIR
namespace SuccTwiceMiniCProof

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment

/-- Lean-level function `n ↦ n + 2`. -/
def leanSuccTwice (n : Nat) : Nat :=
  n + 2

/-- LambdaIR term implementing `leanSuccTwice`. -/
def termSuccTwiceIR : Term [] (Ty.arrow Ty.nat Ty.nat) :=
  Term.lam
    (Term.app
      (Term.app Term.primAddNat (Term.var Var.vz))
      (Term.constNat 2))

end SuccTwiceMiniCProof
end LambdaIR
end HeytingLean
