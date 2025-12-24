import HeytingLean.LambdaIR.NatFunFragment

namespace HeytingLean
namespace LambdaIR
namespace DoubleMiniCProof

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment

/-- Lean-level doubling function. -/
def leanDouble (n : Nat) : Nat :=
  n + n

/-- LambdaIR term implementing `leanDouble`. -/
def termDoubleIR : Term [] (Ty.arrow Ty.nat Ty.nat) :=
  Term.lam
    (Term.app
      (Term.app Term.primAddNat (Term.var Var.vz))
      (Term.var Var.vz))

end DoubleMiniCProof
end LambdaIR
end HeytingLean
