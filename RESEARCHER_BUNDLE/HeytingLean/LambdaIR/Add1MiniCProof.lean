import HeytingLean.LambdaIR.NatFunFragment
import HeytingLean.EndToEnd.NatFunSpec

namespace HeytingLean
namespace LambdaIR
namespace Add1MiniCProof

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatFunFragment
open HeytingLean.EndToEnd

/-- Lean-level add1 function. -/
def leanAdd1 (n : Nat) : Nat := n + 1

/-- LambdaIR term implementing `leanAdd1`. -/
def termAdd1IR : Term [] (Ty.arrow Ty.nat Ty.nat) :=
  Term.lam
    (Term.app
      (Term.app Term.primAddNat (Term.var Var.vz))
      (Term.constNat 1))

end Add1MiniCProof
end LambdaIR
end HeytingLean
