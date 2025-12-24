import HeytingLean.LambdaIR.Nat2FunFragment

namespace HeytingLean
namespace LambdaIR
namespace Min2MiniCProof

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Nat2FunFragment

/-- Lean-level “min-like” function using equality as the guard (returns the
    first argument on equality, otherwise the second). -/
def leanMin2 (x y : Nat) : Nat :=
  if x = y then x else y

/-- LambdaIR encoding of `leanMin2`. -/
def termMin2IR :
    Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat)) :=
  Term.lam <|
    Term.lam <|
      Term.if_
        (Term.app
          (Term.app Term.primEqNat (Term.var (Var.vs Var.vz)))
          (Term.var Var.vz))
        (Term.var (Var.vs Var.vz))
        (Term.var Var.vz)

end Min2MiniCProof
end LambdaIR
end HeytingLean
