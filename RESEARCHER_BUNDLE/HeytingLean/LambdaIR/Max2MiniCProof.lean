import HeytingLean.LambdaIR.Nat2FunFragment

namespace HeytingLean
namespace LambdaIR
namespace Max2MiniCProof

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Nat2FunFragment

/-- Lean-level “max-like” function using equality as the guard. -/
def leanMax2 (x y : Nat) : Nat :=
  if x = y then y else x

/-- LambdaIR encoding of `leanMax2`. -/
def termMax2IR :
    Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat)) :=
  Term.lam <|
    Term.lam <|
      Term.if_
        (Term.app
          (Term.app Term.primEqNat (Term.var (Var.vs Var.vz)))
          (Term.var Var.vz))
        (Term.var Var.vz)
        (Term.var (Var.vs Var.vz))

end Max2MiniCProof
end LambdaIR
end HeytingLean
