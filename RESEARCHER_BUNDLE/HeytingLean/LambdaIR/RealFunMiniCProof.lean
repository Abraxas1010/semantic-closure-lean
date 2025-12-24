import HeytingLean.LambdaIR.Nat2FunFragment

namespace HeytingLean
namespace LambdaIR
namespace RealFunMiniCProof

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Nat2FunFragment

/-- A “zero-or-sum” example: yields `0` when the inputs match, otherwise their sum. -/
def leanXorSum (x y : Nat) : Nat :=
  if x = y then 0 else x + y

/-- LambdaIR encoding of `leanXorSum`. -/
def termXorSumIR :
    Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat)) :=
  Term.lam <|
    Term.lam <|
      Term.if_
        (Term.app
          (Term.app Term.primEqNat (Term.var (Var.vs Var.vz)))
          (Term.var Var.vz))
        (Term.constNat 0)
        (Term.app
          (Term.app Term.primAddNat (Term.var (Var.vs Var.vz)))
          (Term.var Var.vz))

end RealFunMiniCProof
end LambdaIR
end HeytingLean
