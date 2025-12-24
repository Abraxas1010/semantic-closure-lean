import HeytingLean.LambdaIR.Nat2FunFragment

namespace HeytingLean
namespace LambdaIR
namespace Add2MiniCProof

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Nat2FunFragment

/-- Lean-level addition of two naturals. -/
def leanAdd2 (x y : Nat) : Nat :=
  x + y

/-- LambdaIR encoding of `leanAdd2`. -/
def termAdd2IR :
    Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat)) :=
  Term.lam <|
    Term.lam <|
      Term.app
        (Term.app Term.primAddNat (Term.var (Var.vs Var.vz)))
        (Term.var Var.vz)

end Add2MiniCProof
end LambdaIR
end HeytingLean
