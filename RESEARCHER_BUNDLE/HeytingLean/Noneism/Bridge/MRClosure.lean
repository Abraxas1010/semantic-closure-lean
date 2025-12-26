import HeytingLean.ClosingTheLoop.MR.ClosureOperator

namespace HeytingLean
namespace Noneism
namespace Bridge

open HeytingLean.ClosingTheLoop.MR

universe u v

variable {S : MRSystem.{u, v}} {b : S.B}

theorem closeSelector_idem (RI : RightInverseAt S b) (Φ : Selector S) :
    closeSelector S b RI (closeSelector S b RI Φ) = closeSelector S b RI Φ :=
  closeSelector.idem (S := S) (b := b) (RI := RI) Φ

end Bridge
end Noneism
end HeytingLean

