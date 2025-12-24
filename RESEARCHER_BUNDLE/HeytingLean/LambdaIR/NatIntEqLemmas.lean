namespace HeytingLean
namespace LambdaIR

@[simp] theorem int_coe_nat_eq_coe_nat_iff (a b : Nat) :
    ((a : Int) = (b : Int)) ↔ a = b :=
by
  constructor
  · intro h
    exact Int.ofNat.inj h
  · intro h
    simp [h]

@[simp] theorem decide_int_coe_nat_eq_coe_nat (a b : Nat) :
    decide ((a : Int) = (b : Int)) = decide (a = b) := by
  by_cases h : a = b
  · subst h
    simp
  · have : (a : Int) ≠ (b : Int) := by
      intro h'
      exact h ((int_coe_nat_eq_coe_nat_iff _ _).1 h')
    simp [h, this]

end LambdaIR
end HeytingLean
