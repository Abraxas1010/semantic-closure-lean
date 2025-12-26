namespace HeytingLean
namespace Noneism
namespace Zeros

/-- Minimal zero as an empty type. -/
abbrev MinimalZero :=
  PEmpty

theorem minimalZero_noElim (x : MinimalZero) : False := by
  cases x

end Zeros
end Noneism
end HeytingLean

