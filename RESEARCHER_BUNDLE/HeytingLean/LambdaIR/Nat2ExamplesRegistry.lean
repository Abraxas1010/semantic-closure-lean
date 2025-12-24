import HeytingLean.LambdaIR.Add2MiniCProof
import HeytingLean.LambdaIR.Add2EndToEnd
import HeytingLean.LambdaIR.Max2MiniCProof
import HeytingLean.LambdaIR.Min2MiniCProof
import HeytingLean.LambdaIR.Max2EndToEnd
import HeytingLean.LambdaIR.Min2EndToEnd
import HeytingLean.LambdaIR.RealFunMiniCProof
import HeytingLean.LambdaIR.RealFunEndToEnd
import HeytingLean.LambdaIR.Nat2CompileFrag
import HeytingLean.EndToEnd.NatFunSpec
import HeytingLean.EndToEnd.Manifest
import HeytingLean.LoF.NatFunProps

namespace HeytingLean
namespace LambdaIR
namespace Nat2ExamplesRegistry

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.EndToEnd.NatFunSpec
open HeytingLean.EndToEnd
open HeytingLean.LambdaIR.Add2MiniCProof
open HeytingLean.LambdaIR.Add2EndToEnd
open HeytingLean.LambdaIR.Max2MiniCProof
open HeytingLean.LambdaIR.Max2EndToEnd
open HeytingLean.LambdaIR.Min2MiniCProof
open HeytingLean.LambdaIR.Min2EndToEnd
open HeytingLean.LambdaIR.RealFunMiniCProof
open HeytingLean.LambdaIR.RealFunEndToEnd
open HeytingLean.LambdaIR.Nat2CompileFrag
open HeytingLean.LoF

/-- Canonical registry of nat→nat→nat examples. -/
def examples : List Nat2Example :=
  [ { funName := "add2"
      param1 := "x"
      param2 := "y"
      cFunName := "add2"
      leanName := "HeytingLean.LambdaIR.Add2MiniCProof.leanAdd2"
      irName := "HeytingLean.LambdaIR.Add2MiniCProof.termAdd2IR"
      endToEndName := "HeytingLean.LambdaIR.Add2EndToEnd.add2_end_to_end"
      leanF := leanAdd2
      term := termAdd2IR
      endToEndProof := add2_end_to_end
      lofProps :=
        [ { theoremName :=
              "HeytingLean.LoF.NatFunProps.add2_compiled_spec"
            description := "Result equals x + y for every input pair"
            prop :=
              ∀ x y : Nat,
                runCompiledNat2FunFrag "add2" "x" "y" termAdd2IR x y
                  = some (x + y)
            proof := add2_compiled_spec } ] }
  , { funName := "max2"
      param1 := "x"
      param2 := "y"
      cFunName := "max2"
      leanName := "HeytingLean.LambdaIR.Max2MiniCProof.leanMax2"
      irName := "HeytingLean.LambdaIR.Max2MiniCProof.termMax2IR"
      endToEndName := "HeytingLean.LambdaIR.Max2EndToEnd.max2_end_to_end"
      leanF := leanMax2
      term := termMax2IR
      endToEndProof := max2_end_to_end
      lofProps :=
        [ { theoremName :=
              "HeytingLean.LoF.NatFunProps.max2_compiled_select"
            description :=
              "Returns y when x = y; otherwise returns the first argument x"
            prop :=
              ∀ x y : Nat,
                And (x = y ->
                  runCompiledNat2FunFrag "max2" "x" "y" termMax2IR x y = some y)
                    (x ≠ y ->
                  runCompiledNat2FunFrag "max2" "x" "y" termMax2IR x y = some x)
            proof := max2_compiled_select } ] }
  , { funName := "min2"
      param1 := "x"
      param2 := "y"
      cFunName := "min2"
      leanName := "HeytingLean.LambdaIR.Min2MiniCProof.leanMin2"
      irName := "HeytingLean.LambdaIR.Min2MiniCProof.termMin2IR"
      endToEndName := "HeytingLean.LambdaIR.Min2EndToEnd.min2_end_to_end"
      leanF := leanMin2
      term := termMin2IR
      endToEndProof := min2_end_to_end
      lofProps :=
        [ { theoremName :=
              "HeytingLean.LoF.NatFunProps.min2_compiled_select"
            description :=
              "Returns x when x = y; otherwise returns the second argument y"
            prop :=
              ∀ x y : Nat,
                And (x = y ->
                  runCompiledNat2FunFrag "min2" "x" "y" termMin2IR x y = some x)
                    (x ≠ y ->
                  runCompiledNat2FunFrag "min2" "x" "y" termMin2IR x y = some y)
            proof := min2_compiled_select } ] }
  , { funName := "xorSum"
      param1 := "x"
      param2 := "y"
      cFunName := "xorSum"
      leanName := "HeytingLean.LambdaIR.RealFunMiniCProof.leanXorSum"
      irName := "HeytingLean.LambdaIR.RealFunMiniCProof.termXorSumIR"
      endToEndName := "HeytingLean.LambdaIR.RealFunEndToEnd.xorSum_end_to_end"
      leanF := leanXorSum
      term := termXorSumIR
      endToEndProof := xorSum_end_to_end
      lofProps :=
        [ { theoremName :=
              "HeytingLean.LoF.NatFunProps.xorSum_compiled_spec"
            description :=
              "Returns 0 when x = y; otherwise returns x + y"
            prop :=
              ∀ x y : Nat,
                And (x = y ->
                  runCompiledNat2FunFrag "xorSum" "x" "y" termXorSumIR x y = some 0)
                    (x ≠ y ->
                  runCompiledNat2FunFrag "xorSum" "x" "y" termXorSumIR x y
                    = some (x + y))
            proof := xorSum_compiled_spec } ] } ]

end Nat2ExamplesRegistry
end LambdaIR
end HeytingLean
