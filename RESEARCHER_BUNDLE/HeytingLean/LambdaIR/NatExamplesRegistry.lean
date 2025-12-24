import HeytingLean.LambdaIR.Add1MiniCProof
import HeytingLean.LambdaIR.Add1EndToEnd
import HeytingLean.LambdaIR.DoubleMiniCProof
import HeytingLean.LambdaIR.DoubleEndToEnd
import HeytingLean.LambdaIR.ClampMiniCProof
import HeytingLean.LambdaIR.ClampEndToEnd
import HeytingLean.LambdaIR.SuccTwiceMiniCProof
import HeytingLean.LambdaIR.SuccTwiceEndToEnd
import HeytingLean.LambdaIR.Max01MiniCProof
import HeytingLean.LambdaIR.Max01EndToEnd
import HeytingLean.LambdaIR.NatCompileFrag
import HeytingLean.EndToEnd.NatFunSpec
import HeytingLean.EndToEnd.Manifest
import HeytingLean.LoF.NatFunProps

namespace HeytingLean
namespace LambdaIR
namespace NatExamplesRegistry

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.EndToEnd.NatFunSpec
open HeytingLean.EndToEnd
open HeytingLean.LambdaIR.Add1MiniCProof
open HeytingLean.LambdaIR.Add1EndToEnd
open HeytingLean.LambdaIR.DoubleMiniCProof
open HeytingLean.LambdaIR.DoubleEndToEnd
open HeytingLean.LambdaIR.ClampMiniCProof
open HeytingLean.LambdaIR.ClampEndToEnd
open HeytingLean.LambdaIR.SuccTwiceMiniCProof
open HeytingLean.LambdaIR.SuccTwiceEndToEnd
open HeytingLean.LambdaIR.Max01MiniCProof
open HeytingLean.LambdaIR.Max01EndToEnd
open HeytingLean.LambdaIR.NatCompileFrag
open HeytingLean.LoF

/-- Canonical registry of nat→nat examples used by docs, proofs, and the CLI smoke test. -/
def examples : List Nat1Example :=
  [ { funName := "add1"
      paramName := "x"
      cFunName := "add1"
      leanName := "HeytingLean.LambdaIR.Add1MiniCProof.leanAdd1"
      irName := "HeytingLean.LambdaIR.Add1MiniCProof.termAdd1IR"
      endToEndName := "HeytingLean.LambdaIR.Add1EndToEnd.add1_end_to_end"
      leanF := leanAdd1
      term := termAdd1IR
      endToEndProof := add1_end_to_end
      lofProps :=
        [ { theoremName :=
              "HeytingLean.LoF.NatFunProps.add1_compiled_spec"
            description := "Result equals n + 1 for every input n"
            prop :=
              ∀ n : Nat,
                runCompiledNatFunFrag "add1" "x" termAdd1IR n = some (n + 1)
            proof := add1_compiled_spec } ] }
  , { funName := "double"
      paramName := "x"
      cFunName := "double"
      leanName := "HeytingLean.LambdaIR.DoubleMiniCProof.leanDouble"
      irName := "HeytingLean.LambdaIR.DoubleMiniCProof.termDoubleIR"
      endToEndName := "HeytingLean.LambdaIR.DoubleEndToEnd.double_end_to_end"
      leanF := leanDouble
      term := termDoubleIR
      endToEndProof := double_end_to_end
      lofProps :=
        [ { theoremName :=
              "HeytingLean.LoF.NatFunProps.double_compiled_spec"
            description := "Result equals n + n for every input n"
            prop :=
              ∀ n : Nat,
                runCompiledNatFunFrag "double" "x" termDoubleIR n = some (n + n)
            proof := double_compiled_spec } ] }
  , { funName := "clamp01"
      paramName := "x"
      cFunName := "clamp01"
      leanName := "HeytingLean.LambdaIR.ClampMiniCProof.leanClamp01"
      irName := "HeytingLean.LambdaIR.ClampMiniCProof.termClamp01IR"
      endToEndName := "HeytingLean.LambdaIR.ClampEndToEnd.clamp01_end_to_end"
      leanF := leanClamp01
      term := termClamp01IR
      endToEndProof := clamp01_end_to_end
      lofProps :=
        [ { theoremName :=
              "HeytingLean.LoF.NatFunProps.clamp01_compiled_boolish"
            description := "Result is always 0 or 1 (boolish image)"
            prop :=
              ∀ n : Nat,
                Or
                  (runCompiledNatFunFrag "clamp01" "x" termClamp01IR n = some 0)
                  (runCompiledNatFunFrag "clamp01" "x" termClamp01IR n = some 1)
            proof := clamp01_compiled_boolish } ] }
  , { funName := "succ_twice"
      paramName := "x"
      cFunName := "succ_twice"
      leanName := "HeytingLean.LambdaIR.SuccTwiceMiniCProof.leanSuccTwice"
      irName := "HeytingLean.LambdaIR.SuccTwiceMiniCProof.termSuccTwiceIR"
      endToEndName := "HeytingLean.LambdaIR.SuccTwiceEndToEnd.succTwice_end_to_end"
      leanF := leanSuccTwice
      term := termSuccTwiceIR
      endToEndProof := succTwice_end_to_end
      lofProps :=
        [ { theoremName :=
              "HeytingLean.LoF.NatFunProps.succTwice_compiled_spec"
            description := "Result equals n + 2 for every input n"
            prop :=
              ∀ n : Nat,
                runCompiledNatFunFrag "succ_twice" "x" termSuccTwiceIR n
                  = some (n + 2)
            proof := succTwice_compiled_spec } ] }
  , { funName := "max01"
      paramName := "x"
      cFunName := "max01"
      leanName := "HeytingLean.LambdaIR.Max01MiniCProof.leanMax01"
      irName := "HeytingLean.LambdaIR.Max01MiniCProof.termMax01IR"
      endToEndName := "HeytingLean.LambdaIR.Max01EndToEnd.max01_end_to_end"
      leanF := leanMax01
      term := termMax01IR
      endToEndProof := max01_end_to_end
      lofProps :=
        [ { theoremName :=
              "HeytingLean.LoF.NatFunProps.max01_compiled_spec"
            description := "Returns 1 when input is 0, otherwise returns input"
            prop :=
              ∀ n : Nat,
                runCompiledNatFunFrag "max01" "x" termMax01IR n
                  = some (if n = 0 then 1 else n)
            proof := max01_compiled_spec } ] } ]

end NatExamplesRegistry
end LambdaIR
end HeytingLean
