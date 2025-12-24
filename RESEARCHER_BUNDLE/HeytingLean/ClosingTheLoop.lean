import HeytingLean.ClosingTheLoop.MR.Basic
import HeytingLean.ClosingTheLoop.MR.InverseEvaluation
import HeytingLean.ClosingTheLoop.MR.ClosureOperator
import HeytingLean.ClosingTheLoop.MR.PaperMapping
import HeytingLean.ClosingTheLoop.FA.Diagram
import HeytingLean.ClosingTheLoop.FA.Temporal
import HeytingLean.ClosingTheLoop.Semantics.NucleusBridge
import HeytingLean.ClosingTheLoop.Semantics.NucleusFixedPoints
import HeytingLean.ClosingTheLoop.Semantics.PreorderTime
import HeytingLean.ClosingTheLoop.Semantics.FunctorialTime
import HeytingLean.ClosingTheLoop.Semantics.KernelLaws
import HeytingLean.ClosingTheLoop.Semantics.ProcessBridge
import HeytingLean.ClosingTheLoop.Semantics.LambdaIRBridge
import HeytingLean.ClosingTheLoop.Semantics.Mealy
import HeytingLean.ClosingTheLoop.Semantics.RelationalRealizability
import HeytingLean.ClosingTheLoop.Cat.Selector
import HeytingLean.ClosingTheLoop.Cat.Admissible
import HeytingLean.ClosingTheLoop.Cat.InverseEvaluation
import HeytingLean.ClosingTheLoop.Cat.ClosureOperator
import HeytingLean.ClosingTheLoop.Cat.YonedaView
import HeytingLean.ClosingTheLoop.Cat.YonedaViewNat
import HeytingLean.ClosingTheLoop.Cat.EvalImage
import HeytingLean.ClosingTheLoop.Cat.Concreteness
import HeytingLean.ClosingTheLoop.Main
import HeytingLean.ClosingTheLoop.Tests.ClosureIdempotent
import HeytingLean.ClosingTheLoop.Tests.Test_AssumptionMismatch

/-!
# Closing the Loop (semantic closure)

This umbrella module collects the initial Lean formalization described in
`WIP/closure_paper.md`:

- Rosen-style (M,R) scaffold + inverse evaluation and an idempotent loop-closing
  operator on selectors.
- A minimal typed (F,A) diagram skeleton, plus a functorial time-indexed container.
- A generic “retraction ⇒ nucleus” bridge lemma, aligning semantic closure with
  the existing nucleus/Heyting-core story.
- A precise “nucleus ⇒ Heyting core” fixed-point wrapper (using mathlib sublocales).
- Preorder-time semantics: a future-invariant kernel operator and an inflationary reachability nucleus.
- A categorical layer (exponentials + evaluation at a point + section) mirroring the Set proofs,
  plus: a currying/representability (Yoneda-style) view, a subobject-of-exponential encoding of
  admissible maps, and an explicit inverse-on-image guardrail.
- Small toy examples exercising the core theorems.
-/
