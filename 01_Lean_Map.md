# Lean map: modules, declarations, and “where the proof lives”

## Module layout

Tier 1 (M,R + inverse evaluation + loop-closing operator):

- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/Basic.lean`
  - `HeytingLean.ClosingTheLoop.MR.MRSystem`
  - `HeytingLean.ClosingTheLoop.MR.Selector`
  - `HeytingLean.ClosingTheLoop.MR.evalAt`
- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/InverseEvaluation.lean`
  - `HeytingLean.ClosingTheLoop.MR.InjectiveEvalAt` (paper uniqueness-at-b)
  - `HeytingLean.ClosingTheLoop.MR.InverseEvaluation` (chosen inverse-evaluation / section at b)
  - `HeytingLean.ClosingTheLoop.MR.InverseEvaluation.of_evalAt_surjective` (derive a section from surjectivity via choice)
  - `HeytingLean.ClosingTheLoop.MR.InverseEvaluation.beta_leftInverse_of_injective` (injectivity + right-inverse ⇒ left-inverse)
  - `HeytingLean.ClosingTheLoop.MR.InverseEvaluation.beta_injective`
  - `HeytingLean.ClosingTheLoop.MR.EvalImage` (choice-free “inverse on image”)
- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/ClosureOperator.lean`
  - `HeytingLean.ClosingTheLoop.MR.closeSelector`
  - `HeytingLean.ClosingTheLoop.MR.closeSelector.idem`
  - `HeytingLean.ClosingTheLoop.MR.closeSelector.of_evalAt_surjective` (noncomputable closure operator without assuming `RightInverseAt` as data)
  - `HeytingLean.ClosingTheLoop.MR.IsClosed`

Tier 2 ((F,A) skeleton — typed diagram container, no probability yet):

- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/FA/Diagram.lean`
  - `HeytingLean.ClosingTheLoop.FA.Node`
  - `HeytingLean.ClosingTheLoop.FA.Edge`
  - `HeytingLean.ClosingTheLoop.FA.Diagram`
- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/FA/Temporal.lean`
  - `HeytingLean.ClosingTheLoop.FA.TemporalNode`
  - `HeytingLean.ClosingTheLoop.FA.TemporalEdge`
  - `HeytingLean.ClosingTheLoop.FA.TemporalDiagram`

Tier 2b (Yoneda/naturality view):

- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/YonedaViewNat.lean`
  - `HeytingLean.ClosingTheLoop.Cat.curryNatIso`
- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/Admissible.lean`
  - `HeytingLean.ClosingTheLoop.Cat.Admissible.Hom` (admissible maps as `Subobject (A ⟹ B)`)
  - `HeytingLean.ClosingTheLoop.Cat.Admissible.Hom.ι`
  - `HeytingLean.ClosingTheLoop.Cat.Admissible.SelectorSub` (admissible selectors as a subobject)
- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/EvalImage.lean`
  - `HeytingLean.ClosingTheLoop.Cat.EvalImage.betaOnImage` (categorical inverse-on-image under `Mono`)
- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/Concreteness.lean`
  - `HeytingLean.ClosingTheLoop.Cat.idem_of_map_idem` (faithful `U : C ⥤ Type` route)
  - `HeytingLean.ClosingTheLoop.Cat.idem_of_yoneda_map_idem` (canonical Yoneda/presheaf route)
  - `HeytingLean.ClosingTheLoop.Cat.map_close_eq` (scoped “structure preservation” bridge: compute `U.map close` under explicit comparison data)
  - `HeytingLean.ClosingTheLoop.Cat.PreservesSelectorEval` (explicit “U preserves exponential/eval” interface)

Tier 3 (nucleus bridge):

- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/NucleusBridge.lean`
  - `HeytingLean.ClosingTheLoop.Semantics.MeetRetraction`
  - `HeytingLean.ClosingTheLoop.Semantics.MeetRetraction.retractionNucleus`

Tier 3b (preorder-time semantics seed):

- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/PreorderTime.lean`
  - `HeytingLean.ClosingTheLoop.Semantics.futureKernel`
  - `HeytingLean.ClosingTheLoop.Semantics.futureKernel.idem`
  - `HeytingLean.ClosingTheLoop.Semantics.reachabilityNucleus` (inflationary nucleus; adds states unreachable from a chosen base time `t₀` with `∀ t, t₀ ≤ t`)

Tier 3b+ (general time category semantics):

- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/FunctorialTime.lean`
  - `HeytingLean.ClosingTheLoop.Semantics.FunctorialTime.futureKernel` (quantify over morphisms `t ⟶ t'`)
  - `HeytingLean.ClosingTheLoop.Semantics.FunctorialTime.reachabilityNucleus` (inflationary nucleus from base time `t₀`)

Tier 3c (computation/dynamics hooks — λ-calculus + processes + Mealy):

- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/KernelLaws.lean`
  - `HeytingLean.ClosingTheLoop.Semantics.Kernel`
- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/LambdaIRBridge.lean`
  - `HeytingLean.ClosingTheLoop.Semantics.LambdaIRBridge.eval_beta`
  - `HeytingLean.ClosingTheLoop.Semantics.LambdaIRBridge.eval_lam_eq_curry`
- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/ProcessBridge.lean`
  - `HeytingLean.ClosingTheLoop.Semantics.ProcessBridge.KprocKernel`
  - `HeytingLean.ClosingTheLoop.Semantics.ProcessBridge.wellTyped_fixedPoint`
- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/Mealy.lean`
  - `HeytingLean.ClosingTheLoop.Semantics.Mealy` (Mealy machine)
  - `HeytingLean.ClosingTheLoop.Semantics.MRBridge.closeMachine` (closure loop as a Mealy dynamics)

Tier 3d (relational realizability theorem):

- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/RelationalRealizability.lean`
  - `HeytingLean.ClosingTheLoop.Semantics.Realizability.realizable_invariant_of_simulation`

Tests / toy models:

- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Tests/ClosureIdempotent.lean`
  - a tiny MR instance + checks of idempotence and “collapse to b”.

Umbrella import:

- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop.lean`

## Quick local navigation commands

From repo root:

- Find the loop-closing theorem:
  - `rg -n \"theorem idem\" RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/ClosureOperator.lean`
- Find the inverse evaluation structure:
  - `rg -n \"structure InverseEvaluation\" RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/InverseEvaluation.lean`
- Find the Yoneda-style naturality statement:
  - `rg -n \"def curryNatIso\" RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/YonedaViewNat.lean`
- Find the admissible-hom encoding:
  - `rg -n \"abbrev Hom\" RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/Admissible.lean`
- Find the categorical inverse-on-image lemma:
  - `rg -n \"betaOnImage\" RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/EvalImage.lean`
- Find the retraction→nucleus bridge:
  - `rg -n \"def retractionNucleus\" RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/NucleusBridge.lean`

## “Paper ↔ Lean” naming glossary

Paper idea (informal) → Lean encoding:

- “admissible maps” `H(A,B)` → `MRSystem.H : Set (A → B)`
- “selector/replacement map space” `B → H(A,B)` → `Selector S := S.B → {g // g ∈ S.H}`
- “evaluation at b” `Φ ↦ Φ(b)` → `evalAt S b : Selector S → AdmissibleMap S`
- “inverse evaluation” `β_b` with `evalAt b (β_b g) = g` → `InverseEvaluation S b`
- “loop closure operator” `R(Φ)=β_b(Φ(b))` → `closeSelector S b ie Φ`
- “closed organization/selector” fixed point `R(Φ)=Φ` → `IsClosed S b ie Φ`

Important modeling note:
- The paper often emphasizes *injectivity* of evaluation at `b`. In Lean we directly assume a *chosen inverse-evaluation map* (`β` with a right-inverse law). This matches the “inverse evaluation exists” closure hypothesis and is the exact assumption needed to define the loop-closing operator and prove idempotence without `Classical.choice`.
