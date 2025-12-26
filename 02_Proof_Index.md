# Proof index (what is proved, and where)

This is the minimal set of “results you can cite” from this mechanization.

## Tier 1: loop closure on selectors

1. **Inverse evaluation implies injectivity of the inverse map**
   - Lean: `HeytingLean.ClosingTheLoop.MR.InverseEvaluation.beta_injective`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/InverseEvaluation.lean`
   - Informal: if `β x = β y` then applying `evalAt b` and using the right-inverse law gives `x = y`.

1b. **Derive inverse evaluation from surjectivity (existence-only → chosen β, noncomputable)**
   - Lean: `HeytingLean.ClosingTheLoop.MR.InverseEvaluation.of_evalAt_surjective`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/InverseEvaluation.lean`
   - Informal: from `∀ g, ∃ Φ, Φ(b)=g` we can pick `β g := choose Φ` (uses choice) and get `evalAt b (β g)=g`.

1c. **Injectivity upgrades a right inverse to a genuine inverse on selectors**
   - Lean: `HeytingLean.ClosingTheLoop.MR.InverseEvaluation.beta_leftInverse_of_injective`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/InverseEvaluation.lean`
   - Informal: if `evalAt b` is injective and `β` is a right inverse, then `β (Φ(b)) = Φ` for all selectors `Φ`.

2. **Loop-closing operator is idempotent**
   - Lean: `HeytingLean.ClosingTheLoop.MR.closeSelector.idem`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/ClosureOperator.lean`
   - Informal: `close(close Φ) = close Φ` since `close Φ` is definitionally `β (Φ b)` and evaluation at `b` of `β` returns the original map.

3. **Closed selectors (fixed points)**
   - Lean: `HeytingLean.ClosingTheLoop.MR.IsClosed`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/ClosureOperator.lean`
   - Informal: `IsClosed Φ : Prop` is the fixed-point predicate `closeSelector Φ = Φ`.

4. **Closing always yields a closed selector**
   - Lean: `HeytingLean.ClosingTheLoop.MR.IsClosed.close_isClosed`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/ClosureOperator.lean`
   - Informal: immediate from idempotence.

5. **Closed selectors are exactly the image of β (semantic closure = fixed point = reconstructible)**
   - Lean: `HeytingLean.ClosingTheLoop.MR.IsClosed.exists_eq_beta_iff`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/ClosureOperator.lean`
   - Informal: `IsClosed Φ` iff `∃ g, β g = Φ`.

## Tier 3: bridge to nuclei

6. **Meet-preserving section–retraction induces a nucleus**
   - Lean: `HeytingLean.ClosingTheLoop.Semantics.MeetRetraction.retractionNucleus`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/NucleusBridge.lean`
   - Informal: define `R(x) := dec(enc(x))`; meet preservation gives `R(x ⊓ y) = R(x) ⊓ R(y)`; section law yields idempotence; `x ≤ R(x)` is assumed explicitly.

## Tier 3b: preorder-time semantics kernel

7. **Future-kernel operator is idempotent (closure law)**
   - Lean: `HeytingLean.ClosingTheLoop.Semantics.futureKernel.idem`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/PreorderTime.lean`
   - Informal: a state is future-kernel-safe iff its transport to all future times is safe; applying the same
     operator again is redundant.

8. **Reachability nucleus on time-indexed predicates (inflationary, meet-preserving)**
   - Lean: `HeytingLean.ClosingTheLoop.Semantics.reachabilityNucleus`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/PreorderTime.lean`
   - Informal: to align with the repo’s nucleus convention, we close any predicate by unioning in states that are
     unreachable from a chosen base time `t₀` (assumed `t₀ ≤ t` for all `t`); this yields a bona fide `Nucleus`
     on time-indexed predicates.

8b. **General time category kernel/nucleus (beyond preorders)**
   - Lean: `HeytingLean.ClosingTheLoop.Semantics.FunctorialTime.futureKernel`,
     `HeytingLean.ClosingTheLoop.Semantics.FunctorialTime.reachabilityNucleus`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/FunctorialTime.lean`
   - Informal: replace `t ≤ t'` with quantification over morphisms `t ⟶ t'` in a general time category `T`.

## Tier 3c: computation/dynamics hooks (λ-calculus + processes + Mealy)

9. **λ-calculus β-law (functional computation seed)**
   - Lean: `HeytingLean.ClosingTheLoop.Semantics.LambdaIRBridge.eval_beta`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/LambdaIRBridge.lean`
   - Informal: evaluating `(λx. body) arg` extends the environment with the value of `arg`.

10. **Process calculus kernel is exact on well-typed processes (concurrent computation seed)**
   - Lean: `HeytingLean.ClosingTheLoop.Semantics.ProcessBridge.wellTyped_fixedPoint`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/ProcessBridge.lean`
   - Informal: the safety kernel `Kproc` returns exactly the well-typed processes in a fixed context.

11. **(M,R) closure loop as a one-step stabilizing dynamics (Mealy/coalgebra hook)**
   - Lean: `HeytingLean.ClosingTheLoop.Semantics.MRBridge.closeMachine_step_idem`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/Mealy.lean`
   - Informal: viewing `closeSelector` as a state update, idempotence implies stabilization after one step.

12. **Relational realizability (invariants transport along simulations)**
   - Lean: `HeytingLean.ClosingTheLoop.Semantics.Realizability.realizable_invariant_of_simulation`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/RelationalRealizability.lean`
   - Informal: if a relation simulates reachability, then any future-closed predicate on the target yields a
     future-closed predicate on the source via existence-based realizability.

## Tier 2b: Yoneda/naturality view

- File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/YonedaViewNat.lean`
- Result: `HeytingLean.ClosingTheLoop.Cat.curryNatIso`
- Informal: currying is natural in `X`, so `H^B` represents the functor `X ↦ Hom(B ⊗ X, H)`.

## Tier 2c: categorical guardrails (image-only inverse; concreteness vs Yoneda)

1. **Inverse evaluation on the image (no overclaim from mono)**
   - Lean: `HeytingLean.ClosingTheLoop.Cat.EvalImage.betaOnImage_evalAt`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/EvalImage.lean`
   - Informal: if `evalAt b` is mono, there is a canonical map `image(evalAt b) ⟶ (B ⟹ H)` agreeing with
     evaluation on the image (but not a total inverse `H ⟶ (B ⟹ H)`).

2. **No “concreteness assumption” needed for reflection (Yoneda route)**
   - Lean: `HeytingLean.ClosingTheLoop.Cat.idem_of_yoneda_map_idem`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/Concreteness.lean`
   - Informal: the canonical Yoneda embedding is faithful, so equalities/idempotence can be reflected from presheaves.

3. **Scoped “structure preservation” computation of `U.map close` (faithful-embedding viewpoint, made explicit)**
   - Lean: `HeytingLean.ClosingTheLoop.Cat.map_close_eq`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/Concreteness.lean`
   - Informal: assuming explicit comparison data identifying `U(H^B)` with `U(B) → U(H)` and sending `U(evalAt b)`
     to evaluation at the induced point, the mapped closure operator has the expected form “sample at `b` then apply `β`”.

4. **Explicit “U preserves exponential/eval” interface**
   - Lean: `HeytingLean.ClosingTheLoop.Cat.PreservesSelectorEval`
   - File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/Concreteness.lean`
   - Informal: packages exactly the comparison data and compatibility equation required to interpret selector
     objects and evaluation as genuine functions under a functor `U : C ⥤ Type`.

## Toy model / smoke checks

- File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Tests/ClosureIdempotent.lean`
- Purpose: exercises the definitional behavior of `closeSelector` on a tiny MR system and checks idempotence reduces by simp.

---

## Noneism Extension: Eigencomputable Framework

The Noneism layer refines the interpretation of nonconstructive definitions by distinguishing between:
- **Arbitrary choice**: `Classical.choose` without grounding dynamics
- **Eigencomputable**: determined by a stabilizing dynamics with a unique fixed point

### Core Eigencomputable Theorems

13. **Unique fixed point determines value (eigenform uniqueness)**
   - Lean: `HeytingLean.Noneism.Eigen.determined_by_dynamics`
   - File: `RESEARCHER_BUNDLE/HeytingLean/Noneism/Eigen/Basic.lean`
   - Informal: if `e : Eigen α` and `d a = a` for `d = e.dynamics`, then `a = e.val`.

14. **Equal dynamics implies equal values**
   - Lean: `HeytingLean.Noneism.Eigen.val_unique_of_eq_dynamics`
   - File: `RESEARCHER_BUNDLE/HeytingLean/Noneism/Eigen/Basic.lean`
   - Informal: two `Eigen` values with the same dynamics must have the same underlying value.

### Selector Dynamics Theorems

15. **Selector dynamics characterization**
   - Lean: `HeytingLean.Noneism.Bridge.selectorDynamics_stable_iff`
   - File: `RESEARCHER_BUNDLE/HeytingLean/Noneism/Bridge/SelectorDynamics.lean`
   - Informal: `selectorDynamics b Φ = Φ` iff `∀ b', Φ b' = Φ b` (stable selectors are constant).

16. **Unique stable selector per metabolism (key uniqueness theorem)**
   - Lean: `HeytingLean.Noneism.Bridge.selectorDynamics_unique_stable`
   - File: `RESEARCHER_BUNDLE/HeytingLean/Noneism/Bridge/SelectorDynamics.lean`
   - Informal: for each metabolism `f`, there exists a unique selector `Φ` such that `selectorDynamics b Φ = Φ` and `evalAt b Φ = f`.

17. **Fiber dynamics has unique fixed point**
   - Lean: `HeytingLean.Noneism.Bridge.selectorDynamicsAt_unique_fixed`
   - File: `RESEARCHER_BUNDLE/HeytingLean/Noneism/Bridge/BetaEigen.lean`
   - Informal: on the fiber `{Φ // evalAt b Φ = f}`, the induced dynamics has exactly one fixed point.

### Eigencomputable β Construction

18. **β is a right inverse (eigencomputable version)**
   - Lean: `HeytingLean.Noneism.Bridge.beta_right_inverse`
   - File: `RESEARCHER_BUNDLE/HeytingLean/Noneism/Bridge/BetaEigen.lean`
   - Informal: `evalAt b (beta b f) = f` — the eigencomputable β satisfies the paper's eq (2.4).

19. **β is stable under selector dynamics**
   - Lean: `HeytingLean.Noneism.Bridge.beta_stable`
   - File: `RESEARCHER_BUNDLE/HeytingLean/Noneism/Bridge/BetaEigen.lean`
   - Informal: `selectorDynamics b (beta b f) = beta b f` — β outputs are fixed points of the dynamics.

20. **β equals the constant selector**
   - Lean: `HeytingLean.Noneism.Bridge.beta_eq_const`
   - File: `RESEARCHER_BUNDLE/HeytingLean/Noneism/Bridge/BetaConstruction.lean`
   - Informal: `beta b f = (fun _ => f)` — the unique stable selector evaluating to `f` is the constant function.

21. **Eigencomputable β agrees with raw choice when stable**
   - Lean: `HeytingLean.Noneism.Bridge.beta_eq_betaRaw_of_stable`
   - File: `RESEARCHER_BUNDLE/HeytingLean/Noneism/Bridge/BetaConstruction.lean`
   - Informal: if `betaRaw` (classical choice) happens to be stable, it must equal the eigencomputable `beta`.

### Raw Choice Comparison

22. **Raw choice β is a right inverse**
   - Lean: `HeytingLean.Noneism.Bridge.betaRaw_right_inverse`
   - File: `RESEARCHER_BUNDLE/HeytingLean/Noneism/Bridge/BetaConstruction.lean`
   - Informal: `evalAt b (betaRaw b hsurj f) = f` — the choice-based construction also satisfies the right-inverse law.

### Paper Alignment Summary

| Paper | Noneism Lean | Status |
|-------|--------------|--------|
| Eq (2.3) injectivity | `selectorDynamics_stable_iff` | ✓ Dynamics characterization |
| Eq (2.4) β construction | `beta`, `betaEigenAt` | ✓ **Eigencomputable** |
| Eq (2.5) closure loop | `beta_right_inverse` + `beta_stable` | ✓ Loop closes and stabilizes |
| Choice grounding | `beta_eq_betaRaw_of_stable` | ✓ Raw choice = Eigen when stable |
