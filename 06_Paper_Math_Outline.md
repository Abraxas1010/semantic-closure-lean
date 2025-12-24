# Closing the Loop (2025, López‑Díaz & Gershenson) — math outline + Lean mapping

This note summarizes the **basic mathematical scaffolding** used in the paper *Closing the loop: how semantic closure enables open-ended evolution* (J. R. Soc. Interface 22: 20250784) and maps it to the Lean mechanization shipped in this repo, including the standalone researcher-verification bundle under:

- `./RESEARCHER_BUNDLE/`

---

## 1) Core mathematics in the PDF (minimal, paper-facing)

### 1.1 (M,R) systems in a (concrete) category

The paper starts with a **concrete category** `C` and objects `A, B ∈ Ob(C)`. It fixes:

- a “metabolism” morphism `f ∈ H(A, B)`,
- a “repair/replacement” morphism `Φ_f ∈ H(B, H(A, B))`,
- where `H(X, Y)` is treated as a **proper subset** of the hom-set `Hom_C(X, Y)`.

The basic diagram is (paper eq. (2.1)):

`A --f--> B --Φ_f--> H(A,B)`.

### 1.2 Evaluation and inverse evaluation (the closure move)

The evaluation map (paper eq. (2.2)) is the familiar:

- `eval_{Y,X} : Y^X × X → Y` where `Y^X` denotes a hom-set of maps `X → Y`.

Fixing a point `b : B`, the paper specializes evaluation to a map

- `b̂ : H(B, H(A,B)) → H(A,B)`, given by `Φ ↦ Φ(b)`.

The key “closure” condition is the **injectivity-at-b** implication (paper eq. (2.3)):

- if `Φ₁(b) = Φ₂(b)` then `Φ₁ = Φ₂`.

If `b̂` is injective, it admits a left inverse (on its image); the paper denotes this inverse
evaluation map by `β_b := b̂⁻¹` and uses it to build the “closure/replication” arrow (paper eq. (2.4)):

`B --Φ_f--> H(A,B) --β_b--> H(B, H(A,B))`.

Composing yields the canonical closure loop (paper eq. (2.5)):

`A --f--> B --Φ_f--> H(A,B) --β_b--> H(B,H(A,B))`,

and the “closed-to-efficient-causation” loop is expressed as `β_b ∘ Φ_f ∘ f`.

### 1.3 Restricting to a biologically admissible selector space

In the biological example, the paper restricts the selector space to a subset (denoted `S(G)`)
compatible with a fixed genome `G`, and then assumes injectivity of evaluation on that reduced
space at a distinguished configuration `b⋆`.

This is the “inverse evaluation **on the image**” viewpoint: one should not assume a global
`β_b : H(A,B) → H(B,H(A,B))` without additional hypotheses.

### 1.4 Temporal parametrization of (F,A) systems

Later, the paper extends (F,A) systems with explicit **time scales** per process:

- rename arrows into `φ, ψ, θ, α, β`,
- assign each a timescale `τ_x`,
- represent multi-scale coupling as an asynchronous dynamic Bayesian network and write an
  associated joint distribution (paper eqs. (3.3)–(3.5)).

The paper’s math at this stage is primarily:

- (typed) structural diagrams,
- time-indexing and multi-scale coupling constraints,
- probabilistic graphical-model semantics.

---

## 2) What the Lean development implements (and where)

### 2.1 Set-level (Tier 1): selectors, evaluation-at-b, inverse evaluation, closure

Lean implements a conservative “Set/Type” rendering of the paper’s ingredients:

- **admissible metabolisms** `H(A,B)` as a subtype of `A → B`,
- **selectors** `Φ : B → H(A,B)`,
- **evaluation at a point** `evalAt b : Selector → H(A,B)` as `Φ ↦ Φ b`.

Key split (matching the paper’s “injectivity vs inverse evaluation” tension):

- paper’s eq. (2.3) **injectivity-at-b**:
  - Lean: `HeytingLean.ClosingTheLoop.MR.InjectiveEvalAt`
- stronger “chosen inverse evaluation β” (paper’s `β_b` as a total function):
  - Lean: `HeytingLean.ClosingTheLoop.MR.RightInverseAt` (a.k.a. `InverseEvaluation`)
- “β only on the image” (choice-free, always honest):
  - Lean: `HeytingLean.ClosingTheLoop.MR.EvalImage` + `betaOnImage`.

Loop-closing operator (paper’s `β_b ∘ (−)(b)`):

- Lean: `HeytingLean.ClosingTheLoop.MR.closeSelector`
- theorem: `HeytingLean.ClosingTheLoop.MR.closeSelector.idem`
- fixed points: `HeytingLean.ClosingTheLoop.MR.IsClosed`

### 2.2 Category-level (Tier 2): exponentials, evaluation, inverse-on-image, Yoneda route

Lean also provides a categorical mirror that avoids overclaiming:

- works with exponentials / evaluation-at-a-point,
- gives “inverse evaluation” from principled hypotheses (`evalAt` is an iso / split epi),
- provides an explicit “inverse-on-image” guardrail (no global `β` from a mere mono),
- provides a **Yoneda** reflection route to avoid assuming concreteness when not needed.

### 2.3 Time semantics (Tier 2): beyond preorder time

The paper’s “temporal parametrization” is not fully probabilistic-mechanized, but Lean provides:

- preorder-time kernel/nucleus seed (`PreorderTime.lean`),
- **general time category** semantics (`FunctorialTime.lean`): quantification over morphisms `t ⟶ t'`.

### 2.4 Computation hooks (Tier 2): λ-calculus + process calculus + Mealy + realizability

Lean implements *hooks* for the paper’s “models of computation” theme:

- λ-calculus seed via `HeytingLean.LambdaIR` (β-law lemma in `LambdaIRBridge.lean`),
- process calculus safety kernel (`ProcessBridge.lean`),
- Mealy/coalgebra hook for viewing closure as a dynamics (`Mealy.lean`),
- one generic “relational realizability” theorem: invariants transport along simulations.

### 2.5 Reproducibility bundle artifacts (Lean + LambdaIR + C)

The standalone verifier:

- `./RESEARCHER_BUNDLE/scripts/verify_closing_the_loop.sh`

builds and runs `closing_the_loop_bundle_demo`, which emits:

- LambdaIR term (human-readable): `artifacts/compiler/ir/add1.lambdair.txt`
- MiniC repr: `artifacts/compiler/ir/add1.minic.txt`
- generated C source: `artifacts/compiler/c/add1.c`

and compiles/runs the emitted C with `cc`.

---

## 3) Two-track picture (computation vs dynamics)

```text
COMPUTATION TRACK:                                        DYNAMICS TRACK:

Lean (ClosingTheLoop proofs)                               (M,R)/(F,A) diagrams in C
    ↓  (proofs erase; executable remains)                      ↓  (time-indexing / reachability)
LambdaIR semantics (β-law)                                  ReachSystem / Kernel / Nucleus
    ↓  (certified compilation fragments)                         ↓  (simulation relations)
MiniC AST  →  tiny-C AST  →  emitted C  →  cc binary          Process / Mealy / functorial-time semantics
    ↓                                                          ↓
Curry–Howard (proofs-as-programs)                         Relational realizability (invariants transport)

══════════════════════ HEYTING NUCLEUS  Ω_R  ══════════════════════
                         ↓
         Fixed points = semantically closed selectors / invariants
                   (dynamics: halting states / periodic orbits)
```

Notes:

- The “nucleus” line is a *mathematical interface*: semantic closure is expressed as a fixed-point condition,
  and nuclei/kernels provide a uniform language for stable/closed predicates.
- The bundle’s demo pipeline is intentionally tiny (`add1`), but it is a **verifiable template** for exporting
  lambda-level artifacts and concrete C code alongside Lean proofs.

