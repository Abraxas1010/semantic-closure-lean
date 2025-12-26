# ClosingTheLoop — Researcher Agenda Alignment Report

Date: 2025-12-24  
Repo branch: `quantum_extended`  
Key commit: `ac70cb8` (“ClosingTheLoop: paper/cat formalization + researcher bundle”)  
Paper: *Closing the loop: how semantic closure enables open-ended evolution* (J. R. Soc. Interface 22: 20250784)

---

## 0) What I reviewed in the PDF (what “closing the loop” means there)

The paper sets up the canonical Rosen/Hofmeyr-style
(M,R)/(F,A) story and then isolates the “inverse evaluation / closure” move:

- (2.1) an (M,R)-system core diagram with “admissible maps”:
  - objects A, B
  - a metabolism `f ∈ H(A,B)` and a repair/replacement map `Φf ∈ H(B, H(A,B))`
  - where `H(X,Y)` is a proper subset of all maps `X → Y`.
- (2.2) the evaluation map `eval_{Y,X} : Y^X × X → Y`, and then “fix a point” `b ∈ B` to obtain:
  - an evaluation-at-b map “b̂” of the form `b̂ : H(B, H(A,B)) → H(A,B)` sending `Φ ↦ Φ(b)`.
- (2.3) the paper’s uniqueness/injectivity condition at `b`:
  - `Φ1(b) = Φ2(b) ⇒ Φ1 = Φ2`.

Then the excerpt says (paraphrasing): if `b̂` is injective it has a left inverse, denoted `β_b := (b̂)^{-1}`, and uses
that to “close the loop” by forming a composite (2.4–2.6) involving `β_b`.

Key logic point (important for paper honesty):

- In `Set`, injectivity alone does not give a globally-defined inverse `(b̂)^{-1} : H(A,B) → H(B,H(A,B))` without
  additional assumptions (e.g. a section/surjectivity/bijection, or choice + default values). A canonical, choice-free
  inverse exists on the image/range (or if the preimage witness is carried).
- The Lean work below explicitly splits “paper-shaped injectivity” from “chosen inverse evaluation map β” so we do
  not overclaim.

---

## 1) What is formalized in Lean right now (and where)

There are two “presentations” of the same math:

### A) Main repo formalization (paper-facing, in-tree)

All core math lives under:

- `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/**`
- umbrella: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop.lean`
- “main theorems”: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Main.lean`

### B) Independent verification bundle (external-researcher reproducibility)

Self-contained folder:

- `./RESEARCHER_BUNDLE/`
- one-command verify script:
  - `./RESEARCHER_BUNDLE/scripts/verify_closing_the_loop.sh`
- key reports produced/checked:
  - `./RESEARCHER_BUNDLE/reports/ClosingTheLoop_DEPENDENCIES.md`
  - `./RESEARCHER_BUNDLE/reports/ClosingTheLoop_PROOF_INDEX.md`
  - `./RESEARCHER_BUNDLE/reports/BUILD_TRANSCRIPT_STRICT.txt`
  - `./RESEARCHER_BUNDLE/reports/GREP_AXIOM_SORRY_ADMIT.txt`
  - `./RESEARCHER_BUNDLE/reports/CAB_VERIFY.txt`
  - `./RESEARCHER_BUNDLE/reports/SHA256SUMS.txt`

---

## 2) How the Lean math matches the PDF’s “injectivity vs inverse-evaluation” story

### 2.1 Set-level (Tier 1): we split the assumptions cleanly

Paper-shaped hypothesis = injectivity/uniqueness at `b` (matches (2.3))

- File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/InverseEvaluation.lean`
- Definition:
  - `HeytingLean.ClosingTheLoop.MR.InjectiveEvalAt (S) (b)`
- Main lemma (paper’s (2.3) in Lean form):
  - `HeytingLean.ClosingTheLoop.MR.InjectiveEvalAt.eq_of_eval_eq`
  - used in `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Main.lean` as:
    - `HeytingLean.ClosingTheLoop.SetLevel.selector_eq_of_eval_eq`

Stronger hypothesis = an actual chosen inverse evaluation map `β`

- File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/InverseEvaluation.lean`
- Definition:
  - `HeytingLean.ClosingTheLoop.MR.InverseEvaluation (S) (b)` (paper name)
  - alias: `HeytingLean.ClosingTheLoop.MR.RightInverseAt (S) (b)` (precise “section-at-b” name)
  - data: `β : H(A,B) → Selector`
  - law: `evalAt b (β g) = g`
- Consequences are exposed explicitly (so readers see what extra was assumed):
  - `HeytingLean.ClosingTheLoop.MR.InverseEvaluation.beta_injective`
  - `HeytingLean.ClosingTheLoop.MR.InverseEvaluation.evalAt_surjective`

Choice-free “inverse on the image”

- File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/InverseEvaluation.lean`
- Structure: `HeytingLean.ClosingTheLoop.MR.EvalImage`
- Map: `HeytingLean.ClosingTheLoop.MR.EvalImage.betaOnImage`
- This is the correct “no-choice” way to say “inverse evaluation exists on the image”: the witness selector is
  bundled.

### 2.2 Closure operator and idempotence (Tier 1): requires the chosen β

- File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/MR/ClosureOperator.lean`
- Definition:
  - `HeytingLean.ClosingTheLoop.MR.closeSelector`
  - `closeSelector Φ := β (Φ b)`
- Theorem:
  - `HeytingLean.ClosingTheLoop.MR.closeSelector.idem`
- Fixed points:
  - `HeytingLean.ClosingTheLoop.MR.IsClosed` and `HeytingLean.ClosingTheLoop.MR.IsClosed.close_isClosed`

### 2.3 We also prove the mismatch is real (test)

- File: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Tests/Test_AssumptionMismatch.lean`
- It constructs a tiny `Set` example where:
  - `InjectiveEvalAt` holds (selector space is a subsingleton so evaluation is injective),
  - but `RightInverseAt` cannot exist because evaluation is not surjective on the restricted selector space.
- This directly supports a paper-facing statement: “(2.3) does not give a global β_b on all of H(A,B) unless
  additional assumptions hold.”

---

## 3) Alignment with the researchers’ 1–7 agenda (status + gaps)

I’ll use your numbering and say exactly what we have vs what remains.

### (1) “Everyone assumes concreteness is minimal — how valid is that?”

What we did (fits the spirit):

- We did not assume concreteness to define the categorical closure story. We formalized the closure/idempotence
  argument inside an abstract CCC, directly.
- We added a minimal, formal “where concreteness enters” lemma:
  - `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/Concreteness.lean`
  - `HeytingLean.ClosingTheLoop.Cat.idem_of_map_idem`:
    if `U : C ⥤ Type` is faithful, then equality/idempotence after mapping implies equality/idempotence upstairs.

What’s missing to fully meet the agenda:

- A stronger bridge theorem of the form:
  “If `U` is faithful and preserves the relevant structure (products/exponentials), then the categorical construction
  transports to the set-level one.”
  Right now we isolate equality reflection but we don’t formalize preservation assumptions.

### (2) “(M,R)-systems derived functorially via Yoneda”

What we did (partial but real):

- We formalized the CCC currying equivalence:
  - `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/YonedaView.lean`
  - `HeytingLean.ClosingTheLoop.Cat.curryEquiv : Hom(B × X, H) ≃ Hom(X, H^B)`
- We also added the functor-level naturality statement:
  - `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/YonedaViewNat.lean`
  - `HeytingLean.ClosingTheLoop.Cat.curryNatIso`
- This is exactly the representability principle that “feels Yoneda/Lawvere modern” and is the standard categorical
  mechanism behind “selectors represent a hom-functor”.

What’s missing:

- Further Yoneda-facing packaging: presenting the representability statement explicitly as a `Representable`/Yoneda lemma application, not just a `NatIso` between hom-functors (optional; cosmetic but nice for the paper narrative).

### (3) “Rosen’s Eilenberg–MacLane viewpoint: faithful embedding into Set”

What we did:

- We kept the discussion formal: the only “Set transfer” we encoded is the faithful reflection of equality
  (`Cat.idem_of_map_idem`), which is the exact technical content of “reason in Set without losing equality
  information”.

What’s missing:

- If the paper wants to justify “reason in Set without forfeiting structural generality” for this specific
  construction, we should add a lemma stating which categorical structures must be preserved/reflected by `U`.

### (4) “Minimum necessary/sufficient conditions to construct (M,R)-systems from scratch”

What we did (a first step):

- We built a clean “structure ladder” for the closure endomorphism:
  - Need exponentials to have “selectors” (`H^B`).
  - Need a point `b : 𝟙 ⟶ B` to even state “evaluate at `b`”.
  - Need a section `β` of `evalAt b` to define closure and prove idempotence.
- Files:
  - `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/Selector.lean`
  - `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/InverseEvaluation.lean`
  - `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/ClosureOperator.lean`

What’s missing (big, but now well-scoped):

- A categorical formalization of the “proper subset of the hom-set” `H(A,B)` (admissible morphisms). Candidates:
  - subobjects of exponentials,
  - a fibration/displayed category of admissible arrows,
  - or a concreteness+predicate encoding (least categorical).
- A principled route to derive `β` (or an “inverse-on-image”) from categorical assumptions, rather than assuming it.

### (5) “Connections: Mealy machines, fibrations, bicategories, terminal coalgebras, autographs, eigenforms…”

What we did (minimal hook):

- We added a typed diagram skeleton (no probability/temporal semantics yet):
  - `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/FA/Diagram.lean`
- We made fixed-point structure explicit (`IsClosed`), which is a natural starting point for “eigenform” discussion.

What’s missing:

- None of these deep connections are mechanized in `HeytingLean.ClosingTheLoop` yet; they would be separate new
  modules layered on top of the closure operator (coalgebraic/process/Mealy/fibration viewpoints).

### (6) “Unify models of computation (λ-calculus ↔ process algebra) to understand realizability limits”

What we did (foundation only):

- The CCC layer (`CartesianClosed`) is the standard semantic home for simply-typed λ-calculus; we did not yet
  implement a λ-calculus semantics module, but the categorical prerequisites are in place.
- No process algebra / concurrency model is implemented yet in `ClosingTheLoop`.

What’s missing:

- A small λ-calculus object language + semantics into the CCC layer.
- A small process model (e.g. LTS/coalgebra) + relation to closure.
- A formal “realizability boundary” statement: which assumptions yield realizers for relational models.

### (7) “Heyting algebra connections”

What we did (honest and mathlib-based):

- We did not claim “idempotent ⇒ nucleus” without extra hypotheses.
- We added:
  - `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/NucleusBridge.lean` (meet-preserving retraction → nucleus)
  - `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Semantics/NucleusFixedPoints.lean` (construct a `Nucleus` from explicit axioms;
    fixed points via `Order.Sublocale`)
- This gives a clean checklist for when “semantic closure” becomes a modality/nucleus/Heyting-core story.

What’s missing:

- Prove that the specific `closeSelector` is monotone/meet-preserving under explicit conditions on the selector space/
  admissible-map space (currently not assumed, so not claimed).

---

## 4) What still needs doing to better fit the paper excerpt specifically

Priority A (paper-facing correctness):

1. Add a clear paper-facing statement: (2.3) ⇒ uniqueness at `b` only, not a total `β_b` on all `H(A,B)` without more
   assumptions.
   - We already have the Lean split; the paper pack should explicitly adopt that logic.
2. If authors truly want a global `β_b : H(A,B) → H(B,H(A,B))`, specify the missing assumption:
   - e.g. split epi / surjectivity (or bijection in `Set`), or restrict codomain to the image.
3. Add the categorical analogue of “inverse on image” (subobject/range or witness-carrying construction) to mirror
   the set-level `EvalImage`.

Priority B (toward the researchers’ “minimal structure” programme):

4. Weaken CCC assumptions where possible: replace `[CartesianClosed C]` with “`B` is exponentiable” if mathlib supports
   it cleanly.
5. Add an “admissible morphisms” layer categorically (subobject/fibration), so `H(A,B)` is not just “everything”.

Priority C (toward semantic closure enabling open-ended evolution):

6. Introduce a time index / temporal parametrization layer (the excerpt’s extension of (F,A)-systems is temporal).
7. Connect closure/fixed points to concrete computational dynamics (Mealy/coalgebra/etc.) in separate modules.

---

## 5) Reproducibility + “proof artifacts” (what external authors can independently verify)

Independent bundle: `./RESEARCHER_BUNDLE/`

One command:

- `cd ./RESEARCHER_BUNDLE && ./scripts/verify_closing_the_loop.sh`

What it produces/checks (relevant to “authors can verify”):

- Strict build transcript: `./RESEARCHER_BUNDLE/reports/BUILD_TRANSCRIPT_STRICT.txt`
- Repo-wide marker scan inside the bundle: `./RESEARCHER_BUNDLE/reports/GREP_AXIOM_SORRY_ADMIT.txt`
- Dependency pin report: `./RESEARCHER_BUNDLE/reports/ClosingTheLoop_DEPENDENCIES.md`
- Proof index: `./RESEARCHER_BUNDLE/reports/ClosingTheLoop_PROOF_INDEX.md`
- CAB verification: `./RESEARCHER_BUNDLE/reports/CAB_VERIFY.txt` plus CAB artifacts under
  `./RESEARCHER_BUNDLE/artifacts/cab/`
- Compiler outputs (evidence that Lean compiled the modules):
  - `.olean/.ilean/.trace` copies: `./RESEARCHER_BUNDLE/artifacts/compiler/olean/HeytingLean/ClosingTheLoop/**`
  - Lean compiler IR (`.ir`): `./RESEARCHER_BUNDLE/artifacts/compiler/ir/HeytingLean/ClosingTheLoop/**`
  - emitted demo artifacts:
    - LambdaIR (human-readable): `./RESEARCHER_BUNDLE/artifacts/compiler/ir/add1.lambdair.txt`
    - C source: `./RESEARCHER_BUNDLE/artifacts/compiler/c/add1.c`

Scope boundary (important to state in any paper-facing claims):

- We provide artifacts and transcripts showing Lean compiled to C output, but we do not provide a formal semantics-
  equivalence proof between Lean kernel semantics and the generated C code. The CAB artifacts certify the stated
  kernel commitments and rule roots (as implemented by the repo tooling).

---

## 6) Concrete “next tasks” recommended (paper + research agenda)

If the goal is to satisfy the researchers’ agenda “as much as feasible” while keeping the `ClosingTheLoop` namespace
clean:

  1. ~~Add a short, explicit "Assumptions Ladder" narrative section to the paper pack:~~
   - ~~injective-at-b vs section-at-b vs inverse-on-image; and their categorical analogues (mono vs split epi).~~
   - **DONE**: See Noneism extension and `11_Eigencomputable_Framework.md`.
  2. Add categorical "admissible morphisms" as a fibration/subobject layer:
   - new folder suggestion: `RESEARCHER_BUNDLE/HeytingLean/ClosingTheLoop/Cat/Admissible/`
  3. Add a minimal λ-calculus semantics module that targets the CCC layer (to begin addressing "models of computation").
  4. ~~Add a minimal coalgebra/LTS/process layer and relate it to closure/fixed points (to begin addressing concurrency/process algebra).~~
   - **DONE**: See `HeytingLean/Noneism/Cat/Coalgebra.lean` for coalgebraic dynamics perspective.
  5. Extend the (F,A) skeleton to time-parametrized (F,A) systems, as the PDF emphasizes temporal parametrization.

---

## 7) Noneism Extension: Addressing the Choice/β Problem (Added Dec 2025)

**Date:** 2025-12-26
**Commit:** `8740026` ("Add Noneism eigencomputable extension")

### The Problem Addressed

The paper's equations (2.1)-(2.5) require a global inverse evaluation map `β_b`. In Lean, this requires `Classical.choice` when derived from surjectivity. The Noneism extension refines this by distinguishing:

| Level | Meaning | Example |
|-------|---------|---------|
| Computable | Algorithm exists | `def f x := x + 1` |
| **Eigencomputable** | Determined by unique fixed point | `beta` in `BetaEigen.lean` |
| Arbitrary noncomputable | Raw classical selection | `betaRaw` in `BetaConstruction.lean` |

### Key Insight: β is Eigencomputable

The selector dynamics `selectorDynamics b Φ := fun _ => Φ b` "forgets everything but evaluation at b". For each metabolism `f`:

1. **Unique stable selector**: There exists exactly one `Φ` such that `selectorDynamics b Φ = Φ` and `evalAt b Φ = f`.
2. **This unique Φ is β(f)**: The nonconstructive choice is grounded in stabilizing dynamics.
3. **β(f) = (fun _ => f)**: The unique stable selector evaluating to `f` is simply the constant function.

### New Modules

- `HeytingLean/Noneism/Eigen/` — Core eigencomputable framework
- `HeytingLean/Noneism/Bridge/` — β as eigencomputable, bridges to MR structures
- `HeytingLean/Noneism/Cat/` — Categorical foundations (Yoneda, coalgebras, monads)
- `HeytingLean/Noneism/Core/` — Heyting algebra and nucleus structures
- `HeytingLean/Noneism/Zeros/` — Minimal/maximal/recursive structures
- `HeytingLean/Noneism/Crossing/` — Ontological boundary crossings

### Verification

```bash
cd RESEARCHER_BUNDLE
./scripts/verify_noneism.sh
```

### Paper Alignment

| Paper Equation | Status | Lean Declaration |
|----------------|--------|------------------|
| (2.3) Injectivity | ✓ | `selectorDynamics_stable_iff` |
| (2.4) β construction | ✓ **Eigencomputable** | `Bridge.beta`, `Bridge.betaEigenAt` |
| (2.5) Closure loop | ✓ | `beta_right_inverse`, `beta_stable` |

### What This Means for the Paper

The paper's claim that `β_b` exists from injectivity (eq 2.3) is now made precise:

1. **Injectivity alone** gives uniqueness (if two selectors agree at `b`, they're equal).
2. **Surjectivity + dynamics** gives a global `β` that is **grounded in stabilizing dynamics**, not arbitrary choice.
3. **The choice is not arbitrary**: `β(f)` is the unique fixed point of `selectorDynamics` in the fiber over `f`.

This resolves the "subtle part" about noncomputable definitions: they use choice, but the choice is **forced by dynamics**.
