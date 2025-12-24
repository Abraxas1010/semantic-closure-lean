# Closing the Loop (Semantic Closure) — Researcher Pack

This folder is a self-contained orientation + reproducibility bundle for the Lean formalization introduced in:

- `WIP/closure_paper.md`
- Lean sources under `lean/HeytingLean/ClosingTheLoop/**`

It is written for a researcher who wants to (i) understand the formal objects, (ii) locate the proofs in the codebase, and (iii) reproduce all checks locally.

## What is formalized (scope)

We mechanize a minimal “semantic closure” core inspired by the (M,R) / inverse-evaluation move:

1. **Rosen-style (M,R) scaffold (Set-based):**
   - Two types `A`, `B`, a set of admissible maps `H ⊆ (A → B)`, and a distinguished metabolism `f ∈ H`.
   - A *selector space* `Selector := B → H` (bundled as a subtype with proof of admissibility).

2. **Inverse evaluation at a configuration `b : B`:**
   - An assumed map `β : H → Selector` such that evaluation at `b` is a right inverse:
     - `evalAt b (β g) = g`.
   - This provides the “reconstruction step” needed to close the loop.

3. **Loop-closing operator on selectors:**
   - `closeSelector (Φ) := β (Φ b)`.
   - Proven **idempotent**: closing twice is the same as closing once.
   - Defines a fixed-point notion `IsClosed` (“semantically closed selectors at `b`”).

4. **Bridge to nuclei (Heyting-core story):**
   - A generic construction: a meet-preserving section–retraction pair induces a `Nucleus` by `x ↦ dec (enc x)`.
   - This isolates the algebraic conditions needed to connect semantic closure to the existing nucleus framework in the repo.

5. **Temporal parametrization (seed):**
   - A functorial time-indexed (F,A) container (`T ⥤ Type`), a preorder-time future-invariant kernel,
     and an inflationary reachability nucleus (LoF convention).

## Files to read first

- Overview + mapping: `WIP/ClosingTheLoop_PaperPack/01_Lean_Map.md`
- Proof index (what is proved where): `WIP/ClosingTheLoop_PaperPack/02_Proof_Index.md`
- Reproducibility (commands): `WIP/ClosingTheLoop_PaperPack/03_Reproducibility.md`
- Dependencies (Lean/mathlib/Lake pins): `WIP/ClosingTheLoop_PaperPack/04_Dependencies.md`
- Researcher agenda audit (status + gaps): `WIP/ClosingTheLoop_PaperPack/05_Researcher_Agenda_Report.md`
- Paper-style appendix (LaTeX): `WIP/ClosingTheLoop_PaperPack/Blueprint/closing_the_loop_appendix.tex`
- PDF math outline + mapping (incl. two-track diagram): `WIP/ClosingTheLoop_PaperPack/06_Paper_Math_Outline.md`
- Researcher-facing writeup (ODT): `WIP/ClosingTheLoop_PaperPack/07_ClosingTheLoop_Lean_Contribution.odt`

## Standalone verification bundle (for external researchers)

For a self-contained, dependency-pinned verifier that also emits “LambdaIR → C” artifacts:

```bash
cd WIP/ClosingTheLoop_PaperPack/RESEARCHER_BUNDLE
./scripts/verify_closing_the_loop.sh
```

The bundle also contains standalone, offline visuals:

- `WIP/ClosingTheLoop_PaperPack/RESEARCHER_BUNDLE/artifacts/visuals/index.html`

## Status

- All Lean development here is `no_sorry` clean and builds under strict flags.
- Full local QA loop (strict build + all executables + runtime + robustness + portability) has been run successfully on this repo state.
