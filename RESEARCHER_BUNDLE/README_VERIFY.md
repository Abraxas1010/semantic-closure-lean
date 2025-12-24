# ClosingTheLoop Verification (Self-Contained Bundle)

## A) System prerequisites

- Lean is managed by elan; lake will fetch deps.
- Linux/macOS expected.
- Network access is required unless `vendor/git/` is provided.
- Optional: set `CLOSING_THE_LOOP_DISABLE_VENDOR=1` to force network URLs.

## B) One-command verification

```bash
./scripts/verify_closing_the_loop.sh
```

## C) What it checks

- strict build of `HeytingLean.ClosingTheLoop` (no `sorry`, warnings-as-errors)
- axiom audit: key theorems do not depend on `sorryAx` (see `reports/AXIOMS_AUDIT_OUTPUT.txt`)
- strict build + run of the executable `closing_the_loop_bundle_demo` (exercises Lean’s native toolchain)
- hostile-environment smoke tests (no crashes):
  - unwritable `artifacts/compiler/`
  - empty env / empty `PATH` (see `reports/ROBUSTNESS.txt`)
- emits human-readable LambdaIR + generated C source under `artifacts/compiler/`
- compiles the emitted C with `cc` and runs it (sanity check)
- portability spot-check: dynamic deps via `ldd`/`otool` (see `reports/PORTABILITY.txt`)
- grep for axiom/sorry/admit
- grep for TODO/FIXME/stub/TBD
- prints key theorems module list
- reproducible hashes (excluding `.lake/`, `build/`, `vendor/`)

## D) Where to look

- `reports/ClosingTheLoop_PROOF_INDEX.md`
- `reports/ClosingTheLoop_DEPENDENCIES.md`
- `reports/BUILD_TRANSCRIPT_STRICT.txt`
- generated artifacts:
  - `artifacts/compiler/ir/add1.lambdair.txt`
  - `artifacts/compiler/c/add1.c`

## E) Visuals (standalone, no server)

Open:

- `artifacts/visuals/index.html`

Researcher-facing writeup:

- `docs/ClosingTheLoop_Lean_Contribution.odt`
