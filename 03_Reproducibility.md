# Reproducibility (local)

These are the commands a researcher can run to reproduce the formal and runtime checks.

## One-command researcher bundle (recommended)

This paper pack includes a standalone Lake project that pins its dependencies and can be verified
independently of the rest of the repo:

```bash
cd WIP/ClosingTheLoop_PaperPack/RESEARCHER_BUNDLE
./scripts/verify_closing_the_loop.sh
```

This performs a strict `no_sorry` build of `HeytingLean.ClosingTheLoop`, builds and runs an
executable (exercising native compilation), emits LambdaIR + C artifacts, compiles the emitted C
with `cc`, and records a transcript + hashes under `reports/`.

The bundle also ships offline visuals (no build step required):

- `WIP/ClosingTheLoop_PaperPack/RESEARCHER_BUNDLE/artifacts/visuals/index.html`

## Prerequisites

- `elan` installed (Lean toolchain manager).
- System toolchain for Lean executables:
  - C compiler (`cc`), linker toolchain.
  - `bash`, `python3`.
  - Optional but used by some QA scripts: `jq`, `ldd`.

Lean version is pinned by `lean-toolchain` (see `WIP/ClosingTheLoop_PaperPack/04_Dependencies.md`).

## Build only the semantic-closure modules (fast)

From repo root:

```bash
cd lean
lake build HeytingLean.ClosingTheLoop -- -Dno_sorry -DwarningAsError=true
```

## Build the full library strictly (incremental)

```bash
cd lean
lake build -- -Dno_sorry -DwarningAsError=true
```

## Build all executables (C backend + linking)

From repo root:

```bash
scripts/build_all_exes.sh --strict
```

## Run executables (happy path)

```bash
scripts/run_all_exes.sh
```

## Robustness checks (missing files/env/PATH)

```bash
scripts/qa_robustness_all.sh
```

## Portability (dynamic dependencies)

```bash
scripts/qa_portability.sh
```

## Optional: generate a proof dependency graph

The repo contains a proof-graph dumper CLI. Example (small fuel):

```bash
cd lean
lake exe proof_graph_dump --const HeytingLean.ClosingTheLoop.MR.closeSelector.idem --fuel 150 > /tmp/closeSelector_idem_graph.json
```

This is an exploratory tool and not required for the formal “no sorry” guarantee.
