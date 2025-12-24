# Dependencies / pins

This repo is a Lean 4 + mathlib project built with Lake.

## Lean toolchain

- `Blueprint/lean-toolchain`: `leanprover/lean4:v4.24.0`

(`lean-toolchain` at repo root is a symlink to `Blueprint/lean-toolchain`.)

## mathlib

- Pinned in `lean/lakefile.lean` to `mathlib4 @ v4.24.0`.
- Concrete commit recorded in `Blueprint/lake-manifest.json`:
  - `mathlib` rev `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (input rev `v4.24.0`).

## Other Lake packages

The complete dependency set is recorded in:

- `Blueprint/lake-manifest.json`

## Researcher bundle pins

The standalone verifier bundle under `WIP/ClosingTheLoop_PaperPack/RESEARCHER_BUNDLE/` ships its own:

- `WIP/ClosingTheLoop_PaperPack/RESEARCHER_BUNDLE/lean-toolchain`
- `WIP/ClosingTheLoop_PaperPack/RESEARCHER_BUNDLE/lakefile.lean`
- `WIP/ClosingTheLoop_PaperPack/RESEARCHER_BUNDLE/lake-manifest.json`

Notable packages (non-exhaustive):
- `doc-gen4` (docs generation tooling)
- `checkdecls`
- `Cli`
- `batteries`
- `aesop`
- `proofwidgets`
- `importGraph`
- `LeanSearchClient`
- `plausible`

## OS/runtime tools used by QA scripts (non-Lean)

The local QA loop (see `WIP/ClosingTheLoop_PaperPack/03_Reproducibility.md`) may call:

- `bash`
- `python3`
- `cc` (C compiler) and system linker
- `jq`
- `ldd`
