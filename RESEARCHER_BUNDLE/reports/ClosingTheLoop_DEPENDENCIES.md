# Dependencies / pins (verification bundle)

This bundle is a standalone Lake project under:

- `RESEARCHER_BUNDLE/`

## Lean toolchain

- `lean-toolchain`: `leanprover/lean4:v4.24.0`

## Lake packages (pinned)

All package pins are recorded in:

- `lakefile.lean`

Notably:

- `mathlib4` pinned by commit: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (corresponds to tag `v4.24.0`)
- Pinned overrides for mathlib’s upstream deps (to avoid floating `main/master` revisions):
  - `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `quote4` (`Qq`), `batteries`
  - (see `lakefile.lean` for the exact git SHAs)

After running the verifier, the resolved full dependency graph is recorded by Lake in:

- `lake-manifest.json`

## Network / offline

- Default: the verifier runs `lake update`, which fetches the pinned dependencies from GitHub.
- Optional offline mode: if you provide `vendor/git/github.com/**` mirrors, the verifier will prefer them.
  - Set `CLOSING_THE_LOOP_DISABLE_VENDOR=1` to force network URLs even if vendor mirrors exist.
