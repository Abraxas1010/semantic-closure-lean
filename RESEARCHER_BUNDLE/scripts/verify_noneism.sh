#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

mkdir -p reports

TRANSCRIPT="reports/BUILD_TRANSCRIPT_NONEISM_STRICT.txt"
EIGEN_LEAN="reports/NONEISM_EIGEN_AUDIT.lean"
EIGEN_OUT="reports/NONEISM_EIGEN_AUDIT_OUTPUT.txt"
GREP_OUT="reports/NONEISM_GREP_AXIOM_SORRY_ADMIT.txt"
TODO_OUT="reports/NONEISM_GREP_TODO_FIXME_STUB_TBD.txt"

echo "[verify_noneism] root=$ROOT_DIR" | tee "$TRANSCRIPT"

{
  echo
  echo "[versions] lean"
  lean --version
  echo
  echo "[versions] lake"
  lake --version
  echo
  echo "[lake] update"
  lake update
  echo
  echo "[lake] build HeytingLean.Noneism (strict)"
  lake build HeytingLean.Noneism -- -Dno_sorry -DwarningAsError=true
  echo
  echo "[lake] build HeytingLean.Noneism.Tests.Compliance (strict)"
  lake build HeytingLean.Noneism.Tests.Compliance -- -Dno_sorry -DwarningAsError=true
  echo
  echo "[eigen] enumerate tagged decls"
  cat >"$EIGEN_LEAN" <<'LEAN'
import HeytingLean.Noneism
import HeytingLean.Noneism.Bridge.NoncomputableAudit
import Lean

open Lean
open HeytingLean.Noneism.Bridge

run_cmd do
  let env ← getEnv
  let tagged := eigencomputableDecls env
  IO.println s!"count={tagged.size}"
  for (n, dyn) in tagged do
    IO.println s!"{n} -> {dyn}"
LEAN
  lake env lean "$EIGEN_LEAN" | tee "$EIGEN_OUT"
} 2>&1 | tee -a "$TRANSCRIPT"

echo "[audit] grep for markers under HeytingLean/Noneism (word-boundary)" | tee "$GREP_OUT"
rg -n "\\b(axiom|sorry|admit)\\b" HeytingLean/Noneism >>"$GREP_OUT" 2>&1 || true
if rg -n "\\b(axiom|sorry|admit)\\b" HeytingLean/Noneism >/dev/null 2>&1; then
  echo "[audit] FAILED: found forbidden markers" | tee -a "$TRANSCRIPT"
  exit 1
fi

echo "[audit] grep for TODO/FIXME/stub/TBD under HeytingLean/Noneism (word-boundary)" | tee "$TODO_OUT"
rg -n "\\b(TODO|FIXME|stub|TBD)\\b" HeytingLean/Noneism >>"$TODO_OUT" 2>&1 || true
if rg -n "\\b(TODO|FIXME|stub|TBD)\\b" HeytingLean/Noneism >/dev/null 2>&1; then
  echo "[audit] FAILED: found TODO/FIXME/stub/TBD markers" | tee -a "$TRANSCRIPT"
  exit 1
fi

echo "[verify_noneism] PASSED"

