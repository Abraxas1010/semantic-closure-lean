#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

mkdir -p reports artifacts/compiler/{bin,c,ir,olean}

TRANSCRIPT="reports/BUILD_TRANSCRIPT_STRICT.txt"
GREP_OUT="reports/GREP_AXIOM_SORRY_ADMIT.txt"
TODO_OUT="reports/GREP_TODO_FIXME_STUB_TBD.txt"
SHA_OUT="reports/SHA256SUMS.txt"
GITCFG="reports/GITCONFIG_EFFECTIVE.txt"
CAB_OUT="reports/CAB_VERIFY.txt"
AXIOMS_OUT="reports/AXIOMS_AUDIT.txt"
ROBUST_OUT="reports/ROBUSTNESS.txt"
PORT_OUT="reports/PORTABILITY.txt"

echo "[verify_closing_the_loop] root=$ROOT_DIR" | tee "$TRANSCRIPT"

{
  echo
  echo "[git] configure URL policy"
  if [[ "${CLOSING_THE_LOOP_DISABLE_VENDOR:-0}" != "1" ]] && \
     [[ -d "$ROOT_DIR/vendor/git/github.com/leanprover-community/mathlib4" ]]; then
    echo "[git] using vendor mirrors under vendor/git/ (offline-capable)"
    cat >"$GITCFG" <<EOF
[url "vendor/git/github.com/"]
  insteadOf = https://github.com/
EOF
  else
    if [[ "${CLOSING_THE_LOOP_DISABLE_VENDOR:-0}" == "1" ]]; then
      echo "[git] vendor mirrors disabled by CLOSING_THE_LOOP_DISABLE_VENDOR=1; using network URLs"
    else
      echo "[git] no vendor mirrors found; using network URLs"
    fi
    cat >"$GITCFG" <<EOF
# no URL rewrites
EOF
  fi
  export GIT_CONFIG_GLOBAL="$ROOT_DIR/$GITCFG"
  export GIT_CONFIG_NOSYSTEM=1
  echo "GIT_CONFIG_GLOBAL=$GIT_CONFIG_GLOBAL"
  echo "GIT_CONFIG_NOSYSTEM=$GIT_CONFIG_NOSYSTEM"
  echo
  echo "[gitconfig]"
  cat "$GITCFG"
  echo
  echo
  echo "[versions] lean"
  lean --version
  echo
  echo "[versions] lake"
  lake --version
  echo
  echo "[env] disable mathlib cache on update (for portability)"
  export MATHLIB_NO_CACHE_ON_UPDATE="${MATHLIB_NO_CACHE_ON_UPDATE:-1}"
  echo "MATHLIB_NO_CACHE_ON_UPDATE=$MATHLIB_NO_CACHE_ON_UPDATE"
  echo
  echo "[lake] update"
  lake update
  echo
  echo "[lake] build HeytingLean.ClosingTheLoop (strict)"
  lake build HeytingLean.ClosingTheLoop -- -Dno_sorry -DwarningAsError=true
  echo
  echo "[axioms] audit key theorems for sorryAx (should be absent)"
  cat >"$AXIOMS_OUT" <<'LEAN'
import HeytingLean.ClosingTheLoop

#print axioms HeytingLean.ClosingTheLoop.MR.InverseEvaluation.beta_injective
#print axioms HeytingLean.ClosingTheLoop.MR.InverseEvaluation.of_evalAt_surjective
#print axioms HeytingLean.ClosingTheLoop.MR.InverseEvaluation.beta_leftInverse_of_injective
#print axioms HeytingLean.ClosingTheLoop.MR.closeSelector.idem
#print axioms HeytingLean.ClosingTheLoop.MR.IsClosed.exists_eq_beta_iff

#print axioms HeytingLean.ClosingTheLoop.Cat.InverseEvaluationAt.of_isIso_evalAt
#print axioms HeytingLean.ClosingTheLoop.Cat.PreservesSelectorEval
#print axioms HeytingLean.ClosingTheLoop.Cat.idem_of_yoneda_map_idem

#print axioms HeytingLean.ClosingTheLoop.Semantics.MeetRetraction.retractionNucleus
#print axioms HeytingLean.ClosingTheLoop.Semantics.futureKernel.idem
#print axioms HeytingLean.ClosingTheLoop.Semantics.FunctorialTime.futureKernel.idem
#print axioms HeytingLean.ClosingTheLoop.Semantics.LambdaIRBridge.eval_beta
#print axioms HeytingLean.ClosingTheLoop.Semantics.ProcessBridge.wellTyped_fixedPoint
#print axioms HeytingLean.ClosingTheLoop.Semantics.MRBridge.closeMachine_step_idem
#print axioms HeytingLean.ClosingTheLoop.Semantics.Realizability.realizable_invariant_of_simulation
LEAN
  lake env lean "$AXIOMS_OUT" | tee reports/AXIOMS_AUDIT_OUTPUT.txt
  if rg -n "sorryAx" reports/AXIOMS_AUDIT_OUTPUT.txt >/dev/null 2>&1; then
    echo "[axioms] FAILED: found sorryAx in axioms audit output" | tee -a "$TRANSCRIPT"
    exit 1
  fi
  echo
  echo "[lake] build closing_the_loop_bundle_demo (strict; exercises C backend)"
  lake build closing_the_loop_bundle_demo -- -Dno_sorry -DwarningAsError=true
  echo
  echo "[run] closing_the_loop_bundle_demo (emits LambdaIR + C artifacts)"
  lake exe closing_the_loop_bundle_demo
  echo
  echo "[robustness] hostile IO/env/PATH (no crashes)"
  EXE_PATH="$ROOT_DIR/.lake/build/bin/closing_the_loop_bundle_demo"
  {
    echo "exe=$EXE_PATH"
    echo
    echo "== IO: artifacts/compiler unwritable =="
    chmod -R a-w artifacts/compiler 2>/dev/null || true
    "$EXE_PATH"
    chmod -R u+rwX artifacts/compiler 2>/dev/null || true
    echo
    echo "== ENV: empty env (PATH minimal) =="
    env -i PATH="/usr/bin:/bin" "$EXE_PATH"
    echo
    echo "== PATH: empty PATH =="
    env PATH="" "$EXE_PATH"
  } | tee "$ROBUST_OUT"
  echo
  echo "[modules] ClosingTheLoop sources"
  find HeytingLean/ClosingTheLoop -type f -name '*.lean' | sort
  echo
  echo "[reports] proof index"
  if [[ -f reports/ClosingTheLoop_PROOF_INDEX.md ]]; then
    sed -n '1,200p' reports/ClosingTheLoop_PROOF_INDEX.md
  else
    echo "missing reports/ClosingTheLoop_PROOF_INDEX.md"
  fi
} 2>&1 | tee -a "$TRANSCRIPT"

echo "[audit] grep for markers under HeytingLean/ (word-boundary)" | tee "$GREP_OUT"
rg -n "\\b(axiom|sorry|admit)\\b" HeytingLean >>"$GREP_OUT" 2>&1 || true

if rg -n "\\b(axiom|sorry|admit)\\b" HeytingLean >/dev/null 2>&1; then
  echo "[audit] FAILED: found forbidden markers" | tee -a "$TRANSCRIPT"
  exit 1
fi

echo "[audit] grep for TODO/FIXME/stub/TBD under HeytingLean/ (word-boundary)" | tee "$TODO_OUT"
rg -n "\\b(TODO|FIXME|stub|TBD)\\b" HeytingLean >>"$TODO_OUT" 2>&1 || true
if rg -n "\\b(TODO|FIXME|stub|TBD)\\b" HeytingLean >/dev/null 2>&1; then
  echo "[audit] FAILED: found TODO/FIXME/stub/TBD markers" | tee -a "$TRANSCRIPT"
  exit 1
fi

echo "[cab] verify cab.json + kernel.json (hashes + Merkle root)" | tee -a "$TRANSCRIPT"
env ROOT_DIR="$ROOT_DIR" python3 - <<'PY' | tee "$CAB_OUT"
import hashlib, json, os, sys

ROOT = os.environ.get("ROOT_DIR")
if not ROOT:
    print("CAB verifier: missing ROOT_DIR env", file=sys.stderr)
    sys.exit(2)
CAB_PATH = os.path.join(ROOT, "artifacts", "cab", "cab.json")
KERNEL_PATH = os.path.join(ROOT, "artifacts", "cab", "kernel.json")
CAB_HASH_PATH = os.path.join(ROOT, "artifacts", "cab", "cab.hash")
CAB_MERKLE_PATH = os.path.join(ROOT, "artifacts", "cab", "cab.merkle")

def hex_to_bytes(h: str) -> bytes:
    h = h.strip()
    if h.startswith("0x"):
        h = h[2:]
    return bytes.fromhex(h)

def bytes_to_hex(b: bytes) -> str:
    return "0x" + b.hex()

def sha256(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()

def H(tag: str, payload: bytes) -> bytes:
    return sha256(tag.encode("utf-8") + payload)

def serialize_rule(name: str) -> bytes:
    if name == "BetaLamApp":
        return "RuleID:KernelRule:BetaLamApp".encode("utf-8")
    if name == "DeltaPrimNatAdd":
        return "RuleID:KernelRule:DeltaPrimNatAdd".encode("utf-8")
    raise ValueError(f"unknown rule {name}")

def rule_id(rule_name: str) -> bytes:
    return H("LoF.RuleID|", serialize_rule(rule_name))

def le_bytes(a: bytes, b: bytes) -> bool:
    m = min(len(a), len(b))
    for i in range(m):
        if a[i] != b[i]:
            return a[i] <= b[i]
    return len(a) <= len(b)

def cat_sorted(a: bytes, b: bytes) -> bytes:
    return a + b if le_bytes(a, b) else b + a

def merkle_parent(a: bytes, b: bytes) -> bytes:
    return H("LoF.Merkle.Node|", cat_sorted(a, b))

def merkle_root_two(leaves: list[bytes]) -> bytes:
    if len(leaves) != 2:
        raise ValueError("expected exactly two leaves for this verifier")
    return merkle_parent(leaves[0], leaves[1])

with open(CAB_PATH, "r", encoding="utf-8") as f:
    cab = json.load(f)

rules = cab.get("rules", [])
if len(rules) < 2:
    print("CAB: expected >=2 rules in cab.json", file=sys.stderr)
    sys.exit(2)

ridB = rule_id("BetaLamApp")
ridD = rule_id("DeltaPrimNatAdd")

root_exp = merkle_root_two([ridB, ridD])
root_got = hex_to_bytes(cab["rulesRoot"])

fnd_witness_hex = None
for r in rules:
    if r.get("name") == "BetaLamApp":
        fnd_witness_hex = r.get("lofWitness")
if not fnd_witness_hex:
    print("CAB: missing BetaLamApp.lofWitness", file=sys.stderr)
    sys.exit(2)

beta_witness = hex_to_bytes(fnd_witness_hex)
fnd_payload = beta_witness + serialize_rule("BetaLamApp") + serialize_rule("DeltaPrimNatAdd")
fnd_exp = H("LoF.CAB.Foundation|", fnd_payload)
fnd_got = hex_to_bytes(cab["foundationCommitment"])

print(f"CAB path: {CAB_PATH}")
print(f"  rulesRoot expected: {bytes_to_hex(root_exp)}")
print(f"  rulesRoot got:      {bytes_to_hex(root_got)}")
print(f"  foundation expected:{bytes_to_hex(fnd_exp)}")
print(f"  foundation got:     {bytes_to_hex(fnd_got)}")

ok = True
if root_exp != root_got:
    print("CAB: rulesRoot mismatch", file=sys.stderr)
    ok = False
if fnd_exp != fnd_got:
    print("CAB: foundationCommitment mismatch", file=sys.stderr)
    ok = False

if os.path.exists(CAB_HASH_PATH):
    with open(CAB_HASH_PATH, "r", encoding="utf-8") as f:
        cab_hash = f.read().strip()
    if cab_hash != bytes_to_hex(fnd_got):
        print("CAB: cab.hash mismatch", file=sys.stderr)
        ok = False

if os.path.exists(CAB_MERKLE_PATH):
    with open(CAB_MERKLE_PATH, "r", encoding="utf-8") as f:
        cab_mk = f.read().strip()
    if cab_mk != bytes_to_hex(root_got):
        print("CAB: cab.merkle mismatch", file=sys.stderr)
        ok = False

with open(KERNEL_PATH, "r", encoding="utf-8") as f:
    kernel = json.load(f)

kernel_desc = "Kernel:TT0.kernel:v1;rules=[BetaLamApp,DeltaPrimNatAdd];semantics=det"
kc_exp = sha256(kernel_desc.encode("utf-8"))
kc_got = hex_to_bytes(kernel["kernelCommitment"])
print(f"KERNEL path: {KERNEL_PATH}")
print(f"  kernelCommitment expected: {bytes_to_hex(kc_exp)}")
print(f"  kernelCommitment got:      {bytes_to_hex(kc_got)}")
if kc_exp != kc_got:
    print("KERNEL: kernelCommitment mismatch", file=sys.stderr)
    ok = False

if not ok:
    sys.exit(1)
print("CAB/KERNEL: OK")
PY

if [[ "${PIPESTATUS[0]}" -ne 0 ]]; then
  echo "[cab] FAILED: cab/kernel verification" | tee -a "$TRANSCRIPT"
  exit 1
fi

echo "[c] compile emitted C program (artifacts/compiler/c/add1.c)" | tee -a "$TRANSCRIPT"
if ! command -v cc >/dev/null 2>&1; then
  echo "[c] FAILED: missing 'cc' in PATH" | tee -a "$TRANSCRIPT"
  exit 1
fi

cc -O2 -std=c11 artifacts/compiler/c/add1.c -o artifacts/compiler/bin/add1
echo "[c] run emitted binary (expected stdout: 42)" | tee -a "$TRANSCRIPT"
OUT="$(./artifacts/compiler/bin/add1 | tr -d '\r\n')"
echo "[c] stdout=$OUT" | tee -a "$TRANSCRIPT"
if [[ "$OUT" != "42" ]]; then
  echo "[c] FAILED: unexpected output (wanted 42)" | tee -a "$TRANSCRIPT"
  exit 1
fi

echo "[portability] dynamic dependencies" | tee -a "$TRANSCRIPT"
{
  echo "== closing_the_loop_bundle_demo =="
  if command -v ldd >/dev/null 2>&1; then
    ldd .lake/build/bin/closing_the_loop_bundle_demo
  elif command -v otool >/dev/null 2>&1; then
    otool -L .lake/build/bin/closing_the_loop_bundle_demo
  else
    echo "no ldd/otool found"
  fi
  echo
  echo "== emitted C binary (add1) =="
  if command -v ldd >/dev/null 2>&1; then
    ldd artifacts/compiler/bin/add1
  elif command -v otool >/dev/null 2>&1; then
    otool -L artifacts/compiler/bin/add1
  else
    echo "no ldd/otool found"
  fi
} | tee "$PORT_OUT"

echo "[artifacts] collect compiler outputs (olean + C IR)" | tee -a "$TRANSCRIPT"
rm -rf artifacts/compiler/ir/HeytingLean/ClosingTheLoop artifacts/compiler/olean/HeytingLean/ClosingTheLoop
mkdir -p artifacts/compiler/ir/HeytingLean/ClosingTheLoop artifacts/compiler/olean/HeytingLean/ClosingTheLoop

if [[ -d .lake/build/ir/HeytingLean/ClosingTheLoop ]]; then
  cp -a .lake/build/ir/HeytingLean/ClosingTheLoop/. artifacts/compiler/ir/HeytingLean/ClosingTheLoop/
fi

if [[ -d .lake/build/lib/lean/HeytingLean/ClosingTheLoop ]]; then
  cp -a .lake/build/lib/lean/HeytingLean/ClosingTheLoop/. artifacts/compiler/olean/HeytingLean/ClosingTheLoop/
fi

echo "[hashes] sha256 over bundle (excluding .lake/, build/, vendor/)" | tee -a "$TRANSCRIPT"
rm -f "$SHA_OUT"
(
  cd "$ROOT_DIR"
  find . -type f \
    -not -path './.lake/*' \
    -not -path './build/*' \
    -not -path './vendor/*' \
    -not -path './reports/SHA256SUMS.txt' \
    -print0 \
    | sort -z \
    | xargs -0 sha256sum
) >"$SHA_OUT"

echo "[verify_closing_the_loop] PASSED" | tee -a "$TRANSCRIPT"
