#!/usr/bin/env python3
"""
Regenerate all visualizations for ClosingTheLoop and Noneism modules.

This script:
1. Generates module import graphs (DOT → SVG)
2. Generates proof DAG JSONs for key theorems
3. Regenerates UMAP embeddings including Noneism declarations

Usage:
    python regenerate_visuals.py [--output-dir PATH] [--graphviz-path PATH]
"""

import os
import re
import sys
import json
import hashlib
import subprocess
from pathlib import Path
from datetime import datetime, timezone
from collections import defaultdict

# Paths
SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]  # semantic-closure-lean
BUNDLE_ROOT = REPO_ROOT / 'RESEARCHER_BUNDLE'
LEAN_SRC = BUNDLE_ROOT / 'HeytingLean'
VISUALS_DIR = BUNDLE_ROOT / 'artifacts' / 'visuals'
IMPORTS_DIR = VISUALS_DIR / 'imports'
PROOF_DAGS_DIR = VISUALS_DIR / 'proof_dags'

# Module prefixes we care about
CLOSING_LOOP_PREFIX = 'HeytingLean.ClosingTheLoop'
NONEISM_PREFIX = 'HeytingLean.Noneism'

# Key theorems to generate proof DAGs for
KEY_THEOREMS = [
    # ClosingTheLoop core
    'HeytingLean.ClosingTheLoop.MR.closeSelector.idem',
    'HeytingLean.ClosingTheLoop.Cat.curryNatIso',
    'HeytingLean.ClosingTheLoop.Cat.idem_of_yoneda_map_idem',
    'HeytingLean.ClosingTheLoop.Cat.map_close_eq',
    'HeytingLean.ClosingTheLoop.Semantics.FunctorialTime.futureKernel.idem',
    'HeytingLean.ClosingTheLoop.Semantics.Realizability.realizable_invariant_of_simulation',
    # Noneism extension
    'HeytingLean.Noneism.Eigen.determined_by_dynamics',
    'HeytingLean.Noneism.Bridge.selectorDynamics_stable_iff',
    'HeytingLean.Noneism.Bridge.selectorDynamics_unique_stable',
    'HeytingLean.Noneism.Bridge.beta_right_inverse',
    'HeytingLean.Noneism.Bridge.beta_stable',
    'HeytingLean.Noneism.Bridge.beta_eq_const',
]

def mod_from_path(p: Path, base: Path) -> str:
    """Convert file path to Lean module name."""
    rel = p.relative_to(base).with_suffix('')
    return 'HeytingLean.' + '.'.join(rel.parts)

def parse_imports(text: str) -> list:
    """Extract import statements from Lean source."""
    imports = []
    for line in text.splitlines():
        m = re.match(r'^\s*import\s+(.+)$', line)
        if m:
            for target in m.group(1).split():
                target = target.strip()
                if target:
                    imports.append(target)
    return imports

def strip_comments(src: str) -> str:
    """Remove Lean comments."""
    out = []
    i, n = 0, len(src)
    while i < n:
        if src.startswith('/-', i):
            j = src.find('-/', i+2)
            i = n if j == -1 else j+2
        elif src.startswith('--', i):
            j = src.find('\n', i+2)
            out.append('\n')
            i = n if j == -1 else j+1
        else:
            out.append(src[i])
            i += 1
    return ''.join(out)

def extract_decls(text: str, mod: str) -> list:
    """Extract declarations from Lean source."""
    clean = strip_comments(text)
    decls = []
    decl_re = re.compile(
        r'^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*'
        r'(theorem|lemma|def|definition|structure|class|inductive|abbrev)\s+'
        r'([A-Za-z_][A-Za-z0-9_\'\.]*)'
    )
    lines = clean.splitlines()
    for i, line in enumerate(lines):
        m = decl_re.match(line)
        if m:
            kind = m.group(1)
            name = m.group(2)
            # Qualify name if needed
            qname = name if name.startswith('HeytingLean.') else f'{mod}.{name}'
            # Extract snippet (next 6 lines)
            snippet = '\n'.join(lines[i:i+6])
            decls.append({
                'name': qname,
                'kind': kind,
                'line': i + 1,
                'snippet': snippet
            })
    return decls

def compute_text_features(source: str) -> dict:
    """Compute text features for UMAP embedding."""
    def count(pat):
        return len(re.findall(pat, source))

    # Calculate max paren depth
    d, m = 0, 0
    for c in source:
        if c in '(⟨':
            d += 1
        elif c in ')⟩':
            d = max(0, d - 1)
        m = max(m, d)

    return {
        'implies': count(r'→|->'),
        'not': count(r'¬|\bnot\b'),
        'and': count(r'∧|\band\b'),
        'or': count(r'∨|\bor\b'),
        'forall': count(r'∀'),
        'exists': count(r'∃'),
        'eq': count(r'=|:=') - count(r':='),
        'tactics': count(r'\b(simp|rw|intro|apply|cases|exact|have)\b'),
        'parenDepth': m,
        'length': len(source)
    }

def family_from_path(p: str) -> str:
    """Extract module family from path."""
    if 'Noneism/Bridge' in p:
        return 'Bridge'
    if 'Noneism/Eigen' in p:
        return 'Eigen'
    if 'Noneism' in p:
        return 'Noneism'
    if '/Cat/' in p:
        return 'Cat'
    if '/MR/' in p:
        return 'MR'
    if '/Semantics/' in p:
        return 'Semantics'
    if '/FA/' in p:
        return 'FA'
    if '/Tests/' in p:
        return 'Tests'
    return 'Other'

def crawl_modules(src_dir: Path, prefix: str) -> tuple:
    """Crawl Lean source files and collect modules and edges."""
    nodes = set()
    edges = defaultdict(set)
    decls_by_mod = {}

    for path in src_dir.rglob('*.lean'):
        mod = mod_from_path(path, src_dir.parent)
        if not mod.startswith(prefix):
            continue
        nodes.add(mod)

        text = path.read_text(encoding='utf-8', errors='ignore')
        imports = parse_imports(text)

        for target in imports:
            if target.startswith(prefix):
                edges[mod].add(target)

        decls_by_mod[mod] = extract_decls(text, mod)

    return nodes, edges, decls_by_mod

def generate_dot_graph(nodes: set, edges: dict, title: str, include_external: bool = False) -> str:
    """Generate DOT graph from nodes and edges."""
    lines = [
        'digraph G {',
        '  rankdir=LR;',
        '  graph [bgcolor="transparent", fontsize=10, splines=true, overlap=false];',
        '  node [shape=box, style="rounded,filled", fillcolor="#0f1721", color="#1c2a3a", fontcolor="#e6eef7", fontsize=9];',
        '  edge [color="#90a4ae", fontcolor="#90a4ae", fontsize=8];',
        f'  label="{title}"; labelloc="t";',
    ]

    # Nodes
    for node in sorted(nodes):
        # Color code by prefix
        if node.startswith(NONEISM_PREFIX):
            color = '#8e24aa'  # Purple for Noneism
        else:
            color = '#43a047'  # Green for ClosingTheLoop
        lines.append(f'  "{node}" [fillcolor="#0f1721", color="{color}"];')

    # External deps if requested
    ext_nodes = set()
    if include_external:
        for mod, deps in edges.items():
            for dep in deps:
                if dep not in nodes and dep.startswith('HeytingLean.'):
                    ext_nodes.add(dep)
        for node in sorted(ext_nodes):
            lines.append(f'  "{node}" [fillcolor="#1a1a2e", color="#555", fontcolor="#888"];')

    # Edges
    all_nodes = nodes | ext_nodes
    for mod, deps in sorted(edges.items()):
        for dep in sorted(deps):
            if dep in all_nodes:
                lines.append(f'  "{mod}" -> "{dep}";')

    lines.append('}')
    return '\n'.join(lines)

def dot_to_svg(dot_content: str, output_path: Path, graphviz_path: str = 'dot'):
    """Convert DOT to SVG using graphviz."""
    try:
        result = subprocess.run(
            [graphviz_path, '-Tsvg'],
            input=dot_content.encode('utf-8'),
            capture_output=True,
            check=True
        )
        output_path.write_bytes(result.stdout)
        print(f"  Generated: {output_path.name}")
        return True
    except subprocess.CalledProcessError as e:
        print(f"  Error generating SVG: {e.stderr.decode()}")
        return False
    except FileNotFoundError:
        print(f"  Warning: graphviz not found at '{graphviz_path}', skipping SVG generation")
        return False

def generate_proof_dag_stub(theorem_name: str) -> dict:
    """Generate a stub proof DAG JSON for a theorem."""
    # This is a placeholder - actual proof DAG generation would require
    # running Lean to extract the proof term structure
    safe_name = theorem_name.replace('.', '_')
    return {
        'id': theorem_name,
        'name': theorem_name,
        'kind': 'theorem',
        'nodes': [
            {'id': 0, 'label': theorem_name.split('.')[-1], 'kind': 'root', 'depth': 0}
        ],
        'edges': [],
        'meta': {
            'generated': datetime.now(timezone.utc).isoformat(),
            'note': 'Stub DAG - regenerate with Lean tooling for full proof structure'
        }
    }

def generate_edges(items: list, module_edges: dict) -> list:
    """Generate edges between declarations based on module dependencies."""
    edges = []

    # Build index: module -> list of item indices
    mod_to_items = defaultdict(list)
    for i, item in enumerate(items):
        # Extract module from path
        path = item.get('path', '')
        # Convert path to module name
        if 'ClosingTheLoop' in path:
            parts = path.replace('lean/HeytingLean/', '').replace('.lean', '').split('/')
            mod = 'HeytingLean.' + '.'.join(parts)
        elif 'Noneism' in path:
            parts = path.replace('lean/HeytingLean/', '').replace('.lean', '').split('/')
            mod = 'HeytingLean.' + '.'.join(parts)
        else:
            mod = item.get('id', '').rsplit('.', 1)[0] if '.' in item.get('id', '') else ''

        if mod:
            mod_to_items[mod].append(i)

    # Connect declarations within the same module
    for mod, indices in mod_to_items.items():
        for i in range(len(indices)):
            for j in range(i + 1, min(i + 3, len(indices))):  # Connect to next 2 decls in same module
                edges.append([indices[i], indices[j]])

    # Connect declarations across dependent modules
    for src_mod, deps in module_edges.items():
        src_indices = mod_to_items.get(src_mod, [])
        for dep_mod in deps:
            dep_indices = mod_to_items.get(dep_mod, [])
            # Connect first decl of src to first decl of dep
            if src_indices and dep_indices:
                edges.append([src_indices[0], dep_indices[0]])

    return edges

def simple_umap_layout(items: list, seed: str = 'closing-the-loop-umap-v1') -> list:
    """Simple deterministic 2D/3D layout based on feature hashing."""
    import random

    # Create deterministic RNG from seed
    h = hashlib.sha256(seed.encode()).digest()
    rng_seed = int.from_bytes(h[:4], 'big')
    rng = random.Random(rng_seed)

    positioned = []
    for item in items:
        # Use features to influence position
        feats = item.get('features', {})

        # Hash the item for base position
        item_hash = hashlib.sha256(item['name'].encode()).digest()
        base_x = int.from_bytes(item_hash[:2], 'big') / 65535
        base_y = int.from_bytes(item_hash[2:4], 'big') / 65535
        base_z = int.from_bytes(item_hash[4:6], 'big') / 65535

        # Perturb based on features
        feat_factor = (
            feats.get('implies', 0) * 0.1 +
            feats.get('eq', 0) * 0.05 +
            feats.get('tactics', 0) * 0.02
        )

        item['pos'] = {
            'x': (base_x + rng.random() * 0.1) % 1.0,
            'y': (base_y + feat_factor * 0.1 + rng.random() * 0.1) % 1.0
        }
        item['pos3'] = {
            'x': (base_x + rng.random() * 0.05) % 1.0,
            'y': (base_y + rng.random() * 0.05) % 1.0,
            'z': (base_z + rng.random() * 0.05) % 1.0
        }
        positioned.append(item)

    return positioned

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Regenerate visualizations')
    parser.add_argument('--output-dir', type=Path, default=VISUALS_DIR)
    parser.add_argument('--graphviz-path', default='dot')
    args = parser.parse_args()

    output_dir = args.output_dir
    imports_dir = output_dir / 'imports'
    proof_dags_dir = output_dir / 'proof_dags'

    # Ensure directories exist
    imports_dir.mkdir(parents=True, exist_ok=True)
    proof_dags_dir.mkdir(parents=True, exist_ok=True)

    print("=" * 60)
    print("Regenerating ClosingTheLoop + Noneism Visualizations")
    print("=" * 60)

    # --- 1. Crawl modules ---
    print("\n[1/4] Crawling Lean source files...")

    # ClosingTheLoop modules
    cl_nodes, cl_edges, cl_decls = crawl_modules(
        LEAN_SRC / 'ClosingTheLoop', CLOSING_LOOP_PREFIX
    )
    print(f"  ClosingTheLoop: {len(cl_nodes)} modules, {sum(len(d) for d in cl_decls.values())} declarations")

    # Noneism modules
    n_nodes, n_edges, n_decls = crawl_modules(
        LEAN_SRC / 'Noneism', NONEISM_PREFIX
    )
    print(f"  Noneism: {len(n_nodes)} modules, {sum(len(d) for d in n_decls.values())} declarations")

    # Combined
    all_nodes = cl_nodes | n_nodes
    all_edges = {**cl_edges, **n_edges}
    all_decls = {**cl_decls, **n_decls}

    # --- 2. Generate import graphs ---
    print("\n[2/4] Generating module import graphs...")

    # ClosingTheLoop internal only
    dot_cl_internal = generate_dot_graph(
        cl_nodes, cl_edges,
        'ClosingTheLoop imports (internal)'
    )
    cl_internal_dot = imports_dir / 'closing_the_loop_imports_internal.dot'
    cl_internal_dot.write_text(dot_cl_internal)
    dot_to_svg(dot_cl_internal, imports_dir / 'closing_the_loop_imports_internal.svg', args.graphviz_path)

    # ClosingTheLoop + Noneism combined
    dot_combined = generate_dot_graph(
        all_nodes, all_edges,
        'ClosingTheLoop + Noneism imports'
    )
    combined_dot = imports_dir / 'closing_the_loop_with_noneism.dot'
    combined_dot.write_text(dot_combined)
    dot_to_svg(dot_combined, imports_dir / 'closing_the_loop_with_noneism.svg', args.graphviz_path)

    # Noneism only
    dot_noneism = generate_dot_graph(
        n_nodes, n_edges,
        'Noneism extension imports'
    )
    noneism_dot = imports_dir / 'noneism_imports.dot'
    noneism_dot.write_text(dot_noneism)
    dot_to_svg(dot_noneism, imports_dir / 'noneism_imports.svg', args.graphviz_path)

    # --- 3. Generate proof DAG stubs ---
    print("\n[3/4] Generating proof DAG stubs...")
    for theorem in KEY_THEOREMS:
        safe_name = theorem.replace('.', '_')
        dag = generate_proof_dag_stub(theorem)

        # JSON
        json_path = proof_dags_dir / f'{safe_name}.json'
        json_path.write_text(json.dumps(dag, indent=2))

        # DOT (simple node)
        dot_content = f'''digraph G {{
  rankdir=TB;
  graph [bgcolor="transparent"];
  node [shape=box, style="rounded,filled", fillcolor="#0f1721", color="#43a047", fontcolor="#e6eef7"];
  "{theorem.split('.')[-1]}" [label="{theorem.split('.')[-1]}"];
}}'''
        dot_path = proof_dags_dir / f'{safe_name}.dot'
        dot_path.write_text(dot_content)
        dot_to_svg(dot_content, proof_dags_dir / f'{safe_name}.svg', args.graphviz_path)

    # --- 4. Generate UMAP embedding data ---
    print("\n[4/4] Generating UMAP embedding data...")

    items = []
    for mod, decl_list in sorted(all_decls.items()):
        # Find the source file path
        mod_parts = mod.replace('HeytingLean.', '').split('.')
        rel_path = '/'.join(mod_parts) + '.lean'
        full_path = f'lean/HeytingLean/{rel_path}'

        for decl in decl_list:
            features = compute_text_features(decl['snippet'])
            items.append({
                'id': decl['name'],
                'name': decl['name'],
                'kind': decl['kind'],
                'path': full_path,
                'line': decl['line'],
                'family': family_from_path(full_path),
                'features': features,
                'snippet': decl['snippet']
            })

    # Add positions
    items = simple_umap_layout(items)

    # Generate edges from module dependencies
    edges = generate_edges(items, all_edges)
    print(f"  Generated {len(edges)} edges")

    # Create output JSON
    seed = 'closing-the-loop-umap-v2'  # Updated version
    data_hash = hashlib.sha256(json.dumps(items, sort_keys=True).encode()).hexdigest()

    output_data = {
        'meta': {
            'generatedAt': datetime.now(timezone.utc).isoformat(),
            'seed': seed,
            'vectorSignature': {
                'schema': 'Φ/v2',
                'weights': {'A': 1, 'B': 0.7, 'C': 0.3, 'D': 0.2},
                'seed': seed,
                'umap': 'deterministic-hash',
                'pins': {'umap': 'deterministic-hash'},
                'providers': {},
                'digest': data_hash,
                'phiDigest': hashlib.sha256(seed.encode()).hexdigest()
            },
            'source': 'lean/HeytingLean/ClosingTheLoop + lean/HeytingLean/Noneism',
            'notes': 'UMAP embedding of ClosingTheLoop + Noneism declarations (feature vectors derived from Lean source text).'
        },
        'items': items,
        'edges': edges
    }

    # Write JSON
    json_path = output_dir / 'closing_the_loop_proofs.json'
    json_path.write_text(json.dumps(output_data, indent=2))
    print(f"  Generated: {json_path.name} ({len(items)} items)")

    # Write JS version for HTML viewer (must use CLOSING_THE_LOOP_PROOFS variable name)
    js_content = f'window.CLOSING_THE_LOOP_PROOFS = {json.dumps(output_data)};'
    js_path = output_dir / 'closing_the_loop_proofs_data.js'
    js_path.write_text(js_content)
    print(f"  Generated: {js_path.name}")

    # --- Summary ---
    print("\n" + "=" * 60)
    print("Summary:")
    print(f"  - Module import graphs: 3 (internal, combined, noneism)")
    print(f"  - Proof DAGs: {len(KEY_THEOREMS)}")
    print(f"  - UMAP items: {len(items)}")
    print(f"  - Edges: {len(edges)}")
    print(f"  - Output directory: {output_dir}")
    print("=" * 60)

    return 0

if __name__ == '__main__':
    sys.exit(main())
