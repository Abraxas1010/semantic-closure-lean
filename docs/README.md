# ClosingTheLoop visuals (standalone)

Open `index.html` in a browser to explore the ClosingTheLoop slice as:

- a 2D UMAP embedding (`closing_the_loop_2d.html`)
- an interactive 3D UMAP embedding (`closing_the_loop_3d.html`)
- an in-browser computation demo (`compute_add1.html`)

Additional static graphs (SVG):

- module import graphs: `imports/closing_the_loop_imports_internal.svg`, `imports/closing_the_loop_imports_with_deps.svg`
- proof DAG snapshots (selected key theorems): `proof_dags/*.svg`

Data:

- `closing_the_loop_proofs.json` (raw)
- `closing_the_loop_proofs_data.js` (embedded for offline HTML use)

Notes:

- These pages are **self-contained**: no server required, no network required.
- Node positions are computed from Lean source text features (see `server/scripts/export_closing_the_loop_viz.js`).
- The WASM demo embeds its module as base64 (`wasm/add1_wasm_b64.js`) so it works without `fetch()`.
