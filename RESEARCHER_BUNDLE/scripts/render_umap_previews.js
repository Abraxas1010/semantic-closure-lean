#!/usr/bin/env node
"use strict";

/**
 * Render static SVG previews for the ClosingTheLoop + Noneism proof/declaration embedding.
 *
 * Inputs:
 *   - artifacts/visuals/closing_the_loop_proofs.json
 *
 * Outputs:
 *   - artifacts/visuals/closing_the_loop_2d_preview.svg
 *   - artifacts/visuals/closing_the_loop_3d_preview.svg
 *   - artifacts/visuals/closing_the_loop_3d_preview_animated.svg
 *
 * This is intentionally dependency-free (Node stdlib only), so that the bundle remains easy
 * to reproduce in hostile environments.
 *
 * Usage:
 *   node RESEARCHER_BUNDLE/scripts/render_umap_previews.js \
 *     [input.json] [out2d.svg] [out3d.svg] [out3dAnimated.svg]
 */

const fs = require("fs");
const path = require("path");

function fail(msg) {
  console.error(`E: ${msg}`);
  process.exit(1);
}

function hash32(s) {
  // FNV-1a 32-bit
  let h = 0x811c9dc5;
  for (let i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = Math.imul(h, 0x01000193);
  }
  return h >>> 0;
}

function colorForFamily(family) {
  const h = hash32(family) % 360;
  return {
    fill: `hsl(${h} 70% 58%)`,
    stroke: `hsl(${h} 70% 32%)`,
  };
}

function esc(s) {
  return String(s)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#39;");
}

function svgDoc({ width, height, background, body }) {
  return (
    `<?xml version="1.0" encoding="utf-8"?>\n` +
    `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" ` +
    `viewBox="0 0 ${width} ${height}" role="img" aria-label="UMAP preview">\n` +
    `<rect x="0" y="0" width="${width}" height="${height}" fill="${background}"/>\n` +
    `${body}\n` +
    `</svg>\n`
  );
}

function renderLegend({ families, counts, x, y, lineH }) {
  const entries = [...families].sort((a, b) => (counts.get(b) ?? 0) - (counts.get(a) ?? 0));
  let out = "";
  let cy = y;
  for (const fam of entries) {
    const n = counts.get(fam) ?? 0;
    const c = colorForFamily(fam);
    out += `<rect x="${x}" y="${cy}" width="10" height="10" fill="${c.fill}" stroke="${c.stroke}" stroke-width="1"/>\n`;
    out += `<text x="${x + 16}" y="${cy + 9}" fill="#e6eef7" font-size="12" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">${esc(fam)} <tspan fill="#b8c7d9">(${n})</tspan></text>\n`;
    cy += lineH;
  }
  return out;
}

function map2dPoints({ items, getPos, margin, plotW, plotH }) {
  function toCanvas(p) {
    const x = margin + p.x * plotW;
    const y = margin + (1 - p.y) * plotH;
    return { x, y };
  }
  return items.map((it) => toCanvas(getPos(it)));
}

function render2d({ data, outPath }) {
  const items = data.items ?? [];
  const edges = data.edges ?? [];

  const width = 1500;
  const height = 900;
  const background = "#0b0f14";

  const margin = 50;
  const legendW = 310;
  const plotW = width - margin * 2 - legendW;
  const plotH = height - margin * 2;
  const legendX = margin + plotW + 30;

  const counts = new Map();
  for (const it of items) {
    const fam = it.family ?? "Other";
    counts.set(fam, (counts.get(fam) ?? 0) + 1);
  }
  const families = [...counts.keys()];

  const pts = map2dPoints({
    items,
    getPos: (it) => it.pos,
    margin,
    plotW,
    plotH,
  });

  let body = "";
  body += `<text x="${margin}" y="${margin - 18}" fill="#ffffff" font-size="20" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">UMAP 2D — ClosingTheLoop + Noneism proof/declaration map</text>\n`;
  body += `<text x="${margin}" y="${margin - 2}" fill="#b8c7d9" font-size="12" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">Points: declarations • Colors: module family • Edges: similarity links (source-text features)</text>\n`;

  body += `<rect x="${margin}" y="${margin}" width="${plotW}" height="${plotH}" fill="#0f1721" stroke="#1c2a3a" stroke-width="1"/>\n`;

  // Edges (light)
  for (const [i, j] of edges) {
    const a = pts[i];
    const b = pts[j];
    if (!a || !b) continue;
    body += `<line x1="${a.x.toFixed(2)}" y1="${a.y.toFixed(2)}" x2="${b.x.toFixed(2)}" y2="${b.y.toFixed(2)}" stroke="#3b4b5d" stroke-opacity="0.18" stroke-width="1"/>\n`;
  }

  // Nodes
  for (let idx = 0; idx < items.length; idx++) {
    const it = items[idx];
    const p = pts[idx];
    if (!p) continue;
    const fam = it.family ?? "Other";
    const c = colorForFamily(fam);
    body += `<circle cx="${p.x.toFixed(2)}" cy="${p.y.toFixed(2)}" r="4" fill="${c.fill}" stroke="#0b0f14" stroke-width="1">\n`;
    body += `  <title>${esc(it.name ?? it.id ?? "item")}</title>\n`;
    body += `</circle>\n`;
  }

  // Legend
  body += `<text x="${legendX}" y="${margin}" fill="#ffffff" font-size="16" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">Legend</text>\n`;
  body += renderLegend({ families, counts, x: legendX, y: margin + 14, lineH: 16 });

  const svg = svgDoc({ width, height, background, body });
  fs.writeFileSync(outPath, svg, "utf8");
}

function rotateX([x, y, z], a) {
  const ca = Math.cos(a);
  const sa = Math.sin(a);
  return [x, y * ca - z * sa, y * sa + z * ca];
}

function rotateY([x, y, z], a) {
  const ca = Math.cos(a);
  const sa = Math.sin(a);
  return [x * ca + z * sa, y, -x * sa + z * ca];
}

function render3dAnimated({ data, outPath }) {
  const items = data.items ?? [];

  const width = 1500;
  const height = 900;
  const background = "#0b0f14";

  const margin = 50;
  const plotW = width - margin * 2;
  const plotH = height - margin * 2;

  const pitch = 0.48;
  const cameraDist = 3.0;

  const frames = 72; // smooth but still lightweight
  const durSec = 14; // slow rotation

  // Normalize pos3 to centered cube [-1,1]^3 using the full data range.
  const p3s = items.map((it) => it.pos3).filter(Boolean);
  if (!p3s.length) {
    fail(`cannot render animated 3D preview: no pos3 coordinates present`);
  }

  let minx = 1e9, maxx = -1e9, miny = 1e9, maxy = -1e9, minz = 1e9, maxz = -1e9;
  for (const p of p3s) {
    minx = Math.min(minx, p.x); maxx = Math.max(maxx, p.x);
    miny = Math.min(miny, p.y); maxy = Math.max(maxy, p.y);
    minz = Math.min(minz, p.z); maxz = Math.max(maxz, p.z);
  }
  const cx = (minx + maxx) / 2;
  const cy = (miny + maxy) / 2;
  const cz = (minz + maxz) / 2;
  const scale = 2 / Math.max(1e-6, (maxx - minx), (maxy - miny), (maxz - minz));

  const xyz = items.map((it) => {
    const p = it.pos3;
    if (!p) return null;
    return { x: (p.x - cx) * scale, y: (p.y - cy) * scale, z: (p.z - cz) * scale };
  });

  function projectAtYaw(yaw) {
    return xyz.map((p) => {
      if (!p) return null;
      let v = [p.x, p.y, p.z];
      v = rotateY(v, yaw);
      v = rotateX(v, pitch);
      const [rx, ry, rz] = v;
      const s = cameraDist / (cameraDist - rz);
      return { x: rx * s, y: ry * s, z: rz };
    });
  }

  // Precompute projections for all frames (plus a closing frame at 2π).
  const projFrames = [];
  for (let t = 0; t <= frames; t++) {
    const yaw = (2 * Math.PI * t) / frames;
    projFrames.push(projectAtYaw(yaw));
  }

  // Global bounds across all frames to avoid jittering scale.
  let gminX = 1e9, gmaxX = -1e9, gminY = 1e9, gmaxY = -1e9, gminZ = 1e9, gmaxZ = -1e9;
  for (const frame of projFrames) {
    for (const p of frame) {
      if (!p) continue;
      gminX = Math.min(gminX, p.x); gmaxX = Math.max(gmaxX, p.x);
      gminY = Math.min(gminY, p.y); gmaxY = Math.max(gmaxY, p.y);
      gminZ = Math.min(gminZ, p.z); gmaxZ = Math.max(gmaxZ, p.z);
    }
  }

  const invX = 1 / (gmaxX - gminX || 1);
  const invY = 1 / (gmaxY - gminY || 1);
  const invZ = 1 / (gmaxZ - gminZ || 1);

  function toCanvas(p) {
    const nx = (p.x - gminX) * invX;
    const ny = (p.y - gminY) * invY;
    const nz = (p.z - gminZ) * invZ;
    const x = margin + nx * plotW;
    const y = margin + (1 - ny) * plotH;
    return { x, y, z: nz };
  }

  // For each node, build cx/cy/r keyframes.
  const cxValues = Array.from({ length: items.length }, () => []);
  const cyValues = Array.from({ length: items.length }, () => []);
  const rValues = Array.from({ length: items.length }, () => []);

  for (const frame of projFrames) {
    for (let i = 0; i < items.length; i++) {
      const p = frame[i];
      if (!p) {
        cxValues[i].push("");
        cyValues[i].push("");
        rValues[i].push("");
        continue;
      }
      const c = toCanvas(p);
      const r = 2.4 + 4.2 * (c.z ?? 0);
      cxValues[i].push(c.x.toFixed(2));
      cyValues[i].push(c.y.toFixed(2));
      rValues[i].push(r.toFixed(2));
    }
  }

  let body = "";
  body += `<text x="${margin}" y="${margin - 18}" fill="#ffffff" font-size="20" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">UMAP 3D — animated preview (rotation)</text>\n`;
  body += `<text x="${margin}" y="${margin - 2}" fill="#b8c7d9" font-size="12" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">Nonlinear visualization aid (not a formal invariant) • For interactive view open closing_the_loop_3d.html</text>\n`;
  body += `<rect x="${margin}" y="${margin}" width="${plotW}" height="${plotH}" fill="#0f1721" stroke="#1c2a3a" stroke-width="1"/>\n`;

  for (let i = 0; i < items.length; i++) {
    const it = items[i];
    const fam = it.family ?? "Other";
    const col = colorForFamily(fam).fill;

    // If a point is missing coordinates, skip it entirely.
    if (!cxValues[i][0] || !cyValues[i][0]) continue;

    body += `<circle cx="${cxValues[i][0]}" cy="${cyValues[i][0]}" r="${rValues[i][0]}" fill="${col}" fill-opacity="0.92" stroke="#0b0f14" stroke-width="1">\n`;
    body += `  <title>${esc(it.name ?? it.id ?? "item")}</title>\n`;
    body += `  <animate attributeName="cx" dur="${durSec}s" repeatCount="indefinite" values="${cxValues[i].join(";")}"/>\n`;
    body += `  <animate attributeName="cy" dur="${durSec}s" repeatCount="indefinite" values="${cyValues[i].join(";")}"/>\n`;
    body += `  <animate attributeName="r" dur="${durSec}s" repeatCount="indefinite" values="${rValues[i].join(";")}"/>\n`;
    body += `</circle>\n`;
  }

  const svg = svgDoc({ width, height, background, body });
  fs.writeFileSync(outPath, svg, "utf8");
}

function render3d({ data, outPath }) {
  const items = data.items ?? [];
  const edges = data.edges ?? [];

  const width = 1500;
  const height = 900;
  const background = "#0b0f14";

  const margin = 50;
  const legendW = 310;
  const plotW = width - margin * 2 - legendW;
  const plotH = height - margin * 2;
  const legendX = margin + plotW + 30;

  const yaw = 0.75;
  const pitch = 0.48;
  const cameraDist = 3.0;

  const counts = new Map();
  for (const it of items) {
    const fam = it.family ?? "Other";
    counts.set(fam, (counts.get(fam) ?? 0) + 1);
  }
  const families = [...counts.keys()];

  // Rotate + perspective project into an intermediate 2D plane.
  const proj = items.map((it) => {
    const p3 = it.pos3;
    if (!p3) return null;
    let x = (p3.x - 0.5) * 2.0;
    let y = (p3.y - 0.5) * 2.0;
    let z = (p3.z - 0.5) * 2.0;
    let v = [x, y, z];
    v = rotateY(v, yaw);
    v = rotateX(v, pitch);
    const [rx, ry, rz] = v;
    const s = cameraDist / (cameraDist - rz);
    return { x: rx * s, y: ry * s, z: rz };
  });

  // Normalize projected coordinates to [0,1] for plotting.
  const xs = proj.filter(Boolean).map((p) => p.x);
  const ys = proj.filter(Boolean).map((p) => p.y);
  const zs = proj.filter(Boolean).map((p) => p.z);
  const minX = Math.min(...xs), maxX = Math.max(...xs);
  const minY = Math.min(...ys), maxY = Math.max(...ys);
  const minZ = Math.min(...zs), maxZ = Math.max(...zs);

  function norm(p) {
    const nx = (p.x - minX) / (maxX - minX || 1);
    const ny = (p.y - minY) / (maxY - minY || 1);
    const nz = (p.z - minZ) / (maxZ - minZ || 1);
    return { x: nx, y: ny, z: nz };
  }

  const pts = proj.map((p) => (p ? norm(p) : null));

  function toCanvas(p) {
    const x = margin + p.x * plotW;
    const y = margin + (1 - p.y) * plotH;
    return { x, y, z: p.z };
  }

  const canvasPts = pts.map((p) => (p ? toCanvas(p) : null));

  let body = "";
  body += `<text x="${margin}" y="${margin - 18}" fill="#ffffff" font-size="20" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">UMAP 3D — ClosingTheLoop + Noneism proof/declaration map (static projection)</text>\n`;
  body += `<text x="${margin}" y="${margin - 2}" fill="#b8c7d9" font-size="12" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">Perspective projection of 3D coordinates • Nearer points are slightly larger</text>\n`;

  body += `<rect x="${margin}" y="${margin}" width="${plotW}" height="${plotH}" fill="#0f1721" stroke="#1c2a3a" stroke-width="1"/>\n`;

  // Edges (light; draw before nodes).
  for (const [i, j] of edges) {
    const a = canvasPts[i];
    const b = canvasPts[j];
    if (!a || !b) continue;
    const depth = ((a.z ?? 0) + (b.z ?? 0)) / 2;
    const alpha = (0.10 + 0.22 * depth).toFixed(3);
    body += `<line x1="${a.x.toFixed(2)}" y1="${a.y.toFixed(2)}" x2="${b.x.toFixed(2)}" y2="${b.y.toFixed(2)}" stroke="#3b4b5d" stroke-opacity="${alpha}" stroke-width="1"/>\n`;
  }

  // Nodes: draw far-to-near for nicer occlusion.
  const order = [...items.keys()].sort((i, j) => {
    const zi = canvasPts[i]?.z ?? 0;
    const zj = canvasPts[j]?.z ?? 0;
    return zi - zj;
  });

  for (const idx of order) {
    const it = items[idx];
    const p = canvasPts[idx];
    if (!p) continue;
    const fam = it.family ?? "Other";
    const c = colorForFamily(fam);
    const r = 3 + 3 * (p.z ?? 0);
    body += `<circle cx="${p.x.toFixed(2)}" cy="${p.y.toFixed(2)}" r="${r.toFixed(2)}" fill="${c.fill}" stroke="#0b0f14" stroke-width="1">\n`;
    body += `  <title>${esc(it.name ?? it.id ?? "item")}</title>\n`;
    body += `</circle>\n`;
  }

  body += `<text x="${legendX}" y="${margin}" fill="#ffffff" font-size="16" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">Legend</text>\n`;
  body += renderLegend({ families, counts, x: legendX, y: margin + 14, lineH: 16 });

  const svg = svgDoc({ width, height, background, body });
  fs.writeFileSync(outPath, svg, "utf8");
}

function main() {
  const repoRoot = path.resolve(__dirname, "..", "..");
  const defaultJson = path.join(repoRoot, "artifacts", "visuals", "closing_the_loop_proofs.json");

  const jsonPath = process.argv[2] ?? defaultJson;
  const out2d =
    process.argv[3] ??
    path.join(path.dirname(jsonPath), "closing_the_loop_2d_preview.svg");
  const out3d =
    process.argv[4] ??
    path.join(path.dirname(jsonPath), "closing_the_loop_3d_preview.svg");
  const out3dAnimated =
    process.argv[5] ??
    path.join(path.dirname(jsonPath), "closing_the_loop_3d_preview_animated.svg");

  if (!fs.existsSync(jsonPath)) {
    fail(`missing input: ${jsonPath}`);
  }

  const raw = fs.readFileSync(jsonPath, "utf8");
  const data = JSON.parse(raw);
  if (!Array.isArray(data.items)) {
    fail(`expected JSON to have array field: items`);
  }

  render2d({ data, outPath: out2d });
  render3d({ data, outPath: out3d });
  render3dAnimated({ data, outPath: out3dAnimated });

  console.log(`[render_umap_previews] wrote:\n- ${out2d}\n- ${out3d}\n- ${out3dAnimated}`);
}

main();

