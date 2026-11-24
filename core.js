// Land measure core: least-squares plot geometry from side/diagonal lengths.
(function (root) {
  const FEDDAN = 4200.833, QIRAT = FEDDAN / 24, SAHM = QIRAT / 24;

  function solveLinear(A, b) {
    const n = b.length;
    const M = A.map((r, i) => r.concat([b[i]]));
    for (let c = 0; c < n; c++) {
      let p = c;
      for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[p][c])) p = r;
      if (Math.abs(M[p][c]) < 1e-14) return null;
      [M[c], M[p]] = [M[p], M[c]];
      for (let r = c + 1; r < n; r++) {
        const f = M[r][c] / M[c][c];
        for (let k = c; k <= n; k++) M[r][k] -= f * M[c][k];
      }
    }
    const x = new Array(n).fill(0);
    for (let r = n - 1; r >= 0; r--) {
      let s = M[r][n];
      for (let k = r + 1; k < n; k++) s -= M[r][k] * x[k];
      x[r] = s / M[r][r];
    }
    return x;
  }

  const dist = (P, i, j) => Math.hypot(P[i][0] - P[j][0], P[i][1] - P[j][1]);

  // meas: [{i,j,d}] ; n points. Gauge: P0=(0,0), P1.y=0.
  function refine(n, meas, P0) {
    let P = P0.map(p => p.slice());
    P[0] = [0, 0]; P[1] = [P[1][0], 0];
    const idx = [];
    for (let k = 1; k < n; k++) { idx.push([k, 0]); if (k >= 2) idx.push([k, 1]); }
    const np = idx.length;
    const slot = {}; idx.forEach((v, s) => slot[v[0] + "," + v[1]] = s);
    const cost = Q => meas.reduce((s, m) => s + (dist(Q, m.i, m.j) - m.d) ** 2, 0);
    let lam = 1e-3, c = cost(P);
    for (let it = 0; it < 200; it++) {
      const JTJ = Array.from({ length: np }, () => new Array(np).fill(0));
      const JTr = new Array(np).fill(0);
      for (const m of meas) {
        const d = Math.max(dist(P, m.i, m.j), 1e-9), r = d - m.d;
        const dx = (P[m.i][0] - P[m.j][0]) / d, dy = (P[m.i][1] - P[m.j][1]) / d;
        const g = [];
        const add = (pt, ax, v) => { const s = slot[pt + "," + ax]; if (s !== undefined) g.push([s, v]); };
        add(m.i, 0, dx); add(m.i, 1, dy); add(m.j, 0, -dx); add(m.j, 1, -dy);
        for (const [a, va] of g) { JTr[a] += va * r; for (const [b, vb] of g) JTJ[a][b] += va * vb; }
      }
      let improved = false;
      for (let t = 0; t < 12; t++) {
        const A = JTJ.map((row, i) => row.map((v, j) => v + (i === j ? lam * (JTJ[i][i] + 1e-9) : 0)));
        const step = solveLinear(A, JTr.map(v => -v));
        if (!step) { lam *= 10; continue; }
        const Q = P.map(p => p.slice());
        idx.forEach(([k, ax], s) => { Q[k][ax] += step[s]; });
        const cq = cost(Q);
        if (cq < c) { const gain = c - cq; P = Q; c = cq; lam = Math.max(lam / 5, 1e-12); improved = gain > 1e-16; break; }
        lam *= 10;
      }
      if (!improved) break;
    }
    return { P, cost: c };
  }

  function initial(n, meas, signs) {
    const known = (a, b) => { const m = meas.find(m => (m.i === a && m.j === b) || (m.i === b && m.j === a)); return m ? m.d : null; };
    const P = [[0, 0]];
    P[1] = [known(0, 1) || 1, 0];
    for (let k = 2; k < n; k++) {
      const refs = [];
      for (let j = 0; j < k; j++) { const d = known(k, j); if (d !== null) refs.push([j, d]); }
      if (refs.length >= 2) {
        // choose the two references farthest apart
        let best = [refs[0], refs[1]], bd = -1;
        for (let a = 0; a < refs.length; a++) for (let b = a + 1; b < refs.length; b++) {
          const dd = dist(P, refs[a][0], refs[b][0]); if (dd > bd) { bd = dd; best = [refs[a], refs[b]]; }
        }
        const [[ja, da], [jb, db]] = best;
        const D = Math.max(dist(P, ja, jb), 1e-9);
        const x = (da * da - db * db + D * D) / (2 * D);
        const h = Math.sqrt(Math.max(da * da - x * x, 0));
        const ux = (P[jb][0] - P[ja][0]) / D, uy = (P[jb][1] - P[ja][1]) / D;
        const s = signs[k - 2];
        P[k] = [P[ja][0] + x * ux - s * h * uy, P[ja][1] + x * uy + s * h * ux];
      } else if (refs.length === 1) {
        const [j, d] = refs[0]; P[k] = [P[j][0] + d * 0.7, P[j][1] + d * 0.7 * signs[k - 2]];
      } else P[k] = [k, signs[k - 2]];
    }
    return P;
  }

  function segInter(a, b, c, d) {
    const o = (p, q, r) => (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0]);
    return o(a, b, c) * o(a, b, d) < 0 && o(c, d, a) * o(c, d, b) < 0;
  }
  function selfIntersects(P) {
    const n = P.length;
    for (let i = 0; i < n; i++) for (let j = i + 2; j < n; j++) {
      if (i === 0 && j === n - 1) continue;
      if (segInter(P[i], P[(i + 1) % n], P[j], P[(j + 1) % n])) return true;
    }
    return false;
  }
  function area(P) {
    let s = 0;
    for (let i = 0; i < P.length; i++) { const j = (i + 1) % P.length; s += P[i][0] * P[j][1] - P[j][0] * P[i][1]; }
    return Math.abs(s) / 2;
  }

  function solve(n, meas) {
    if (n < 3) return { error: "need at least 3 corners" };
    const dof = 2 * n - 3;
    if (meas.length < dof) return { error: "need at least " + dof + " lengths (sides + diagonals), have " + meas.length };
    let best = null;
    const combos = 1 << (n - 2);
    for (let m = 0; m < combos; m++) {
      const signs = []; for (let k = 0; k < n - 2; k++) signs.push((m >> k) & 1 ? -1 : 1);
      if (signs[0] === -1) continue; // mirror image
      const r = refine(n, meas, initial(n, meas, signs));
      r.simple = !selfIntersects(r.P);
      const better = !best || (r.simple && !best.simple) || (r.simple === best.simple && r.cost < best.cost - 1e-9);
      if (better) best = r;
    }
    const P = best.P;
    const residuals = meas.map(m => ({ i: m.i, j: m.j, measured: m.d, fitted: dist(P, m.i, m.j), diff: dist(P, m.i, m.j) - m.d }));
    const redundancy = meas.length - dof;
    const rms = Math.sqrt(best.cost / meas.length);
    const out = { points: P, area: area(P), residuals, redundancy, rms, simple: best.simple, suspects: [] };
    // Perimeter along the sides i -> i+1
    out.perimeter = 0;
    for (let i = 0; i < n; i++) out.perimeter += dist(P, i, (i + 1) % n);
    // Leave-one-out: predict each length from all the others
    if (redundancy >= 1) {
      const sus = [];
      for (let k = 0; k < meas.length; k++) {
        const rest = meas.filter((_, q) => q !== k);
        if (rest.length < dof) continue;
        const rr = refine(n, rest, P);
        const sub = { points: rr.P, area: area(rr.P) };
        const pred = dist(sub.points, meas[k].i, meas[k].j);
        sus.push({ i: meas[k].i, j: meas[k].j, measured: meas[k].d, predicted: pred, misfit: meas[k].d - pred, areaWithout: sub.area });
      }
      sus.sort((a, b) => Math.abs(b.misfit) - Math.abs(a.misfit));
      out.suspects = sus;
    }
    const areas = [out.area].concat(out.suspects.map(s => s.areaWithout));
    out.areaMin = Math.min(...areas); out.areaMax = Math.max(...areas);
    return out;
  }
  function solveNoLoo(n, meas) {
    let best = null;
    for (let m = 0; m < (1 << (n - 2)); m++) {
      const signs = []; for (let k = 0; k < n - 2; k++) signs.push((m >> k) & 1 ? -1 : 1);
      if (signs[0] === -1) continue;
      const r = refine(n, meas, initial(n, meas, signs));
      r.simple = !selfIntersects(r.P);
      if (!best || (r.simple && !best.simple) || (r.simple === best.simple && r.cost < best.cost - 1e-9)) best = r;
    }
    return { points: best.P, area: area(best.P) };
  }

  function formatArea(m2) {
    let f = Math.floor(m2 / FEDDAN); let rem = m2 - f * FEDDAN;
    let q = Math.floor(rem / QIRAT); rem -= q * QIRAT;
    const s = rem / SAHM;
    return { m2, feddan: f, qirat: q, sahm: s };
  }

  const api = { solve, area, formatArea, FEDDAN, QIRAT, SAHM };
  if (typeof module !== "undefined") module.exports = api; else root.LandCore = api;
})(typeof self !== "undefined" ? self : this);
