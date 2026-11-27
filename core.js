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


  // ---------- v2: GPS / AR / RTK points + weighted combination ----------
  function llToLocal(pts, origin) {
    const R = 6378137, k = Math.PI / 180, c = Math.cos(origin.lat * k);
    return pts.map(p => [R * (p.lon - origin.lon) * k * c, R * (p.lat - origin.lat) * k]);
  }
  // Average several GPS fixes of one corner. Honest sigma: errors of consecutive
  // fixes are strongly correlated, so averaging is NOT credited with sqrt(N) gain.
  function averageFixes(fixes) {
    const f = fixes.filter(x => isFinite(x.acc) && x.acc > 0 && isFinite(x.lat) && isFinite(x.lon));
    if (!f.length) return null;
    const w = f.map(x => 1 / (x.acc * x.acc)), sw = w.reduce((a, b) => a + b, 0);
    const lat = f.reduce((a, x, i) => a + w[i] * x.lat, 0) / sw;
    const lon = f.reduce((a, x, i) => a + w[i] * x.lon, 0) / sw;
    const loc = llToLocal(f, { lat, lon });
    const scatter = Math.sqrt(loc.reduce((a, p) => a + p[0] * p[0] + p[1] * p[1], 0) / loc.length / 2);
    const accs = f.map(x => x.acc).sort((a, b) => a - b);
    const med = accs[Math.floor(accs.length / 2)];
    return { lat, lon, n: f.length, scatter, medianAcc: med, sigma: Math.max(med, scatter) };
  }
  function signedArea(P) {
    let s = 0;
    for (let i = 0; i < P.length; i++) { const j = (i + 1) % P.length; s += P[i][0] * P[j][1] - P[j][0] * P[i][1]; }
    return s / 2;
  }
  function alignShape(shape, priors) {
    const wsum = priors.reduce((a, p) => a + 1 / (p.sigma * p.sigma), 0);
    const cp = [priors.reduce((a, p) => a + p.x / (p.sigma * p.sigma), 0) / wsum, priors.reduce((a, p) => a + p.y / (p.sigma * p.sigma), 0) / wsum];
    if (priors.length === 1) {
      const p = priors[0], q = shape[p.i];
      return shape.map(v => [v[0] - q[0] + p.x, v[1] - q[1] + p.y]);
    }
    let best = null;
    for (const mir of [false, true]) {
      const Q = shape.map(v => [mir ? -v[0] : v[0], v[1]]);
      const cq = [priors.reduce((a, p) => a + Q[p.i][0] / (p.sigma * p.sigma), 0) / wsum, priors.reduce((a, p) => a + Q[p.i][1] / (p.sigma * p.sigma), 0) / wsum];
      let a = 0, b = 0;
      for (const p of priors) {
        const w = 1 / (p.sigma * p.sigma), qx = Q[p.i][0] - cq[0], qy = Q[p.i][1] - cq[1], px = p.x - cp[0], py = p.y - cp[1];
        a += w * (qx * px + qy * py); b += w * (qx * py - qy * px);
      }
      const th = Math.atan2(b, a), c = Math.cos(th), sn = Math.sin(th);
      const R = Q.map(v => { const x = v[0] - cq[0], y = v[1] - cq[1]; return [c * x - sn * y + cp[0], sn * x + c * y + cp[1]]; });
      const cost = priors.reduce((s2, p) => s2 + ((R[p.i][0] - p.x) ** 2 + (R[p.i][1] - p.y) ** 2) / (p.sigma * p.sigma), 0);
      if (!best || cost < best.cost) best = { R, cost };
    }
    return best.R;
  }

  // dists: [{i,j,d,sigma}] meters; priors: [{i,x,y,sigma}] local meters (GPS/RTK).
  function solveCombined(n, dists, priors) {
    priors = priors || [];
    const dof0 = 2 * n - 3;
    let P = null;
    if (dists.length >= dof0) {
      const s0 = solve(n, dists.map(m => ({ i: m.i, j: m.j, d: m.d })));
      if (!s0.error) P = s0.points;
    }
    const covered = new Set(priors.map(p => p.i));
    if (P) {
      if (priors.length) P = alignShape(P, priors);
    } else if (covered.size === n) {
      P = Array.from({ length: n }, (_, i) => { const p = priors.find(q => q.i === i); return [p.x, p.y]; });
    } else {
      return { error: "need GPS points for every corner, or at least " + dof0 + " lengths" };
    }
    P = P.map(p => p.slice());
    const rows = (Q) => {
      const R = [];
      for (const m of dists) {
        const d = Math.max(Math.hypot(Q[m.i][0] - Q[m.j][0], Q[m.i][1] - Q[m.j][1]), 1e-9);
        const dx = (Q[m.i][0] - Q[m.j][0]) / d, dy = (Q[m.i][1] - Q[m.j][1]) / d, s = m.sigma;
        R.push({ kind: "len", i: m.i, j: m.j, r: (d - m.d) / s, diff: d - m.d, t: [[2 * m.i, dx / s], [2 * m.i + 1, dy / s], [2 * m.j, -dx / s], [2 * m.j + 1, -dy / s]] });
      }
      for (const p of priors) {
        R.push({ kind: "gps", i: p.i, r: (Q[p.i][0] - p.x) / p.sigma, diff: Q[p.i][0] - p.x, t: [[2 * p.i, 1 / p.sigma]] });
        R.push({ kind: "gps", i: p.i, r: (Q[p.i][1] - p.y) / p.sigma, diff: Q[p.i][1] - p.y, t: [[2 * p.i + 1, 1 / p.sigma]] });
      }
      return R;
    };
    const np = 2 * n, cost = R => R.reduce((a, x) => a + x.r * x.r, 0);
    let R = rows(P), c = cost(R), lam = 1e-3;
    for (let it = 0; it < 300; it++) {
      const A = Array.from({ length: np }, () => new Array(np).fill(0)), g = new Array(np).fill(0);
      for (const row of R) for (const [a, va] of row.t) { g[a] += va * row.r; for (const [b, vb] of row.t) A[a][b] += va * vb; }
      let ok = false;
      for (let t = 0; t < 14; t++) {
        const M = A.map((r, i) => r.map((v, j) => v + (i === j ? lam * (A[i][i] + 1e-9) + 1e-12 : 0)));
        const st = solveLinear(M, g.map(v => -v));
        if (!st) { lam *= 10; continue; }
        const Q = P.map((p, i) => [p[0] + st[2 * i], p[1] + st[2 * i + 1]]);
        const R2 = rows(Q), c2 = cost(R2);
        if (c2 < c) { const gain = c - c2; P = Q; R = R2; c = c2; lam = Math.max(lam / 5, 1e-12); ok = gain > 1e-12; break; }
        lam *= 10;
      }
      if (!ok) break;
    }
    // covariance of the corners, then area variance by propagation
    const A = Array.from({ length: np }, () => new Array(np).fill(0));
    for (const row of R) for (const [a, va] of row.t) for (const [b, vb] of row.t) A[a][b] += va * vb;
    const tr = A.reduce((s2, r, i) => s2 + r[i], 0) / np;
    const M = A.map((r, i) => r.map((v, j) => v + (i === j ? 1e-9 * tr : 0)));
    const sa = signedArea(P), sg = sa >= 0 ? 1 : -1;
    const grad = new Array(np).fill(0);
    for (let i = 0; i < n; i++) {
      const nx = P[(i + 1) % n], pv = P[(i + n - 1) % n];
      grad[2 * i] = sg * (nx[1] - pv[1]) / 2; grad[2 * i + 1] = sg * (pv[0] - nx[0]) / 2;
    }
    const y = solveLinear(M, grad);
    let varA = y ? grad.reduce((s2, v, i) => s2 + v * y[i], 0) : NaN;
    const nobs = R.length, gauge = priors.length >= 2 ? 0 : priors.length === 1 ? 1 : 3;
    const dof = nobs - (np - gauge);
    let infl = 1;
    if (dof > 0) infl = Math.max(1, Math.sqrt(c / dof));
    const out = {
      points: P, area: Math.abs(sa), sigmaArea: Math.sqrt(Math.max(varA, 0)) * infl,
      chi2: c, dof, inflation: infl, simple: !selfIntersects(P),
      residuals: R.filter(r => r.kind === "len").map(r => ({ i: r.i, j: r.j, z: r.r, diff: r.diff })),
      gpsResiduals: priors.map(p => ({ i: p.i, dx: P[p.i][0] - p.x, dy: P[p.i][1] - p.y, z: Math.hypot((P[p.i][0] - p.x), (P[p.i][1] - p.y)) / p.sigma })),
      mode: dists.length && priors.length ? "combined" : priors.length ? "gps" : "lengths"
    };
    out.perimeter = 0; for (let i = 0; i < n; i++) out.perimeter += dist(P, i, (i + 1) % n);
    return out;
  }

  // ---------- v3: photo precision mode (reference object in the plane) ----------
  function convexQuad(P) {
    if (P.length !== 4) return false;
    let s = 0;
    for (let i = 0; i < 4; i++) {
      const a = P[i], b = P[(i + 1) % 4], c = P[(i + 2) % 4];
      const cr = (b[0] - a[0]) * (c[1] - b[1]) - (b[1] - a[1]) * (c[0] - b[0]);
      if (Math.abs(cr) < 1e-9) return false;
      const sg = cr > 0 ? 1 : -1;
      if (s === 0) s = sg; else if (sg !== s) return false;
    }
    return true;
  }
  // DLT homography: 4 src points -> 4 dst points. Returns 3x3 row-major (h33=1).
  function homography(src, dst) {
    const A = [], b = [];
    for (let k = 0; k < 4; k++) {
      const [x, y] = src[k], [X, Y] = dst[k];
      A.push([x, y, 1, 0, 0, 0, -X * x, -X * y]); b.push(X);
      A.push([0, 0, 0, x, y, 1, -Y * x, -Y * y]); b.push(Y);
    }
    const h = solveLinear(A, b);
    if (!h) return null;
    return [[h[0], h[1], h[2]], [h[3], h[4], h[5]], [h[6], h[7], 1]];
  }
  function applyH(H, p) {
    const w = H[2][0] * p[0] + H[2][1] * p[1] + H[2][2];
    return [(H[0][0] * p[0] + H[0][1] * p[1] + H[0][2]) / w, (H[1][0] * p[0] + H[1][1] * p[1] + H[1][2]) / w];
  }
  function polyStats(P) {
    const n = P.length, lengths = [];
    let per = 0;
    for (let i = 0; i < n; i++) { const d = dist(P, i, (i + 1) % n); lengths.push(d); per += d; }
    return { lengths, perimeter: per, area: area(P), simple: !selfIntersects(P) };
  }
  // area sigma from per-vertex isotropic sigma (same units), polygon in any unit
  function areaSigma(P, s) {
    const n = P.length; let v = 0;
    for (let i = 0; i < n; i++) {
      const nx = P[(i + 1) % n], pv = P[(i + n - 1) % n];
      const gx = (nx[1] - pv[1]) / 2, gy = (pv[0] - nx[0]) / 2;
      v += (gx * gx + gy * gy) * s * s;
    }
    return Math.sqrt(v);
  }
  const worse = (a, b) => ({ good: 0, mid: 1, bad: 2 })[a] >= ({ good: 0, mid: 1, bad: 2 })[b] ? a : b;
  // Shared quality machinery. opts: {imgDiagPx, blurVar}
  function qualityChecks(refDiagPx, perspRatio, opts) {
    const checks = [];
    let q = "good";
    if (opts.imgDiagPx) {
      const frac = refDiagPx / opts.imgDiagPx;
      const lvl = frac >= 0.25 ? "good" : frac >= 0.12 ? "mid" : "bad";
      checks.push({ id: "refsize", level: lvl, value: frac }); q = worse(q, lvl);
    }
    if (perspRatio) {
      const lvl = perspRatio <= 1.2 ? "good" : perspRatio <= 1.6 ? "mid" : "bad";
      checks.push({ id: "persp", level: lvl, value: perspRatio }); q = worse(q, lvl);
    }
    if (isFinite(opts.blurVar)) {
      const lvl = opts.blurVar >= 80 ? "good" : opts.blurVar >= 25 ? "mid" : "bad";
      checks.push({ id: "blur", level: lvl, value: opts.blurVar }); q = worse(q, lvl);
    }
    return { q, checks };
  }
  const tapSigmaPx = blurVar => !isFinite(blurVar) ? 2.5 : blurVar >= 80 ? 2 : blurVar >= 25 ? 3.5 : 6;
  // 4-corner rectangular reference (A4 etc). refPx: 4 tapped corners IN ORDER.
  // refW/refH mm (A4: 210/297; orientation auto-matched to the tapped quad).
  function photoQuad(refPx, plotPx, opts) {
    opts = opts || {};
    const refW = opts.refW || 210, refH = opts.refH || 297;
    if (!convexQuad(refPx)) return { error: "ref_not_convex" };
    if (plotPx.length < 3) return { error: "need_3_points" };
    const d = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1]);
    const s0 = d(refPx[0], refPx[1]), s1 = d(refPx[1], refPx[2]), s2 = d(refPx[2], refPx[3]), s3 = d(refPx[3], refPx[0]);
    const longFirst = (s0 + s2) >= (s1 + s3);
    const W = longFirst ? Math.max(refW, refH) : Math.min(refW, refH);
    const Ht = longFirst ? Math.min(refW, refH) : Math.max(refW, refH);
    const H = homography(refPx, [[0, 0], [W, 0], [W, Ht], [0, Ht]]);
    if (!H) return { error: "homography_failed" };
    const P = plotPx.map(p => applyH(H, p));
    const st = polyStats(P);
    const persp = Math.max(s0 / s2, s2 / s0, s1 / s3, s3 / s1);
    const refDiagPx = d(refPx[0], refPx[2]);
    const { q, checks } = qualityChecks(refDiagPx, persp, opts);
    if (!st.simple) { checks.push({ id: "selfx", level: "bad", value: 1 }); }
    const quality = st.simple ? q : "bad";
    // mean local scale mm/px along the reference sides
    const scale = ((W / s0) + (Ht / s1) + (W / s2) + (Ht / s3)) / 4;
    const tsp = tapSigmaPx(opts.blurVar);
    const sigmaPtMm = tsp * scale;
    const out = {
      ok: true, mode: "quad", H, rectW: W, rectH: Ht, scaleMmPerPx: scale,
      lengthsMm: st.lengths, perimeterMm: st.perimeter, areaMm2: st.area,
      areaM2: st.area / 1e6, simple: st.simple, quality, checks,
      lenSigmaMm: sigmaPtMm * Math.SQRT2, areaSigmaM2: areaSigma(P, sigmaPtMm) / 1e6,
      plotMm: P, perspRatio: persp
    };
    return out;
  }
  // 2-point reference (card long side, coin diameter, custom length). No perspective correction.
  function photoLine(refPx, refLenMm, plotPx, opts) {
    opts = opts || {};
    if (plotPx.length < 3) return { error: "need_3_points" };
    const dpx = Math.hypot(refPx[0][0] - refPx[1][0], refPx[0][1] - refPx[1][1]);
    if (dpx < 5) return { error: "ref_too_small" };
    const scale = refLenMm / dpx; // mm per px
    const P = plotPx.map(p => [p[0] * scale, p[1] * scale]);
    const st = polyStats(P);
    const { q, checks } = qualityChecks(dpx, null, opts);
    checks.push({ id: "lineRef", level: "mid", value: 0 }); // no tilt correction possible
    if (!st.simple) checks.push({ id: "selfx", level: "bad", value: 1 });
    let quality = st.simple ? q : "bad";
    if (quality === "good") quality = "mid"; // line reference can never be top grade
    const tsp = tapSigmaPx(opts.blurVar);
    const sigmaPtMm = tsp * scale;
    return {
      ok: true, mode: "line", scaleMmPerPx: scale,
      lengthsMm: st.lengths, perimeterMm: st.perimeter, areaMm2: st.area,
      areaM2: st.area / 1e6, simple: st.simple, quality, checks,
      lenSigmaMm: sigmaPtMm * Math.SQRT2, areaSigmaM2: areaSigma(P, sigmaPtMm) / 1e6,
      plotMm: P, perspRatio: null
    };
  }

  const api = { solveCombined, llToLocal, averageFixes, solve, area, formatArea, FEDDAN, QIRAT, SAHM,
    homography, applyH, photoQuad, photoLine, convexQuad };
  if (typeof module !== "undefined") module.exports = api; else root.LandCore = api;
})(typeof self !== "undefined" ? self : this);
