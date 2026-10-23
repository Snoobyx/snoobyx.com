/*
   Meadow: grass and flowers on a 24x24 tile grid below the sky, a piece of
   land under them, wind, flowers that bloom, and a butterfly.

   Sprites (scenery/meadow.png, 72x432, black + white):
     rows 0-11   tuft1, tuft1-m, tuft2, tuft2-m, tuft3, tuft3-m,
                 short, short-m, tall, tall-m, pair, pair-m
     rows 12-17  the 6 flower rows again with the heads in key colours:
                 magenta/cyan = head A petals/centre, orange/blue = head B
     columns     rest, lean 1, lean 2
   scenery/butterfly.png, 36x8: wings open, half, closed (12x8 each).

   Sizes: one sprite pixel is S screen pixels (a whole number, about one CSS
   px: 0.67 to 1.33), so everything stays sharp. The canvases hold one pixel
   per sprite pixel and the browser scales them up by S (image-rendering:
   pixelated), which keeps their memory small. Units in this file: "tiles"
   (24 sprite px), sprite px, and screen px (device pixels, most of the maths).

   All colours come from style.css. The settings below were tuned in the
   meadow lab (a separate test page).
*/
(function () {
  "use strict";

  const root = document.querySelector(".meadow");
  const links = document.querySelector(".links");
  const scene = document.querySelector(".scene");
  const main = document.querySelector("main");
  if (!root || !links || !scene || !main || !window.CanvasRenderingContext2D) return;

  const SET = {
    density: 0.3, // at the bottom row; thinner further up
    patch: 0.8, // how much the grass gathers in patches (0 = even)
    patchSize: 8, // tiles
    flowers: 0.15,
    clearance: 1, // tiles of bare ground around each link label
    soft: 2.5, // tiles over which the grass thins out near a label
    edgeScale: 6, // tiles: length of the land edge's hills
    land: { // tiles: sky above the land, the edge's wobble, land above the first link
      wide: { sky: 1, amp: 2, pad: 1 },
      phone: { sky: 0.5, amp: 1, pad: 0.5 }, // under 640px
    },
    gustEvery: 3, gustSpeed: 10, gustWidth: 5, burst: 0.4, breeze: 1,
    bf: { arrive: 1.5, stay: 45, away: 15, speed: 60, cross: 0.35 }, // seconds, CSS px/s, share of flights
  };
  const TUFTS = [0, 1, 2];
  const FLOWERS = [3, 3, 4, 4, 5]; // short and tall twice as likely as a pair
  const PETALS = ["violet", "red", "pink", "blue"];
  const KEYS = [[255, 0, 255], [0, 255, 255], [255, 128, 0], [0, 128, 255]];

  /* ---------- elements ---------- */
  const ground = document.createElement("div"); // plain colour under the land edge
  const edge = document.createElement("canvas"); // the land's top edge
  const grass = document.createElement("canvas"); // the grass, and the butterfly
  ground.className = "ground";
  edge.className = "edge";
  grass.className = "grass";
  root.append(ground, edge, grass);
  const ectx = edge.getContext("2d");
  const ctx = grass.getContext("2d");

  /* ---------- colours (from style.css, any CSS colour format) ---------- */
  const css = getComputedStyle(document.documentElement);
  const tok = (name) => css.getPropertyValue(name).trim();
  const COL = {
    near: tok("--grass"), mid: tok("--grass-mid"), far: tok("--grass-far"),
    ground: tok("--ground"), rim: tok("--rim"), centre: tok("--petal-centre"),
  };
  const PETAL = Object.fromEntries(PETALS.map((p) => [p, tok("--petal-" + p)]));
  const probe = document.createElement("canvas").getContext("2d", { willReadFrequently: true });
  const rgbCache = new Map();
  function rgb(colour) { // any CSS colour -> [r, g, b], by painting one pixel
    let v = rgbCache.get(colour);
    if (v) return v;
    probe.clearRect(0, 0, 1, 1);
    probe.fillStyle = "#000";
    probe.fillStyle = colour;
    probe.fillRect(0, 0, 1, 1);
    const d = probe.getImageData(0, 0, 1, 1).data;
    v = [d[0], d[1], d[2]];
    rgbCache.set(colour, v);
    return v;
  }
  const near = (a, i, c) => Math.abs(a[i] - c[0]) + Math.abs(a[i + 1] - c[1]) + Math.abs(a[i + 2] - c[2]) < 24;

  /* ---------- randomness: hashed per tile, so a resize keeps the pattern ---------- */
  const seed = (Math.random() * 2 ** 31) | 0; // a new meadow on every visit
  function hash(x, y, k) {
    let h = seed ^ Math.imul(x, 0x27d4eb2d) ^ Math.imul(y, 0x165667b1) ^ Math.imul(k, 0x9e3779b9);
    h = Math.imul(h ^ (h >>> 15), 0x85ebca6b);
    h = Math.imul(h ^ (h >>> 13), 0xc2b2ae35);
    return ((h ^ (h >>> 16)) >>> 0) / 4294967296;
  }
  const ease = (t) => t * t * (3 - 2 * t);
  const smooth = (lo, hi, x) => ease(Math.min(1, Math.max(0, (x - lo) / (hi - lo))));
  function noise(x, y, scale, k) {
    x /= scale; y /= scale;
    const xi = Math.floor(x), yi = Math.floor(y), u = ease(x - xi), v = ease(y - yi);
    const a = hash(xi, yi, k), b = hash(xi + 1, yi, k), c = hash(xi, yi + 1, k), d = hash(xi + 1, yi + 1, k);
    return a + (b - a) * u + (c - a) * v + (a - b - c + d) * u * v;
  }
  const key = (c, r) => c + "," + r;

  /* ---------- state ---------- */
  let sheet = null, moth = null, atlas = null; // the sprite images, and the sheet's pixels (null if the browser won't share them)
  let dpr = 1, S = 1, T = 24, W = 0, H = 0, cx = 0, bottom = 0, gridTop = 0, grassTop = 0, rows = 0;
  let zones = [], top = null, cells = new Map(), list = [];
  const painted = new Map(); // bloomed flowers survive a relayout
  const bases = new Map(), coloured = new Map();
  const reduce = matchMedia("(prefers-reduced-motion: reduce)");
  const phone = () => innerWidth < 640; // same width as the CSS media query (scrollbar included)

  function readScale() {
    const n = parseFloat(tok("--n")) || 1, d = parseFloat(tok("--d")) || 1;
    dpr = window.devicePixelRatio || 1;
    S = Math.max(1, Math.round(dpr * Math.min(1, n / d))); // screen px per sprite px (--tile in style.css is the usual result)
    T = 24 * S;
  }
  const cssPx = (v) => v / dpr + "px";
  // A canvas only lands on whole screen pixels if its size and position are
  // whole multiples of a step that is both a whole number of CSS px (5 screen
  // px at 125%, 21 at 2.625x, 1 at 1x/2x/3x) and of sprite pixels.
  let step = 1;
  function findStep() {
    let unit = 1;
    for (let k = 1; k <= 64; k++) if (Math.abs(k * dpr - Math.round(k * dpr)) < 1e-6) { unit = Math.round(k * dpr); break; }
    const gcd = (a, b) => (b ? gcd(b, a % b) : a);
    step = (unit * S) / gcd(unit, S);
  }
  // Size and place a canvas (one pixel per sprite pixel) so it covers screen
  // px [y0, y1) of the page at full width. Returns where its top really is.
  function place(c, y0, y1) {
    const top0 = Math.floor(y0 / step) * step;
    const w = Math.ceil(W / step) * step, h = Math.max(step, Math.ceil((y1 - top0) / step) * step);
    c.width = w / S;
    c.height = h / S;
    c.style.width = cssPx(w);
    c.style.height = cssPx(h);
    c.style.top = cssPx(top0);
    return top0;
  }

  /* ---------- sprites, recoloured once per colour ---------- */
  function baseFor(colour) { // rows 0-11 with black swapped for an ink colour
    if (!atlas) return sheet; // fallback: the sheet as it is, black
    let c = bases.get(colour);
    if (c) return c;
    const ink = rgb(colour), d = new ImageData(new Uint8ClampedArray(atlas.data), atlas.width, atlas.height), a = d.data;
    for (let i = 0; i < a.length; i += 4) if (a[i + 3] && near(a, i, [0, 0, 0])) { a[i] = ink[0]; a[i + 1] = ink[1]; a[i + 2] = ink[2]; }
    c = document.createElement("canvas");
    c.width = d.width; c.height = d.height;
    c.getContext("2d").putImageData(d, 0, 0);
    bases.set(colour, c);
    return c;
  }
  function colouredRow(type, mir, pa, pb, colour) { // one flower's 3 frames with its heads in petal colours
    const id = [type, mir, pa, pb, colour].join();
    let c = coloured.get(id);
    if (c) return c;
    const row = 12 + (type - 3) * 2 + mir, w = atlas.width, src = atlas.data;
    const to = [rgb(PETAL[pa]), rgb(COL.centre), rgb(PETAL[pb]), rgb(COL.centre)], ink = rgb(colour);
    const d = new ImageData(72, 24), o = d.data;
    for (let y = 0; y < 24; y++) for (let x = 0; x < 72; x++) {
      const i = ((row * 24 + y) * w + x) * 4, j = (y * 72 + x) * 4;
      if (!src[i + 3]) continue;
      const k = KEYS.findIndex((kc) => near(src, i, kc));
      const px = k >= 0 ? to[k] : near(src, i, [0, 0, 0]) ? ink : [src[i], src[i + 1], src[i + 2]];
      o[j] = px[0]; o[j + 1] = px[1]; o[j + 2] = px[2]; o[j + 3] = 255;
    }
    c = document.createElement("canvas");
    c.width = 72; c.height = 24;
    c.getContext("2d").putImageData(d, 0, 0);
    coloured.set(id, c);
    return c;
  }
  // Depth: far rows fade toward the sky in 3 flat steps, like distance in real air.
  const inkFor = (fromTop) => (rows < 3 ? COL.near : [COL.far, COL.mid, COL.near][Math.min(2, Math.floor((3 * fromTop) / rows))]);

  /* ---------- the land's edge ---------- */
  // An edge the way a pixel artist draws one: straight stretches joined by
  // clean slopes only (1:1, 1:2, 1:3, 1:4), changing by one notch at a time
  // so hills come out round, and never turning back before rising 2px.
  // Follows a smooth noise; stays between 0 and amp sprite px.
  const SLOPES = [-1, -1 / 2, -1 / 3, -1 / 4, 0, 1 / 4, 1 / 3, 1 / 2, 1];
  function wander(len, amp, scale, salt) {
    const out = new Int32Array(len);
    let x = 0, y = Math.round(noise(0, salt, scale, 41) * amp), si = 4, n = 0, dir = 0, climb = 2;
    while (x < len) {
      const want = noise(x, salt, scale, 41) * amp - y;
      const goal = 4 + Math.max(-4, Math.min(4, Math.round(want / Math.max(1, amp / 6))));
      si += Math.sign(goal - si);
      if (Math.sign(SLOPES[si]) === -dir && climb < 2) si = 4;
      const sl = SLOPES[si], r = hash(salt, n++, 42);
      if (sl && Math.sign(sl) !== dir) { dir = Math.sign(sl); climb = 0; }
      if (!sl) { // level stretch, 4-15px
        for (let k = 4 + Math.floor(r * 12); k > 0 && x < len; k--) out[x++] = y;
        continue;
      }
      const run = Math.round(1 / Math.abs(sl)), steps = 1 + Math.floor(r * 3);
      for (let st = 0; st < steps; st++) {
        for (let k = 0; k < run && x < len; k++) out[x++] = y;
        const ny = y + Math.sign(sl);
        if (ny < 0 || ny > amp) { si = 4; break; } // hit the limit: level out
        y = ny;
        climb++;
      }
    }
    return out;
  }
  // Rounded lumps along the lip, like turf: in clusters with smooth stretches
  // between, three sizes (small 6-10px wide, 2px tall; medium 12-20px, 2-3px;
  // wide 24-44px, 3-4px), shoulders that grow with the width, never under
  // 2px tall, and at least 6px of level ground between two lumps.
  function lumps(len, salt) {
    const out = new Int32Array(len);
    let x = 0, n = 0;
    while (x < len) {
      const r = hash(salt, n++, 43);
      if (noise(x, salt, 140, 46) < 0.45) { x += 12 + Math.floor(r * 30); continue; }
      const size = hash(salt, n++, 47), rw = hash(salt, n++, 45);
      let w, h;
      if (size < 0.3) { w = 6 + Math.floor(rw * 5); h = 2; }
      else if (size < 0.75) { w = 12 + Math.floor(rw * 9); h = r < 0.5 ? 2 : 3; }
      else { w = 24 + Math.floor(rw * 21); h = r < 0.5 ? 3 : 4; }
      const f = Math.max(1, Math.floor((w - 2) / 2 / ((h * (h + 1)) / 2)));
      const rise = [];
      for (let k = 1; k <= h; k++) for (let c = 0; c < k * f; c++) rise.push(k);
      w = Math.max(w, 2 * rise.length + 2);
      for (let c = 0; c < w && x + c < len; c++) { const d = Math.min(c, w - 1 - c); out[x + c] = d < rise.length ? rise[d] : h; }
      x += w + 6 + Math.floor(hash(salt, n++, 44) * 16);
    }
    return out;
  }

  /* ---------- layout ---------- */
  let lastW = -1, lastH = -1, laidOut = false;
  function measure() { // [width, height] of the page in CSS px, without the meadow itself
    root.style.height = "0px";
    const de = document.documentElement;
    const pad = parseFloat(getComputedStyle(document.body).paddingBottom) || 0;
    const page = main.getBoundingClientRect().bottom + scrollY + pad;
    return [de.clientWidth, Math.max(de.clientHeight, page)];
  }

  function layout() {
    const oldDpr = dpr;
    readScale();
    findStep();
    const [cssW, cssH] = measure();
    lastW = cssW; lastH = cssH;
    W = Math.round(cssW * dpr);
    H = Math.round(cssH * dpr);
    root.style.height = cssH + "px";
    bottom = Math.floor(H / S) * S; // grass rows stand on the bottom edge

    // where nothing grows: each link's icon and label (plus room for the menu
    // cursor and its 4px step), so grass creeps in beside short labels
    const m = SET.clearance * T;
    zones = [...links.querySelectorAll("span")].map((s) => {
      const r = s.getBoundingClientRect();
      return { l: (r.left + scrollX - 18) * dpr - m, r: (r.right + scrollX) * dpr + m, t: (r.top + scrollY) * dpr - m, b: (r.bottom + scrollY) * dpr + m };
    });
    const lr = links.getBoundingClientRect();
    cx = Math.round((((lr.left + lr.right) / 2 + scrollX) * dpr) / S) * S; // grid centred on the links

    // The land: its edge sits `pad` tiles above the first label and rises from
    // there, never into the sky band under the logo. The CSS margin above the
    // list makes the room; if a screen gives less, the hills just get lower.
    const p = phone() ? SET.land.phone : SET.land.wide;
    const LX = Math.ceil(W / S);
    const firstLink = zones.length ? Math.min(...zones.map((z) => z.t)) + m : bottom;
    const hy = Math.floor((firstLink - p.pad * T) / S); // sprite px
    const sky = Math.ceil(((scene.getBoundingClientRect().bottom + scrollY) * dpr + p.sky * T) / S);
    const amp = Math.max(0, Math.min(Math.round(p.amp * 24), hy - sky - 4)); // 4 = tallest lump
    const rise = wander(LX, amp, SET.edgeScale * 24, 1), bumps = lumps(LX, 4);
    top = new Int32Array(LX);
    for (let i = 0; i < LX; i++) top[i] = Math.max(sky, hy - rise[i] - bumps[i]);
    for (let i = 1; i < LX - 1; i++) { // where a lump meets a slope: no 1px spike or notch
      const a = top[i - 1], b = top[i + 1];
      if ((top[i] < a && top[i] < b) || (top[i] > a && top[i] > b)) top[i] = Math.abs(top[i] - a) < Math.abs(top[i] - b) ? a : b;
    }
    drawLand(hy);

    // grass rows: from the highest point of the land down to the bottom
    rows = Math.max(0, Math.floor((bottom - Math.min(...top) * S) / T));
    gridTop = bottom - rows * T;
    grassTop = place(grass, gridTop, bottom);
    twitch.clear(); // leans and gusts belong to the old cells
    generate();
    ctx.imageSmoothingEnabled = false;
    for (const cl of list) draw(cl);

    // the butterfly keeps flying: same spot on screen, but it picks a new flower
    if (oldDpr !== dpr && bf.state !== "away") { bf.x *= dpr / oldDpr; bf.y *= dpr / oldDpr; }
    if (bf.state === "land") bf.state = "fly";
    bf.target = null;
    bf.prev = null;
    laidOut = true;
  }

  // The edge strip: ground under a wandering 1px rim, plus a few rows of
  // overlap with the plain ground block below it, so no seam shows.
  function drawLand(hy) {
    const LX = top.length, t0 = Math.min(...top);
    const off = place(edge, t0 * S, (hy + 5) * S) / S; // sprite px
    ground.style.top = Math.ceil(((hy + 1) * S) / dpr) + "px"; // inside the strip's overlap, never above the rim
    const px = (i, j, w, h) => ectx.fillRect(i, j - off, w, h);
    ectx.fillStyle = COL.ground;
    for (let i = 0; i < LX; ) { // ground in runs of equal height: few draw calls
      let k = i;
      while (k < LX && top[k] === top[i]) k++;
      px(i, top[i], k - i, hy + 5 - top[i]);
      i = k;
    }
    // Rim: one solid colour, no in-between shades. Where the edge steps more
    // than 1px, the rim runs down the side so the line never breaks.
    ectx.fillStyle = COL.rim;
    for (let i = 0; i < LX; i++) {
      const l = i > 0 ? top[i - 1] : top[i], r = i < LX - 1 ? top[i + 1] : top[i];
      px(i, top[i], 1, Math.max(1, Math.max(l, r) - top[i]));
    }
  }

  // a tile may hold grass only if it sits entirely on the land, under the rim
  function onLand(x, y) {
    const i0 = Math.floor(x / S), j = Math.floor(y / S) - 1;
    for (let i = i0; i < i0 + 24; i++) if (i < 0 || i >= top.length || top[i] > j) return false;
    return true;
  }

  function below(x, r) { // tiles in the row below that sit under [x, x + T)
    const out = [];
    for (let c = Math.floor((x - cx) / T); c <= Math.floor((x + T - 1 - cx) / T); c++) { const cl = cells.get(key(c, r - 1)); if (cl) out.push(cl); }
    return out;
  }

  function generate() {
    cells = new Map(); list = [];
    for (let r = 0; r < rows; r++) {
      const y = bottom - (r + 1) * T, fromTop = rows - 1 - r;
      const p = SET.density * Math.max(0.04, (fromTop + 0.5) / rows); // thickens all the way down
      const cmin = Math.ceil(-cx / T), cmax = Math.floor((W - cx) / T) - 1; // whole tiles only
      for (let c = cmin; c <= cmax; c++) {
        const x = cx + c * T;
        let dist = Infinity; // to the nearest label zone, in tiles
        for (const z of zones) {
          const dx = Math.max(z.l - (x + T), x - z.r, 0), dy = Math.max(z.t - (y + T), y - z.b, 0);
          dist = Math.min(dist, Math.hypot(dx, dy) / T);
        }
        if (dist === 0 || !onLand(x, y)) continue;
        const edgeFade = smooth(0, SET.soft, dist - 0.5 + hash(c, r, 5)); // thins out near the links, unevenly
        const patch = smooth(0.3, 0.7, noise(c, r, SET.patchSize, 11));
        const prob = Math.min(1, p * edgeFade * (1 - SET.patch + SET.patch * patch * 1.8));
        if (hash(c, r, 1) >= prob) continue;
        const l1 = cells.get(key(c - 1, r));
        if (l1 && cells.get(key(c - 2, r))) continue; // never 3 in a row
        const banned = new Set(below(x, r).map((b) => b.type));
        if (l1) banned.add(l1.type); // no identical neighbours
        const fp = SET.flowers * (noise(c, r, 3, 21) > 0.6 ? 2.5 : 0.35); // flowers in clusters
        let opts = (hash(c, r, 2) < fp ? FLOWERS : TUFTS).filter((t) => !banned.has(t));
        if (!opts.length) opts = TUFTS.filter((t) => !banned.has(t));
        if (!opts.length) continue;
        const type = opts[Math.floor(hash(c, r, 3) * opts.length)];
        const cell = { c, r, x, y, type, mir: hash(c, r, 4) < 0.5 ? 1 : 0, f: 0, col: null, mid: x + T / 2, fromTop, ink: inkFor(fromTop) };
        const was = painted.get(key(c, r));
        if (was && was.type === type && was.mir === cell.mir) cell.col = was.col;
        cells.set(key(c, r), cell);
        list.push(cell);
      }
    }
  }

  function draw(cl) { // one tile, in sprite px on the grass canvas
    const x = cl.x / S, y = (cl.y - grassTop) / S;
    ctx.clearRect(x, y, 24, 24);
    const src = cl.col ? colouredRow(cl.type, cl.mir, cl.col[0], cl.col[1], cl.ink) : baseFor(cl.ink);
    ctx.drawImage(src, cl.f * 24, cl.col ? 0 : (cl.type * 2 + cl.mir) * 24, 24, 24, x, y, 24, 24);
    if (bf.prev && overlaps(cl.x, cl.y, T, T, bf.prev)) drawMoth(); // keep the butterfly on top
  }
  const overlaps = (x, y, w, h, r) => x < r[0] + r[2] && x + w > r[0] && y < r[1] + r[3] && y + h > r[1];

  function bloom(cl) {
    if (cl.col || !atlas) return;
    const pa = PETALS[(Math.random() * 4) | 0];
    let pb = pa;
    while (pb === pa) pb = PETALS[(Math.random() * 4) | 0];
    cl.col = [pa, pb];
    painted.set(key(cl.c, cl.r), { type: cl.type, mir: cl.mir, col: cl.col });
    draw(cl);
  }

  /* ---------- wind ---------- */
  const motionOK = () => !reduce.matches;
  let gusts = [], loop = 0, wait = 0, lastT = 0, onScreen = true;
  const twitch = new Map(); // cell -> end time

  function startGust() {
    if (!motionOK() || !list.length) return;
    // no two gusts alike: speed 75-130%, width one tile either way
    const w = Math.max(2, SET.gustWidth + ((Math.random() * 3) | 0) - 1);
    const speed = (SET.gustSpeed * (0.75 + Math.random() * 0.55) * T) / 1000;
    gusts.push({ t0: performance.now(), strong: Math.random() < 0.7, w, speed });
    if (Math.random() < SET.burst) setTimeout(() => { // real wind comes in bursts
      if (!motionOK() || !onScreen) return;
      gusts.push({ t0: performance.now(), strong: false, w: Math.max(2, w - 1), speed: speed * 1.15 });
      run();
    }, 500 + Math.random() * 700);
    run();
  }
  (function schedule() {
    setTimeout(() => { if (onScreen && !document.hidden) startGust(); schedule(); }, SET.gustEvery * 1000 * (0.6 + Math.random() * 0.8));
  })();
  const run = () => { if (!loop && !wait) loop = requestAnimationFrame(tick); }; // one loop, never two
  function rest() {
    gusts = []; twitch.clear();
    for (const cl of list) if (cl.f) { cl.f = 0; draw(cl); }
  }
  // Runs ~30 times a second during a gust, ~16 between gusts (the breeze),
  // and not at all off screen, in a hidden tab, or with reduced motion.
  function tick(now) {
    loop = 0;
    if (!motionOK() || !onScreen || !laidOut) return rest();
    const dt = Math.min(200, now - (lastT || now));
    lastT = now;
    let n = SET.breeze * (list.length / 100) * (dt / 1000); // a tuft here and there leans for a moment
    n = Math.floor(n) + (Math.random() < n % 1 ? 1 : 0);
    while (n-- > 0) { const cl = list[(Math.random() * list.length) | 0]; if (!twitch.has(cl)) twitch.set(cl, now + 240 + Math.random() * 220); }
    // gusts: bands crossing left to right; lean 1, 2, 2, 1
    const maxLag = (0.6 + Math.max(0, rows - 1) * 0.15) * T;
    for (const g of gusts) g.front = -2 * T + (now - g.t0) * g.speed;
    const before = gusts.length;
    gusts = gusts.filter((g) => g.front - (g.w + 1) * T - maxLag <= W);
    const todo = gusts.length || gusts.length < before ? list : [...twitch.keys()];
    for (const cl of todo) {
      let f = 0;
      if (gusts.length) {
        const lag = (hash(cl.r, 0, 9) - 0.5) * 1.2 * T + cl.fromTop * 0.15 * T; // uneven, slightly slanted front
        for (const g of gusts) { const d = (g.front - cl.mid - lag) / T; if (d > 0 && d < g.w) f = Math.max(f, g.strong && d > g.w * 0.25 && d < g.w * 0.75 ? 2 : 1); }
      }
      const end = twitch.get(cl);
      if (end) { if (now < end) f = Math.max(f, 1); else twitch.delete(cl); }
      if (f !== cl.f) { cl.f = f; draw(cl); }
    }
    wait = setTimeout(() => { wait = 0; run(); }, gusts.length ? 33 : 60);
  }
  new IntersectionObserver((entries) => {
    onScreen = entries[entries.length - 1].isIntersecting; // the latest state wins
    if (onScreen) run();
  }).observe(grass);
  reduce.addEventListener("change", () => (motionOK() ? run() : rest()));

  /* ---------- flowers bloom under a mouse, and stay ---------- */
  let pointer = null, hoverRaf = 0, lastPt = null; // pointer in CSS px of the window
  const pointerAt = () => pointer && { x: (pointer.x + scrollX) * dpr, y: (pointer.y + scrollY) * dpr }; // on the page, in screen px
  addEventListener("pointermove", (e) => {
    pointer = { x: e.clientX, y: e.clientY }; // the butterfly keeps away from it
    if (e.pointerType !== "mouse" || !laidOut) return;
    lastPt = e;
    if (!hoverRaf) hoverRaf = requestAnimationFrame(() => {
      hoverRaf = 0;
      const x = lastPt.pageX * dpr, r = Math.floor((bottom - lastPt.pageY * dpr) / T);
      const cl = r >= 0 && r < rows && cells.get(key(Math.floor((x - cx) / T), r));
      if (cl && cl.type >= 3) bloom(cl);
    });
  }, { passive: true });
  addEventListener("pointerdown", (e) => { // a tap scares the butterfly too, then the finger is gone
    if (e.pointerType === "mouse") return;
    pointer = { x: e.clientX, y: e.clientY };
    setTimeout(() => (pointer = null), 400);
  }, { passive: true });
  document.documentElement.addEventListener("pointerleave", () => (pointer = null));

  /* ---------- the butterfly ---------- */
  // Always black. Drawn on the grass canvas, so it is exactly as sharp as the
  // grass. It flutters in from a side, lands on any flower (which blooms),
  // gets pushed by gusts, darts away from the pointer and then settles on a
  // flower nearby, crosses the links now and then, and after a while leaves
  // (calmly, from a flower) and comes back later.
  const PERCH = [1, 0, 1, 2], FLAP = [0, 1, 2, 1];
  const heads = {}; // flower type -> mirrored -> [{x, top}] in sprite px, from the key rows
  function findHeads() {
    for (let type = 3; type <= 5; type++) {
      heads[type] = [];
      for (let mir = 0; mir <= 1; mir++) {
        const row = 12 + (type - 3) * 2 + mir, found = [[], []];
        for (let y = 0; y < 24; y++) for (let x = 0; x < 24; x++) {
          const i = ((row * 24 + y) * atlas.width + x) * 4;
          const k = atlas.data[i + 3] ? KEYS.findIndex((kc) => near(atlas.data, i, kc)) : -1;
          if (k >= 0) found[k >> 1].push([x, y]);
        }
        heads[type][mir] = found.filter((f) => f.length).map((f) => ({ x: f.reduce((a, q) => a + q[0], 0) / f.length, top: Math.min(...f.map((q) => q[1])) }));
      }
    }
  }
  const headsOf = (cl) => (heads[cl.type] && heads[cl.type][cl.mir]) || [{ x: 12, top: 8 }];

  // Positions are in screen px on the page. (lx, ly) is where it will land.
  const bf = {
    state: "away", // away | fly | land | leave
    x: 0, y: 0, vx: 0, vy: 0, t: 0, inside: false,
    target: null, head: 0, lx: 0, ly: 0, legEnd: 0, wander: null, wanderUntil: 0, wanderDone: false,
    until: 0, exitX: 0, perchUntil: 0,
    flee: 0, fleeCool: 0, settleUntil: 0, recheck: 0,
    f: 0, prevF: 0, i: 0, nextF: 0, seq: null, glide: 0,
    prev: null, // where it was last drawn: [x, y, w, h]
  };
  let bfTimer = 0, bfLoop = 0, lastBT = 0;
  const bfOK = () => motionOK() && onScreen && !document.hidden && laidOut && !!moth;
  const view = () => [scrollY * dpr, (scrollY + innerHeight) * dpr];
  const sp = () => SET.bf.speed * dpr;
  const skyLimit = () => grassTop + 8 * S; // it can't fly above the grass canvas

  function arrive() {
    bfTimer = 0;
    const [v0, v1] = view();
    if (!bfOK() || gridTop > v1 - 2 * T) { bfTimer = setTimeout(arrive, 400); return; } // waits for the meadow to be on screen
    const lo = Math.max(skyLimit() + T, v0 + T), hi = Math.max(lo + T, Math.min(bottom, v1) - 2 * T);
    const left = Math.random() < 0.5;
    const seen = list.filter((c) => c.type >= 3 && c.y > lo && c.y < hi && (c.mid < cx) === left);
    Object.assign(bf, {
      state: "fly", x: left ? -3 * S : W + 3 * S, y: seen.length ? seen[(Math.random() * seen.length) | 0].y : lo + Math.random() * (hi - lo),
      vx: 0, vy: 0, target: null, wander: null, flee: 0, inside: false, until: performance.now() + SET.bf.stay * 1000,
    });
    bfRun(0);
  }
  function away() {
    bf.state = "away";
    eraseMoth();
    clearTimeout(bfTimer);
    bfTimer = setTimeout(arrive, SET.bf.away * 1000 * (0.7 + Math.random() * 0.6));
  }
  function aim(cl) { // land on top of one of its heads
    const hs = headsOf(cl), h = hs[Math.min(bf.head, hs.length - 1)];
    bf.lx = cl.x + h.x * S;
    bf.ly = cl.y + (h.top + 2) * S;
  }
  // Next flower: one of the 4 nearest on screen; about one flight in three
  // goes across the links. Just after a scare (settle): the nearest one that
  // isn't next to the cursor. Returns false if no flower is on screen.
  function pickTarget(settle) {
    const [v0, v1] = view(), pt = pointerAt();
    const calm = (c) => !pt || Math.hypot(c.mid - pt.x, c.y - pt.y) > (settle ? 80 : 120) * dpr;
    const onView = (c) => c.type >= 3 && c !== bf.target && c.y > v0 && c.y + T < v1;
    const mine = (c) => (c.mid < cx) === (bf.x < cx);
    const other = !settle && Math.random() < SET.bf.cross;
    let fl = list.filter((c) => onView(c) && calm(c) && mine(c) !== other);
    if (!fl.length) fl = list.filter((c) => onView(c) && calm(c));
    if (!fl.length) fl = list.filter(onView);
    if (!fl.length) return false;
    fl.sort((a, b) => Math.hypot(a.mid - bf.x, a.y - bf.y) - Math.hypot(b.mid - bf.x, b.y - bf.y));
    const cl = settle ? fl[0] : fl[(Math.random() * Math.min(4, fl.length)) | 0];
    bf.target = cl;
    bf.wander = null;
    bf.wanderUntil = 0;
    bf.head = (Math.random() * headsOf(cl).length) | 0;
    aim(cl);
    bf.legEnd = performance.now() + 4000 + (Math.hypot(bf.lx - bf.x, bf.ly - bf.y) / sp()) * 1500; // then think again
    return true;
  }
  // No flower on screen: flutter about the visible meadow for a while, looking.
  function pickWander(now) {
    const [v0, v1] = view();
    const lo = Math.max(skyLimit() + T, v0 + T), hi = Math.max(lo + T, Math.min(bottom, v1) - T);
    bf.wander = { x: (0.1 + Math.random() * 0.8) * W, y: lo + Math.random() * (hi - lo) };
    bf.wanderDone = false;
    if (!bf.wanderUntil || bf.wanderUntil < now) bf.wanderUntil = now + 12000;
  }
  function perch(now) {
    bf.state = "land";
    bf.vx = bf.vy = 0;
    bf.perchUntil = now + 2500 + Math.random() * 3500;
    bloom(bf.target);
    bf.seq = null; bf.f = 2; bf.nextF = now + 1200 + Math.random() * 1500;
  }
  function takeOff() { bf.state = "fly"; bf.target = null; bf.vy = -sp(); }
  const leave = () => { bf.state = "leave"; bf.target = null; bf.wander = null; bf.exitX = bf.x < W / 2 ? -40 * S : W + 40 * S; };

  // 30 updates a second in flight, 20 while sitting, none when it can't be seen
  const bfRun = (ms) => { if (!bfLoop) bfLoop = setTimeout(() => requestAnimationFrame(bfTick), ms); };
  function bfTick(now) {
    bfLoop = 0;
    if (!bfOK()) { eraseMoth(); lastBT = 0; return; }
    if (bf.state === "away") return;
    const dt = Math.min(60, now - (lastBT || now)) / 1000, v = sp();
    lastBT = now;
    bf.t += dt;

    // too close to the pointer: dart away (at most every 1.2 s), and take off if sitting
    const pt = pointerAt();
    let pd = Infinity, pdx = 0, pdy = 0;
    if (pt) { pdx = bf.x - pt.x; pdy = bf.y - pt.y; pd = Math.hypot(pdx, pdy) || 1; }
    if (pd < 48 * dpr && now > bf.fleeCool && bf.state !== "leave") {
      if (bf.state === "land") takeOff();
      bf.flee = 0.5;
      bf.fleeCool = now + 1200;
      bf.settleUntil = now + 4000;
      bf.target = null;
      bf.until = Math.max(bf.until, now + 10000); // startled, not gone
      bf.vx = (pdx / pd) * v * 3;
      bf.vy = (pdy / pd) * v * 3 - v;
    }

    if (bf.state === "land") {
      bf.x = bf.lx + bf.target.f * S; // rides the flower as it sways
      bf.y = bf.ly;
      if (!list.includes(bf.target)) bf.state = "fly";
      else if (now > bf.perchUntil) { takeOff(); if (now > bf.until) leave(); } // a visit ends calmly, from a flower
    } else {
      let tx, ty;
      if (bf.state === "fly" && now > bf.until + 20000) leave(); // never managed to land
      if (bf.state === "leave") {
        tx = bf.exitX; ty = bf.y - 20 * dpr;
        if (bf.x < -14 * S || bf.x > W + 14 * S) return away();
      } else {
        const settling = now < bf.settleUntil;
        if (bf.target && now > bf.legEnd) bf.target = null;
        if (bf.flee > 0) bf.target = null; // mid-dart: no plans yet
        else if (!bf.target || !list.includes(bf.target)) { if (!pickTarget(settling) && (!bf.wander || bf.wanderDone)) pickWander(now); }
        else if (settling && now > bf.recheck) { // the cursor may have moved on: a nearer flower?
          bf.recheck = now + 400;
          const was = bf.target, wh = bf.head, wd = Math.hypot(bf.lx - bf.x, bf.ly - bf.y);
          if (!pickTarget(true) || Math.hypot(bf.lx - bf.x, bf.ly - bf.y) >= wd) { bf.target = was; bf.head = wh; aim(was); }
        }
        if (!bf.target && bf.wander && now > bf.wanderUntil) leave(); // looked long enough: flies off
        if (bf.target) { tx = bf.lx + bf.target.f * S; ty = bf.ly; }
        else if (bf.wander && bf.flee <= 0) {
          tx = bf.wander.x; ty = bf.wander.y;
          bf.wanderDone = Math.hypot(tx - bf.x, ty - bf.y) < T; // reached: look again, or pick another spot
        } else { tx = bf.x + bf.vx; ty = bf.y + bf.vy; } // coasting through the dart
      }
      const dx = tx - bf.x, dy = ty - bf.y, d = Math.hypot(dx, dy) || 1;
      const homing = bf.state === "fly" && !!bf.target;
      const slow = homing ? Math.min(1, d / (2 * T)) : 1; // slows down to land
      const flutter = Math.min(1, d / T);
      const cruise = 1 + 0.8 * Math.min(1, Math.max(0, (d - 4 * T) / (10 * T))); // long trips go faster
      let wx = (dx / d) * v * slow * cruise + Math.sin(bf.t * 2.3) * v * 0.5 * flutter;
      let wy = (dy / d) * v * slow * cruise + (Math.sin(bf.t * 7.1) * 0.6 + Math.cos(bf.t * 1.7) * 0.3) * v * flutter;
      if (d >= 1.5 * T) for (const g of gusts) { const gd = (g.front - bf.x) / T; if (gd > 0 && gd < g.w) wx += v * 1.5; } // blown along
      const final = homing && d < 1.5 * T; // last stretch: straight in
      if (final) { wx = (dx / d) * Math.min(v, d * 4); wy = (dy / d) * Math.min(v, d * 4); }
      if (bf.flee > 0) bf.flee -= dt;
      else {
        if (pd < 110 * dpr && bf.state === "fly") { const push = (1 - pd / (110 * dpr)) * v * 2.5; wx += (pdx / pd) * push; wy += (pdy / pd) * push; } // around the cursor
        const k = Math.min(1, dt * (final ? 10 : 3));
        bf.vx += (wx - bf.vx) * k; bf.vy += (wy - bf.vy) * k;
      }
      bf.x += bf.vx * dt; bf.y += bf.vy * dt;
      if (bf.state === "fly") { // once inside, a scare never chases it off screen
        const [v0, v1] = view();
        if (bf.x > 6 * S && bf.x < W - 6 * S) bf.inside = true;
        if (bf.inside) { if (bf.x < 6 * S) bf.vx = Math.abs(bf.vx); if (bf.x > W - 6 * S) bf.vx = -Math.abs(bf.vx); }
        if (bf.y < Math.max(v0 + T, skyLimit())) bf.vy = Math.abs(bf.vy);
        if (bf.y > v1 - T / 2) bf.vy = -Math.abs(bf.vy);
      }
      bf.y = Math.max(bf.y, skyLimit()); // never above the grass canvas
      if (homing && bf.flee <= 0 && Math.hypot(tx - bf.x, ty - bf.y) < 3 * S) perch(now);
    }

    // wings: fast flaps with the odd glide in flight; a slow flap now and then when sitting
    if (now >= bf.nextF) {
      if (bf.state === "land") {
        if (!bf.seq) bf.seq = [...PERCH];
        bf.f = bf.seq.shift();
        bf.nextF = now + (bf.seq.length ? 150 : 1500 + Math.random() * 2000);
        if (!bf.seq.length) bf.seq = null;
      } else if (bf.glide > now) { bf.f = 0; bf.nextF = bf.glide; }
      else if (Math.random() < 0.06) { bf.glide = now + 300 + Math.random() * 400; bf.f = 0; bf.nextF = bf.glide; }
      else { bf.i = (bf.i + 1) % FLAP.length; bf.f = FLAP[bf.i]; bf.nextF = now + 65; }
    }
    // at whole sprite pixels; its body is column 5.5 of the frame, its feet on row 7
    const x = Math.round((bf.x - 5.5 * S) / S) * S, y = Math.round((bf.y - 7 * S) / S) * S;
    if (!bf.prev || bf.prev[0] !== x || bf.prev[1] !== y || bf.f !== bf.prevF) {
      eraseMoth();
      bf.prev = [x, y, 12 * S, 8 * S];
      bf.prevF = bf.f;
      drawMoth();
    }
    bfRun(bf.state === "land" ? 50 : 33);
  }
  function drawMoth() {
    const [x, y] = bf.prev;
    ctx.drawImage(moth, bf.f * 12, 0, 12, 8, x / S, (y - grassTop) / S, 12, 8);
  }
  function eraseMoth() { // clear where it was and redraw the tiles under it
    if (!bf.prev) return;
    const [x, y, w, h] = bf.prev;
    bf.prev = null;
    ctx.clearRect(x / S, (y - grassTop) / S, w / S, h / S);
    for (let c = Math.floor((x - cx) / T); c <= Math.floor((x + w - 1 - cx) / T); c++) {
      for (let r = Math.floor((bottom - (y + h)) / T); r <= Math.floor((bottom - y - 1) / T); r++) {
        const cl = cells.get(key(c, r));
        if (cl) draw(cl);
      }
    }
  }
  setInterval(() => { // restarts the visitor when the page or the meadow comes back into view
    if (!bfOK()) return;
    if (bf.state === "away") { if (!bfTimer) bfTimer = setTimeout(arrive, SET.bf.away * 500); }
    else if (!bfLoop) { lastBT = 0; bfRun(0); }
  }, 1000);

  /* ---------- start: once the sprites and the font are ready ---------- */
  const loadImg = (src) => new Promise((ok) => { const im = new Image(); im.onload = () => ok(im); im.onerror = () => ok(null); im.src = src; });
  Promise.all([loadImg("scenery/meadow.png"), loadImg("scenery/butterfly.png"), document.fonts ? document.fonts.ready : null]).then(([im, bm]) => {
    if (!im) return; // no sprites, no meadow (the page is fine without it)
    sheet = im;
    moth = bm;
    try { // reading the pixels lets us recolour; browsers refuse it for file:// pages
      const c = document.createElement("canvas");
      c.width = im.width; c.height = im.height;
      const x = c.getContext("2d");
      x.drawImage(im, 0, 0);
      atlas = x.getImageData(0, 0, c.width, c.height);
      findHeads();
    } catch (e) {
      atlas = null; // plain black grass, no blooming: the meadow still shows
    }
    layout();
    setTimeout(startGust, 900); // one gust soon after load, so the wind is noticed
    run();
    bfTimer = setTimeout(arrive, SET.bf.arrive * 1000);
    let rt = 0;
    addEventListener("resize", () => {
      clearTimeout(rt);
      rt = setTimeout(() => {
        const [w, h] = measure();
        root.style.height = h + "px"; // always: no sky strip, no extra scroll
        // phones: the address bar showing and hiding changes only the height a
        // little; keep the meadow as it is then (rebuilding would flicker)
        const bar = phone() && w === lastW && Math.abs(h - lastH) < T / dpr;
        if (!bar || dpr !== (window.devicePixelRatio || 1)) layout();
      }, 150);
    });
  });

  // for automated tests only: open the page with ?meadow-test
  if (/[?&]meadow-test\b/.test(location.search)) {
    window.__meadow = { get: () => ({ list, top, zones, S, T, dpr, cx, rows, gridTop, bottom, bf, atlas: !!atlas }) };
  }
})();
