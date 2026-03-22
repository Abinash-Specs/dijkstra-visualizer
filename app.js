(function () {
  "use strict";

  const canvas = document.getElementById("graph");
  const ctx = canvas.getContext("2d");
  const overlay = document.getElementById("canvas-overlay");
  const canvasWrap = canvas.closest(".canvas-wrap");

  const btnStart = document.getElementById("btn-start");
  const btnPause = document.getElementById("btn-pause");
  const btnResume = document.getElementById("btn-resume");
  const btnReset = document.getElementById("btn-reset");
  const btnClear = document.getElementById("btn-clear");
  const speedInput = document.getElementById("speed");
  const speedValue = document.getElementById("speed-value");
  const statusSource = document.getElementById("status-source");
  const statusDest = document.getElementById("status-dest");
  const statusCurrent = document.getElementById("status-current");
  const btnRandom = document.getElementById("btn-random");
  const btnRandomInstant = document.getElementById("btn-random-instant");
  const btnDeleteMode = document.getElementById("btn-delete-mode");
  const modeIndicatorEl = document.getElementById("mode-indicator");

  const weightDialog = document.getElementById("weight-dialog");
  const weightForm = document.getElementById("weight-form");
  const weightInput = document.getElementById("weight-input");
  const weightCancel = document.getElementById("weight-cancel");
  const edgeFromLabel = document.getElementById("edge-from-label");
  const edgeToLabel = document.getElementById("edge-to-label");

  const COLORS = {
    edge: "rgba(139, 156, 179, 0.55)",
    edgeHighlight: "rgba(62, 207, 142, 0.85)",
    weightText: "#a8b5c4",
    label: "#e6edf3",
    unvisited: "#5c6570",
    visiting: "#e6c547",
    visited: "#4c8dff",
    path: "#3ecf8e",
    ring: "rgba(255,255,255,0.12)",
    distText: "#8b9cb3",
    distBg: "rgba(10, 14, 20, 0.92)",
    sourceRing: "#3d8bfd",
  };

  const NODE_R = 22;
  const EDGE_HIT_PX = 14;
  const EDGE_PICK_NODE_BLOCK = NODE_R + 12;
  const PULSE_BASE = 1.08;
  const BLEND_MS_DEFAULT = 300;

  const prefersReducedMotion =
    typeof window.matchMedia === "function" &&
    window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  const BLEND_MS = prefersReducedMotion ? 0 : BLEND_MS_DEFAULT;

  let nodes = [];
  let edges = [];
  let nextId = 1;
  let mode = "add";
  let connectFrom = null;
  let sourceId = null;
  let destId = null;

  let animationFrames = [];
  let frameIndex = 0;
  let playing = false;
  let animPaused = false;
  let timerId = null;
  let blendFromFrame = null;
  let blendToFrame = null;
  let blendStart = 0;
  let prePlaybackState = null;
  let hoveredNodeId = null;
  let hoveredEdgeKey = null;
  let deleteModeActive = false;
  const HOLD_TO_DRAG_MS = 150;
  let pointerSession = null;

  function createMinHeap() {
    const heap = [];
    function parent(i) {
      return (i - 1) >> 1;
    }
    function left(i) {
      return 2 * i + 1;
    }
    function right(i) {
      return 2 * i + 2;
    }
    function swap(i, j) {
      const t = heap[i];
      heap[i] = heap[j];
      heap[j] = t;
    }
    function siftUp(i) {
      while (i > 0) {
        const p = parent(i);
        if (heap[p][0] <= heap[i][0]) break;
        swap(p, i);
        i = p;
      }
    }
    function siftDown(i) {
      const n = heap.length;
      while (true) {
        let sm = i;
        const l = left(i);
        const r = right(i);
        if (l < n && heap[l][0] < heap[sm][0]) sm = l;
        if (r < n && heap[r][0] < heap[sm][0]) sm = r;
        if (sm === i) break;
        swap(i, sm);
        i = sm;
      }
    }
    return {
      push(entry) {
        heap.push(entry);
        siftUp(heap.length - 1);
      },
      pop() {
        if (heap.length === 0) return null;
        const min = heap[0];
        const last = heap.pop();
        if (heap.length) {
          heap[0] = last;
          siftDown(0);
        }
        return min;
      },
      get size() {
        return heap.length;
      },
    };
  }

  function easeOutCubic(t) {
    return 1 - Math.pow(1 - t, 3);
  }

  function hexToRgb(hex) {
    const h = hex.replace("#", "");
    const full = h.length === 3 ? h.split("").map((c) => c + c).join("") : h;
    return {
      r: parseInt(full.slice(0, 2), 16),
      g: parseInt(full.slice(2, 4), 16),
      b: parseInt(full.slice(4, 6), 16),
    };
  }

  function parseFillColor(s) {
    if (!s) return hexToRgb(COLORS.unvisited);
    if (s.startsWith("#")) return hexToRgb(s);
    const m = s.match(/rgba?\(\s*(\d+)\s*,\s*(\d+)\s*,\s*(\d+)/);
    if (m) return { r: +m[1], g: +m[2], b: +m[3] };
    return hexToRgb(COLORS.unvisited);
  }

  function lerp(a, b, t) {
    return a + (b - a) * t;
  }

  function lerpRgb(c0, c1, t) {
    return {
      r: Math.round(lerp(c0.r, c1.r, t)),
      g: Math.round(lerp(c0.g, c1.g, t)),
      b: Math.round(lerp(c0.b, c1.b, t)),
    };
  }

  function rgbToFill(c) {
    return "rgb(" + c.r + "," + c.g + "," + c.b + ")";
  }

  function cloneFrame(f) {
    if (!f) return null;
    return {
      dist: new Map(f.dist),
      settled: new Set(f.settled),
      current: f.current,
      path: f.path ? new Set(f.path) : null,
      note: f.note,
    };
  }

  function virtualIdleState() {
    const dist = new Map();
    const INF = Infinity;
    for (const n of nodes) dist.set(n.id, INF);
    if (sourceId != null) dist.set(sourceId, 0);
    return {
      dist,
      settled: new Set(),
      current: null,
      path: null,
    };
  }

  function nodeCategory(state, id) {
    if (!state) return "unvisited";
    if (state.path && state.path.has(id)) return "path";
    if (state.current === id) return "visiting";
    if (state.settled && state.settled.has(id)) return "visited";
    return "unvisited";
  }

  function categoryFill(cat) {
    switch (cat) {
      case "path":
        return COLORS.path;
      case "visiting":
        return COLORS.visiting;
      case "visited":
        return COLORS.visited;
      default:
        return COLORS.unvisited;
    }
  }

  function getNodeFillColor(fromF, toF, id, te) {
    const a = fromF || toF;
    const b = toF || fromF;
    if (!b) return categoryFill("unvisited");
    if (!a || a === b || te >= 1) return categoryFill(nodeCategory(b, id));
    if (te <= 0) return categoryFill(nodeCategory(a, id));
    const c0 = nodeCategory(a, id);
    const c1 = nodeCategory(b, id);
    if (c0 === c1) return categoryFill(c1);
    const rgb0 = hexToRgb(categoryFill(c0));
    const rgb1 = hexToRgb(categoryFill(c1));
    return rgbToFill(lerpRgb(rgb0, rgb1, te));
  }

  function getDisplayDist(fromF, toF, id, te) {
    const a = fromF || toF;
    const b = toF || fromF;
    if (!b || !b.dist) return null;
    if (!a || a === b) {
      const d = b.dist.get(id);
      return Number.isFinite(d) ? d : null;
    }
    const d0 = a.dist.get(id);
    const d1 = b.dist.get(id);
    if (Number.isFinite(d0) && Number.isFinite(d1)) {
      return Math.round(lerp(d0, d1, te));
    }
    if (te >= 1) return Number.isFinite(d1) ? d1 : null;
    return Number.isFinite(d0) ? d0 : Number.isFinite(d1) ? d1 : null;
  }

  function getBlendContext(now) {
    if (!blendFromFrame || !blendToFrame) {
      return { te: 1, from: null, to: null };
    }
    const raw = BLEND_MS <= 0 ? 1 : Math.min(1, (now - blendStart) / BLEND_MS);
    return { te: easeOutCubic(raw), from: blendFromFrame, to: blendToFrame };
  }

  function edgePathStrength(fromF, toF, a, b, te) {
    if (!fromF || !toF || fromF === toF) {
      return edgeOnPath(a, b, toF?.path) ? 1 : 0;
    }
    const o0 = edgeOnPath(a, b, fromF.path);
    const o1 = edgeOnPath(a, b, toF.path);
    if (o0 && o1) return 1;
    if (!o0 && !o1) return 0;
    return o1 ? te : 1 - te;
  }

  function beginBlend(from, to) {
    blendFromFrame = cloneFrame(from);
    blendToFrame = cloneFrame(to);
    blendStart = performance.now();
  }

  function syncCanvasHoverClass() {
    const interactive = (!playing || animPaused) && overlay.hidden;
    canvasWrap.classList.toggle("has-hover-node", interactive && hoveredNodeId != null);
    canvasWrap.classList.toggle(
      "has-hover-edge",
      interactive && deleteModeActive && hoveredEdgeKey != null && hoveredNodeId == null
    );
  }

  function syncPlayPauseButtons() {
    if (!btnPause || !btnResume) return;
    const len = animationFrames.length;
    const atEnd = len > 0 && frameIndex >= len - 1;
    const canPause = playing && !animPaused && len > 0 && !atEnd;
    btnPause.disabled = !canPause;
    btnResume.disabled = !(playing && animPaused);
  }

  function pauseAnimation() {
    if (!playing || animPaused) return;
    animPaused = true;
    if (timerId) {
      clearTimeout(timerId);
      timerId = null;
    }
    overlay.hidden = true;
    syncPlayPauseButtons();
    syncCanvasHoverClass();
  }

  function resumeAnimation() {
    if (!playing || !animPaused) return;
    animPaused = false;
    overlay.hidden = false;
    timerId = setTimeout(stepNext, getBaseDelayMs());
    syncPlayPauseButtons();
    syncCanvasHoverClass();
  }

  function clearPointerHoldTimer(ps) {
    if (ps && ps.holdTimerId != null) {
      clearTimeout(ps.holdTimerId);
      ps.holdTimerId = null;
    }
  }
  function strokeRoundRect(ctx, x, y, w, h, r) {
    const rr = Math.min(r, w / 2, h / 2);
    ctx.beginPath();
    ctx.moveTo(x + rr, y);
    ctx.lineTo(x + w - rr, y);
    ctx.quadraticCurveTo(x + w, y, x + w, y + rr);
    ctx.lineTo(x + w, y + h - rr);
    ctx.quadraticCurveTo(x + w, y + h, x + w - rr, y + h);
    ctx.lineTo(x + rr, y + h);
    ctx.quadraticCurveTo(x, y + h, x, y + h - rr);
    ctx.lineTo(x, y + rr);
    ctx.quadraticCurveTo(x, y, x + rr, y);
    ctx.closePath();
    ctx.stroke();
  }

  function fillRoundRect(ctx, x, y, w, h, r) {
    const rr = Math.min(r, w / 2, h / 2);
    ctx.beginPath();
    ctx.moveTo(x + rr, y);
    ctx.lineTo(x + w - rr, y);
    ctx.quadraticCurveTo(x + w, y, x + w, y + rr);
    ctx.lineTo(x + w, y + h - rr);
    ctx.quadraticCurveTo(x + w, y + h, x + w - rr, y + h);
    ctx.lineTo(x + rr, y + h);
    ctx.quadraticCurveTo(x, y + h, x, y + h - rr);
    ctx.lineTo(x, y + rr);
    ctx.quadraticCurveTo(x, y, x + rr, y);
    ctx.closePath();
    ctx.fill();
  }

  function nodeById(id) {
    return nodes.find((n) => n.id === id);
  }

  function labelFor(id) {
    const n = nodeById(id);
    return n ? String(n.label) : "—";
  }

  function resizeCanvas() {
    const rect = canvas.getBoundingClientRect();
    const dpr = Math.min(window.devicePixelRatio || 1, 2);
    const w = Math.max(320, rect.width);
    const h = Math.max(480, rect.height);
    canvas.width = Math.floor(w * dpr);
    canvas.height = Math.floor(h * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    nodes.forEach(clampNode);
    draw();
  }

  function distToNode(px, py, n) {
    const dx = px - n.x;
    const dy = py - n.y;
    return Math.hypot(dx, dy);
  }

  function distToNodeSq(px, py, n) {
    const dx = px - n.x;
    const dy = py - n.y;
    return dx * dx + dy * dy;
  }

  function hitNode(px, py) {
    let best = null;
    let bestD = NODE_R + 8;
    for (const n of nodes) {
      const d = distToNode(px, py, n);
      if (d <= bestD) {
        bestD = d;
        best = n;
      }
    }
    return best;
  }

  function hitNodeHover(px, py) {
    let best = null;
    let bestD = NODE_R + 30;
    for (const n of nodes) {
      const d = distToNode(px, py, n);
      if (d <= bestD) {
        bestD = d;
        best = n;
      }
    }
    return best;
  }

  function canvasCoords(ev) {
    const rect = canvas.getBoundingClientRect();
    return {
      x: ev.clientX - rect.left,
      y: ev.clientY - rect.top,
    };
  }

  function updateModeIndicator() {
    if (!modeIndicatorEl) return;
    if (deleteModeActive) {
      modeIndicatorEl.textContent =
        "Delete mode — click a node to remove it and its edges, or click near an edge to remove that edge only. Node IDs are renumbered after node deletion.";
      modeIndicatorEl.classList.add("mode-indicator-delete");
      return;
    }
    modeIndicatorEl.classList.remove("mode-indicator-delete");
    const hints = {
      add: "Add nodes — click empty canvas to place a node. Hold on a node, then drag to move.",
      connect: "Connect — click two nodes in order; enter the edge weight when prompted.",
      source: "Set source — click the node that will be the Dijkstra start.",
      dest: "Set destination — click the target node for the shortest path.",
    };
    modeIndicatorEl.textContent = hints[mode] || hints.add;
  }

  function setDeleteMode(on) {
    if (on && deleteModeActive) return;
    if (!on && !deleteModeActive) return;
    deleteModeActive = on;
    connectFrom = null;
    hoveredEdgeKey = null;
    if (on) {
      document.querySelectorAll(".btn-mode").forEach((b) => b.classList.remove("active"));
      canvasWrap.className = "canvas-wrap mode-delete";
      if (btnDeleteMode) {
        btnDeleteMode.classList.add("active");
        btnDeleteMode.setAttribute("aria-pressed", "true");
      }
    } else {
      document.querySelectorAll(".btn-mode").forEach((b) => {
        b.classList.toggle("active", b.dataset.mode === mode);
      });
      canvasWrap.className = "canvas-wrap mode-" + mode;
      if (btnDeleteMode) {
        btnDeleteMode.classList.remove("active");
        btnDeleteMode.setAttribute("aria-pressed", "false");
      }
    }
    updateModeIndicator();
    syncCanvasHoverClass();
  }

  function setMode(m) {
    mode = m;
    connectFrom = null;
    if (deleteModeActive) {
      deleteModeActive = false;
      if (btnDeleteMode) {
        btnDeleteMode.classList.remove("active");
        btnDeleteMode.setAttribute("aria-pressed", "false");
      }
    }
    document.querySelectorAll(".btn-mode").forEach((b) => {
      b.classList.toggle("active", b.dataset.mode === m);
    });
    canvasWrap.className = "canvas-wrap mode-" + mode;
    updateModeIndicator();
    syncCanvasHoverClass();
  }

  function setHint() {}

  function updateStatus() {
    statusSource.textContent = sourceId != null ? labelFor(sourceId) : "—";
    statusDest.textContent = destId != null ? labelFor(destId) : "—";
    statusCurrent.textContent = "—";
  }

  function buildAdjacency() {
    const adj = new Map();
    for (const n of nodes) adj.set(n.id, []);
    for (const e of edges) {
      if (!nodeById(e.from) || !nodeById(e.to) || e.from === e.to) continue;
      adj.get(e.from).push({ to: e.to, w: e.weight });
      adj.get(e.to).push({ to: e.from, w: e.weight });
    }
    return adj;
  }

  function computeDijkstraSteps(srcId, destId) {
    const ids = nodes.map((n) => n.id);
    if (ids.length === 0) return { frames: [], prev: new Map(), finalDist: new Map() };

    const adj = buildAdjacency();
    const INF = Infinity;
    const dist = new Map();
    const prev = new Map();
    const settled = new Set();

    for (const id of ids) {
      dist.set(id, id === srcId ? 0 : INF);
      prev.set(id, null);
    }

    const frames = [];
    frames.push({
      dist: new Map(dist),
      settled: new Set(),
      current: null,
      path: null,
      note:
        "Step 0 — Initialize: source " +
        labelFor(srcId) +
        " has distance 0; all other nodes ∞. Priority queue holds the source.",
    });

    const pq = createMinHeap();
    pq.push([0, srcId]);

    while (pq.size > 0) {
      const popped = pq.pop();
      if (!popped) break;
      const d = popped[0];
      const u = popped[1];
      if (d !== dist.get(u)) continue;
      if (settled.has(u)) continue;

      frames.push({
        dist: new Map(dist),
        settled: new Set(settled),
        current: u,
        path: null,
        note:
          "Extract min from heap: node " +
          labelFor(u) +
          " (distance " +
          d +
          "). Relax its edges and improve neighbor distances if shorter.",
      });

      for (const { to, w } of adj.get(u) || []) {
        if (settled.has(to)) continue;
        const nd = dist.get(u) + w;
        if (nd < dist.get(to)) {
          dist.set(to, nd);
          prev.set(to, u);
          pq.push([nd, to]);
        }
      }

      settled.add(u);
      frames.push({
        dist: new Map(dist),
        settled: new Set(settled),
        current: null,
        path: null,
        note:
          "Node " +
          labelFor(u) +
          " is settled (optimal). Updated distances are shown; stale heap entries are skipped.",
      });
    }

    const pathSet = new Set();
    if (destId != null && dist.get(destId) !== INF) {
      let cur = destId;
      while (cur != null) {
        pathSet.add(cur);
        cur = prev.get(cur);
      }
    }

    frames.push({
      dist: new Map(dist),
      settled: new Set(settled),
      current: null,
      path: pathSet,
      note:
        dist.get(destId) === INF
          ? "Done — No path to destination (unreachable)."
          : "Done — Shortest path from source to destination highlighted (green).",
    });

    return { frames, prev, finalDist: dist };
  }

  function getBaseDelayMs() {
    const mult = parseFloat(speedInput.value, 10) || 1;
    return Math.round(780 / mult);
  }

  function stopPlayback() {
    playing = false;
    animPaused = false;
    if (timerId) {
      clearTimeout(timerId);
      timerId = null;
    }
    overlay.hidden = true;
    syncPlayPauseButtons();
    syncCanvasHoverClass();
  }

  function applyFrame(i) {
    if (i < 0 || i >= animationFrames.length) return;
    const f = animationFrames[i];
    frameIndex = i;
    statusCurrent.textContent = f.current != null ? labelFor(f.current) : "—";
    if (f.note) setHint(f.note);
    let fromSnap;
    if (i === 0 && prePlaybackState) {
      fromSnap = prePlaybackState;
    } else if (i > 0) {
      fromSnap = animationFrames[i - 1];
    } else {
      fromSnap = f;
    }
    beginBlend(fromSnap, f);
    draw();
  }

  function stepNext() {
    if (!playing || animPaused) return;
    if (frameIndex >= animationFrames.length - 1) {
      stopPlayback();
      btnStart.disabled = false;
      setHint(animationFrames[animationFrames.length - 1]?.note || "Done.");
      syncPlayPauseButtons();
      draw();
      return;
    }
    frameIndex += 1;
    applyFrame(frameIndex);
    timerId = setTimeout(stepNext, getBaseDelayMs());
  }

  function startAnimation() {
    if (deleteModeActive) setDeleteMode(false);
    if (sourceId == null) {
      setHint("Select a source node first.", true);
      return;
    }
    if (destId == null) {
      setHint("Select a destination node first.", true);
      return;
    }
    if (nodes.length === 0) {
      setHint("Add at least one node.", true);
      return;
    }

    prePlaybackState = virtualIdleState();
    const { frames } = computeDijkstraSteps(sourceId, destId);
    animationFrames = frames;
    frameIndex = 0;
    playing = true;
    animPaused = false;
    btnStart.disabled = true;
    overlay.hidden = false;
    hoveredNodeId = null;
    syncCanvasHoverClass();
    applyFrame(0);
    syncPlayPauseButtons();
    timerId = setTimeout(stepNext, getBaseDelayMs());
  }

  function resetVisualization() {
    stopPlayback();
    animationFrames = [];
    frameIndex = 0;
    prePlaybackState = null;
    blendFromFrame = null;
    blendToFrame = null;
    btnStart.disabled = false;
    statusCurrent.textContent = "—";
    setHint("");
    syncPlayPauseButtons();
    draw();
  }

  function resetAll() {
    stopPlayback();
    nodes = [];
    edges = [];
    nextId = 1;
    sourceId = null;
    destId = null;
    connectFrom = null;
    animationFrames = [];
    frameIndex = 0;
    prePlaybackState = null;
    blendFromFrame = null;
    blendToFrame = null;
    hoveredNodeId = null;
    hoveredEdgeKey = null;
    if (deleteModeActive) {
      deleteModeActive = false;
      if (btnDeleteMode) {
        btnDeleteMode.classList.remove("active");
        btnDeleteMode.setAttribute("aria-pressed", "false");
      }
    }
    btnStart.disabled = false;
    updateStatus();
    statusCurrent.textContent = "—";
    setHint("Graph cleared.");
    canvasWrap.className = "canvas-wrap mode-" + mode;
    document.querySelectorAll(".btn-mode").forEach((b) => {
      b.classList.toggle("active", b.dataset.mode === mode);
    });
    updateModeIndicator();
    syncCanvasHoverClass();
    syncPlayPauseButtons();
    draw();
  }

  function getCanvasCssSize() {
    const rect = canvas.getBoundingClientRect();
    return { w: Math.max(1, rect.width), h: Math.max(1, rect.height) };
  }

  function clampNode(n) {
    const { w, h } = getCanvasCssSize();
    const pad = NODE_R + 16;
    n.x = Math.min(w - pad, Math.max(pad, n.x));
    n.y = Math.min(h - pad, Math.max(pad, n.y));
  }

  function addUndirectedEdge(a, b, weight, bend) {
    if (a === b) return false;
    const wantKey = a < b ? a + ":" + b : b + ":" + a;
    if (edges.some((e) => edgeKey(e) === wantKey)) return false;
    edges.push(
      canonicalizeUndirectedEdge({
        from: a,
        to: b,
        weight,
        bend: bend != null ? bend : undefined,
      })
    );
    return true;
  }

  function edgeKey(e) {
    return e.from < e.to ? e.from + ":" + e.to : e.to + ":" + e.from;
  }

  function canonicalizeUndirectedEdge(e) {
    let from = e.from;
    let to = e.to;
    let bend = e.bend;
    if (from > to) {
      const t = from;
      from = to;
      to = t;
      if (bend != null) bend = -bend;
    }
    if (bend == null) bend = edgeBendSign(from, to);
    return { from, to, weight: e.weight, bend };
  }

  function normalizeAndDedupeEdges() {
    const seen = new Set();
    const out = [];
    for (const e of edges) {
      if (!Number.isFinite(e.from) || !Number.isFinite(e.to) || e.from === e.to) continue;
      const c = canonicalizeUndirectedEdge(e);
      const key = c.from + ":" + c.to;
      if (seen.has(key)) continue;
      seen.add(key);
      out.push(c);
    }
    edges = out;
  }

  function quadBoundingBoxPad(x0, y0, cx, cy, x1, y1, pad) {
    return {
      minX: Math.min(x0, cx, x1) - pad,
      maxX: Math.max(x0, cx, x1) + pad,
      minY: Math.min(y0, cy, y1) - pad,
      maxY: Math.max(y0, cy, y1) + pad,
    };
  }

  function pointInPadBox(px, py, box) {
    return px >= box.minX && px <= box.maxX && py >= box.minY && py <= box.maxY;
  }

  function distanceSqPointToQuadBezier(px, py, x0, y0, cx, cy, x1, y1, budgetSq) {
    const coarse = 20;
    let bestT = 0;
    let bestSq = Infinity;
    for (let i = 0; i <= coarse; i++) {
      const t = i / coarse;
      const p = quadPoint(x0, y0, cx, cy, x1, y1, t);
      const dx = px - p.x;
      const dy = py - p.y;
      const s = dx * dx + dy * dy;
      if (s < bestSq) {
        bestSq = s;
        bestT = t;
      }
    }
    let span = 1 / coarse;
    for (let pass = 0; pass < 4; pass++) {
      const lo = Math.max(0, bestT - span);
      const hi = Math.min(1, bestT + span);
      const range = hi - lo;
      let improved = false;
      const inner = 12;
      for (let j = 0; j <= inner; j++) {
        const t = range <= 0 ? bestT : lo + (j / inner) * range;
        const p = quadPoint(x0, y0, cx, cy, x1, y1, t);
        const dx = px - p.x;
        const dy = py - p.y;
        const s = dx * dx + dy * dy;
        if (s < bestSq) {
          bestSq = s;
          bestT = t;
          improved = true;
        }
      }
      span *= 0.35;
      if (bestSq <= budgetSq * 0.2) break;
      if (!improved && pass > 1) break;
    }
    return bestSq;
  }

  function pickEdgeAt(px, py, maxDist) {
    const maxSq = maxDist * maxDist;
    const nodeBlockSq = EDGE_PICK_NODE_BLOCK * EDGE_PICK_NODE_BLOCK;
    let best = null;
    let bestSq = maxSq;
    const pad = maxDist + 4;
    for (let ei = 0; ei < edges.length; ei++) {
      const e = edges[ei];
      const na = nodeById(e.from);
      const nb = nodeById(e.to);
      if (!na || !nb) continue;
      if (distToNodeSq(px, py, na) < nodeBlockSq || distToNodeSq(px, py, nb) < nodeBlockSq) {
        continue;
      }
      const bend = e.bend != null ? e.bend : edgeBendSign(e.from, e.to);
      const { cx, cy } = getCurveControl(na.x, na.y, nb.x, nb.y, bend);
      const box = quadBoundingBoxPad(na.x, na.y, cx, cy, nb.x, nb.y, pad);
      if (!pointInPadBox(px, py, box)) continue;
      const dSq = distanceSqPointToQuadBezier(
        px,
        py,
        na.x,
        na.y,
        cx,
        cy,
        nb.x,
        nb.y,
        bestSq
      );
      if (dSq < bestSq) {
        bestSq = dSq;
        best = e;
      }
    }
    return best;
  }

  function compactNodeIds() {
    if (nodes.length === 0) {
      nextId = 1;
      edges = [];
      return;
    }
    const idMap = new Map();
    nodes.forEach((n, i) => idMap.set(n.id, i + 1));
    nodes = nodes.map((n, i) => ({
      id: i + 1,
      label: i + 1,
      x: n.x,
      y: n.y,
    }));
    nextId = nodes.length + 1;
    const remapped = [];
    for (const e of edges) {
      const a = idMap.get(e.from);
      const b = idMap.get(e.to);
      if (a == null || b == null || a === b) continue;
      remapped.push({
        from: a,
        to: b,
        weight: e.weight,
        bend: e.bend,
      });
    }
    edges = remapped;
    normalizeAndDedupeEdges();
    if (sourceId != null) {
      const ns = idMap.get(sourceId);
      sourceId = ns === undefined ? null : ns;
    }
    if (destId != null) {
      const nd = idMap.get(destId);
      destId = nd === undefined ? null : nd;
    }
    connectFrom = null;
  }

  function afterGraphMutation() {
    hoveredNodeId = null;
    hoveredEdgeKey = null;
    resetPlaybackOnly();
    blendFromFrame = null;
    blendToFrame = null;
    syncPlayPauseButtons();
    syncCanvasHoverClass();
  }

  function deleteGraphNode(node) {
    const id = node.id;
    edges = edges.filter((e) => e.from !== id && e.to !== id);
    nodes = nodes.filter((n) => n.id !== id);
    if (sourceId === id) sourceId = null;
    if (destId === id) destId = null;
    if (nodes.length > 0) compactNodeIds();
    else {
      nextId = 1;
      edges = [];
      connectFrom = null;
    }
    afterGraphMutation();
    updateStatus();
    beginBlend(virtualIdleState(), virtualIdleState());
    blendStart = performance.now() - BLEND_MS;
  }

  function deleteGraphEdge(edge) {
    const targetKey = edgeKey(edge);
    edges = edges.filter((e) => edgeKey(e) !== targetKey);
    normalizeAndDedupeEdges();
    afterGraphMutation();
    beginBlend(virtualIdleState(), virtualIdleState());
    blendStart = performance.now() - BLEND_MS;
  }

  function resetPlaybackOnly() {
    stopPlayback();
    animationFrames = [];
    frameIndex = 0;
    prePlaybackState = null;
    blendFromFrame = null;
    blendToFrame = null;
    btnStart.disabled = false;
    statusCurrent.textContent = "—";
  }

  function showInstantShortestPath(summaryPrefix) {
    if (sourceId == null || destId == null) {
      setHint("Set source and destination first.", true);
      return;
    }
    if (nodes.length === 0) {
      setHint("No nodes in the graph.", true);
      return;
    }
    resetPlaybackOnly();
    const { frames } = computeDijkstraSteps(sourceId, destId);
    if (frames.length === 0) return;
    animationFrames = frames;
    const lastIdx = frames.length - 1;
    frameIndex = lastIdx;
    playing = false;
    overlay.hidden = true;
    btnStart.disabled = false;
    statusCurrent.textContent = "—";
    const last = frames[lastIdx];
    const prev = lastIdx > 0 ? frames[lastIdx - 1] : virtualIdleState();
    beginBlend(prev, last);
    const note = last.note || "";
    setHint((summaryPrefix ? summaryPrefix + " " : "") + note);
    hoveredNodeId = null;
    syncCanvasHoverClass();
    syncPlayPauseButtons();
    draw();
  }

  function generateRandomGraph(instantPath) {
    if (deleteModeActive) setDeleteMode(false);
    resetPlaybackOnly();
    connectFrom = null;
    const { w, h } = getCanvasCssSize();
    nodes = [];
    edges = [];
    nextId = 1;

    const count = 7 + Math.floor(Math.random() * 5);
    const ids = [];
    for (let i = 0; i < count; i++) {
      const t = (i / count) * Math.PI * 2 + Math.random() * 0.45;
      const r = Math.min(w, h) * (0.17 + Math.random() * 0.11);
      const id = nextId++;
      ids.push(id);
      nodes.push({
        id,
        x: w / 2 + Math.cos(t) * r + (Math.random() - 0.5) * 42,
        y: h / 2 + Math.sin(t) * r + (Math.random() - 0.5) * 42,
        label: i + 1,
      });
    }
    nodes.forEach(clampNode);

    for (let i = 1; i < ids.length; i++) {
      const j = Math.floor(Math.random() * i);
      addUndirectedEdge(
        ids[i],
        ids[j],
        1 + Math.floor(Math.random() * 14),
        Math.random() < 0.5 ? 1 : -1
      );
    }

    let tries = count * 4;
    const seen = new Set();
    while (tries-- > 0) {
      const a = ids[Math.floor(Math.random() * ids.length)];
      const b = ids[Math.floor(Math.random() * ids.length)];
      if (a === b) continue;
      const key = a < b ? a + ":" + b : b + ":" + a;
      if (seen.has(key)) continue;
      seen.add(key);
      addUndirectedEdge(a, b, 1 + Math.floor(Math.random() * 18), Math.random() < 0.5 ? 1 : -1);
    }

    sourceId = ids[0];
    destId = ids[ids.length - 1];
    updateStatus();

    if (instantPath) {
      showInstantShortestPath(
        "Random graph (" +
          count +
          " nodes, " +
          edges.length +
          " edges). Source " +
          labelFor(sourceId) +
          ", destination " +
          labelFor(destId) +
          "."
      );
    } else {
      setHint(
        "Random graph: " +
          count +
          " nodes, " +
          edges.length +
          " edges. Source " +
          labelFor(sourceId) +
          ", destination " +
          labelFor(destId) +
          ". Press Start for a stepped run with delays and transitions."
      );
      blendFromFrame = null;
      blendToFrame = null;
      syncPlayPauseButtons();
    }
    draw();
  }

  function handleNodeClick(hit) {
    if (mode === "connect") {
      if (connectFrom == null) {
        connectFrom = hit.id;
        setHint("Select second node for " + labelFor(hit.id) + ".");
        draw();
        return;
      }
      if (connectFrom === hit.id) {
        connectFrom = null;
        setHint("Connection cancelled.");
        draw();
        return;
      }
      edgeFromLabel.textContent = labelFor(connectFrom);
      edgeToLabel.textContent = labelFor(hit.id);
      weightInput.value = "1";
      weightDialog.dataset.from = String(connectFrom);
      weightDialog.dataset.to = String(hit.id);
      weightDialog.showModal();
      connectFrom = null;
      return;
    }
    if (mode === "source") {
      sourceId = hit.id;
      updateStatus();
      setHint("Source set to " + labelFor(hit.id) + ".");
      draw();
      return;
    }
    if (mode === "dest") {
      destId = hit.id;
      updateStatus();
      setHint("Destination set to " + labelFor(hit.id) + ".");
      draw();
    }
  }

  function edgeOnPath(a, b, pathSet) {
    if (!pathSet || pathSet.size === 0) return false;
    return pathSet.has(a) && pathSet.has(b);
  }

  function edgeBendSign(fromId, toId) {
    return (fromId + toId) % 2 === 0 ? 1 : -1;
  }

  function getCurveControl(x1, y1, x2, y2, bend) {
    const mx = (x1 + x2) / 2;
    const my = (y1 + y2) / 2;
    const dx = x2 - x1;
    const dy = y2 - y1;
    const len = Math.hypot(dx, dy) || 1;
    const nx = -dy / len;
    const ny = dx / len;
    const offset = Math.min(len * 0.24, 64) * bend;
    return { cx: mx + nx * offset, cy: my + ny * offset };
  }

  function quadPoint(x1, y1, cx, cy, x2, y2, t) {
    const mt = 1 - t;
    const x = mt * mt * x1 + 2 * mt * t * cx + t * t * x2;
    const y = mt * mt * y1 + 2 * mt * t * cy + t * t * y2;
    return { x, y };
  }

  function quadTangentAngle(x1, y1, cx, cy, x2, y2, t) {
    const mt = 1 - t;
    const dx = 2 * mt * (cx - x1) + 2 * t * (x2 - cx);
    const dy = 2 * mt * (cy - y1) + 2 * t * (y2 - cy);
    return Math.atan2(dy, dx);
  }

  function drawEdgeGlowCurve(x1, y1, cx, cy, x2, y2) {
    ctx.save();
    ctx.strokeStyle = "rgba(61, 139, 253, 0.22)";
    ctx.lineWidth = 16;
    ctx.lineCap = "round";
    ctx.lineJoin = "round";
    ctx.beginPath();
    ctx.moveTo(x1, y1);
    ctx.quadraticCurveTo(cx, cy, x2, y2);
    ctx.stroke();
    ctx.restore();
  }

  function drawEdgeStrokeCurve(
    x1,
    y1,
    cx,
    cy,
    x2,
    y2,
    pathStrength,
    incidentHover,
    deleteHover
  ) {
    const baseRgb = { r: 139, g: 156, b: 179 };
    const pathRgb = hexToRgb(COLORS.path);
    const delRgb = { r: 248, g: 113, b: 113 };
    let rgb;
    let alpha;
    if (deleteHover) {
      rgb = lerpRgb(baseRgb, delRgb, 0.75);
      alpha = 0.95;
    } else {
      rgb = lerpRgb(baseRgb, pathRgb, pathStrength);
      alpha = lerp(0.5, 0.96, pathStrength);
    }
    let lw = deleteHover ? 4.2 : lerp(2.2, 4, pathStrength);
    if (incidentHover && !deleteHover) lw += 1;
    if (deleteHover) lw += 0.5;
    ctx.save();
    ctx.strokeStyle = "rgba(" + rgb.r + "," + rgb.g + "," + rgb.b + "," + alpha + ")";
    ctx.lineWidth = lw;
    ctx.lineCap = "round";
    ctx.lineJoin = "round";
    ctx.beginPath();
    ctx.moveTo(x1, y1);
    ctx.quadraticCurveTo(cx, cy, x2, y2);
    ctx.stroke();
    ctx.restore();
  }

  function drawEdge(x1, y1, x2, y2, w, pathStrength, incidentHover, bend, deleteHover) {
    const { cx, cy } = getCurveControl(x1, y1, x2, y2, bend);
    if (deleteHover) {
      ctx.save();
      ctx.strokeStyle = "rgba(248, 113, 113, 0.35)";
      ctx.lineWidth = 18;
      ctx.lineCap = "round";
      ctx.beginPath();
      ctx.moveTo(x1, y1);
      ctx.quadraticCurveTo(cx, cy, x2, y2);
      ctx.stroke();
      ctx.restore();
    } else if (incidentHover && pathStrength < 0.55) {
      drawEdgeGlowCurve(x1, y1, cx, cy, x2, y2);
    }
    drawEdgeStrokeCurve(x1, y1, cx, cy, x2, y2, pathStrength, incidentHover, deleteHover);

    const mid = quadPoint(x1, y1, cx, cy, x2, y2, 0.5);
    const ang = quadTangentAngle(x1, y1, cx, cy, x2, y2, 0.5);
    ctx.save();
    ctx.translate(mid.x, mid.y);
    ctx.rotate(ang);
    const padX = 22;
    const padY = 12;
    const text = String(w);
    ctx.font = "600 13px JetBrains Mono, monospace";
    const tw = ctx.measureText(text).width;
    const rx = -tw / 2 - padX / 2;
    const ry = -padY / 2;
    const rw = tw + padX;
    const rh = padY;
    ctx.fillStyle = COLORS.distBg;
    fillRoundRect(ctx, rx, ry, rw, rh, 5);
    const chipRgb = lerpRgb(hexToRgb("#1e2630"), hexToRgb(COLORS.path), pathStrength);
    ctx.strokeStyle =
      "rgba(" +
      chipRgb.r +
      "," +
      chipRgb.g +
      "," +
      chipRgb.b +
      "," +
      lerp(0.35, 0.65, pathStrength) +
      ")";
    ctx.lineWidth = 1.25;
    strokeRoundRect(ctx, rx, ry, rw, rh, 5);
    const wtRgb = lerpRgb(hexToRgb(COLORS.weightText), hexToRgb(COLORS.path), pathStrength);
    ctx.fillStyle = "rgb(" + wtRgb.r + "," + wtRgb.g + "," + wtRgb.b + ")";
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.fillText(text, 0, 0);
    ctx.restore();
  }

  function drawSoftGlow(x, y, r, rgb, strength) {
    const peak = 0.52 * strength;
    const outer = r * 2.45;
    const grd = ctx.createRadialGradient(x, y, r * 0.12, x, y, outer);
    grd.addColorStop(0, "rgba(" + rgb.r + "," + rgb.g + "," + rgb.b + "," + peak + ")");
    grd.addColorStop(0.5, "rgba(" + rgb.r + "," + rgb.g + "," + rgb.b + "," + peak * 0.38 + ")");
    grd.addColorStop(1, "rgba(" + rgb.r + "," + rgb.g + "," + rgb.b + ",0)");
    ctx.fillStyle = grd;
    ctx.beginPath();
    ctx.arc(x, y, outer, 0, Math.PI * 2);
    ctx.fill();
  }

  function drawNode(n, logicState, fromF, toF, te, pulseT, isHighlighted, uiInteraction, deleteTargetHover) {
    const { x, y, label } = n;
    const fill = getNodeFillColor(fromF, toF, n.id, te);
    const fillRgb = parseFillColor(fill);

    let r = NODE_R;
    if (logicState.current === n.id && pulseT != null) {
      const pulse = 1 + 0.1 * Math.sin(pulseT * 0.0055);
      r = NODE_R * PULSE_BASE * pulse;
    }
    if (isHighlighted && uiInteraction) {
      r *= 1.08;
    }

    let glowStrength = 0.4;
    if (logicState.current === n.id) glowStrength = 1;
    else if (logicState.path && logicState.path.has(n.id)) glowStrength = 0.92;
    else if (logicState.settled && logicState.settled.has(n.id)) glowStrength = 0.58;
    if (isHighlighted && uiInteraction) glowStrength = Math.min(1, glowStrength + 0.32);

    ctx.save();
    drawSoftGlow(x, y, r, fillRgb, glowStrength);

    if (logicState.current === n.id) {
      const g = ctx.createRadialGradient(x, y, r * 0.15, x, y, r * 2.35);
      g.addColorStop(0, "rgba(230, 197, 71, 0.42)");
      g.addColorStop(1, "rgba(230, 197, 71, 0)");
      ctx.fillStyle = g;
      ctx.beginPath();
      ctx.arc(x, y, r * 2.35, 0, Math.PI * 2);
      ctx.fill();
    }

    if (isHighlighted && uiInteraction) {
      const hg = ctx.createRadialGradient(x, y, r * 0.2, x, y, r * 2.75);
      hg.addColorStop(0, "rgba(61, 139, 253, 0.35)");
      hg.addColorStop(1, "rgba(61, 139, 253, 0)");
      ctx.fillStyle = hg;
      ctx.beginPath();
      ctx.arc(x, y, r * 2.75, 0, Math.PI * 2);
      ctx.fill();
    }

    if (deleteTargetHover) {
      ctx.strokeStyle = "rgba(248, 113, 113, 0.95)";
      ctx.lineWidth = 3;
      ctx.beginPath();
      ctx.arc(x, y, r + 5, 0, Math.PI * 2);
      ctx.stroke();
    }

    ctx.beginPath();
    ctx.arc(x, y, r, 0, Math.PI * 2);
    ctx.fillStyle = fill;
    ctx.fill();
    ctx.strokeStyle = isHighlighted && uiInteraction ? "rgba(255,255,255,0.35)" : COLORS.ring;
    ctx.lineWidth = isHighlighted && uiInteraction ? 2.75 : 2;
    ctx.stroke();

    const hiRgb = lerpRgb(fillRgb, { r: 255, g: 255, b: 255 }, 0.22);
    ctx.strokeStyle = "rgba(" + hiRgb.r + "," + hiRgb.g + "," + hiRgb.b + ",0.35)";
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.arc(x, y, r - 1.5, 0, Math.PI * 2);
    ctx.stroke();

    if (n.id === sourceId) {
      ctx.strokeStyle = COLORS.sourceRing;
      ctx.shadowColor = "rgba(61, 139, 253, 0.55)";
      ctx.shadowBlur = 12;
      ctx.lineWidth = 3;
      ctx.beginPath();
      ctx.arc(x, y, r + 5, 0, Math.PI * 2);
      ctx.stroke();
      ctx.shadowBlur = 0;
    }
    if (n.id === destId) {
      ctx.strokeStyle = COLORS.path;
      ctx.shadowColor = "rgba(62, 207, 142, 0.45)";
      ctx.shadowBlur = 10;
      ctx.lineWidth = 2;
      ctx.setLineDash([4, 4]);
      ctx.beginPath();
      ctx.arc(x, y, r + 9, 0, Math.PI * 2);
      ctx.stroke();
      ctx.setLineDash([]);
      ctx.shadowBlur = 0;
    }
    if (mode === "connect" && connectFrom === n.id && uiInteraction) {
      ctx.strokeStyle = "rgba(230, 197, 71, 0.85)";
      ctx.lineWidth = 2;
      ctx.setLineDash([6, 4]);
      ctx.beginPath();
      ctx.arc(x, y, r + 12, 0, Math.PI * 2);
      ctx.stroke();
      ctx.setLineDash([]);
    }

    ctx.fillStyle = COLORS.label;
    ctx.font = "600 14px DM Sans, system-ui, sans-serif";
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.shadowColor = "rgba(0,0,0,0.45)";
    ctx.shadowBlur = 4;
    ctx.fillText(String(label), x, y);
    ctx.shadowBlur = 0;

    const dDisp = getDisplayDist(fromF, toF, n.id, te);
    let distStr = "∞";
    if (dDisp != null && Number.isFinite(dDisp)) distStr = String(dDisp);

    ctx.font = "500 11px JetBrains Mono, monospace";
    const dw = ctx.measureText(distStr).width;
    const bx = x - dw / 2 - 6;
    const by = y + r + 6;
    ctx.fillStyle = COLORS.distBg;
    fillRoundRect(ctx, bx, by, dw + 12, 18, 5);
    ctx.strokeStyle =
      isHighlighted && uiInteraction ? "rgba(61,139,253,0.45)" : "rgba(255,255,255,0.1)";
    ctx.lineWidth = 1;
    strokeRoundRect(ctx, bx, by, dw + 12, 18, 5);
    ctx.fillStyle = COLORS.distText;
    ctx.textBaseline = "middle";
    ctx.fillText(distStr, x, by + 9);

    ctx.restore();
  }

  function currentFrameState() {
    if (animationFrames.length && frameIndex < animationFrames.length) {
      return animationFrames[frameIndex];
    }
    const dist = new Map();
    const INF = Infinity;
    for (const n of nodes) dist.set(n.id, INF);
    if (sourceId != null) dist.set(sourceId, 0);
    return {
      dist,
      settled: new Set(),
      current: null,
      path: null,
    };
  }

  function draw() {
    const rect = canvas.getBoundingClientRect();
    const w = rect.width;
    const h = rect.height;
    ctx.save();
    ctx.clearRect(0, 0, w, h);

    const gridStep = 32;
    ctx.strokeStyle = "rgba(255,255,255,0.032)";
    ctx.lineWidth = 1;
    for (let gx = 0; gx < w; gx += gridStep) {
      ctx.beginPath();
      ctx.moveTo(gx, 0);
      ctx.lineTo(gx, h);
      ctx.stroke();
    }
    for (let gy = 0; gy < h; gy += gridStep) {
      ctx.beginPath();
      ctx.moveTo(0, gy);
      ctx.lineTo(w, gy);
      ctx.stroke();
    }

    const now = performance.now();
    const logicState = currentFrameState();
    const bc = getBlendContext(now);
    const fromF = bc.from || logicState;
    const toF = bc.to || logicState;
    const te = bc.from ? bc.te : 1;
    const animAdvancing = playing && !animPaused;
    const pulseT = logicState.current != null && animAdvancing ? now : null;
    const allowHover = (!playing || animPaused) && overlay.hidden;
    const draggingId =
      pointerSession && pointerSession.dragging && pointerSession.hit
        ? pointerSession.hit.id
        : null;
    const uiInteraction = !playing || animPaused;

    const deleteUi = deleteModeActive && allowHover;

    for (const e of edges) {
      const na = nodeById(e.from);
      const nb = nodeById(e.to);
      if (!na || !nb) continue;
      const pathStrength = edgePathStrength(fromF, toF, e.from, e.to, te);
      const incident =
        allowHover &&
        hoveredNodeId != null &&
        (e.from === hoveredNodeId || e.to === hoveredNodeId);
      const bend = e.bend != null ? e.bend : edgeBendSign(e.from, e.to);
      const edgeDelHover = deleteUi && hoveredNodeId == null && hoveredEdgeKey === edgeKey(e);
      drawEdge(
        na.x,
        na.y,
        nb.x,
        nb.y,
        e.weight,
        pathStrength,
        incident && !edgeDelHover,
        bend,
        edgeDelHover
      );
    }

    for (const n of nodes) {
      const isHighlighted =
        (allowHover && hoveredNodeId === n.id) || draggingId === n.id;
      const deleteTargetHover = deleteUi && hoveredNodeId === n.id;
      drawNode(
        n,
        logicState,
        fromF,
        toF,
        te,
        logicState.current === n.id ? pulseT : null,
        isHighlighted,
        uiInteraction,
        deleteTargetHover
      );
    }

    ctx.restore();
  }

  function loop() {
    draw();
    requestAnimationFrame(loop);
  }

  canvas.addEventListener("pointermove", (ev) => {
    const { x, y } = canvasCoords(ev);
    if (pointerSession && pointerSession.hit && pointerSession.dragArmed) {
      if (!pointerSession.dragging) {
        pointerSession.dragging = true;
        canvasWrap.classList.add("is-dragging");
      }
      pointerSession.hit.x = x - pointerSession.offX;
      pointerSession.hit.y = y - pointerSession.offY;
      clampNode(pointerSession.hit);
      return;
    }
    const canHover = (!playing || animPaused) && overlay.hidden;
    if (canHover && (!pointerSession || !pointerSession.dragging)) {
      if (deleteModeActive) {
        const hn = hitNodeHover(x, y);
        const nid = hn ? hn.id : null;
        let ek = null;
        if (!hn) {
          const pe = pickEdgeAt(x, y, EDGE_HIT_PX + 6);
          ek = pe ? edgeKey(pe) : null;
        }
        if (nid !== hoveredNodeId || ek !== hoveredEdgeKey) {
          hoveredNodeId = nid;
          hoveredEdgeKey = ek;
          syncCanvasHoverClass();
        }
      } else {
        const hit = hitNodeHover(x, y);
        const id = hit ? hit.id : null;
        if (id !== hoveredNodeId || hoveredEdgeKey != null) {
          hoveredNodeId = id;
          hoveredEdgeKey = null;
          syncCanvasHoverClass();
        }
      }
    }
  });

  canvas.addEventListener("pointerleave", () => {
    if (pointerSession && pointerSession.dragging) return;
    if (hoveredNodeId != null || hoveredEdgeKey != null) {
      hoveredNodeId = null;
      hoveredEdgeKey = null;
      syncCanvasHoverClass();
    }
  });

  function finishPointerClick(ev) {
    if (!pointerSession) return;
    if (pointerSession.deleteMode) {
      const { x, y } = canvasCoords(ev);
      const nHit = hitNode(x, y);
      if (nHit) {
        deleteGraphNode(nHit);
      } else {
        const ee = pickEdgeAt(x, y, EDGE_HIT_PX);
        if (ee) deleteGraphEdge(ee);
      }
      try {
        canvas.releasePointerCapture(ev.pointerId);
      } catch (_) {}
      pointerSession = null;
      draw();
      return;
    }
    clearPointerHoldTimer(pointerSession);
    const { hit, dragging, emptyAdd, addX, addY } = pointerSession;
    if (dragging) {
      try {
        canvas.releasePointerCapture(ev.pointerId);
      } catch (_) {}
      canvasWrap.classList.remove("is-dragging");
      pointerSession = null;
      return;
    }
    try {
      canvas.releasePointerCapture(ev.pointerId);
    } catch (_) {}
    if (hit) {
      if (mode !== "add") {
        handleNodeClick(hit);
      }
    } else if (emptyAdd && mode === "add") {
      nodes.push({
        id: nextId++,
        x: addX,
        y: addY,
        label: nodes.length + 1,
      });
      clampNode(nodes[nodes.length - 1]);
      setHint("Node added. Drag to move. Use Connect to add edges.");
      draw();
    } else if (!hit && mode !== "add") {
      setHint("Click a node.", true);
    }
    pointerSession = null;
  }

  canvas.addEventListener("pointerdown", (ev) => {
    if (playing && !animPaused) return;
    const { x, y } = canvasCoords(ev);
    if (deleteModeActive) {
      pointerSession = {
        pointerId: ev.pointerId,
        deleteMode: true,
      };
      try {
        canvas.setPointerCapture(ev.pointerId);
      } catch (_) {}
      return;
    }
    const hit = hitNode(x, y);
    const ps = {
      pointerId: ev.pointerId,
      startX: x,
      startY: y,
      hit: hit,
      offX: hit ? x - hit.x : 0,
      offY: hit ? y - hit.y : 0,
      dragging: false,
      dragArmed: false,
      holdTimerId: null,
      emptyAdd: !hit,
      addX: x,
      addY: y,
    };
    pointerSession = ps;
    if (hit) {
      ps.holdTimerId = setTimeout(() => {
        if (pointerSession === ps && pointerSession.hit === hit) {
          pointerSession.dragArmed = true;
        }
      }, HOLD_TO_DRAG_MS);
    }
    try {
      canvas.setPointerCapture(ev.pointerId);
    } catch (_) {}
  });

  canvas.addEventListener("pointerup", (ev) => {
    finishPointerClick(ev);
  });

  canvas.addEventListener("pointercancel", (ev) => {
    if (pointerSession) clearPointerHoldTimer(pointerSession);
    if (pointerSession && pointerSession.dragging) {
      canvasWrap.classList.remove("is-dragging");
    }
    try {
      canvas.releasePointerCapture(ev.pointerId);
    } catch (_) {}
    pointerSession = null;
  });

  canvas.addEventListener("contextmenu", (ev) => {
    if (deleteModeActive) ev.preventDefault();
  });

  weightCancel.addEventListener("click", () => weightDialog.close());

  weightForm.addEventListener("submit", (ev) => {
    ev.preventDefault();
    const from = parseInt(weightDialog.dataset.from, 10);
    const to = parseInt(weightDialog.dataset.to, 10);
    const w = Math.max(1, parseInt(weightInput.value, 10) || 1);
    const wantKey = from < to ? from + ":" + to : to + ":" + from;
    const exists = edges.some((e) => edgeKey(e) === wantKey);
    if (!exists) {
      edges.push(
        canonicalizeUndirectedEdge({ from, to, weight: w, bend: undefined })
      );
      afterGraphMutation();
      beginBlend(virtualIdleState(), virtualIdleState());
      blendStart = performance.now() - BLEND_MS;
    } else setHint("Edge already exists between these nodes.", true);
    weightDialog.close();
    if (!exists) setHint("Edge added (weight " + w + ").");
    draw();
  });

  document.querySelectorAll(".btn-mode").forEach((b) => {
    b.addEventListener("click", () => setMode(b.dataset.mode));
  });

  if (btnDeleteMode) {
    btnDeleteMode.addEventListener("click", () => setDeleteMode(!deleteModeActive));
  }

  btnStart.addEventListener("click", () => startAnimation());

  if (btnPause) btnPause.addEventListener("click", () => pauseAnimation());
  if (btnResume) btnResume.addEventListener("click", () => resumeAnimation());

  btnReset.addEventListener("click", () => resetVisualization());

  btnClear.addEventListener("click", () => {
    if (nodes.length === 0) return;
    resetAll();
  });

  btnRandom.addEventListener("click", () => generateRandomGraph(false));

  btnRandomInstant.addEventListener("click", () => generateRandomGraph(true));

  speedInput.addEventListener("input", () => {
    const v = parseFloat(speedInput.value, 10);
    speedValue.textContent = v + "×";
  });

  window.addEventListener("resize", resizeCanvas);

  resizeCanvas();
  updateStatus();
  updateModeIndicator();
  syncPlayPauseButtons();
  requestAnimationFrame(loop);
})();
