import { readdirSync, statSync, readFileSync, mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR || '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR || '/output';

const GLOBAL_BUDGET = 12000000;
const ROOM_BFS_CAP = 2000000;
const WHOLE_BFS_CAP = 6000000;
const ASTAR_CAP = 4000000;
const GREEDY_CAP = 4000000;
const BUDGET_GREEDY_CAP = 200000;
const INF = 1000000000;

let globalStatesCreated = 0;

const permCache = new Map();

function getPermutations(n) {
  if (permCache.has(n)) return permCache.get(n);
  const res = [];
  const cur = [];
  const used = new Array(n).fill(false);

  function rec() {
    if (cur.length === n) {
      res.push(cur.slice());
      return;
    }
    for (let i = 0; i < n; i++) {
      if (!used[i]) {
        used[i] = true;
        cur.push(i);
        rec();
        cur.pop();
        used[i] = false;
      }
    }
  }

  rec();
  permCache.set(n, res);
  return res;
}

function parseLevel(text) {
  let lines = text.split(/\r\n|\r|\n/);
  while (lines.length && lines[lines.length - 1] === '') lines.pop();
  if (lines.length === 0) throw new Error('empty level');

  let rawH = lines.length;
  let rawW = 0;
  for (const line of lines) {
    if (line.length > rawW) rawW = line.length;
  }
  if (rawW === 0) throw new Error('empty level');

  const W = rawW + 2;
  const H = rawH + 2;
  const N = W * H;

  const wall = new Uint8Array(N).fill(1);
  const goals = [];
  const boxes = [];
  let player = -1;

  for (let y = 0; y < rawH; y++) {
    const line = lines[y];
    for (let x = 0; x < rawW; x++) {
      // The outermost frame of the parsed rectangle counts as wall.
      if (y === 0 || x === 0 || y === rawH - 1 || x === rawW - 1) continue;
      // Squares outside this row's length count as wall.
      if (x >= line.length) continue;

      const ch = line[x];
      if (ch === '#') continue;

      const idx = (y + 1) * W + (x + 1);
      wall[idx] = 0;

      if (ch === '.' || ch === '*' || ch === '+') goals.push(idx);
      if (ch === '$' || ch === '*') boxes.push(idx);
      if (ch === '@' || ch === '+') player = idx;
    }
  }

  goals.sort((a, b) => a - b);
  boxes.sort((a, b) => a - b);

  if (player < 0) throw new Error('no player');

  return { W, H, N, wall, goals, boxes, player };
}

function solveLevel(text) {
  const level = parseLevel(text);
  const width = level.W;
  const height = level.H;
  const N = level.N;
  const levelWall = level.wall;
  const allGoals = level.goals;
  const allBoxes = level.boxes;
  const startPlayer = level.player;

  const DIR_CHARS = ['u', 'd', 'l', 'r'];
  const PUSH_CHARS = ['U', 'D', 'L', 'R'];
  const dx = [0, 0, -1, 1];
  const dy = [-1, 1, 0, 0];

  const neigh = new Int32Array(N * 4).fill(-1);
  const pushStand = new Int32Array(N * 4).fill(-1);
  const pushTarget = new Int32Array(N * 4).fill(-1);
  const revCand = new Int32Array(N * 4).fill(-1);
  const revStand = new Int32Array(N * 4).fill(-1);

  for (let sq = 0; sq < N; sq++) {
    const x = sq % width;
    const y = (sq - x) / width;
    const base = sq * 4;

    for (let d = 0; d < 4; d++) {
      let nx = x + dx[d];
      let ny = y + dy[d];
      if (nx >= 0 && nx < width && ny >= 0 && ny < height) {
        neigh[base + d] = ny * width + nx;
      }

      nx = x - dx[d];
      ny = y - dy[d];
      if (nx >= 0 && nx < width && ny >= 0 && ny < height) {
        pushStand[base + d] = ny * width + nx;
      }

      nx = x + dx[d];
      ny = y + dy[d];
      if (nx >= 0 && nx < width && ny >= 0 && ny < height) {
        pushTarget[base + d] = ny * width + nx;
      }

      const cx = x - dx[d];
      const cy = y - dy[d];
      const sx = x - 2 * dx[d];
      const sy = y - 2 * dy[d];
      if (cx >= 0 && cx < width && cy >= 0 && cy < height) {
        revCand[base + d] = cy * width + cx;
        if (sx >= 0 && sx < width && sy >= 0 && sy < height) {
          revStand[base + d] = sy * width + sx;
        }
      }
    }
  }

  const seenWork = new Int32Array(N);
  const seenRegion = new Int32Array(N);
  const boxMark = new Int32Array(N);
  let workStamp = 0;
  let regionStamp = 0;
  let boxStamp = 0;

  function nextWorkStamp() {
    workStamp++;
    if (workStamp === 0x7fffffff) {
      seenWork.fill(0);
      workStamp = 1;
    }
    return workStamp;
  }

  function nextRegionStamp() {
    regionStamp++;
    if (regionStamp === 0x7fffffff) {
      seenRegion.fill(0);
      regionStamp = 1;
    }
    return regionStamp;
  }

  function nextBoxStamp() {
    boxStamp++;
    if (boxStamp === 0x7fffffff) {
      boxMark.fill(0);
      boxStamp = 1;
    }
    return boxStamp;
  }

  const floodQ = new Int32Array(N);
  const pathPrev = new Int32Array(N);
  const pathDir = new Int8Array(N);

  function floodRegion(start, baseBoxStamp, movedFrom, movedTo, seenArr, stamp, walls) {
    if (start < 0 || start >= N || walls[start]) return -1;
    if (start === movedTo) return -1;
    if (start !== movedFrom && boxMark[start] === baseBoxStamp) return -1;

    let head = 0;
    let tail = 0;
    floodQ[tail++] = start;
    seenArr[start] = stamp;
    let low = start;

    while (head < tail) {
      const sq = floodQ[head++];
      if (sq < low) low = sq;
      const base = sq * 4;

      for (let d = 0; d < 4; d++) {
        const nb = neigh[base + d];
        if (nb < 0) continue;
        if (walls[nb]) continue;
        if (nb === movedTo) continue;
        if (nb !== movedFrom && boxMark[nb] === baseBoxStamp) continue;
        if (seenArr[nb] === stamp) continue;

        seenArr[nb] = stamp;
        floodQ[tail++] = nb;
      }
    }

    return low;
  }

  function computeLiveOnly(walls, goals) {
    const live = new Uint8Array(N);
    let head = 0;
    let tail = 0;

    for (const g of goals) {
      if (!walls[g] && !live[g]) {
        live[g] = 1;
        floodQ[tail++] = g;
      }
    }

    while (head < tail) {
      const sq = floodQ[head++];
      const base = sq * 4;

      for (let d = 0; d < 4; d++) {
        const cand = revCand[base + d];
        if (cand < 0) continue;
        if (walls[cand]) continue;

        const stand = revStand[base + d];
        if (stand < 0 || walls[stand]) continue;

        if (!live[cand]) {
          live[cand] = 1;
          floodQ[tail++] = cand;
        }
      }
    }

    return live;
  }

  function computeDists(walls, goals) {
    const live = new Uint8Array(N);
    const dists = [];

    for (const g of goals) {
      const dist = new Int32Array(N).fill(INF);
      let head = 0;
      let tail = 0;

      if (!walls[g]) {
        dist[g] = 0;
        live[g] = 1;
        floodQ[tail++] = g;
      }

      while (head < tail) {
        const sq = floodQ[head++];
        const base = sq * 4;
        const nd = dist[sq] + 1;

        for (let d = 0; d < 4; d++) {
          const cand = revCand[base + d];
          if (cand < 0) continue;
          if (walls[cand]) continue;

          const stand = revStand[base + d];
          if (stand < 0 || walls[stand]) continue;

          if (dist[cand] === INF) {
            dist[cand] = nd;
            live[cand] = 1;
            floodQ[tail++] = cand;
          }
        }
      }

      dists.push(dist);
    }

    return { live, dists };
  }

  // Already solved?
  {
    const isGoalInit = new Uint8Array(N);
    for (const g of allGoals) isGoalInit[g] = 1;
    if (allBoxes.length === allGoals.length) {
      let solved = true;
      for (const b of allBoxes) {
        if (!isGoalInit[b]) {
          solved = false;
          break;
        }
      }
      if (solved) return '';
    }
  }

  const isBoxLevel = new Uint8Array(N);
  const isGoalLevel = new Uint8Array(N);
  for (const b of allBoxes) isBoxLevel[b] = 1;
  for (const g of allGoals) isGoalLevel[g] = 1;

  function decompose() {
    const globalLive = computeLiveOnly(levelWall, allGoals);
    const cut = new Uint8Array(N);
    const playerRow = (startPlayer / width) | 0;
    const rowBase = playerRow * width;

    for (let x = 0; x < width; x++) {
      const idx = rowBase + x;
      if (!levelWall[idx] && !globalLive[idx]) cut[idx] = 1;
    }

    for (const b of allBoxes) {
      if (cut[b] || levelWall[b]) return null;
    }
    for (const g of allGoals) {
      if (cut[g] || levelWall[g]) return null;
    }

    const rooms = [];
    const stamp = nextWorkStamp();

    for (let start = 0; start < N; start++) {
      if (levelWall[start] || cut[start]) continue;
      if (seenWork[start] === stamp) continue;

      const compBoxes = [];
      const compGoals = [];

      let head = 0;
      let tail = 0;
      floodQ[tail++] = start;
      seenWork[start] = stamp;

      while (head < tail) {
        const sq = floodQ[head++];

        if (isBoxLevel[sq]) compBoxes.push(sq);
        if (isGoalLevel[sq]) compGoals.push(sq);

        const base = sq * 4;
        for (let d = 0; d < 4; d++) {
          const nb = neigh[base + d];
          if (nb < 0) continue;
          if (levelWall[nb] || cut[nb]) continue;
          if (seenWork[nb] === stamp) continue;

          seenWork[nb] = stamp;
          floodQ[tail++] = nb;
        }
      }

      if (compBoxes.length > 0) {
        if (compBoxes.length !== compGoals.length) return null;
        compBoxes.sort((a, b) => a - b);
        compGoals.sort((a, b) => a - b);
        rooms.push({ boxes: compBoxes, goals: compGoals });
      } else if (compGoals.length > 0) {
        return null;
      }
    }

    return rooms;
  }

  function applyMoves(p, moves) {
    for (let i = 0; i < moves.length; i++) {
      const c = moves[i];
      if (c === 'u' || c === 'U') p -= width;
      else if (c === 'd' || c === 'D') p += width;
      else if (c === 'l' || c === 'L') p -= 1;
      else if (c === 'r' || c === 'R') p += 1;
    }
    return p;
  }

  function runSearch(walls, goalArr, boxArr, playerStart, mode, cap) {
    const startBoxes = boxArr.slice();
    startBoxes.sort((a, b) => a - b);

    const bLen = startBoxes.length;
    const gLen = goalArr.length;

    if (bLen !== gLen) return { sol: null, hitCap: false };
    if (bLen === 0) return { sol: '', hitCap: false };

    const isGoal = new Uint8Array(N);
    for (const g of goalArr) {
      if (walls[g]) return { sol: null, hitCap: false };
      isGoal[g] = 1;
    }

    for (const b of startBoxes) {
      if (walls[b]) return { sol: null, hitCap: false };
    }

    let solved = true;
    for (const b of startBoxes) {
      if (!isGoal[b]) {
        solved = false;
        break;
      }
    }
    if (solved) return { sol: '', hitCap: false };

    let live;
    let dists = null;
    let perms = null;

    if (mode === 'bfs') {
      live = computeLiveOnly(walls, goalArr);
    } else {
      const cd = computeDists(walls, goalArr);
      live = cd.live;
      dists = cd.dists;
      if (bLen <= 8 && bLen === gLen) perms = getPermutations(bLen);
    }

    for (const b of startBoxes) {
      if (!live[b]) return { sol: null, hitCap: false };
    }

    const keyCodes = new Array(bLen + 1);

    function makeKey(low, arr) {
      keyCodes[0] = low;
      for (let i = 0; i < bLen; i++) keyCodes[i + 1] = arr[i];
      return String.fromCharCode.apply(null, keyCodes);
    }

    function heuristicTemp(temp) {
      if (bLen === 0) return 0;

      if (perms) {
        let best = INF;
        for (const perm of perms) {
          let sum = 0;
          for (let i = 0; i < bLen; i++) {
            const d = dists[perm[i]][temp[i]];
            if (d >= INF) {
              sum = INF;
              break;
            }
            sum += d;
            if (sum >= best) break;
          }
          if (sum < best) best = sum;
        }
        return best;
      }

      let sum = 0;
      for (let i = 0; i < bLen; i++) {
        let mn = INF;
        for (let j = 0; j < gLen; j++) {
          const d = dists[j][temp[i]];
          if (d < mn) mn = d;
        }
        if (mn >= INF) return INF;
        sum += mn;
        if (sum >= INF) return INF;
      }
      return sum;
    }

    let initH = 0;
    if (mode !== 'bfs') {
      initH = heuristicTemp(startBoxes);
      if (initH >= INF) return { sol: null, hitCap: false };
    }

    const initStamp = nextBoxStamp();
    for (const b of startBoxes) boxMark[b] = initStamp;

    const initLow = floodRegion(
      playerStart,
      initStamp,
      -1,
      -1,
      seenWork,
      nextWorkStamp(),
      walls
    );
    if (initLow < 0) return { sol: null, hitCap: false };

    const initKey = makeKey(initLow, startBoxes);

    let maxEntries;
    if (mode === 'bfs') {
      maxEntries = cap;
    } else {
      if (mode === 'astar') maxEntries = cap * 2 + 1000;
      else maxEntries = cap * 3 + 1000;
      if (bLen > 8) maxEntries = Math.min(maxEntries, 1500000);
      maxEntries = Math.min(maxEntries, 6000000);
    }
    maxEntries = Math.max(1, Math.floor(maxEntries));

    let capacity = Math.min(16, maxEntries);

    let playerSq = new Uint16Array(capacity);
    let parent = new Int32Array(capacity);
    let moveFrom = new Uint16Array(capacity);
    let moveDir = new Uint8Array(capacity);

    let gArr = null;
    let hArr = null;
    let heapPosArr = null;

    if (mode !== 'bfs') {
      hArr = new Int32Array(capacity);
      if (mode === 'astar') {
        gArr = new Int32Array(capacity);
        heapPosArr = new Int32Array(capacity).fill(-1);
      }
    }

    const stateKeys = [];
    let stateCount = 0;

    function ensureStates(n) {
      if (n <= capacity) return true;
      if (n > maxEntries) return false;

      let newCap = capacity;
      while (newCap < n && newCap < maxEntries) {
        newCap = Math.min(maxEntries, newCap * 2);
      }
      if (newCap < n) newCap = n;

      function growTyped(old, TypedArrayCtor) {
        const a = new TypedArrayCtor(newCap);
        a.set(old);
        return a;
      }

      playerSq = growTyped(playerSq, Uint16Array);
      parent = growTyped(parent, Int32Array);
      moveFrom = growTyped(moveFrom, Uint16Array);
      moveDir = growTyped(moveDir, Uint8Array);

      if (gArr) gArr = growTyped(gArr, Int32Array);
      if (hArr) hArr = growTyped(hArr, Int32Array);

      if (heapPosArr) {
        const old = heapPosArr;
        heapPosArr = new Int32Array(newCap);
        heapPosArr.set(old);
        heapPosArr.fill(-1, old.length, newCap);
      }

      capacity = newCap;
      return true;
    }

    function addState(key, player, par, dir, from, gVal, hVal) {
      if (stateCount >= maxEntries) return -1;
      if (!ensureStates(stateCount + 1)) return -1;

      const idx = stateCount++;
      stateKeys.push(key);

      playerSq[idx] = player;
      parent[idx] = par;
      moveDir[idx] = dir;
      moveFrom[idx] = from;

      if (gArr) gArr[idx] = gVal;
      if (hArr) hArr[idx] = hVal;
      if (heapPosArr) heapPosArr[idx] = -1;

      globalStatesCreated++;
      return idx;
    }

    const visited = new Map();
    visited.set(initKey, 0);

    const initIdx = addState(initKey, playerStart, -1, 0, 0, 0, initH);
    if (initIdx < 0) return { sol: null, hitCap: true };

    function isGoalTemp(temp) {
      for (let i = 0; i < bLen; i++) {
        if (!isGoal[temp[i]]) return false;
      }
      return true;
    }

    function isGoalKey(key) {
      for (let i = 0; i < bLen; i++) {
        if (!isGoal[key.charCodeAt(1 + i)]) return false;
      }
      return true;
    }

    function frozen(target, movedFromSq, oldStamp) {
      const tx = target % width;
      const ty = (target - tx) / width;

      for (let ox = tx - 1; ox <= tx; ox++) {
        if (ox < 0 || ox + 1 >= width) continue;
        for (let oy = ty - 1; oy <= ty; oy++) {
          if (oy < 0 || oy + 1 >= height) continue;

          const a = oy * width + ox;
          const b = a + 1;
          const c = a + width;
          const d = c + 1;

          let all = true;
          let nonGoalBox = false;
          const squares = [a, b, c, d];

          for (let k = 0; k < 4; k++) {
            const s = squares[k];

            if (walls[s]) continue;

            let isBox;
            if (s === target) isBox = true;
            else if (s === movedFromSq) isBox = false;
            else isBox = boxMark[s] === oldStamp;

            if (isBox) {
              if (!isGoal[s]) nonGoalBox = true;
            } else {
              all = false;
              break;
            }
          }

          if (all && nonGoalBox) return true;
        }
      }

      return false;
    }

    function markStateBoxes(idx) {
      const st = nextBoxStamp();
      const key = stateKeys[idx];
      for (let i = 0; i < bLen; i++) {
        boxMark[key.charCodeAt(1 + i)] = st;
      }
      return st;
    }

    function findPath(start, target, stateIdx) {
      if (start === target) return '';

      const stamp = markStateBoxes(stateIdx);
      if (walls[start] || walls[target]) return '';
      if (boxMark[start] === stamp || boxMark[target] === stamp) return '';

      const st = nextWorkStamp();
      let head = 0;
      let tail = 0;

      floodQ[tail++] = start;
      seenWork[start] = st;

      while (head < tail) {
        const sq = floodQ[head++];
        const base = sq * 4;

        for (let d = 0; d < 4; d++) {
          const nb = neigh[base + d];
          if (nb < 0) continue;
          if (walls[nb]) continue;
          if (boxMark[nb] === stamp) continue;
          if (seenWork[nb] === st) continue;

          seenWork[nb] = st;
          pathPrev[nb] = sq;
          pathDir[nb] = d;

          if (nb === target) {
            const chars = [];
            let cur = target;
            let guard = 0;
            while (cur !== start && guard++ <= N) {
              chars.push(DIR_CHARS[pathDir[cur]]);
              cur = pathPrev[cur];
            }
            if (cur !== start) return '';
            chars.reverse();
            return chars.join('');
          }

          floodQ[tail++] = nb;
        }
      }

      return '';
    }

    function buildSolution(goalIdx) {
      const segments = [];
      let cur = goalIdx;
      let guard = 0;

      while (parent[cur] !== -1 && guard++ < 10000000) {
        const p = parent[cur];
        const dir = moveDir[cur];
        const from = moveFrom[cur];
        const stand = from - (dir === 0 ? -width : dir === 1 ? width : dir === 2 ? -1 : 1);

        const walk = findPath(playerSq[p], stand, p);
        segments.push(walk + PUSH_CHARS[dir]);
        cur = p;
      }

      let out = '';
      for (let i = segments.length - 1; i >= 0; i--) out += segments[i];
      return out;
    }

    // Queue for BFS
    let queue = null;
    let qHead = 0;
    let qTail = 0;

    function queuePush(idx) {
      if (qTail >= queue.length) {
        if (qHead > 0) {
          queue.copyWithin(0, qHead, qTail);
          qTail -= qHead;
          qHead = 0;
        }
        if (qTail >= queue.length) {
          let newLen = queue.length * 2;
          if (newLen > maxEntries) newLen = maxEntries;
          if (newLen > queue.length) {
            const nq = new Int32Array(newLen);
            nq.set(queue);
            queue = nq;
          }
        }
      }
      queue[qTail++] = idx;
    }

    // Heap for A* / greedy
    let heap = null;
    let heapSize = 0;

    function heapLess(a, b) {
      if (mode === 'astar') {
        const fa = gArr[a] + hArr[a];
        const fb = gArr[b] + hArr[b];
        if (fa < fb) return true;
        if (fa > fb) return false;
        if (gArr[a] > gArr[b]) return true;
        if (gArr[a] < gArr[b]) return false;
        return a < b;
      }

      if (hArr[a] < hArr[b]) return true;
      if (hArr[a] > hArr[b]) return false;
      return a < b;
    }

    function heapGrow() {
      if (heapSize < heap.length) return;
      let newLen = heap.length * 2;
      if (newLen < 1) newLen = 1;
      if (newLen > maxEntries && heap.length < maxEntries) newLen = maxEntries;
      if (newLen <= heap.length) return;
      const nh = new Int32Array(newLen);
      nh.set(heap);
      heap = nh;
    }

    function heapSiftUp(i) {
      const idx = heap[i];
      while (i > 0) {
        const p = (i - 1) >> 1;
        if (!heapLess(idx, heap[p])) break;
        heap[i] = heap[p];
        if (heapPosArr) heapPosArr[heap[i]] = i;
        i = p;
      }
      heap[i] = idx;
      if (heapPosArr) heapPosArr[idx] = i;
    }

    function heapSiftDown(i) {
      const half = heapSize >> 1;
      const idx = heap[i];

      while (i < half) {
        let l = i * 2 + 1;
        const r = l + 1;
        let c = l;

        if (r < heapSize && heapLess(heap[r], heap[l])) c = r;
        if (!heapLess(heap[c], idx)) break;

        heap[i] = heap[c];
        if (heapPosArr) heapPosArr[heap[i]] = i;
        i = c;
      }

      heap[i] = idx;
      if (heapPosArr) heapPosArr[idx] = i;
    }

    function heapPush(idx) {
      heapGrow();
      heap[heapSize] = idx;
      if (heapPosArr) heapPosArr[idx] = heapSize;
      heapSize++;
      heapSiftUp(heapSize - 1);
    }

    function heapPop() {
      const top = heap[0];
      heapSize--;

      if (heapSize > 0) {
        heap[0] = heap[heapSize];
        if (heapPosArr) heapPosArr[heap[0]] = 0;
        heapSiftDown(0);
      }

      if (heapPosArr) heapPosArr[top] = -2;
      return top;
    }

    if (mode === 'bfs') {
      queue = new Int32Array(Math.min(1024, maxEntries));
      queuePush(initIdx);
    } else {
      heap = new Int32Array(Math.min(1024, maxEntries));
      heapPush(initIdx);
    }

    const temp = new Array(bLen);
    const ABORT = {};

    function expandState(idx, newG) {
      const key = stateKeys[idx];
      const player = playerSq[idx];

      const oldStamp = nextBoxStamp();
      for (let i = 0; i < bLen; i++) {
        boxMark[key.charCodeAt(1 + i)] = oldStamp;
      }

      const regStamp = nextRegionStamp();
      const regionLow = floodRegion(
        player,
        oldStamp,
        -1,
        -1,
        seenRegion,
        regStamp,
        walls
      );
      if (regionLow < 0) return null;

      for (let bi = 0; bi < bLen; bi++) {
        const boxSq = key.charCodeAt(1 + bi);
        const boxBase = boxSq * 4;

        for (let dir = 0; dir < 4; dir++) {
          const stand = pushStand[boxBase + dir];
          const target = pushTarget[boxBase + dir];
          if (stand < 0 || target < 0) continue;

          if (seenRegion[stand] !== regStamp) continue;
          if (walls[target]) continue;
          if (boxMark[target] === oldStamp) continue;
          if (!live[target]) continue;
          if (frozen(target, boxSq, oldStamp)) continue;

          let pos = 0;
          let inserted = false;

          for (let k = 0; k < bLen; k++) {
            if (k === bi) continue;
            const v = key.charCodeAt(1 + k);
            if (!inserted && target < v) {
              temp[pos++] = target;
              inserted = true;
            }
            temp[pos++] = v;
          }
          if (!inserted) temp[pos++] = target;

          const newLow = floodRegion(
            boxSq,
            oldStamp,
            boxSq,
            target,
            seenWork,
            nextWorkStamp(),
            walls
          );
          if (newLow < 0) continue;

          let hVal = 0;
          if (mode !== 'bfs') {
            hVal = heuristicTemp(temp);
            if (hVal >= INF) continue;
          }

          const newKey = makeKey(newLow, temp);

          if (mode === 'bfs') {
            if (visited.has(newKey)) continue;
            if (globalStatesCreated > GLOBAL_BUDGET) return ABORT;
            if (stateCount >= maxEntries) return ABORT;

            const nidx = addState(newKey, boxSq, idx, dir, boxSq, 0, 0);
            if (nidx < 0) return ABORT;

            visited.set(newKey, nidx);
            queuePush(nidx);

            if (isGoalTemp(temp)) {
              return buildSolution(nidx);
            }
          } else if (mode === 'greedy') {
            if (visited.has(newKey)) continue;
            if (stateCount >= maxEntries) return ABORT;

            const nidx = addState(newKey, boxSq, idx, dir, boxSq, 0, hVal);
            if (nidx < 0) return ABORT;

            visited.set(newKey, nidx);
            heapPush(nidx);
          } else {
            const ex = visited.get(newKey);

            if (ex === undefined) {
              if (globalStatesCreated > GLOBAL_BUDGET) return ABORT;
              if (stateCount >= maxEntries) return ABORT;

              const nidx = addState(newKey, boxSq, idx, dir, boxSq, newG, hVal);
              if (nidx < 0) return ABORT;

              visited.set(newKey, nidx);
              heapPush(nidx);
            } else if (newG < gArr[ex]) {
              parent[ex] = idx;
              moveDir[ex] = dir;
              moveFrom[ex] = boxSq;
              playerSq[ex] = boxSq;
              gArr[ex] = newG;

              const p = heapPosArr[ex];
              if (p === -2 || p === -1) {
                heapPush(ex);
              } else if (p >= 0) {
                heapSiftUp(p);
              }
            }
          }
        }
      }

      return null;
    }

    if (mode === 'bfs') {
      while (qHead < qTail) {
        if (stateCount >= maxEntries) return { sol: null, hitCap: true };
        if (globalStatesCreated > GLOBAL_BUDGET) return { sol: null, hitCap: true };

        const idx = queue[qHead++];
        const res = expandState(idx, 0);

        if (res === ABORT) return { sol: null, hitCap: true };
        if (typeof res === 'string') return { sol: res, hitCap: false };
      }

      return { sol: null, hitCap: false };
    }

    let expansions = 0;

    while (heapSize > 0) {
      if (expansions >= cap) return { sol: null, hitCap: true };
      if (mode === 'astar' && globalStatesCreated > GLOBAL_BUDGET) {
        return { sol: null, hitCap: true };
      }

      const idx = heapPop();
      expansions++;

      if (isGoalKey(stateKeys[idx])) {
        return { sol: buildSolution(idx), hitCap: false };
      }

      const newG = mode === 'astar' ? gArr[idx] + 1 : 0;
      const res = expandState(idx, newG);

      if (res === ABORT) return { sol: null, hitCap: true };
      if (typeof res === 'string') return { sol: res, hitCap: false };
    }

    return { sol: null, hitCap: false };
  }

  function attemptSearches(walls, goals, boxes, player, bfsCap) {
    if (globalStatesCreated > GLOBAL_BUDGET) {
      const r = runSearch(walls, goals, boxes, player, 'greedy', BUDGET_GREEDY_CAP);
      return r.sol;
    }

    let r = runSearch(walls, goals, boxes, player, 'bfs', bfsCap);
    if (r.sol !== null) return r.sol;
    if (!r.hitCap) return null;

    if (globalStatesCreated > GLOBAL_BUDGET) {
      r = runSearch(walls, goals, boxes, player, 'greedy', BUDGET_GREEDY_CAP);
      return r.sol;
    }

    r = runSearch(walls, goals, boxes, player, 'astar', ASTAR_CAP);
    if (r.sol !== null) return r.sol;
    if (!r.hitCap) return null;

    if (globalStatesCreated > GLOBAL_BUDGET) {
      r = runSearch(walls, goals, boxes, player, 'greedy', BUDGET_GREEDY_CAP);
      return r.sol;
    }

    r = runSearch(walls, goals, boxes, player, 'greedy', GREEDY_CAP);
    return r.sol;
  }

  const rooms = decompose();

  if (!rooms) {
    const sol = attemptSearches(levelWall, allGoals, allBoxes, startPlayer, WHOLE_BFS_CAP);
    return sol === null ? '' : sol;
  }

  let currentPlayer = startPlayer;
  const solvedRooms = new Uint8Array(rooms.length);
  const answerParts = [];

  for (let i = 0; i < rooms.length; i++) {
    const room = rooms[i];

    const walls = levelWall.slice();

    for (let j = 0; j < rooms.length; j++) {
      if (j === i) continue;
      const other = rooms[j];

      if (solvedRooms[j]) {
        for (const g of other.goals) walls[g] = 1;
      } else {
        for (const b of other.boxes) walls[b] = 1;
      }
    }

    const sol = attemptSearches(walls, room.goals, room.boxes, currentPlayer, ROOM_BFS_CAP);

    if (sol === null) break;

    if (sol) answerParts.push(sol);
    currentPlayer = applyMoves(currentPlayer, sol);
    solvedRooms[i] = 1;
  }

  return answerParts.join('');
}

function main() {
  let ids = [];

  try {
    ids = readdirSync(INPUT_DIR).sort();
  } catch (e) {
    return;
  }

  for (const id of ids) {
    let isDir = false;
    try {
      isDir = statSync(join(INPUT_DIR, id)).isDirectory();
    } catch (e) {
      isDir = false;
    }
    if (!isDir) continue;

    let solution = '';

    try {
      const levelText = readFileSync(join(INPUT_DIR, id, 'level.txt'), 'utf8');
      const s = solveLevel(levelText);
      if (typeof s === 'string') solution = s;
    } catch (e) {
      solution = '';
    }

    try {
      const outDir = join(OUTPUT_DIR, id);
      mkdirSync(outDir, { recursive: true });
      writeFileSync(join(outDir, 'solution.txt'), solution + '\n');
    } catch (e) {
      // Ignore output errors deterministically.
    }
  }
}

main();
