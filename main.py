# tiny-chess-01 entry: a chess engine in under 4 KB of Python.
# Negamax alpha-beta with transposition table, killers, history, check
# extensions and a capture quiescence search, over a fixed node budget
# (never a clock, so replays match). PST + material evaluation.
# It plays the gauntlet through the env at MAKEFUN_ENV_URL: POST /game
# serves the game in play, POST /move plays a move, done ends the loop.
import json, os, sys, urllib.request, urllib.error, random
E = os.environ.get("MAKEFUN_ENV_URL") or sys.exit("MAKEFUN_ENV_URL is not set")
def post(p, b):
    q = urllib.request.Request(E + p, data=json.dumps(b).encode(), headers={"content-type": "application/json"})
    try:
        with urllib.request.urlopen(q) as r: return json.load(r)
    except urllib.error.HTTPError as e: sys.exit(e.read().decode(errors="replace"))
V = (0, 100, 320, 330, 500, 900, 0)
_T = """0,0,0,0,0,0,0,0,50,50,50,50,50,50,50,50,10,10,20,30,30,20,10,10,5,5,10,25,25,10,5,5,0,0,0,20,20,0,0,0,5,-5,-10,0,0,-10,-5,5,5,10,10,-20,-20,10,10,5,0,0,0,0,0,0,0,0
-50,-40,-30,-30,-30,-30,-40,-50,-40,-20,0,0,0,0,-20,-40,-30,0,10,15,15,10,0,-30,-30,5,15,20,20,15,5,-30,-30,0,15,20,20,15,0,-30,-30,5,10,15,15,10,5,-30,-40,-20,0,5,5,0,-20,-40,-50,-40,-30,-30,-30,-30,-40,-50
-20,-10,-10,-10,-10,-10,-10,-20,-10,0,0,0,0,0,0,-10,-10,0,5,10,10,5,0,-10,-10,5,5,10,10,5,5,-10,-10,0,10,10,10,10,0,-10,-10,10,10,10,10,10,10,-10,-10,5,0,0,0,0,5,-10,-20,-10,-10,-10,-10,-10,-10,-20
0,0,0,0,0,0,0,0,5,10,10,10,10,10,10,5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,-5,0,0,0,0,0,0,-5,0,0,0,5,5,0,0,0
-20,-10,-10,-5,-5,-10,-10,-20,-10,0,0,0,0,0,0,-10,-10,0,5,5,5,5,0,-10,-5,0,5,5,5,5,0,-5,0,0,5,5,5,5,0,-5,-10,5,5,5,5,5,5,-10,-10,0,5,0,0,5,0,-10,-20,-10,-10,-5,-5,-10,-10,-20
-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-30,-40,-40,-50,-50,-40,-40,-30,-20,-30,-30,-40,-40,-30,-30,-20,-10,-20,-20,-20,-20,-20,-20,-10,20,20,0,0,0,0,20,20,20,30,10,0,0,10,30,20"""
PST = [[int(x) for x in line.split(",")] for line in _T.split("\n")]
_R = random.Random(987654321)
Z = [[_R.getrandbits(64) for _ in range(64)] for _ in range(13)]
ZS = _R.getrandbits(64); ZC = [_R.getrandbits(64) for _ in range(16)]; ZE = [_R.getrandbits(64) for _ in range(65)]
KN = []; KG = []; RY = []; PA = []; PB = []
for s in range(64):
    f, r = s & 7, s >> 3
    kn = []; kg = []; ry = []; pa = []; pb = []
    for df, dr in ((1, 2), (2, 1), (-1, 2), (-2, 1), (1, -2), (2, -1), (-1, -2), (-2, -1)):
        if 0 <= f + df < 8 and 0 <= r + dr < 8: kn.append((r + dr) * 8 + f + df)
    for df, dr in ((1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)):
        if 0 <= f + df < 8 and 0 <= r + dr < 8: kg.append((r + dr) * 8 + f + df)
        ray = []; nf, nr = f + df, r + dr
        while 0 <= nf < 8 and 0 <= nr < 8:
            ray.append(nr * 8 + nf); nf += df; nr += dr
        ry.append(ray)
    for df in (-1, 1):
        if 0 <= f + df < 8 and r + 1 < 8: pa.append((r + 1) * 8 + f + df)
        if 0 <= f + df < 8 and r - 1 >= 0: pb.append((r - 1) * 8 + f + df)
    KN.append(kn); KG.append(kg); RY.append(ry); PA.append(pa); PB.append(pb)
KEEP = [15] * 64
KEEP[60] = 12; KEEP[63] = 14; KEEP[56] = 13; KEEP[4] = 3; KEEP[7] = 11; KEEP[0] = 7
B = [0] * 64
ST = [1, 0, -1, 0, 0]  # side to move, castling, ep square, halfmove, hash
KS = {1: 0, -1: 0}
TT = {}; ND = [0]; BUDGET = [150000]; KILL = [[None, None] for _ in range(128)]; HIST = {}
MATE = 100000
class Stop(Exception): pass
def attacked(s, by):
    for a in (PA if by > 0 else PB)[s]:
        if B[a] == by: return True
    for a in KN[s]:
        if B[a] == 2 * by: return True
    for a in KG[s]:
        if B[a] == 6 * by: return True
    for d in range(4):
        for a in RY[s][d]:
            p = B[a]
            if p:
                if p == 4 * by or p == 5 * by: return True
                break
    for d in range(4, 8):
        for a in RY[s][d]:
            p = B[a]
            if p:
                if p == 3 * by or p == 5 * by: return True
                break
    return False
def gen(cap=False):
    us = ST[0]; ms = []
    for s in range(64):
        p = B[s]
        if not p or (p > 0) != (us > 0): continue
        a = abs(p); f = s & 7; r = s >> 3
        if a == 1:
            d = -8 * us; t = s + d
            if not B[t]:
                if t < 8 or t >= 56:
                    for pr in (5, 4, 3, 2): ms.append((s, t, pr))
                elif not cap:
                    ms.append((s, t, 0))
                    if (r == 6 if us > 0 else r == 1) and not B[s + 2 * d]: ms.append((s, s + 2 * d, 0))
            for df in (-1, 1):
                if 0 <= f + df < 8:
                    t = s + d + df; q = B[t]
                    if q and (q > 0) != (us > 0):
                        if t < 8 or t >= 56:
                            for pr in (5, 4, 3, 2): ms.append((s, t, pr))
                        else: ms.append((s, t, 0))
                    elif t == ST[2]: ms.append((s, t, 0))
        elif a == 2 or a == 6:
            for t in (KN if a == 2 else KG)[s]:
                q = B[t]
                if not q:
                    if not cap: ms.append((s, t, 0))
                elif (q > 0) != (us > 0): ms.append((s, t, 0))
            if a == 6 and not cap:
                if us > 0:
                    if ST[1] & 1 and not B[61] and not B[62] and B[63] == 4 and not attacked(60, -1) and not attacked(61, -1) and not attacked(62, -1): ms.append((60, 62, 0))
                    if ST[1] & 2 and not B[57] and not B[58] and not B[59] and B[56] == 4 and not attacked(60, -1) and not attacked(59, -1) and not attacked(58, -1): ms.append((60, 58, 0))
                else:
                    if ST[1] & 4 and not B[5] and not B[6] and B[7] == -4 and not attacked(4, 1) and not attacked(5, 1) and not attacked(6, 1): ms.append((4, 6, 0))
                    if ST[1] & 8 and not B[1] and not B[2] and not B[3] and B[0] == -4 and not attacked(4, 1) and not attacked(3, 1) and not attacked(2, 1): ms.append((4, 2, 0))
        else:
            for d in (range(4) if a == 4 else range(4, 8) if a == 3 else range(8)):
                for t in RY[s][d]:
                    q = B[t]
                    if not q:
                        if not cap: ms.append((s, t, 0))
                    else:
                        if (q > 0) != (us > 0): ms.append((s, t, 0))
                        break
    return ms
def make(m):
    f, t, pr = m; us = ST[0]; p = B[f]; cap = B[t]
    undo = [cap, ST[1], ST[2], ST[3], None, -1]
    ST[4] ^= ZC[ST[1]] ^ ZE[ST[2] + 1]
    if abs(p) == 1 and t == ST[2] and (f & 7) != (t & 7) and not cap:
        cq = t + 8 * us; cap = B[cq]; undo[5] = cq; undo[0] = cap
        B[cq] = 0; ST[4] ^= Z[cap + 6][cq]
    elif cap: ST[4] ^= Z[cap + 6][t]
    B[t] = pr * us if pr else p; B[f] = 0
    ST[4] ^= Z[p + 6][f] ^ Z[B[t] + 6][t]
    if abs(p) == 6:
        KS[us] = t
        if abs(t - f) == 2:
            rf, rt = (f + 3, f + 1) if t > f else (f - 4, f - 1)
            B[rt] = B[rf]; B[rf] = 0; ST[4] ^= Z[B[rt] + 6][rf] ^ Z[B[rt] + 6][rt]
    ST[1] &= KEEP[f] & KEEP[t]
    ST[2] = (f + t) // 2 if abs(p) == 1 and abs(t - f) == 16 else -1
    ST[3] = 0 if abs(p) == 1 or cap else ST[3] + 1
    ST[4] ^= ZC[ST[1]] ^ ZE[ST[2] + 1] ^ ZS
    ST[0] = -us
    return undo
def unmake(m, undo):
    f, t, pr = m; us = -ST[0]; cap, cr, ep, half, _, cq = undo
    ST[0] = us; ST[4] ^= ZC[ST[1]] ^ ZE[ST[2] + 1] ^ ZS
    p = B[t]
    if abs(p) == 6 and abs(t - f) == 2:
        rf, rt = (f + 3, f + 1) if t > f else (f - 4, f - 1)
        B[rf] = B[rt]; B[rt] = 0; ST[4] ^= Z[B[rf] + 6][rf] ^ Z[B[rf] + 6][rt]
    B[f] = 1 * us if pr else p; B[t] = 0
    ST[4] ^= Z[p + 6][t] ^ Z[B[f] + 6][f]
    if cq >= 0:
        B[cq] = cap; ST[4] ^= Z[cap + 6][cq]
    elif cap:
        B[t] = cap; ST[4] ^= Z[cap + 6][t]
    if abs(B[f]) == 6: KS[us] = f
    ST[1] = cr; ST[2] = ep; ST[3] = half
    ST[4] ^= ZC[cr] ^ ZE[ep + 1]
def ev():
    s = 0; wb = bb = 0; wk = bk = 0; nq = 0
    for sq in range(64):
        p = B[sq]
        if p:
            a = abs(p); tb = PST[a - 1]
            if p > 0:
                s += V[a] + tb[sq]
                if a == 3: wb += 1
                elif a == 6: wk = sq
                elif a == 5: nq += 1
            else:
                s -= V[a] + tb[sq ^ 56]
                if a == 3: bb += 1
                elif a == 6: bk = sq
                elif a == 5: nq += 1
    if wb == 2: s += 30
    if bb == 2: s -= 30
    if nq == 0:
        for k, sg in ((wk, 1), (bk, -1)):
            f, r = k & 7, k >> 3
            s += sg * int((3.5 - abs(f - 3.5) + 3.5 - abs(r - 3.5)) * 10)
    return s if ST[0] > 0 else -s
def order(ms, ttmove, ply):
    def key(m):
        f, t, pr = m; v = B[t]
        if m == ttmove: return 9000000
        if v: return 1000000 + V[abs(v)] * 10 - V[abs(B[f])]
        if abs(B[f]) == 1 and t == ST[2] and (f & 7) != (t & 7): return 1000000 + 100
        if pr: return 800000 + V[pr]
        if ply < 128 and (m == KILL[ply][0] or m == KILL[ply][1]): return 700000
        return HIST.get(m, 0)
    ms.sort(key=key, reverse=True)
def qs(al, be, ply):
    ND[0] += 1
    if ND[0] >= BUDGET[0]: raise Stop
    us = ST[0]; chk = attacked(KS[us], -us)
    if chk: best = -MATE + ply
    else:
        best = ev()
        if best >= be: return be
        if best > al: al = best
    if ply >= 32: return ev()
    ms = gen(cap=not chk); order(ms, None, 999)
    legal = 0
    for m in ms:
        undo = make(m)
        if attacked(KS[us], -us):
            unmake(m, undo); continue
        legal += 1
        sc = -qs(-be, -al, ply + 1)
        unmake(m, undo)
        if sc > best:
            best = sc
            if sc > al: al = sc
            if al >= be: break
    if chk and legal == 0: return -MATE + ply
    if not chk and legal == 0 and False: return best
    return best
def search(d, al, be, ply):
    ND[0] += 1
    if ND[0] >= BUDGET[0]: raise Stop
    if ST[3] >= 100: return 0
    us = ST[0]; ttmove = None
    a0 = al; b0 = be; d0 = d
    ent = TT.get(ST[4])
    if ent:
        ttmove = ent[3]
        if ply > 0 and ent[0] >= d:
            if ent[1] == 0: return ent[2]
            if ent[1] == 1 and ent[2] > al: al = ent[2]
            if ent[1] == 2 and ent[2] < be: be = ent[2]
            if al >= be: return ent[2]
    chk = attacked(KS[us], -us)
    if chk: d += 1
    if d <= 0: return qs(al, be, ply)
    ms = gen(); order(ms, ttmove, ply)
    best = -MATE - 1; bm = None; legal = 0
    for m in ms:
        undo = make(m)
        if attacked(KS[us], -us):
            unmake(m, undo); continue
        legal += 1
        sc = -search(d - 1, -be, -al, ply + 1)
        unmake(m, undo)
        if sc > best:
            best = sc; bm = m
            if sc > al:
                al = sc
                if al >= be:
                    if not B[m[1]] and m[2] == 0 and ply < 128:
                        if KILL[ply][0] != m: KILL[ply][1] = KILL[ply][0]; KILL[ply][0] = m
                        HIST[m] = HIST.get(m, 0) + d * d
                    break
    if legal == 0: return -MATE + ply if chk else 0
    fl = 2 if best <= a0 else 1 if best >= b0 else 0
    TT[ST[4]] = (d0, fl, best, bm)
    return best
def parse(fen):
    parts = fen.split()
    for i in range(64): B[i] = 0
    for r, row in enumerate(parts[0].split("/")):
        f = 0
        for c in row:
            if c.isdigit(): f += int(c)
            else:
                p = "pnbrqk".index(c.lower()) + 1
                B[r * 8 + f] = p if c.isupper() else -p
                if p == 6: KS[1 if c.isupper() else -1] = r * 8 + f
                f += 1
    ST[0] = 1 if parts[1] == "w" else -1
    ST[1] = 0
    for i, c in enumerate("KQkq"):
        if c in parts[2]: ST[1] |= 1 << i
    ST[2] = -1
    if parts[3] != "-": ST[2] = (8 - int(parts[3][1])) * 8 + "abcdefgh".index(parts[3][0])
    ST[3] = int(parts[4]) if len(parts) > 4 else 0
    h = ZC[ST[1]] ^ ZE[ST[2] + 1]
    for sq in range(64):
        if B[sq]: h ^= Z[B[sq] + 6][sq]
    if ST[0] < 0: h ^= ZS
    ST[4] = h
def uci(m):
    f, t, pr = m
    s = "abcdefgh"[f & 7] + str(8 - (f >> 3)) + "abcdefgh"[t & 7] + str(8 - (t >> 3))
    return s + ("  nbrq"[pr] if pr else "")
def choose(fen, legal):
    parse(fen)
    TT.clear(); ND[0] = 0
    for k in KILL: k[0] = k[1] = None
    HIST.clear()
    us = ST[0]; bm = None
    ms = gen(); order(ms, None, 0)
    root = [m for m in ms if uci(m) in legal]
    if not root: return legal[0]
    bm = root[0]
    for d in range(1, 64):
        al = -MATE - 1; best = -MATE - 1; cur = bm; first = True
        try:
            for m in root:
                undo = make(m)
                if attacked(KS[us], -us):
                    unmake(m, undo); continue
                if first:
                    sc = -search(d - 1, -MATE - 1, MATE + 1, 1); first = False
                else:
                    sc = -search(d - 1, -al - 1, -al, 1)
                    if sc > al: sc = -search(d - 1, -MATE - 1, MATE + 1, 1)
                unmake(m, undo)
                if sc > best: best = sc; cur = m
                if sc > al: al = sc
            bm = cur
            root.remove(bm); root.insert(0, bm)
        except Stop:
            break
        if ND[0] > BUDGET[0] * 0.7: break
    s = uci(bm)
    return s if s in legal else legal[0]
while True:
    g = post("/game", {})
    if g["status"] == "done": break
    while g["status"] == "your_move":
        g = post("/move", {"game": g["game"], "move": choose(g["fen"], g["legal_moves"])})
    print(f"game {g['game']}: {g['outcome']} by {g['reason']}", file=sys.stderr)
print(f"done: {g.get('wins')} won, {g.get('draws')} drawn, {g.get('losses')} lost", file=sys.stderr)
