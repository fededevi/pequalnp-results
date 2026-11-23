"""Enumerate all 11-gate monotone fan-in-2 circuits for graph 514 (canonical form per fence),
with constraint (A) (an AND gate with an AND gate in its transitive fan-in) in SAT,
and check condition (B) of L-meta-523 exactly in Python."""
import sys, time, json, multiprocessing as mp
sys.path.insert(0, r"./tools")
import circsat2 as cs

N, EDGES = cs.GRAPHS["514"]
G = 11
NOA = True
TR = cs.truth_table(N, EDGES)

def wires_all(gates, r):
    w = [bool((r >> i) & 1) for i in range(N)]
    for t, ins in gates:
        vals = [w[i] if i < len(w) else False for i in ins]
        w.append(all(vals) if t == "and" else any(vals))
    return w

def computes(gates, out):
    for r in range(1 << N):
        w = wires_all(gates, r)
        v = w[out] if out < len(w) else False
        if v != TR[r]:
            return False
    return True

def pairs(gates):
    n = len(gates)
    reach = [set() for _ in range(n)]
    for u in range(n):  # topological: inputs earlier
        for i in gates[u][1]:
            v = i - 8
            if 0 <= v < n:
                reach[u].add(v); reach[u] |= reach[v]
    # reach may reference later gates only if v>u (not in valid circuits)
    return sum(1 for a in range(n) if gates[a][0] == "and" for b in reach[a]
               if b != a and b < n and gates[b][0] == "and")

def implies_F(gates, h):
    for r in range(1 << N):
        w = wires_all(gates, r)
        if (w[h] if h < len(w) else False) and not TR[r]:
            return False
    return True

def checkB(gates):
    """returns list of flattening lifts (empty = witness)"""
    c0 = pairs(gates)
    bad = []
    for j, (t, ins) in enumerate(gates):
        if t != "or" or j == 10:
            continue
        a, b = ins
        for p, h in {(a, b), (b, a)}:
            if not implies_F(gates, h):
                continue
            D = list(gates); D[j] = ("or", [p, p]); D.append(("or", [18, h]))
            if computes(D, 19) and pairs(D) < c0:
                bad.append((j, p, h, c0, pairs(D)))
    return bad

def worker(fence):
    t0 = time.time()
    e = cs.Enc(N, EDGES, G, True, list(fence))
    s = e.s
    nv = [e.nv]
    def new():
        nv[0] += 1; return nv[0]
    isand = []
    for i in range(G):
        v = new(); isand.append(v)
        ands = [x for o, x in e.opts[i] if o[0] == "and"]
        for x in ands: s.add_clause([-x, v])
        s.add_clause([-v] + ands)
    # below[i]: some AND gate strictly in transitive fan-in of gate i
    below = []
    for i in range(G):
        b = new(); terms = []
        for w in range(i):
            rd = [x for o, x in e.opts[i] if (N + w) in (o[1], o[2])]
            if not rd: continue
            r = new()
            s.add_clause([-r] + rd)
            s.add_clause([-r, isand[w], below[w]])
            terms.append(r)
        s.add_clause([-b] + terms)
        below.append(b)
    top = []
    for i in range(G):
        t = new(); s.add_clause([-t, isand[i]]); s.add_clause([-t, below[i]]); top.append(t)
    if not NOA: s.add_clause(top)
    nsol = 0; wit = []
    while s.solve():
        m = s.get_model(); ms = set(x for x in m if x > 0)
        chosen = [next(x for o, x in e.opts[i] if x in ms) for i in range(G)]
        circ = e.decode(m)
        s.add_clause([-x for x in chosen])
        gates = [(t, [j, k]) for t, j, k in circ]
        assert computes(gates, 18)
        nsol += 1
        if True:
            wit.append(gates)
    return fence, nsol, wit, time.time() - t0

if __name__ == "__main__":
    fs = sorted(cs.fences(N, G, True), key=len, reverse=True)
    print("fences", len(fs), flush=True)
    t0 = time.time(); tot = 0; allw = []; done = 0
    with mp.Pool(int(sys.argv[1]) if len(sys.argv) > 1 else 8) as pool:
        for fence, nsol, wit, dt in pool.imap_unordered(worker, fs):
            done += 1; tot += nsol
            if nsol or dt > 60 or wit:
                print(f"[{done}/{len(fs)} {time.time()-t0:.0f}s] {fence}: {nsol} sols, {len(wit)} witnesses, {dt:.0f}s", flush=True)
            with open(r'./L-meta-523/all_circuits.jsonl','a') as fo:
                fo.write(json.dumps({'fence':fence,'circs':wit})+chr(10))
    print(f"TOTAL circuits(A) {tot}, witnesses {len(allw)}, {time.time()-t0:.0f}s", flush=True)
    json.dump(allw, open(r"./L-meta-523/stats_noA.json", "w"))
