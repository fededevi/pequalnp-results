"""SAT search: is there a fan-in-2 AND/OR/NOT circuit with G gates for the L-meta-518 function?
usage: python circsat.py G [mono]   (mono: AND/OR only)"""
import sys, time, itertools
from pysat.solvers import Cadical153
from pysat.card import CardEnc

N = 10
EDGES = [(0, 1), (0, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 1), (0, 8), (1, 9)]
G = int(sys.argv[1])
MONO = len(sys.argv) > 2 and sys.argv[2] == "mono"
ROWS = list(range(1 << N))


def f(r):
    return any((r >> a) & 1 and (r >> b) & 1 for a, b in EDGES)


cnt = [0]


def new():
    cnt[0] += 1
    return cnt[0]


cls = []
W = N + G
# value of wire w on row r: inputs are constants, gates are variables
val = {}
for g in range(G):
    for r in ROWS:
        val[(N + g, r)] = new()


def lit(w, r):
    """return ('const', bool) or ('var', v)"""
    if w < N:
        return ("c", bool((r >> w) & 1))
    return ("v", val[(w, r)])


TYPES = ["and", "or"] if MONO else ["and", "or", "not"]
sa, sb, ty = {}, {}, {}
for g in range(G):
    wires = list(range(N + g))
    sa[g] = {w: new() for w in wires}
    sb[g] = {w: new() for w in wires}
    ty[g] = {t: new() for t in TYPES}
    for d in (sa[g], sb[g], ty[g]):
        enc = CardEnc.equals(lits=list(d.values()), bound=1, top_id=cnt[0])
        cnt[0] = max(cnt[0], enc.nv)
        cls.extend(enc.clauses)
    # symmetry: index(a) <= index(b); for NOT, b == a
    for w in wires:
        for u in wires:
            if u < w:
                cls.append([-sa[g][w], -sb[g][u]])
    if "not" in ty[g]:
        for w in wires:
            cls.append([-ty[g]["not"], -sa[g][w], sb[g][w]])

# every gate except the last is used by a later gate (no dead gates)
for g in range(G - 1):
    users = []
    for h in range(g + 1, G):
        users += [sa[h][N + g], sb[h][N + g]]
    cls.append(users)

for g in range(G):
    for r in ROWS:
        A, B = new(), new()
        for side, X in ((sa[g], A), (sb[g], B)):
            for w, s in side.items():
                k, x = lit(w, r)
                if k == "c":
                    cls.append([-s, X if x else -X])
                else:
                    cls.append([-s, -X, x])
                    cls.append([-s, X, -x])
        v = val[(N + g, r)]
        t = ty[g]
        # AND
        cls += [[-t["and"], -v, A], [-t["and"], -v, B], [-t["and"], v, -A, -B]]
        # OR
        cls += [[-t["or"], v, -A], [-t["or"], v, -B], [-t["or"], -v, A, B]]
        if "not" in t:
            cls += [[-t["not"], v, A], [-t["not"], -v, -A]]

# output = last gate
for r in ROWS:
    v = val[(N + G - 1, r)]
    cls.append([v] if f(r) else [-v])

print(f"G={G} mono={MONO} vars={cnt[0]} clauses={len(cls)}", flush=True)
t0 = time.time()
with Cadical153(bootstrap_with=cls) as s:
    res = s.solve()
    print("SAT" if res else "UNSAT", f"{time.time() - t0:.1f}s", flush=True)
    if res:
        m = set(x for x in s.get_model() if x > 0)
        for g in range(G):
            a = next(w for w, v in sa[g].items() if v in m)
            b = next(w for w, v in sb[g].items() if v in m)
            t = next(k for k, v in ty[g].items() if v in m)
            print(f"gate {N + g} = {t}({a}, {b})")
        # verify
        for r in ROWS:
            w = [bool((r >> i) & 1) for i in range(N)]
            for g in range(G):
                a = next(x for x, v in sa[g].items() if v in m)
                b = next(x for x, v in sb[g].items() if v in m)
                t = next(k for k, v in ty[g].items() if v in m)
                w.append(w[a] and w[b] if t == "and" else w[a] or w[b] if t == "or" else not w[a])
            assert w[-1] == f(r), r
        print("verified on all rows")
