"""Exact synthesis: is there a fan-in-2 AND/OR/NOT circuit with G gates for
'both ends of some edge are true' on a graph?  (pequalnp.com L-meta-514/515/518)

usage: python -I circsat2.py GRAPH G [--mono] [--solver NAME] [--timeout SEC]
                                     [--fences WORKERS] [--fence 3,2,1]
  GRAPH: 514, 515, 518 or an edge list like "0-1,1-2,..."
  --mono: AND/OR gates only (rows = minimal true + maximal false points: exact for
          a monotone circuit); default AND/OR/NOT with CEGAR over all 2^n rows
  --fences W: split by level profile ("fence": number of gates at each depth) and
          solve the fences on W processes; --fence a,b,..: one fence only

Encoding (Haaswijk/Soeken SSV-style selection, Kojevnikov-Kulikov-Yaroslavtsev
symmetry breaking). Every restriction below holds for SOME minimum-size circuit, so
UNSAT (of all fences) proves that no G-gate circuit exists:
  * gate i picks exactly one option (AND j<k | OR j<k | NOT j) over earlier wires;
    gates are in topological order, the output is the last gate (gates past the
    output would be dead).
  * options are ordered by (max wire, min wire, type); consecutive gates have
    strictly increasing keys (if gate i+1 does not read gate i they can be swapped;
    if it does, its key is larger anyway). No two gates pick the same option.
    With fences: gates sorted by depth, the rule applies within a depth (gates of one
    depth are independent); a gate of depth L reads a wire of depth L-1 and none deeper.
  * every gate but the output is read later; every input is read (f depends on all).
  * no gate reads (j, i) where gate i reads j: it would be constant (i = NOT j) or
    equal i or j (absorption / idempotence).  No NOT of a NOT.
  * read slots: AND/OR read 2 distinct wires, NOT reads 1; every input and non-output
    gate is read at least once, so (#extra reads beyond the first of each wire) +
    #NOT <= 2G - (N + G - 1) = G - N + 1 (cardinality constraint, totalizer).
SAT answers are re-verified on all 2^n rows in plain Python.
"""
import argparse, bisect, itertools, threading, time, random, sys

GRAPHS = {
    "514": (8, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5), (0, 6), (1, 7)]),
    "515": (8, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5), (0, 6), (3, 7)]),
    "518": (10, [(0, 1), (0, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 1), (0, 8), (1, 9)]),
}
TC = {"and": 0, "or": 1, "not": 2}


def key(o):
    t, j, k = o
    return (j, -1, 2) if t == "not" else (k, j, TC[t])


def parse_graph(g):
    if g in GRAPHS:
        return GRAPHS[g]
    edges = [tuple(map(int, e.split("-"))) for e in g.split(",")]
    return max(max(e) for e in edges) + 1, edges


def truth_table(N, EDGES):
    return [any((r >> a) & 1 and (r >> b) & 1 for a, b in EDGES) for r in range(1 << N)]


def evaluate(N, circ, r):
    w = [bool((r >> i) & 1) for i in range(N)]
    for t, j, k in circ:
        w.append(w[j] and w[k] if t == "and" else w[j] or w[k] if t == "or" else not w[j])
    return w[-1]


class Enc:
    def __init__(self, N, EDGES, G, mono, fence=None, solver="Cadical195", card=True,
                 allrows=False, distinct=False):
        from pysat import solvers as S
        from pysat.card import CardEnc, EncType
        self.N, self.G, self.mono = N, G, mono
        self.ROWS = 1 << N
        self.TRUTH = truth_table(N, EDGES)
        TR = self.TRUTH
        self.nv = 0
        cls = []
        if fence:
            assert sum(fence) == G and fence[-1] == 1
            lev = [0] * N
            for L, s in enumerate(fence, 1):
                lev += [L] * s
        else:
            lev = None
        self.lev = lev

        def allowed(i):
            w = N + i
            res = []
            for k in range(w):
                for j in range(k):
                    if lev and not (max(lev[j], lev[k]) == lev[w] - 1):
                        continue
                    res += [("and", j, k), ("or", j, k)]
                if not mono and (not lev or lev[k] == lev[w] - 1):
                    res.append(("not", k, -1))
            res.sort(key=key)
            return res

        self.opts, self.keys, ge = [], [], []
        for i in range(G):
            os_ = allowed(i)
            vs = [self.new() for _ in os_]
            self.opts.append(list(zip(os_, vs)))
            self.keys.append([key(o) for o in os_])
            if not vs:
                cls.append([])
                ge.append([])
                continue
            cls.append(vs)
            g = [self.new() for _ in vs]
            for v in range(len(vs)):
                cls.append([-vs[v], g[v]])
                if v + 1 < len(vs):
                    cls.append([-g[v + 1], g[v]])
                    cls.append([-vs[v], -g[v + 1]])
            ge.append(g)
        isnot = [None] * G
        reads = [dict() for _ in range(G)]
        for i in range(G):
            if not mono:
                nots = [v for o, v in self.opts[i] if o[0] == "not"]
                isnot[i] = self.new()
                for v in nots:
                    cls.append([-v, isnot[i]])
                cls.append([-isnot[i]] + nots)
            for w in range(N + i):
                srcs = [v for o, v in self.opts[i] if w in (o[1], o[2])]
                r = self.new()
                reads[i][w] = r
                for v in srcs:
                    cls.append([-v, r])
                cls.append([-r] + srcs)
        same = (lambda a, b: True) if not lev else (lambda a, b: lev[N + a] == lev[N + b])
        # strictly increasing keys for consecutive (swappable) gates
        for i in range(G - 1):
            if not same(i, i + 1):
                continue
            for o, v in self.opts[i + 1]:
                pos = bisect.bisect_left(self.keys[i], key(o))   # gate i must be < pos
                if pos < len(ge[i]):
                    cls.append([-v, -ge[i][pos]])
        # no two gates pick the same option
        for i in range(G):
            for l in range(i + 2, G):
                if not same(i, l):
                    continue
                d = dict(self.opts[i])
                for o, v2 in self.opts[l]:
                    if o in d:
                        cls.append([-d[o], -v2])
        for i in range(G - 1):
            cls.append([reads[l][N + i] for l in range(i + 1, G)])
        for x in range(N):
            cls.append([reads[l][x] for l in range(G)])
        for l in range(G):
            for o, v in self.opts[l]:
                t, j, k = o
                if t == "not":
                    if j >= N:
                        cls.append([-v, -isnot[j - N]])
                elif k >= N:
                    cls.append([-v, -reads[k - N][j]])
        if card:
            K = G - N + 1
            extra = []
            for w in range(N + G - 1):
                prev = None
                for l in range(max(0, w - N + 1), G):
                    r = reads[l][w]
                    if prev is not None:
                        e = self.new()
                        cls.append([-r, -prev, e])
                        extra.append(e)
                    p2 = self.new()
                    cls.append([-r, p2])
                    if prev is not None:
                        cls.append([-prev, p2])
                    prev = p2
            if not mono:
                extra += isnot
            if K < 0:
                cls.append([])
            elif len(extra) > K:
                enc = CardEnc.atmost(lits=extra, bound=K, top_id=self.nv, encoding=EncType.totalizer)
                self.nv = max(self.nv, enc.nv)
                cls += enc.clauses
        self.nbase = len(cls)
        self.val = {}
        self.s = getattr(S, solver)(bootstrap_with=cls)
        mint = [(1 << a) | (1 << b) for a, b in EDGES]
        maxf = [r for r in range(self.ROWS) if not TR[r]
                and all(TR[r | (1 << v)] for v in range(N) if not (r >> v) & 1)]
        self.rows = []
        rows = sorted(set(mint + maxf + ([] if mono else [0, self.ROWS - 1])))
        if allrows:
            rows = list(range(self.ROWS))
        for r in rows:
            self.add_row(r)
        if distinct:
            assert allrows
            self.add_distinct()

    def new(self):
        self.nv += 1
        return self.nv

    def add_row(self, r):
        N, G, val, s = self.N, self.G, self.val, self.s
        self.rows.append(r)
        for i in range(G):
            val[(i, r)] = self.new()

        def wire(w):
            return bool((r >> w) & 1) if w < N else val[(w - N, r)]

        def add(c):
            res = []
            for x in c:
                if x is True:
                    return
                if x is not False:
                    res.append(x)
            s.add_clause(res)

        def neg(x):
            return (not x) if isinstance(x, bool) else -x

        for i in range(G):
            y = val[(i, r)]
            for o, v in self.opts[i]:
                t, j, k = o
                a = wire(j)
                if t == "not":
                    add([-v, y, a]); add([-v, -y, neg(a)])
                    continue
                b = wire(k)
                if t == "and":
                    add([-v, -y, a]); add([-v, -y, b]); add([-v, y, neg(a), neg(b)])
                else:
                    add([-v, y, neg(a)]); add([-v, y, neg(b)]); add([-v, -y, a, b])
        y = val[(G - 1, r)]
        s.add_clause([y] if self.TRUTH[r] else [-y])

    def add_distinct(self):
        # sound only over all rows: a minimal circuit has no constant gate and no gate
        # equal to an input or to another gate
        val, s, R = self.val, self.s, range(self.ROWS)
        for i in range(self.G):
            col = [val[(i, r)] for r in R]
            s.add_clause(col); s.add_clause([-x for x in col])
            for w in range(self.N):
                s.add_clause([-val[(i, r)] if (r >> w) & 1 else val[(i, r)] for r in R])
            for l in range(i):
                ds = []
                for r in R:
                    d = self.new(); ds.append(d)
                    s.add_clause([-d, val[(i, r)], val[(l, r)]])
                    s.add_clause([-d, -val[(i, r)], -val[(l, r)]])
                s.add_clause(ds)

    def decode(self, model):
        m = set(x for x in model if x > 0)
        return [next(o for o, v in self.opts[i] if v in m) for i in range(self.G)]

    def run(self, deadline=None, seed=0, log=None):
        """CEGAR loop. returns ('SAT', circ) / ('UNSAT', None) / ('TIMEOUT', None)"""
        rng = random.Random(seed)
        it = 0
        while True:
            it += 1
            if deadline:
                rem = deadline - time.time()
                if rem <= 0:
                    return "TIMEOUT", None
                timer = threading.Timer(rem, self.s.interrupt)
                timer.start()
                res = self.s.solve_limited(expect_interrupt=True)
                timer.cancel()
            else:
                res = self.s.solve()
            if res is None:
                return "TIMEOUT", None
            if res is False:
                return "UNSAT", None
            circ = self.decode(self.s.get_model())
            bad = [r for r in range(self.ROWS) if evaluate(self.N, circ, r) != self.TRUTH[r]]
            if not bad:
                return "SAT", circ
            assert not self.mono, "monotone circuit wrong on some row: encoding bug"
            for r in rng.sample(bad, min(len(bad), 2)):
                self.add_row(r)
            if log and (it % 20 == 0):
                log(f"  iter {it} rows={len(self.rows)} bad={len(bad)}")


def fmt(N, circ):
    out = []
    for i, (t, j, k) in enumerate(circ):
        out.append(f"  w{N + i} = {t.upper()}(w{j}" + (f", w{k})" if t != "not" else ")"))
    out.append(f"  output w{N + len(circ) - 1}")
    return "\n".join(out)


def fences(N, G, mono):
    """level profiles: compositions of G ending in 1; level L gates are all read by
    deeper gates (s_L <= 2 * gates deeper); level 1 has at most 2*C(N,2)(+N) gates."""
    res = []
    for cuts in itertools.product([0, 1], repeat=G - 2):
        parts, c = [], 1
        for b in cuts:
            if b:
                parts.append(c); c = 1
            else:
                c += 1
        parts.append(c)
        parts.append(1)
        ok = all(parts[L] <= 2 * sum(parts[L + 1:]) for L in range(len(parts) - 1))
        ok = ok and parts[0] <= 2 * N * (N - 1) // 2 + (0 if mono else N)
        if ok:
            res.append(tuple(parts))
    return res


def worker(job):
    N, EDGES, G, mono, fence, solver, deadline = job
    t0 = time.time()
    e = Enc(N, EDGES, G, mono, list(fence), solver)
    st, circ = e.run(deadline)
    return fence, st, time.time() - t0, circ


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("graph")
    ap.add_argument("G", type=int)
    ap.add_argument("--mono", action="store_true")
    ap.add_argument("--solver", default="Cadical195")
    ap.add_argument("--timeout", type=float, default=0)
    ap.add_argument("--fences", type=int, default=0, help="worker processes for the fence split")
    ap.add_argument("--fence", default="")
    ap.add_argument("--nocard", action="store_true")
    ap.add_argument("--allrows", action="store_true")
    ap.add_argument("--distinct", action="store_true")
    a = ap.parse_args()
    N, EDGES = parse_graph(a.graph)
    t0 = time.time()
    deadline = t0 + a.timeout if a.timeout else None
    head = f"graph={a.graph} N={N} G={a.G} mono={a.mono} solver={a.solver}"
    if a.fences:
        import multiprocessing as mp
        fs = fences(N, a.G, a.mono)
        print(f"{head} fences={len(fs)} workers={a.fences}", flush=True)
        jobs = [(N, EDGES, a.G, a.mono, f, a.solver, deadline) for f in fs]
        done = unsat = 0
        timeouts = []
        with mp.Pool(a.fences) as pool:
            for fence, st, dt, circ in pool.imap_unordered(worker, jobs):
                done += 1
                if st == "UNSAT":
                    unsat += 1
                elif st == "TIMEOUT":
                    timeouts.append(fence)
                if st != "UNSAT" or dt > 30:
                    print(f"  [{done}/{len(fs)} {time.time() - t0:.0f}s] fence {fence}: {st} {dt:.1f}s", flush=True)
                elif done % 100 == 0:
                    print(f"  [{done}/{len(fs)} {time.time() - t0:.0f}s] {unsat} unsat so far", flush=True)
                if st == "SAT":
                    print(f"SAT {time.time() - t0:.1f}s fence={fence}\n{fmt(N, circ)}\n"
                          f"  verified on all {1 << N} rows", flush=True)
                    pool.terminate()
                    return
        if timeouts:
            print(f"TIMEOUT {time.time() - t0:.1f}s: {unsat} fences UNSAT, {len(timeouts)} timed out: {timeouts}", flush=True)
        else:
            print(f"UNSAT {time.time() - t0:.1f}s (all {len(fs)} fences)", flush=True)
        return
    fence = [int(x) for x in a.fence.split(",")] if a.fence else None
    e = Enc(N, EDGES, a.G, a.mono, fence, a.solver, not a.nocard, a.allrows, a.distinct)
    print(f"{head} fence={fence} base_clauses={e.nbase} rows={len(e.rows)} vars={e.nv}", flush=True)
    st, circ = e.run(deadline, log=lambda s: print(s, flush=True))
    print(f"{st} {time.time() - t0:.1f}s rows={len(e.rows)}", flush=True)
    if circ:
        print(fmt(N, circ) + f"\n  verified on all {1 << N} rows", flush=True)


if __name__ == "__main__":
    main()
