import sys, json, collections
sys.path.insert(0, r"./L-meta-523")
sys.path.insert(0, r"./tools")
import enum523 as E
tot = 0; nA = 0; outcomes = collections.Counter(); wit = []
fences_done = 0
for line in open(r"./L-meta-523/all_circuits.jsonl"):
    d = json.loads(line); fences_done += 1
    for gates in d["circs"]:
        tot += 1
        gates = [(t, ins) for t, ins in gates]
        if E.pairs(gates) == 0:
            continue
        nA += 1
        c0 = E.pairs(gates)
        lifts = []
        for j, (t, ins) in enumerate(gates):
            if t != "or" or j == 10: continue
            a, b = ins
            for p, h in {(a, b), (b, a)}:
                if not E.implies_F(gates, h): continue
                D = list(gates); D[j] = ("or", [p, p]); D.append(("or", [18, h]))
                ok = E.computes(D, 19); cD = E.pairs(D)
                lifts.append((j, p, h, ok, cD))
        flat = [l for l in lifts if l[3] and l[4] < c0]
        key = ("flattened" if flat else "WITNESS", len(lifts), sum(1 for l in lifts if l[3]))
        outcomes[key] += 1
        if not flat: wit.append(gates)
        if "-v" in sys.argv:
            print(c0, gates, lifts)
print("fences", fences_done, "circuits", tot, "with A", nA)
for k, v in sorted(outcomes.items()): print(" ", k, v)
print("witnesses", len(wit))
for w in wit: print(json.dumps(w))
