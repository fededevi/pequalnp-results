# pequalnp-results

Results and proofs from working on open steps of [pequalnp.com](https://pequalnp.com), the open,
Lean-checked attack on P vs NP. Proofs target
[brilliant-hq/pequalnp-proofs](https://github.com/brilliant-hq/pequalnp-proofs) (Lean 4.36.0, the
Mathlib commit pinned there).

## L-meta-523: no witness exists (exhaustive search)

The step asks for an 11-gate circuit of fan-in-two AND and OR gates for the edge function of the
6-cycle with leaves at two adjacent vertices (edges 01 12 23 34 45 05 06 17, 8 inputs). The circuit must
have one AND gate above another, and no lift may flatten it. A lift takes a non-output gate
OR(p, h) with h implying the function, replaces it by a copy of p and adds OR(output, h) as the new
output.

**Result: no such circuit exists.** An exact SAT enumeration ([`tools/circsat2.py`](tools/circsat2.py),
fence-split, every solution blocked and listed) finds:

| | circuits (up to gate order) |
|---|---|
| all 11-gate AND/OR circuits computing the function (10 gates are impossible) | 518 |
| with an AND gate above another AND gate | 218 |
| flattened by some lift | 218 (all) |
| witnesses | **0** |

- **Lifts never break the function:** every lift whose h implies the function gives a circuit that
  still computes it.
- **Every circuit with stacked ANDs is flattened:**
  - 186 of the 218 have three such lifts, and the best one drops the number of AND-above-AND pairs to 0.
  - The other 32 have two, and the best one lowers the count by one.
- **The total matches the fleet's:** the 518 equals the number of circuits the fleet examined through
  four size-preserving moves, so that search had covered every circuit.

**Files** in [`L-meta-523/`](L-meta-523/):

- [`lift_outcomes.json`](L-meta-523/lift_outcomes.json): every circuit with its pair count and every lift
  `(j, p, h, D computes F, D's pair count)`.
- `all_circuits.jsonl`: all 518 circuits.
- `analysis_verbose.txt`: one line per circuit with stacked ANDs.
- `enum523_all.py`: the enumeration script.
- `analyze.py`: the lift check, written to follow the Lean statement's wording.
- `leantest/`: Lean pieces for evaluation by `decide` and for a decidable TransGen.

## L-gct-210: the 5 × 5 level-space ceiling (≤ 8): routes tried

Notes in [`L-gct-210/theory/NOTES.md`](L-gct-210/theory/NOTES.md) and
[`L-gct-210/routes2/NOTES.md`](L-gct-210/routes2/NOTES.md). Exact facts found:

- **σ₂ (sum of 2 × 2 sub-permanents)** is ½ tᵀ A t with A = (J − I) ⊗ (J − I).
  - It is nondegenerate, with explicit inverse (J/4 − I) ⊗ (J/4 − I).
  - On {σ₁ = 0} it has rank 24 and signature (16, 8), so the isotropic-subspace bound gives only dim ≤ 12.
  - On doubly centred matrices it is a sum of squares, so the bound there is 8. But the reduction to that
    case costs dimension, and the known 7-dimensional spaces meet it only in 0.
- **σ₂ and σ₃ diagonalise after centring.** With row and column sums r and c, put
  s_ij = t_ij − (r_i + c_j)/2. Then:
  - 2σ₂ = Σs² − (n/4)(Σr² + Σc²)
  - σ₃ = ⅔Σs³ + ((n − 2)/12)(Σr³ + Σc³)
- **Routes tried and why each fails:**
  - linear use of σ₃
  - gradient span
  - zero-row induction (no rectangular base is checked)
  - torus degeneration
  - pencils of quadrics
  - the literature

## L-gct-179: a 7-dimensional 4 × 5 level space? (search: none found)

Notes in [`L-gct-179/NOTES.md`](L-gct-179/NOTES.md): a Fourier-graded analysis, exact constraints on the
graded cases, numerical searches (random, masked, symmetric, grown from 6-dimensional solutions). No
7-dimensional space in about 1,600 numerical starts. The best cost was 0.24, against 0 for a witness, while
6-dimensional solutions appear from about 30% of random starts. Exact facts: C^4 ⊗ (1, ζ, …, ζ⁴) is a
4-dimensional level space (ζ a primitive fifth root of unity), and a graded 7-dimensional space must fall
under one of six frequency profiles, all infeasible numerically. Evidence, not proof, that the maximum is 6.

## Proofs written

[`proofs/`](proofs/): Lean proofs, each written for one step, each building against the pinned
toolchain with axioms only `propext`, `Classical.choice`, `Quot.sound`. None was merged: the steps were
proved first by others, or stood down.

| step | statement |
|---|---|
| L-meta-491 | index arithmetic bound |
| L-meta-497 | the placed cover graph's member list has no repeats |
| L-meta-535 | every nested cover circuit has \|A\| + \|E\| + t − 1 gates |
| L-meta-238, 240, 241, 242 | circuit sizes over all two-input gates (xor, constants, monotone bound) |

## Machine toolkit

[`kit/Kit.lean`](kit/Kit.lean) is the project's `PEqualNP.Library.Machines` (composition, bounded
iteration, pairing, constants, clocks) as one file.

- **Imports:** only `Mathlib` and `PEqualNP.Defs`.
- **Plain-file rules:** it passes the repository's guard.
- **Use:** a `ComputableInPolyTime` step can paste it in.
- **Licence and origin:** Apache-2.0, derived from brilliant-hq/pequalnp-proofs; see
  [`kit/README.md`](kit/README.md) and [`kit/LICENSE`](kit/LICENSE).

## Tools

[`tools/circsat2.py`](tools/circsat2.py) is exact synthesis of small AND/OR(/NOT) circuits with
python-sat. It uses symmetry breaking, a fence split (gates per depth level) and solution enumeration.
`tools/circsat.py` is the first, plain encoding.
