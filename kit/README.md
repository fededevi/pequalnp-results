# Kit: the machine library as one plain step file

`Kit.lean` is the project's machine library (brilliant-hq/pequalnp-proofs,
`lean/PEqualNP/Library/Machines`, Apache-2.0) inlined into one file under the namespace
`PEqualNP.Outside.Kit`. It imports only `Mathlib` and `PEqualNP.Defs` and passes the
plain-file rule of `.github/scripts/outside-guard.mjs` (no comments, no quotes, no `#`, no
`inductive`/`instance`/`structure`, no attributes except `@[simp]`). 5340 lines, 241 KB
(the step limit is 512 KiB); about 30 s to elaborate. Only the standard axioms.

Inlined, in import order: Run, Compose, ComposeRun, ComposeTime, FilterMap, TwoPass, First,
FirstRun, FirstPoly, Pairing, Mul, Clock, FirstTime, Iter, IterRun, IterMeasure, ConstList,
Const, Reverse, LenLE, ReduceNP, AllTrue, SquareClock, Transducer, FirstG, FirstGRun, ExpPad.
Left out: NormalForm (imports `PEqualNP.Library.L055`).

Changes from the source: comments and imports stripped; namespace renamed; the enum
`inductive` types with their `Fintype` instances (FX, FL, IX, IL, TPK, TPL, MulK, MulL, LL,
TrK, PadK, PadL, Gen.FX, Gen.FL) became `abbrev T : Type := Fin n`, constructors became
typed literals `(i : T)`, and their `cases` proofs became `fin_cases`; `@[reducible] def`
became `abbrev`; the `local notation stp` was expanded in place.

## Use in a step

Paste `Kit.lean` below the step's imports (drop its two import lines), then prove the step's
theorem with `open PEqualNP.Library PEqualNP.Outside.Kit`. To keep names unique per step,
regenerate with the step's namespace (see below), e.g. `PEqualNP.Outside.L_gct_200.Kit`.
Unused modules can be cut from `MODULES` in the generator to shrink the file.

`ComputableInPolyTime ea eb f` is by definition `Nonempty (Turing.TM2ComputableInPolyTime ea eb f)`,
so the `Nonempty ...` lemmas below prove it directly. `KitUse.lean` is the check that the API
works: `cpt_comp cpt_dup cpt_append` proves `x ↦ x ++ x` polynomial-time.

Below `id` is `(fun x : List Bool => x)`, `CPT` is `PEqualNP.Library.ComputableInPolyTime`,
`TM2CPT` is `Turing.TM2ComputableInPolyTime`, `CIT` is `PEqualNP.Library.ComputableInTime`.

Namespace `PEqualNP.Outside.Kit`:

- `cpt_comp (hf : CPT ea eb f) (hg : CPT eb ec g) : CPT ea ec (fun a => g (f a))`
- `cpt_id : CPT id id (fun x => x)`
- `cpt_dup : CPT id encodePair (fun x => (x, x))`
- `cpt_swap : CPT encodePair encodePair (fun p => (p.2, p.1))`
- `cpt_fst`, `cpt_snd : CPT encodePair id (fun p => p.1)` / `(fun p => p.2)`
- `cpt_append : CPT encodePair id (fun p => p.1 ++ p.2)`
- `cpt_first (hf : CPT id id f) : CPT encodePair encodePair (fun p => (f p.1, p.2))`; `cpt_second` likewise on `p.2`
- `cpt_pair (hf : CPT id id f) (hg : CPT id id g) : CPT id encodePair (fun x => (f x, g x))`
- `comp_polyTime ea eb ec f g (c1 : TM2CPT ea eb f) (c2 : TM2CPT eb ec g) : Nonempty (TM2CPT ea ec (g ∘ f))`
- `filterMap_polyTime [Fintype αΓ] ea eb f (φ : αΓ → Option βΓ) (h : ∀ a, eb (f a) = (ea a).filterMap φ) : Nonempty (TM2CPT ea eb f)`
- `twoPass_polyTime [Fintype αΓ] ea eb f φ₁ φ₂ (h : ∀ a, eb (f a) = (ea a).filterMap φ₁ ++ (ea a).filterMap φ₂) : Nonempty (TM2CPT ea eb f)`
- `fst_polyTime [Fintype αΓ] [Fintype Q] ea eb f δ fin q₀ (h : ∀ a, eb (f a) = fstRun δ fin q₀ (ea a)) : Nonempty (TM2CPT ea eb f)` (a finite-state transducer)
- `first_polyTime f (c : TM2CPT id id f) : Nonempty (TM2CPT encodePair encodePair (fun p => (f p.1, p.2)))`
- `constList_polyTime (l) : Nonempty (TM2CPT id id (fun _ => l))`; `constBoolComputable b : TM2CPT id Computability.encodeBool (fun _ => b)`
- `Rev.reverseComputable : TM2CPT id id (fun x => x.reverse)`
- `mul_polyTime : Nonempty (TM2CPT encodePair id (fun p => List.replicate (p.1.length * p.2.length) true))`
- `clock_polyTime (hconst : ∀ l, CPT id id (fun _ => l)) (p : Polynomial ℕ) : CPT id id (fun x => List.replicate (p.eval x.length) true)`
- `allTrue_polyTime : Nonempty (TM2CPT encodePair Computability.encodeBool (fun p => (p.1 ++ p.2).all id))`
- `output_length_poly f (hf : CPT id id f) : ∃ q : Polynomial ℕ, ∀ x, (f x).length ≤ q.eval x.length`
- time bounds: `comp_time`, `time_of_polyTime (h : CPT ea eb f) : ∃ p, CIT ea eb f (p.eval ·)`, `clockPair_time`, `dup_time`, `mul_time`, `square_time`

Namespace `PEqualNP.Outside.Kit.Iter`:

- `iter_polyTime g (c : TM2CPT id id g) (k) (hk : ∀ y, (g y).length ≤ y.length + k) : Nonempty (TM2CPT encodePair id (fun p => g^[p.2.length] p.1))`
- `iter_polyTime_measure g c (m : List Bool → ℕ) (a) (hm : ∀ y, m (g y) ≤ m y) (hg : ∀ y, (g y).length ≤ y.length + m y) (ha : ∀ y, m y ≤ a * y.length + a) : Nonempty (TM2CPT encodePair id (fun p => g^[p.2.length] p.1))`

Others: `LenCmp.lenLE_polyTime : Nonempty (TM2CPT encodePair Computability.encodeBool (fun p => decide (p.2.length ≤ p.1.length)))`;
`Gen.first_polyTime` (first component over any alphabets, `gpair`); `ExpPad.expPad_time`.

## Regenerate

From a clone of pequalnp-proofs:

    python gen_kit.py <clone>/lean/PEqualNP/Library/Machines Kit.lean [namespace]
    node check_plain.mjs <clone>/.github/scripts/outside-guard.mjs Kit.lean

`check_plain.mjs` runs the guard's own `checkImports` (import rule and plain-file rule) on
the file. To build, put the file under `lean/PEqualNP/Outside/` in the clone and run
`lake build PEqualNP.Outside.<Name>`. If the library changes, a new enum or a new
`cases` proof on an enum is the likely thing to add to `ENUMS`/`ENUM_USERS` in the generator.
