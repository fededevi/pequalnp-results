import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

def isAndB : GateOp → Bool
  | GateOp.and => true
  | _ => false

lemma isAndB_iff (o : GateOp) : o = GateOp.and ↔ isAndB o = true := by
  cases o <;> simp [isAndB]

def relB (gs : List Gate) (u v : ℕ) : Bool :=
  match gs[u]? with
  | some g => decide (8 + v ∈ g.inputs)
  | none => false

lemma rel_iff (gs : List Gate) (u v : ℕ) :
    (∃ g : Gate, gs[u]? = some g ∧ 8 + v ∈ g.inputs) ↔ relB gs u v = true := by
  unfold relB
  cases gs[u]? <;> simp

def reachB (gs : List Gate) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | n + 1, a, b => relB gs a b || (List.range a).any (fun c => relB gs a c && reachB gs n c b)

lemma reachB_mono (gs : List Gate) : ∀ n m a b, n ≤ m → reachB gs n a b = true → reachB gs m a b = true := by
  intro n
  induction n with
  | zero => intro m a b _ h; simp [reachB] at h
  | succ n ih =>
    intro m a b hnm h
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [reachB, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true] at h ⊢
    rcases h with h | ⟨c, hc, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, h1, ih m c b (by omega) h2⟩

lemma reachB_sound (gs : List Gate) : ∀ n a b, reachB gs n a b = true →
    Relation.TransGen (fun u v : ℕ => ∃ g : Gate, gs[u]? = some g ∧ 8 + v ∈ g.inputs) a b := by
  intro n
  induction n with
  | zero => intro a b h; simp [reachB] at h
  | succ n ih =>
    intro a b h
    simp only [reachB, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true] at h
    rcases h with h | ⟨c, _, h1, h2⟩
    · exact Relation.TransGen.single ((rel_iff gs a b).2 h)
    · exact Relation.TransGen.head ((rel_iff gs a c).2 h1) (ih c b h2)

lemma reachB_complete (gs : List Gate) (hg : ∀ u v, relB gs u v = true → v < u) (a b : ℕ)
    (h : Relation.TransGen (fun u v : ℕ => ∃ g : Gate, gs[u]? = some g ∧ 8 + v ∈ g.inputs) a b) :
    reachB gs (a + 1) a b = true := by
  induction h using Relation.TransGen.head_induction_on with
  | single h =>
    simp [reachB, (rel_iff _ _ _).1 h]
  | @head a c h _ ih =>
    have hr := (rel_iff _ _ _).1 h
    have hca := hg _ _ hr
    simp only [reachB, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true]
    exact Or.inr ⟨c, hca, hr, reachB_mono gs _ _ _ _ (by omega) ih⟩

lemma tg_iff (gs : List Gate) (hg : ∀ u v, relB gs u v = true → v < u) (a b : ℕ) :
    Relation.TransGen (fun u v : ℕ => ∃ g : Gate, gs[u]? = some g ∧ 8 + v ∈ g.inputs) a b ↔
      reachB gs (a + 1) a b = true :=
  ⟨reachB_complete gs hg a b, reachB_sound gs _ a b⟩

def andB (gs : List Gate) (u : ℕ) : Bool :=
  match gs[u]? with
  | some g => isAndB g.op
  | none => false

lemma and_iff (gs : List Gate) (u : ℕ) :
    (∃ g : Gate, gs[u]? = some g ∧ g.op = GateOp.and) ↔ andB gs u = true := by
  unfold andB
  cases gs[u]? <;> simp [isAndB_iff]

lemma relB_lt (gs : List Gate) (u v : ℕ) (h : relB gs u v = true) : u < gs.length := by
  unfold relB at h
  rcases hu : gs[u]? with _ | g
  · simp [hu] at h
  · exact (List.getElem?_eq_some_iff.1 hu).1

lemma andB_lt (gs : List Gate) (u : ℕ) (h : andB gs u = true) : u < gs.length := by
  unfold andB at h
  rcases hu : gs[u]? with _ | g
  · simp [hu] at h
  · exact (List.getElem?_eq_some_iff.1 hu).1

lemma pairs_eq (gs : List Gate) (hg : ∀ u v, relB gs u v = true → v < u) :
    {q : ℕ × ℕ | q.1 ≠ q.2 ∧ (∃ g : Gate, gs[q.1]? = some g ∧ g.op = GateOp.and) ∧
      (∃ g : Gate, gs[q.2]? = some g ∧ g.op = GateOp.and) ∧
      Relation.TransGen (fun u v : ℕ => ∃ g : Gate, gs[u]? = some g ∧ 8 + v ∈ g.inputs) q.1 q.2} =
    ↑(((Finset.range gs.length) ×ˢ (Finset.range gs.length)).filter
      (fun q => q.1 ≠ q.2 ∧ andB gs q.1 = true ∧ andB gs q.2 = true ∧ reachB gs (q.1 + 1) q.1 q.2 = true)) := by
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_product, Finset.mem_range,
    and_iff, tg_iff gs hg]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨andB_lt gs a h2, andB_lt gs b h3⟩, h1, h2, h3, h4⟩
  · rintro ⟨_, h⟩
    exact h

def tG : List Gate := [⟨GateOp.or, [1,5]⟩, ⟨GateOp.or, [8,6]⟩, ⟨GateOp.and, [0,9]⟩, ⟨GateOp.or, [2,7]⟩,
  ⟨GateOp.and, [1,11]⟩, ⟨GateOp.or, [2,4]⟩, ⟨GateOp.and, [3,13]⟩, ⟨GateOp.and, [4,5]⟩,
  ⟨GateOp.or, [10,12]⟩, ⟨GateOp.or, [14,15]⟩, ⟨GateOp.or, [16,17]⟩]

lemma tG_good : ∀ u v, relB tG u v = true → v < u := by
  intro u v h
  have hu := relB_lt tG u v h
  simp only [tG, List.length_cons, List.length_nil] at hu
  interval_cases u <;> simp [relB, tG] at h <;> omega

example : Set.ncard {q : ℕ × ℕ | q.1 ≠ q.2 ∧ (∃ g : Gate, tG[q.1]? = some g ∧ g.op = GateOp.and) ∧
      (∃ g : Gate, tG[q.2]? = some g ∧ g.op = GateOp.and) ∧
      Relation.TransGen (fun u v : ℕ => ∃ g : Gate, tG[u]? = some g ∧ 8 + v ∈ g.inputs) q.1 q.2} = 0 := by
  rw [pairs_eq tG tG_good, Set.ncard_coe_finset]
  decide
