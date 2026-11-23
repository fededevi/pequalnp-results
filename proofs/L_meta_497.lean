import Mathlib
import PEqualNP.Defs

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

theorem l497_off_succ (φ : CNF) (i : ℕ) (hi : i < φ.length) :
    ((φ.take (i+1)).map (fun c => c.length + 1)).sum =
      ((φ.take i).map (fun c => c.length + 1)).sum + (φ.getD i []).length + 1 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.map_append, List.sum_append]
  simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  omega

theorem l497_off_mono (φ : CNF) {i i' : ℕ} (h : i ≤ i') :
    ((φ.take i).map (fun c => c.length + 1)).sum ≤
      ((φ.take i').map (fun c => c.length + 1)).sum := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.map_append, List.sum_append]
  omega

theorem l497_clause_le (c : Clause) : c.length + 1 ≤ (encodeClause c).length := by
  unfold encodeClause
  induction c with
  | nil => simp
  | cons l c ih => simp [List.flatMap_cons, encodeLiteral] at ih ⊢; omega

theorem l497_sum_le (φ : CNF) :
    (φ.map (fun c => c.length + 1)).sum ≤ (encodeCNF φ).length := by
  unfold encodeCNF
  induction φ with
  | nil => simp
  | cons c φ ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
    have := l497_clause_le c
    omega

theorem l497_off_le (φ : CNF) (i : ℕ) :
    ((φ.take i).map (fun c => c.length + 1)).sum ≤ (encodeCNF φ).length := by
  calc _ ≤ ((φ.take (i + φ.length)).map (fun c => c.length + 1)).sum :=
        l497_off_mono φ (by omega)
    _ = (φ.map (fun c => c.length + 1)).sum := by rw [List.take_of_length_le (by omega)]
    _ ≤ _ := l497_sum_le φ

theorem l497_flat (φ : CNF) (p : ℕ) (l : Literal)
    (h : (φ.flatMap (fun c => c.map some ++ [none]))[p]? = some (some l)) :
    ∃ i < φ.length, ∃ j < (φ.getD i []).length,
      p = ((φ.take i).map (fun c => c.length + 1)).sum + j ∧ (φ.getD i [])[j]? = some l := by
  induction φ generalizing p with
  | nil => simp at h
  | cons c φ ih =>
    rw [List.flatMap_cons] at h
    by_cases hp : p < c.length + 1
    · rw [List.getElem?_append_left (by simp; omega)] at h
      by_cases hp' : p < c.length
      · rw [List.getElem?_append_left (by simpa using hp')] at h
        refine ⟨0, by simp, p, by simpa using hp', by simp, ?_⟩
        simp only [List.getElem?_map, Option.map_eq_some_iff, Option.some.injEq] at h
        obtain ⟨a, ha, rfl⟩ := h
        simpa using ha
      · rw [List.getElem?_append_right (by simp; omega)] at h
        have : p - (List.map some c).length = 0 := by simp; omega
        rw [this] at h
        simp at h
    · rw [List.getElem?_append_right (by simp; omega)] at h
      obtain ⟨i, hi, j, hj, hp2, hl⟩ := ih _ h
      refine ⟨i+1, by simp; omega, j, by simpa using hj, ?_, by simpa using hl⟩
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      simp only [List.length_append, List.length_map, List.length_singleton] at hp2
      omega

theorem l497_cvc_lt (φ : CNF) (i : ℕ) (hi : i < φ.length) :
    (cvcFormula φ).getD i [] = φ.getD i [] ++ [(fresh φ, true)] := by
  unfold cvcFormula
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi)]
  simp [List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD]

theorem l497_cvc_eq (φ : CNF) : (cvcFormula φ).getD φ.length [] = [(fresh φ, false)] := by
  simp [cvcFormula, List.getD_eq_getElem?_getD]

theorem l497_cvc_gt (φ : CNF) (i : ℕ) (hi : φ.length < i) : (cvcFormula φ).getD i [] = [] := by
  simp [cvcFormula, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none]
  · simp
  · simp; omega

theorem l497_vars_cvc (φ : CNF) (z : ℕ) :
    z ∈ vars (cvcFormula φ) ↔ z ∈ vars φ ∨ z = fresh φ := by
  simp only [vars, cvcFormula, List.mem_toFinset, List.mem_flatMap, List.mem_append,
    List.mem_map, List.mem_singleton]
  constructor
  · rintro ⟨c, hc, a, ha, rfl⟩
    rcases hc with ⟨c', hc', rfl⟩ | rfl
    · simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact Or.inl ⟨c', hc', a, ha, rfl⟩
      · exact Or.inr rfl
    · simp at ha; subst ha; exact Or.inr rfl
  · rintro (⟨c, hc, a, ha, rfl⟩ | rfl)
    · exact ⟨c ++ [(fresh φ, true)], Or.inl ⟨c, hc, rfl⟩, a, by simp [ha], rfl⟩
    · exact ⟨[(fresh φ, false)], Or.inr rfl, (fresh φ, false), by simp, rfl⟩

theorem l497_var_mem (φ : CNF) (i j : ℕ) (a : Literal) (h : (φ.getD i [])[j]? = some a) :
    a.1 ∈ vars φ := by
  simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map]
  rw [List.getD_eq_getElem?_getD] at h
  rcases hi : φ[i]? with _ | c
  · rw [hi] at h; simp at h
  · rw [hi] at h
    simp only [Option.getD_some] at h
    exact ⟨c, List.mem_of_getElem? hi, a, List.mem_of_getElem? h, rfl⟩

theorem l497_dec (N k u v t : ℕ) (hv : v < N) (ht : t < 2 * k) :
    (N + 2 * k * (u * N + v) + t - N) / (2 * k) / N = u ∧
      (N + 2 * k * (u * N + v) + t - N) / (2 * k) % N = v := by
  have hk : 0 < 2 * k := by omega
  have h1 : (N + 2 * k * (u * N + v) + t - N) / (2 * k) = u * N + v := by
    rw [show N + 2 * k * (u * N + v) + t - N = t + 2 * k * (u * N + v) by omega,
      Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt ht, zero_add]
  rw [h1]
  constructor
  · rw [show u * N + v = v + N * u by ring, Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt hv, zero_add]
  · rw [show u * N + v = v + N * u by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]

theorem l497_nodup_flatMap {α β : Type} (L : List α) (F : α → List β) (hL : L.Nodup)
    (hF : ∀ a ∈ L, (F a).Nodup) (hd : ∀ a ∈ L, ∀ b ∈ L, ∀ x ∈ F a, x ∈ F b → a = b) :
    (L.flatMap F).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨hF, hL.pairwise_of_forall_ne fun a ha b hb hab => ?_⟩
  intro x hxa hxb
  exact hab (hd a ha b hb x hxa hxb)

theorem l497_mem_ite {p : Prop} [Decidable p] {x : ℕ} {l : List ℕ} :
    x ∈ (if p then l else []) ↔ p ∧ x ∈ l := by
  split_ifs <;> simp_all

theorem l497_par (t : ℕ) (b : Bool) : (((t % 2 == 1) == b) = true) ↔ (t % 2 = 1 ↔ b = true) := by
  cases b <;> simp

theorem l497_nodup_app (D : ℕ → ℕ) (m : ℕ) {l1 l2 : List ℕ} (h1 : l1.Nodup ∧ ∀ x ∈ l1, D x < m)
    (h2 : l2.Nodup) (hd2 : ∀ x ∈ l2, D x = m) :
    (l1 ++ l2).Nodup ∧ ∀ x ∈ l1 ++ l2, D x < m + 1 := by
  refine ⟨List.nodup_append.2 ⟨h1.1, h2, ?_⟩, ?_⟩
  · intro a ha b hb hab
    subst hab
    have := h1.2 a ha
    have := hd2 a hb
    omega
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · have := h1.2 x hx; omega
    · have := hd2 x hx; omega

theorem PEqualNP.Outside.L_meta_497 : ∀ k : ℕ, ∀ (φ : PEqualNP.Search.CNF) (E N : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length → N = 3 * (E + 1) → (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') → (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∃ l : PEqualNP.Search.Literal, (φ.flatMap (fun c => c.map some ++ [none]))[e z]? = some (some l) ∧ l.1 = z) → ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ, (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool, num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) → (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) = 2 * E + (if b then 1 else 0)) → (∀ i j, i < φ.length → j ≤ (φ.getD i []).length → num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) → num (Sum.inr (φ.length, 0)) = 3 * E + 2 → ∀ H : SimpleGraph (Fin N), (∀ a b : Fin N, H.Adj a b ↔ ∃ u v, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ (f : ℕ → ℕ), (∀ i, f i = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).findIdx (fun l => l.2)) → ∀ TH : ℕ → Prop, (∀ a, TH a ↔ ((∃ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, a = 2 * e z + 1) ∨ a = 2 * E + 1 ∨ (∃ i < φ.length, ∃ j ≤ (φ.getD i []).length, j ≠ f i ∧ a = 2 * (E + 1) + off i + j) ∨ a = 3 * E + 2)) → ∀ lit : ℕ → ℕ → PEqualNP.Search.Literal, (∀ i j, lit i j = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).getD j (0, false)) → ∀ inner : ℕ → ℕ → Bool → List ℕ, (∀ u v b, inner u v b = ((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map (fun t => N + 2 * k * (u * N + v) + t)) → ∀ TL : List ℕ, TL = (List.range φ.length).flatMap (fun i => (List.range ((φ.getD i []).length + 1)).flatMap (fun j => inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++ ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false else []) ++ (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then [num (Sum.inl ((lit i j).1, true))] else []))) ++ (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++ inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++ [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)), num (Sum.inr (φ.length, 0))]) → TL.Nodup ∧ ∀ x : ℕ, x ∈ TL ↔ (TH x ∨ ∃ u v : Fin N, u < v ∧ H.Adj u v ∧ ∃ t < 2 * k, x = N + 2 * k * (u.val * N + v.val) + t ∧ (t % 2 = 1 ↔ TH u.val)) := by
  intro k φ E N off e hE hN hoff he_lt he_inj he_pos num hnl hnf hno hnlast H hH f hf TH hTH
    lit hlit inner hinner TL hTL
  have hoffs : ∀ i, i < φ.length → off (i+1) = off i + (φ.getD i []).length + 1 := by
    intro i hi; rw [hoff, hoff]; exact l497_off_succ φ i hi
  have hoffE : ∀ i, i < φ.length → off i + (φ.getD i []).length + 1 ≤ E := by
    intro i hi; rw [← hoffs i hi, hoff, hE]; exact l497_off_le φ (i+1)
  have hoffm : ∀ i i', i ≤ i' → off i ≤ off i' := by
    intro i i' h; rw [hoff, hoff]; exact l497_off_mono φ h
  have hoffinj : ∀ i i' j j', i < φ.length → i' < φ.length → j ≤ (φ.getD i []).length →
      j' ≤ (φ.getD i' []).length → off i + j = off i' + j' → i = i' ∧ j = j' := by
    intro i i' j j' hi hi' hj hj' h
    rcases lt_trichotomy i i' with h1 | rfl | h1
    · have := hoffm (i+1) i' h1; have := hoffs i hi; omega
    · omega
    · have := hoffm (i'+1) i h1; have := hoffs i' hi'; omega
  have hlitlt : ∀ i j, j < (φ.getD i []).length → (φ.getD i [])[j]? = some (lit i j) := by
    intro i j hj
    rw [hlit]
    generalize φ.getD i [] = c at hj ⊢
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
  have hlitlast : ∀ i, lit i (φ.getD i []).length = (fresh φ, true) := by
    intro i; rw [hlit]
    generalize φ.getD i [] = c
    simp [List.getD_eq_getElem?_getD]
  have hcvc : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      ((cvcFormula φ).getD i [])[j]? = some (lit i j) := by
    intro i j hi hj
    rw [l497_cvc_lt φ i hi, hlit]
    generalize φ.getD i [] = c at hj ⊢
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
    rfl
  have hvar : ∀ i j, j < (φ.getD i []).length → (lit i j).1 ∈ vars φ :=
    fun i j hj => l497_var_mem φ i j _ (hlitlt i j hj)
  have hTHlit : ∀ z ∈ vars φ, ∀ b : Bool, (TH (2 * e z + (if b then 1 else 0)) ↔ b = true) := by
    intro z hz b
    rw [hTH]
    have := he_lt z hz
    cases b
    · simp only [Bool.false_eq_true, ite_false, add_zero, iff_false]
      rintro (⟨z', hz', h⟩ | h | ⟨i, hi, j, hj, -, h⟩ | h) <;> omega
    · simp only [ite_true, iff_true]; exact Or.inl ⟨z, hz, rfl⟩
  have hTHfr : ∀ b : Bool, (TH (2 * E + (if b then 1 else 0)) ↔ b = true) := by
    intro b
    rw [hTH]
    cases b
    · simp only [Bool.false_eq_true, ite_false, add_zero, iff_false]
      rintro (⟨z', hz', h⟩ | h | ⟨i, hi, j, hj, -, h⟩ | h) <;> omega
    · simp only [ite_true, iff_true]; exact Or.inr (Or.inl (by simp))
  have hTHocc : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      (TH (2 * (E + 1) + off i + j) ↔ j ≠ f i) := by
    intro i j hi hj
    rw [hTH]
    constructor
    · rintro (⟨z, hz, h⟩ | h | ⟨i', hi', j', hj', hne, h⟩ | h)
      · have := he_lt z hz; omega
      · omega
      · obtain ⟨rfl, rfl⟩ := hoffinj i i' j j' hi hi' hj hj' (by omega); exact hne
      · have := hoffE i hi; omega
    · intro hne; exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj, hne, rfl⟩))
  have hTHlast : TH (3 * E + 2) := (hTH _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hnumlit : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      num (Sum.inl (lit i j)) < 2 * E + 2 ∧
        (TH (num (Sum.inl (lit i j))) ↔ (lit i j).2 = true) := by
    intro i j hi hj
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · have hz := hvar i j hj
      generalize lit i j = a at hz ⊢
      obtain ⟨z, b⟩ := a
      rw [hnl z hz b]
      have := he_lt z hz
      refine ⟨by split_ifs <;> omega, hTHlit z hz b⟩
    · rw [hlitlast, hnf]
      exact ⟨by simp, hTHfr true⟩
  have hinmem : ∀ u v b x, x ∈ inner u v b ↔
      ∃ t < 2 * k, (t % 2 = 1 ↔ b = true) ∧ x = N + 2 * k * (u * N + v) + t := by
    intro u v b x
    rw [hinner]
    simp only [List.mem_map, List.mem_filter, List.mem_range, l497_par]
    constructor
    · rintro ⟨t, ⟨ht, hb⟩, rfl⟩
      exact ⟨t, ht, hb, rfl⟩
    · rintro ⟨t, ht, hb, rfl⟩
      exact ⟨t, ⟨ht, hb⟩, rfl⟩
  have hedge : ∀ (U V : Vertex) (b : Bool) (x : ℕ), (cvcGraph φ).Adj U V → num U < num V →
      num V < N → (b = true ↔ TH (num U)) → x ∈ inner (num U) (num V) b →
      (TH x ∨ ∃ u v : Fin N, u < v ∧ H.Adj u v ∧ ∃ t < 2 * k,
        x = N + 2 * k * (u.val * N + v.val) + t ∧ (t % 2 = 1 ↔ TH u.val)) := by
    intro U V b x hadj huv hvN hb hx
    rw [hinmem] at hx
    obtain ⟨t, ht, hpar, rfl⟩ := hx
    right
    refine ⟨⟨num U, by omega⟩, ⟨num V, hvN⟩, Fin.mk_lt_mk.2 huv,
      (hH _ _).2 ⟨U, V, hadj, rfl, rfl⟩, t, ht, rfl, ?_⟩
    rw [hpar, hb]
  have hEN : 3 * E + 2 < N := by omega
  have hmem : ∀ x, x ∈ TL ↔ (TH x ∨ ∃ u v : Fin N, u < v ∧ H.Adj u v ∧ ∃ t < 2 * k,
        x = N + 2 * k * (u.val * N + v.val) + t ∧ (t % 2 = 1 ↔ TH u.val)) := by
    intro x
    rw [hTL]
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_filter,
      decide_eq_true_eq, l497_mem_ite, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc]
    constructor
    · rintro (⟨i, hi, j, hj, h1 | ⟨l, ⟨hl, hjl⟩, h2⟩ | ⟨⟨hjlen, hz⟩, h3⟩ | ⟨hjf, h4⟩ |
        ⟨⟨hjlen, hz⟩, h5⟩⟩ | h6 | h7 | h8 | h9)
      · have hl := hnumlit i j hi (by omega)
        have hno' := hno i j hi (by omega)
        have hoE := hoffE i hi
        refine hedge (Sum.inl (lit i j)) (Sum.inr (i, j)) _ x ?_ (by omega) (by omega) hl.2.symm h1
        show ((cvcFormula φ).getD i [])[j]? = some (lit i j)
        exact hcvc i j hi (by omega)
      · have hoE := hoffE i hi
        refine hedge (Sum.inr (i, j)) (Sum.inr (i, l)) _ x ?_ ?_ ?_ ?_ h2
        · show i = i ∧ j ≠ l ∧ j < ((cvcFormula φ).getD i []).length ∧
            l < ((cvcFormula φ).getD i []).length
          rw [l497_cvc_lt φ i hi]
          simp only [List.length_append, List.length_singleton]
          exact ⟨trivial, by omega, by omega, by omega⟩
        · rw [hno i j hi (by omega), hno i l hi (by omega)]; omega
        · rw [hno i l hi (by omega)]; omega
        · rw [hno i j hi (by omega), hTHocc i j hi (by omega)]; simp
      · have hzv := hvar i j hjlen
        refine hedge (Sum.inl ((lit i j).1, false)) (Sum.inl ((lit i j).1, true)) false x
          ?_ ?_ ?_ ?_ h3
        · show ((lit i j).1, false).1 = ((lit i j).1, true).1 ∧
            ((lit i j).1, false).2 ≠ ((lit i j).1, true).2 ∧
            ((lit i j).1, false).1 ∈ vars (cvcFormula φ)
          exact ⟨rfl, by simp, (l497_vars_cvc φ _).2 (Or.inl hzv)⟩
        · rw [hnl _ hzv, hnl _ hzv]; simp
        · rw [hnl _ hzv]; have := he_lt _ hzv; simp; omega
        · rw [hnl _ hzv, hTHlit _ hzv false]
      · left; rw [h4, hno i j hi (by omega)]; exact (hTHocc i j hi (by omega)).2 hjf
      · left; rw [h5, hnl _ (hvar i j hjlen)]; exact (hTHlit _ (hvar i j hjlen) true).2 rfl
      · refine hedge (Sum.inl (fresh φ, false)) (Sum.inl (fresh φ, true)) false x ?_ ?_ ?_ ?_ h6
        · show (fresh φ, false).1 = (fresh φ, true).1 ∧ (fresh φ, false).2 ≠ (fresh φ, true).2 ∧
            (fresh φ, false).1 ∈ vars (cvcFormula φ)
          exact ⟨rfl, by simp, (l497_vars_cvc φ _).2 (Or.inr rfl)⟩
        · rw [hnf, hnf]; simp
        · rw [hnf]; simp; omega
        · rw [hnf, hTHfr false]
      · refine hedge (Sum.inl (fresh φ, false)) (Sum.inr (φ.length, 0)) false x ?_ ?_ ?_ ?_ h7
        · show ((cvcFormula φ).getD φ.length [])[0]? = some (fresh φ, false)
          rw [l497_cvc_eq]; rfl
        · rw [hnf, hnlast]; simp; omega
        · rw [hnlast]; omega
        · rw [hnf, hTHfr false]
      · left; rw [h8, hnf]; exact (hTHfr true).2 rfl
      · left; rw [h9, hnlast]; exact hTHlast
    · rintro (hx | ⟨u, v, huv, hadj, t, ht, rfl, hpar⟩)
      · rw [hTH] at hx
        rcases hx with ⟨z, hz, rfl⟩ | rfl | ⟨i, hi, j, hj, hne, rfl⟩ | rfl
        · obtain ⟨l, hl, hl1⟩ := he_pos z hz
          obtain ⟨i, hi, j, hj, hp, hij⟩ := l497_flat φ _ _ hl
          rw [← hoff i] at hp
          have hli : lit i j = l := by
            have := hlitlt i j hj; rw [this] at hij; exact Option.some.inj hij
          refine Or.inl ⟨i, hi, j, by omega, Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨hj, ?_⟩, ?_⟩)))⟩
          · rw [hli, hl1]; omega
          · rw [hli, hl1, hnl z hz true]; simp
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hnf]; simp))))
        · refine Or.inl ⟨i, hi, j, by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, ?_⟩)))⟩
          rw [hno i j hi hj]
        · exact Or.inr (Or.inr (Or.inr (Or.inr hnlast.symm)))
      · obtain ⟨U, V, hUV, hU, hV⟩ := (hH u v).1 hadj
        have huv' : u.val < v.val := huv
        have hvN := v.isLt
        rcases U with ⟨z, b⟩ | ⟨i, j⟩ <;> rcases V with ⟨z', b'⟩ | ⟨i', j'⟩
        · obtain ⟨hzz, hbb, hzv⟩ : z = z' ∧ b ≠ b' ∧ z ∈ vars (cvcFormula φ) := hUV
          subst hzz
          rcases (l497_vars_cvc φ z).1 hzv with hz | hz
          · cases b <;> cases b'
            · exact absurd rfl hbb
            · obtain ⟨l, hl, hl1⟩ := he_pos z hz
              obtain ⟨i, hi, j, hj, hp, hij⟩ := l497_flat φ _ _ hl
              rw [← hoff i] at hp
              have hli : lit i j = l := by
                have := hlitlt i j hj; rw [this] at hij; exact Option.some.inj hij
              refine Or.inl ⟨i, hi, j, by omega, Or.inr (Or.inr (Or.inl ⟨⟨hj, ?_⟩, ?_⟩))⟩
              · rw [hli, hl1]; omega
              · rw [hli, hl1, hinmem]
                refine ⟨t, ht, ?_, by rw [hU, hV]⟩
                rw [hpar, ← hU, hnl z hz, hTHlit z hz false]
            · rw [hnl z hz] at hU hV; simp at hU hV; omega
            · exact absurd rfl hbb
          · subst hz
            cases b <;> cases b'
            · exact absurd rfl hbb
            · refine Or.inr (Or.inl ?_)
              rw [hinmem]
              refine ⟨t, ht, ?_, by rw [hU, hV]⟩
              rw [hpar, ← hU, hnf, hTHfr false]
            · rw [hnf] at hU hV; simp at hU hV; omega
            · exact absurd rfl hbb
        · have hUV' : ((cvcFormula φ).getD i' [])[j']? = some (z, b) := hUV
          rcases lt_trichotomy i' φ.length with hi | rfl | hi
          · have hlen := (List.getElem?_eq_some_iff.1 hUV').1
            rw [l497_cvc_lt φ i' hi] at hlen
            simp only [List.length_append, List.length_singleton] at hlen
            have hj : j' ≤ (φ.getD i' []).length := by omega
            have hli : lit i' j' = (z, b) := by
              have := hcvc i' j' hi hj; rw [this] at hUV'; exact Option.some.inj hUV'
            refine Or.inl ⟨i', hi, j', by omega, Or.inl ?_⟩
            rw [hinmem]
            refine ⟨t, ht, ?_, by rw [hli, hU, hV]⟩
            rw [hpar, ← hU, ← hli]
            exact (hnumlit i' j' hi hj).2
          · rw [l497_cvc_eq] at hUV'
            have hj : j' = 0 := by
              have := (List.getElem?_eq_some_iff.1 hUV').1; simp at this; omega
            subst hj
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hUV'
            obtain ⟨rfl, rfl⟩ := hUV'
            refine Or.inr (Or.inr (Or.inl ?_))
            rw [hinmem]
            refine ⟨t, ht, ?_, by rw [hU, hV]⟩
            rw [hpar, ← hU, hnf, hTHfr false]
          · rw [l497_cvc_gt φ i' hi] at hUV'; simp at hUV'
        · have hUV' : ((cvcFormula φ).getD i [])[j]? = some (z', b') := hUV
          exfalso
          rcases lt_trichotomy i φ.length with hi | rfl | hi
          · have hlen := (List.getElem?_eq_some_iff.1 hUV').1
            rw [l497_cvc_lt φ i hi] at hlen
            simp only [List.length_append, List.length_singleton] at hlen
            have hj : j ≤ (φ.getD i []).length := by omega
            have hli : lit i j = (z', b') := by
              have := hcvc i j hi hj; rw [this] at hUV'; exact Option.some.inj hUV'
            rw [hno i j hi hj] at hU
            rw [← hli] at hV
            have := (hnumlit i j hi hj).1
            omega
          · rw [l497_cvc_eq] at hUV'
            have hj : j = 0 := by
              have := (List.getElem?_eq_some_iff.1 hUV').1; simp at this; omega
            subst hj
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hUV'
            obtain ⟨rfl, rfl⟩ := hUV'
            rw [hnlast] at hU
            rw [hnf] at hV
            simp at hV
            omega
          · rw [l497_cvc_gt φ i hi] at hUV'; simp at hUV'
        · obtain ⟨rfl, hne, hj, hj'⟩ : i = i' ∧ j ≠ j' ∧ j < ((cvcFormula φ).getD i []).length ∧
              j' < ((cvcFormula φ).getD i []).length := hUV
          rcases lt_trichotomy i φ.length with hi | rfl | hi
          · rw [l497_cvc_lt φ i hi] at hj hj'
            simp only [List.length_append, List.length_singleton] at hj hj'
            rw [hno i j hi (by omega)] at hU
            rw [hno i j' hi (by omega)] at hV
            refine Or.inl ⟨i, hi, j, by omega, Or.inr (Or.inl ⟨j', ⟨by omega, by omega⟩, ?_⟩)⟩
            rw [hinmem, hno i j hi (by omega), hno i j' hi (by omega)]
            refine ⟨t, ht, ?_, by rw [hU, hV]⟩
            rw [hpar, ← hU, hTHocc i j hi (by omega)]
            simp
          · rw [l497_cvc_eq] at hj hj'
            simp at hj hj'
            omega
          · rw [l497_cvc_gt φ i hi] at hj; simp at hj
  refine ⟨?_, hmem⟩
  have hdec : ∀ u v b x, v < N → x ∈ inner u v b →
      N ≤ x ∧ (x - N) / (2 * k) / N = u ∧ (x - N) / (2 * k) % N = v := by
    intro u v b x hv hx
    rw [hinmem] at hx
    obtain ⟨t, ht, -, rfl⟩ := hx
    exact ⟨(Nat.le_add_right N _).trans (Nat.le_add_right _ _), l497_dec N k u v t hv ht⟩
  have hinnodup : ∀ u v b, (inner u v b).Nodup := by
    intro u v b
    rw [hinner]
    exact (List.nodup_range.filter _).map (fun a b h => Nat.add_left_cancel h)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ → ℕ, ∀ x, κ x = if x < N then (if 2 * E + 2 ≤ x then x - (2 * E + 2)
      else x / 2) else (if 2 * E + 2 ≤ (x - N) / (2 * k) / N then (x - N) / (2 * k) / N - (2 * E + 2)
      else if 2 * E + 2 ≤ (x - N) / (2 * k) % N then (x - N) / (2 * k) % N - (2 * E + 2)
      else (x - N) / (2 * k) / N / 2) := ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℕ, ∀ x, D x = if x < N then (if 2 * E + 2 ≤ x then 3 else 4)
      else (if 2 * E + 2 ≤ (x - N) / (2 * k) / N then 1
      else if 2 * E + 2 ≤ (x - N) / (2 * k) % N then 0 else 2) := ⟨_, fun _ => rfl⟩
  have hκin : ∀ u v b x, v < N → x ∈ inner u v b →
      κ x = (if 2 * E + 2 ≤ u then u - (2 * E + 2) else if 2 * E + 2 ≤ v then v - (2 * E + 2)
        else u / 2) ∧
      D x = (if 2 * E + 2 ≤ u then 1 else if 2 * E + 2 ≤ v then 0 else 2) := by
    intro u v b x hv hx
    obtain ⟨hxN, hu', hv'⟩ := hdec u v b x hv hx
    have hx' : ¬ x < N := by omega
    constructor
    · rw [hκ, if_neg hx', hu', hv']
    · rw [hD, if_neg hx', hu', hv']
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ → List ℕ, ∀ i j, P i j =
      (inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
        ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
          else []) ++
        (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else [])) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : List ℕ, T =
      (inner (num (Sum.inl (fresh φ, false))) (num (Sum.inl (fresh φ, true))) false ++
        inner (num (Sum.inl (fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++
        [num (Sum.inl (fresh φ, true)), num (Sum.inr (φ.length, 0))]) := ⟨_, rfl⟩
  have hTL' : TL = (List.range φ.length).flatMap
      (fun i => (List.range ((φ.getD i []).length + 1)).flatMap (fun j => P i j)) ++ T := by
    rw [hTL, hT]
    simp only [hP]
  have hPfacts : ∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      (P i j).Nodup ∧ ∀ x ∈ P i j, κ x = off i + j := by
    intro i j hi hj
    have hoE := hoffE i hi
    have hno0 := hno i j hi hj
    have hnl0 := hnumlit i j hi hj
    have p1 : ∀ x ∈ inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2,
        κ x = off i + j ∧ D x = 0 := by
      intro x hx
      obtain ⟨h1, h2⟩ := hκin _ _ _ x (by omega) hx
      rw [hno0] at h1 h2
      rw [h1, h2]
      refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
    have p2 : ∀ l, j < l → l ≤ (φ.getD i []).length →
        ∀ x ∈ inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i)),
        κ x = off i + j ∧ D x = 1 ∧ (x - N) / (2 * k) % N = 2 * (E + 1) + off i + l := by
      intro l hjl hl x hx
      have hnol := hno i l hi hl
      obtain ⟨h1, h2⟩ := hκin _ _ _ x (by omega) hx
      obtain ⟨-, -, h3⟩ := hdec _ _ _ x (by omega) hx
      rw [hno0, hnol] at h1 h2
      rw [hnol] at h3
      rw [h1, h2]
      refine ⟨?_, ?_, h3⟩ <;> split_ifs <;> omega
    have p3 : ∀ x ∈ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
          else []), κ x = off i + j ∧ D x = 2 := by
      intro x hx
      rw [l497_mem_ite] at hx
      obtain ⟨⟨hjl, hz⟩, hx⟩ := hx
      have hzv := hvar i j hjl
      have hez := he_lt _ hzv
      rw [hnl _ hzv, hnl _ hzv] at hx
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hx
      obtain ⟨h1, h2⟩ := hκin _ _ _ x (by omega) hx
      rw [h1, h2]
      refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
    have p4 : ∀ x ∈ (if j ≠ f i then [num (Sum.inr (i, j))] else []), κ x = off i + j ∧ D x = 3 := by
      intro x hx
      rw [l497_mem_ite, List.mem_singleton, hno0] at hx
      obtain ⟨-, rfl⟩ := hx
      rw [hκ, hD]
      refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
    have p5 : ∀ x ∈ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else []), κ x = off i + j ∧ D x = 4 := by
      intro x hx
      rw [l497_mem_ite, List.mem_singleton] at hx
      obtain ⟨⟨hjl, hz⟩, rfl⟩ := hx
      have hzv := hvar i j hjl
      have hez := he_lt _ hzv
      rw [hnl _ hzv, hκ, hD]
      simp only [↓reduceIte]
      refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
    have n2 : (((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i)))).Nodup := by
      refine l497_nodup_flatMap _ _ (List.nodup_range.filter _) (fun l _ => hinnodup _ _ _) ?_
      intro l hl l' hl' x hx hx'
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hl hl'
      have := (p2 l hl.2 (by omega) x hx).2.2
      have := (p2 l' hl'.2 (by omega) x hx').2.2
      omega
    have m2 : ∀ x ∈ ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))),
          κ x = off i + j ∧ D x = 1 := by
      intro x hx
      rw [List.mem_flatMap] at hx
      obtain ⟨l, hl, hx⟩ := hx
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hl
      have := p2 l hl.2 (by omega) x hx
      exact ⟨this.1, this.2.1⟩
    have n3 : (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
          else []).Nodup := by
      split_ifs
      · exact hinnodup _ _ _
      · exact List.nodup_nil
    have n4 : (if j ≠ f i then [num (Sum.inr (i, j))] else []).Nodup := by
      split_ifs <;> simp
    have n5 : (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else []).Nodup := by
      split_ifs <;> simp
    rw [hP]
    refine ⟨(l497_nodup_app D 4 (l497_nodup_app D 3 (l497_nodup_app D 2 (l497_nodup_app D 1
      ⟨hinnodup _ _ _, fun x hx => by rw [(p1 x hx).2]; omega⟩ n2 (fun x hx => (m2 x hx).2))
      n3 (fun x hx => (p3 x hx).2)) n4 (fun x hx => (p4 x hx).2)) n5 (fun x hx => (p5 x hx).2)).1, ?_⟩
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (((hx | hx) | hx) | hx) | hx
    · exact (p1 x hx).1
    · exact (m2 x hx).1
    · exact (p3 x hx).1
    · exact (p4 x hx).1
    · exact (p5 x hx).1
  have hTfacts : T.Nodup ∧ ∀ x ∈ T, κ x = E := by
    have hfr0 : num (Sum.inl (fresh φ, false)) = 2 * E := by rw [hnf]; simp
    have hfr1 : num (Sum.inl (fresh φ, true)) = 2 * E + 1 := by rw [hnf]; simp
    rw [hT, hfr0, hfr1, hnlast]
    have q1 : ∀ x ∈ inner (2 * E) (2 * E + 1) false, κ x = E ∧ D x = 2 := by
      intro x hx
      obtain ⟨h1, h2⟩ := hκin _ _ _ x (by omega) hx
      rw [h1, h2]
      refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
    have q2 : ∀ x ∈ inner (2 * E) (3 * E + 2) false, κ x = E ∧ D x = 0 := by
      intro x hx
      obtain ⟨h1, h2⟩ := hκin _ _ _ x (by omega) hx
      rw [h1, h2]
      refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
    have q3 : ∀ x ∈ [2 * E + 1, 3 * E + 2], κ x = E ∧ D x ≥ 3 := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rw [hκ, hD] <;> refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
    refine ⟨List.nodup_append.2 ⟨List.nodup_append.2 ⟨hinnodup _ _ _, hinnodup _ _ _, ?_⟩, ?_, ?_⟩, ?_⟩
    · intro a ha b hb hab
      subst hab
      have := (q1 a ha).2; have := (q2 a hb).2; omega
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, not_false_eq_true, and_true]
      omega
    · intro a ha b hb hab
      subst hab
      have := (q3 a hb).2
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · have := (q1 a ha).2; omega
      · have := (q2 a ha).2; omega
    · intro x hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact (q1 x hx).1
      · exact (q2 x hx).1
      · exact (q3 x hx).1
  rw [hTL', List.nodup_append]
  refine ⟨?_, hTfacts.1, ?_⟩
  · refine l497_nodup_flatMap _ _ List.nodup_range (fun i hi => ?_) ?_
    · rw [List.mem_range] at hi
      refine l497_nodup_flatMap _ _ List.nodup_range
        (fun j hj => (hPfacts i j hi (by rw [List.mem_range] at hj; omega)).1) ?_
      intro j hj j' hj' x hx hx'
      rw [List.mem_range] at hj hj'
      have := (hPfacts i j hi (by omega)).2 x hx
      have := (hPfacts i j' hi (by omega)).2 x hx'
      omega
    · intro i hi i' hi' x hx hx'
      rw [List.mem_range] at hi hi'
      rw [List.mem_flatMap] at hx hx'
      obtain ⟨j, hj, hx⟩ := hx
      obtain ⟨j', hj', hx'⟩ := hx'
      rw [List.mem_range] at hj hj'
      have h1 := (hPfacts i j hi (by omega)).2 x hx
      have h2 := (hPfacts i' j' hi' (by omega)).2 x hx'
      exact (hoffinj i i' j j' hi hi' (by omega) (by omega) (by omega)).1
  · intro a ha b hb hab
    subst hab
    have hb' := hTfacts.2 a hb
    rw [List.mem_flatMap] at ha
    obtain ⟨i, hi, ha⟩ := ha
    rw [List.mem_flatMap] at ha
    obtain ⟨j, hj, ha⟩ := ha
    rw [List.mem_range] at hi hj
    have := (hPfacts i j hi (by omega)).2 a ha
    have := hoffE i hi
    omega
