import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_535_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem sum_count (l : List ℕ) (S : Finset ℕ) (h : ∀ i ∈ l, i ∈ S) :
    ∑ w ∈ S, l.count w = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a ∈ S := h a (by simp)
    have := ih (fun i hi => h i (by simp [hi]))
    simp only [List.count_cons, Finset.sum_add_distrib, List.length_cons, this]
    simp [ha]

theorem tree_card {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ} (h : IsOrTree n C G L ρ) :
    L.card = G.card + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  by_cases hG : G = ∅
  · rw [if_pos hG] at h4
    subst hG
    simp [h4]
  rw [if_neg hG] at h4
  obtain ⟨j0, hj0, hρ⟩ := h4
  have hdisj : Disjoint L (G.image (fun j => n + j)) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw'
    exact (h2 _ hw).1 ⟨by omega, by simpa using hj⟩
  have e1 : ∀ j ∈ G, (gateAt C j).inputs.length =
      ∑ w ∈ L ∪ G.image (fun j => n + j), (gateAt C j).inputs.count w := by
    intro j hj
    symm
    apply sum_count
    intro i hi
    rcases (h1 j hj).2.2 i hi with h | ⟨h5, h6⟩
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i - n, h6, by omega⟩)
  have hsum : ∑ j ∈ G, (gateAt C j).inputs.length =
      ∑ w ∈ L, readsIn C G w + ∑ j ∈ G, readsIn C G (n + j) := by
    rw [Finset.sum_congr rfl e1, Finset.sum_comm, Finset.sum_union hdisj,
      Finset.sum_image (by intro a _ b _ h; simpa using h)]
    rfl
  have hL : ∑ w ∈ L, readsIn C G w = L.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro w hw
    rw [(h2 w hw).2, if_neg]
    intro he
    apply (h2 w hw).1
    rw [he, hρ]
    simp [hj0]
  have hGs : ∑ j ∈ G, readsIn C G (n + j) = G.card - 1 := by
    have hc : ∀ j ∈ G.erase j0, readsIn C G (n + j) = 1 := by
      intro j hj
      rw [h3 j (Finset.mem_of_mem_erase hj), if_neg]
      intro he
      have := Finset.ne_of_mem_erase hj
      omega
    rw [← Finset.add_sum_erase G _ hj0, h3 j0 hj0, if_pos hρ.symm, Finset.sum_congr rfl hc,
      Finset.sum_const, Finset.card_erase_of_mem hj0]
    simp
  have h2G : ∑ j ∈ G, (gateAt C j).inputs.length = 2 * G.card := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j hj => by simp [(h1 j hj).2.1])
  have hpos : 0 < G.card := Finset.card_pos.mpr ⟨j0, hj0⟩
  omega

end PEqualNP.Outside.L_meta_535_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Outside.L_meta_535_aux in
theorem PEqualNP.Outside.L_meta_535 : ∀ (n t : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.NestedCover.IsNestedCoverCircuit n K A C → (∃ S : Finset (Fin n), K.IsVertexCover (S : Set (Fin n)) ∧ S.card = t) → (∀ S : Finset (Fin n), K.IsVertexCover (S : Set (Fin n)) → t ≤ S.card) → C.size + 1 = A.card + K.edgeFinset.card + t := by
  intro n t K _ A C hC hex hmin
  obtain ⟨d, hRB, hMin, hOwn, hTie, hRoles, hT, hTop⟩ := hC
  obtain ⟨S, hS, hSc⟩ := hex
  have hTc : d.cover.card = t := by
    have a1 := hMin.2 S hS
    have a2 := hmin _ hMin.1
    omega
  have hbw : ∀ s ∈ d.cover, ∃ j < C.gates.length, d.bw s = n + j ∧ d.role j = (Kind.b, s.val) := by
    intro s hs
    obtain ⟨j, hj, e, r, _⟩ := (hT s hs).1
    exact ⟨j, hj, e, r⟩
  have hbwinj : Set.InjOn d.bw (d.cover : Set (Fin n)) := by
    intro s hs s' hs' he
    obtain ⟨j, _, e, r⟩ := hbw s hs
    obtain ⟨j', _, e', r'⟩ := hbw s' hs'
    have hjj : j = j' := by omega
    subst hjj
    rw [r] at r'
    exact Fin.ext (Prod.ext_iff.mp r').2
  have hZ : ∀ s ∈ d.cover, (zLeaves d s).card =
      (d.cover.filter (fun s' => d.tie s' = some s)).card + 1 := by
    intro s hs
    unfold zLeaves
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injOn]
    · exact hbwinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
    · intro hm
      obtain ⟨s', hs', he⟩ := Finset.mem_image.mp hm
      obtain ⟨j, _, e, _⟩ := hbw s' (Finset.mem_filter.mp hs').1
      have := s.isLt
      omega
  have hkey : ∀ s ∈ d.cover, ∀ r, d.owns s r = true →
      (if d.lam s r < n then d.lam s r else (d.role (d.lam s r - n)).2) = r.val := by
    intro s hs r hr
    have hl := (hT s hs).2.2.2 r hr
    unfold LamOK at hl
    split_ifs at hl with hrc
    · obtain ⟨_, h | ⟨j, _, hj, hjr⟩, _⟩ := hl
      · rw [h, if_pos r.isLt]
      · rw [hj, if_neg (by omega), Nat.add_sub_cancel_left, hjr]
    · rw [hl, if_pos r.isLt]
  have hO : ∀ s ∈ d.cover, (oLeaves d s).card =
      (Finset.univ.filter (fun r => d.owns s r = true)).card := by
    intro s hs
    unfold oLeaves
    apply Finset.card_image_of_injOn
    intro r1 hr1 r2 hr2 he
    have k1 := hkey s hs r1 (Finset.mem_filter.mp (Finset.mem_coe.mp hr1)).2
    have k2 := hkey s hs r2 (Finset.mem_filter.mp (Finset.mem_coe.mp hr2)).2
    rw [he] at k1
    exact Fin.ext (k1.symm.trans k2)
  have hTL : (topLeaves d A).card =
      A.card + (d.cover.filter (fun s => d.tie s = none)).card := by
    unfold topLeaves
    rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injOn (hbwinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1))]
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨s', hs', he⟩ := Finset.mem_image.mp hw'
    obtain ⟨j, _, e, _⟩ := hbw s' (Finset.mem_filter.mp hs').1
    have := a.isLt
    omega
  have hB : ∀ s ∈ d.cover, (gatesOf d C Kind.b s.val).card = 1 := by
    intro s hs
    obtain ⟨j0, hj0, e0, r0⟩ := hbw s hs
    rw [Finset.card_eq_one]
    refine ⟨j0, ?_⟩
    ext j
    simp only [gatesOf, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hr⟩
      rcases hRoles j hj with h | ⟨s', _, h2, h3⟩
      · rw [hr] at h
        simp at h
      · rw [hr] at h2 h3
        have hss : s = s' := Fin.ext h2
        subst hss
        have := h3 rfl
        omega
    · rintro rfl
      exact ⟨hj0, r0⟩
  have hfib : ∀ k, k ≠ Kind.top → ∀ u : ℕ,
      (((Finset.range C.gates.length).filter (fun j => ¬ (d.role j).1 = Kind.top)).filter
        (fun j => (d.role j).2 = u)).filter (fun j => (d.role j).1 = k) = gatesOf d C k u := by
    intro k hk u
    ext j
    simp only [gatesOf, Finset.mem_filter, Finset.mem_range, Prod.ext_iff]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, h2⟩, h3⟩
      exact ⟨h1, h3, h2⟩
    · rintro ⟨h1, h3, h2⟩
      exact ⟨⟨⟨h1, by rw [h3]; exact hk⟩, h2⟩, h3⟩
  have hNT : ((Finset.range C.gates.length).filter (fun j => ¬ (d.role j).1 = Kind.top)).card =
      ∑ s ∈ d.cover, ((gatesOf d C Kind.z s.val).card + (gatesOf d C Kind.o s.val).card +
        (gatesOf d C Kind.b s.val).card) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun j => (d.role j).2) (t := d.cover.image Fin.val)]
    · rw [Finset.sum_image (by intro a _ b _ h; exact Fin.ext h)]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.card_eq_sum_card_fiberwise (f := fun j => (d.role j).1)
        (t := {Kind.z, Kind.o, Kind.b})]
      · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
          hfib _ (by decide), hfib _ (by decide), hfib _ (by decide)]
        ring
      · intro j hj
        simp only [Finset.mem_coe, Finset.mem_filter] at hj
        have h := hj.1.2
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
        generalize (d.role j).1 = k at h ⊢
        cases k <;> simp_all
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
      rcases hRoles j hj.1 with h | ⟨s', hs', h2, _⟩
      · exact absurd h hj.2
      · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s', hs', h2.symm⟩)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.range C.gates.length) (fun j => (d.role j).1 = Kind.top)
  have htopc := tree_card hTop
  rw [hTL] at htopc
  have hsum1 : ∑ s ∈ d.cover, ((gatesOf d C Kind.z s.val).card + (gatesOf d C Kind.o s.val).card +
        (gatesOf d C Kind.b s.val).card) =
      ∑ s ∈ d.cover, (d.cover.filter (fun s' => d.tie s' = some s)).card +
      ∑ s ∈ d.cover, (Finset.univ.filter (fun r => d.owns s r = true)).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have a1 := tree_card (hT s hs).2.1
    have a2 := tree_card (hT s hs).2.2.1
    have a3 := hB s hs
    rw [hZ s hs] at a1
    rw [hO s hs] at a2
    omega
  have htied : ∑ s ∈ d.cover, (d.cover.filter (fun s' => d.tie s' = some s)).card +
      (d.cover.filter (fun s => d.tie s = none)).card = d.cover.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := d.tie) (s := d.cover) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)), Fintype.sum_option,
      Finset.sum_subset (Finset.subset_univ d.cover)]
    · ring
    · intro u _ hu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro s _ hs
      exact hu (hOwn.1 _ _ (hTie s u hs).2).2
  have hown : ∑ s ∈ d.cover, (Finset.univ.filter (fun r => d.owns s r = true)).card =
      K.edgeFinset.card := by
    rw [Finset.sum_subset (Finset.subset_univ d.cover)]
    · have hP : (Finset.univ.filter (fun p : Fin n × Fin n => d.owns p.1 p.2 = true)).card =
          ∑ u, (Finset.univ.filter (fun r => d.owns u r = true)).card := by
        rw [Finset.card_filter, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.card_filter]
      rw [← hP]
      apply Finset.card_bij (fun p _ => s(p.1, p.2))
      · intro p hp
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact (hOwn.1 _ _ (Finset.mem_filter.mp hp).2).1
      · intro p hp q hq he
        have hp' := (Finset.mem_filter.mp hp).2
        have hq' := (Finset.mem_filter.mp hq).2
        rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Prod.ext h1 h2
        · exfalso
          have hadj := (hOwn.1 _ _ hp').1
          apply hOwn.2 _ _ hadj
          rw [hp', h1, h2, hq']
      · intro e he
        induction e using Sym2.ind with
        | h u v =>
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
          have hne := hOwn.2 u v he
          by_cases huv : d.owns u v = true
          · exact ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩, rfl⟩
          · have hvu : d.owns v u = true := by
              cases h1 : d.owns u v <;> cases h2 : d.owns v u <;> simp_all
            exact ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvu⟩, Sym2.eq_swap⟩
    · intro u _ hu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro r _ hr
      exact hu (hOwn.1 _ _ hr).2
  have hsize : C.size = (Finset.range C.gates.length).card := by
    rw [Finset.card_range]
    rfl
  unfold topGates at htopc
  omega
