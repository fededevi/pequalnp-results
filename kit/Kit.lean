import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

theorem iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem simulate {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ) (emb : σ → τ)
    (h : ∀ c c', f c = some c' → g (emb c) = some (emb c')) :
    ∀ (n : ℕ) (a b : σ), (flip bind f)^[n] (some a) = some b →
      (flip bind g)^[n] (some (emb a)) = some (emb b) := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; rfl
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab ⊢
    cases hfa : f a with
    | none =>
      have e : flip bind f (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind f (some a) = some c := hfa
      have e' : flip bind g (some (emb a)) = some (emb c) := h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab

section pushes

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_cons]; omega
    · rw [Function.update_of_ne h]; omega
  | peek k' f q ih => exact ih _ _
  | pop k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_tail]; omega
    · rw [Function.update_of_ne h]
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, pushes]
    cases f v
    · exact (ih₂ v S).trans (by have := le_max_right (pushes q₁) (pushes q₂); omega)
    · exact (ih₁ v S).trans (by have := le_max_left (pushes q₁) (pushes q₂); omega)
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

end pushes

noncomputable def maxPush (tm : FinTM2) : ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l => pushes (tm.m l)

theorem step_length (tm : FinTM2) (c c' : TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h : TM2.step tm.m c = some c') (k : tm.K) :
    (c'.stk k).length ≤ (c.stk k).length + maxPush tm := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    refine (stepAux_length _ _ _ _).trans ?_
    have : pushes (tm.m l) ≤ maxPush tm :=
      Finset.le_sup (f := fun l => pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
    simpa using this

theorem run_length (tm : FinTM2) (k : tm.K) :
    ∀ (n : ℕ) (a b : TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (TM2.step tm.m))^[n] (some a) = some b →
      (b.stk k).length ≤ (a.stk k).length + maxPush tm * n := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; simp
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab
    cases hfa : TM2.step tm.m a with
    | none =>
      have e : flip bind (TM2.step tm.m) (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind (TM2.step tm.m) (some a) = some c := hfa
      rw [e] at hab
      have h1 := ih c b hab
      have h2 := step_length tm a c hfa k
      rw [Nat.mul_succ]; omega

theorem initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

theorem haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add]; exact add_le_add hp hq
  | monomial d c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

section update

variable {ι : Type} [DecidableEq ι] {β : ι → Type}

theorem update3_fst (E : ∀ i, β i) {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
    (x x' : β a) (y : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) a x' =
      Function.update (Function.update (Function.update E a x') b y) c z := by
  rw [Function.update_comm hac.symm, Function.update_comm hab.symm, Function.update_idem]

theorem update3_snd (E : ∀ i, β i) {a b c : ι} (hbc : b ≠ c)
    (x : β a) (y y' : β b) (z : β c) :
    Function.update (Function.update (Function.update (Function.update E a x) b y) c z) b y' =
      Function.update (Function.update (Function.update E a x) b y') c z := by
  rw [Function.update_comm hbc.symm, Function.update_idem]

end update

variable (M1 M2 : FinTM2)

abbrev CK : Type := Option (M1.K ⊕ M2.K)

abbrev CΓ : CK M1 M2 → Type
  | none => M2.Γ M2.k₀
  | some (Sum.inl k) => M1.Γ k
  | some (Sum.inr k) => M2.Γ k

abbrev CΛ : Type := M1.Λ ⊕ M2.Λ ⊕ Bool

abbrev Cσ : Type := M1.σ × M2.σ × Option (M2.Γ M2.k₀)

variable {M1 M2}

def tr1 : TM2.Stmt M1.Γ M1.Λ M1.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inl k)) (fun s => f s.1) (tr1 q)
  | .peek k f q => .peek (some (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .pop k f q => .pop (some (Sum.inl k)) (fun s o => (f s.1 o, s.2)) (tr1 q)
  | .load a q => .load (fun s => (a s.1, s.2)) (tr1 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (tr1 q₁) (tr1 q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inr false))

def tr2 : TM2.Stmt M2.Γ M2.Λ M2.σ → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | .push k f q => .push (some (Sum.inr k)) (fun s => f s.2.1) (tr2 q)
  | .peek k f q => .peek (some (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .pop k f q => .pop (some (Sum.inr k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (tr2 q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (tr2 q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (tr2 q₁) (tr2 q₂)
  | .goto f => .goto (fun s => Sum.inr (Sum.inl (f s.2.1)))
  | .halt => .halt

variable (M1 M2)

def tA (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) :
    Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop (some (Sum.inl M1.k₁)) (fun s o => (s.1, s.2.1, o.map φ))
      (.branch (fun s => s.2.2.isSome)
        (.push none (fun s => s.2.2.getD d) (.goto fun _ => Sum.inr (Sum.inr false)))
        (.goto fun _ => Sum.inr (Sum.inr true)))

def tB : Option (M2.Γ M2.k₀) → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | none => .goto (fun _ => Sum.inr (Sum.inl M2.main))
  | some d =>
    .pop none (fun s o => (s.1, s.2.1, o))
      (.branch (fun s => s.2.2.isSome)
        (.push (some (Sum.inr M2.k₀)) (fun s => s.2.2.getD d)
          (.goto fun _ => Sum.inr (Sum.inr true)))
        (.goto fun _ => Sum.inr (Sum.inl M2.main)))

def prog (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) :
    CΛ M1 M2 → TM2.Stmt (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)
  | Sum.inl l => tr1 (M1.m l)
  | Sum.inr (Sum.inl l) => tr2 (M2.m l)
  | Sum.inr (Sum.inr false) => tA M1 M2 φ d
  | Sum.inr (Sum.inr true) => tB M1 M2 d

def comp (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀)) : FinTM2 :=
  haveI := M1.kFin
  haveI := M2.kFin
  haveI := M1.ΛFin
  haveI := M2.ΛFin
  haveI := M1.σFin
  haveI := M2.σFin
  haveI := M2.Γk₀Fin
  { K := CK M1 M2
    k₀ := some (Sum.inl M1.k₀)
    k₁ := some (Sum.inr M2.k₁)
    Γ := CΓ M1 M2
    Λ := CΛ M1 M2
    main := Sum.inl M1.main
    σ := Cσ M1 M2
    initialState := (M1.initialState, M2.initialState, none)
    Γk₀Fin := M1.Γk₀Fin
    m := prog M1 M2 φ d }

variable {M1 M2}

def embStk1 (S : ∀ k, List (M1.Γ k)) : ∀ k, List (CΓ M1 M2 k)
  | none => []
  | some (Sum.inl k) => S k
  | some (Sum.inr _) => []

def embStk2 (S : ∀ k, List (M2.Γ k)) : ∀ k, List (CΓ M1 M2 k)
  | none => []
  | some (Sum.inl _) => []
  | some (Sum.inr k) => S k

theorem embStk1_update (S : ∀ k, List (M1.Γ k)) (k : M1.K) (x : List (M1.Γ k)) :
    (embStk1 (Function.update S k x) : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (embStk1 S) (some (Sum.inl k)) x := by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j = x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j = S j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rfl

theorem embStk2_update (S : ∀ k, List (M2.Γ k)) (k : M2.K) (x : List (M2.Γ k)) :
    (embStk2 (Function.update S k x) : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (embStk2 S) (some (Sum.inr k)) x := by
  funext j
  rcases j with _ | j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show Function.update S j x j = x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show Function.update S k x j = S j
      rw [Function.update_of_ne h]

theorem embStk1_nil :
    (embStk1 (fun _ => []) : ∀ k, List (CΓ M1 M2 k)) = fun _ => [] := by
  funext j; rcases j with _ | j | j <;> rfl

theorem embStk2_nil :
    (embStk2 (fun _ => []) : ∀ k, List (CΓ M1 M2 k)) = fun _ => [] := by
  funext j; rcases j with _ | j | j <;> rfl

def emb1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c : TM2.Cfg M1.Γ M1.Λ M1.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨some (c.l.elim (Sum.inr (Sum.inr false)) Sum.inl), (c.var, w), embStk1 c.stk⟩

def emb2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c : TM2.Cfg M2.Γ M2.Λ M2.σ) :
    TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2) :=
  ⟨c.l.map (fun l => Sum.inr (Sum.inl l)), (u, c.var, b), embStk2 c.stk⟩

theorem sim1 (w : M2.σ × Option (M2.Γ M2.k₀)) (q : TM2.Stmt M1.Γ M1.Λ M1.σ) (v : M1.σ)
    (S : ∀ k, List (M1.Γ k)) :
    TM2.stepAux (tr1 q) ((v, w) : Cσ M1 M2) (embStk1 S) = emb1 w (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [embStk1_update] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [embStk1_update] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr1, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem sim2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (q : TM2.Stmt M2.Γ M2.Λ M2.σ) (v : M2.σ)
    (S : ∀ k, List (M2.Γ k)) :
    TM2.stepAux (tr2 q) ((u, v, b) : Cσ M1 M2) (embStk2 S) = emb2 u b (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [embStk2_update] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [embStk2_update] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr2, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

variable (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀) (d : Option (M2.Γ M2.k₀))

theorem step1 (w : M2.σ × Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M1.Γ M1.Λ M1.σ)
    (h : TM2.step M1.m c = some c') :
    TM2.step (prog M1 M2 φ d) (emb1 w c) = some (emb1 w c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim1 w (M1.m l) v S)

theorem step2 (u : M1.σ) (b : Option (M2.Γ M2.k₀)) (c c' : TM2.Cfg M2.Γ M2.Λ M2.σ)
    (h : TM2.step M2.m c = some c') :
    TM2.step (prog M1 M2 φ d) (emb2 u b c) = some (emb2 u b c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (sim2 u b (M2.m l) v S)

def st (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) : ∀ k, List (CΓ M1 M2 k) :=
  Function.update (Function.update (Function.update (fun _ => [])
    (some (Sum.inl M1.k₁)) l) none t) (some (Sum.inr M2.k₀)) u

theorem st_fst (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) = l := by
  unfold st
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]

theorem st_snd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) none = t := by
  unfold st
  rw [Function.update_of_ne (by simp), Function.update_self]

theorem st_thd (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) = u := by
  unfold st
  rw [Function.update_self]

theorem st_set_fst (l l' : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l' = st l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _

theorem st_set_snd (l : List (M1.Γ M1.k₁)) (t t' u : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) none t' = st l t' u :=
  update3_snd _ (by simp) _ _ _ _

theorem st_set_thd (l : List (M1.Γ M1.k₁)) (t u u' : List (M2.Γ M2.k₀)) :
    Function.update (st l t u : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u' = st l t u' :=
  Function.update_idem _ _ _

theorem st_start (l : List (M1.Γ M1.k₁)) :
    (st l [] [] : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) l := by
  unfold st
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]

theorem st_end (u : List (M2.Γ M2.k₀)) :
    (st [] [] u : ∀ k, List (CΓ M1 M2 k)) =
      Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) u := by
  unfold st
  congr 1
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

variable {M1 M2 : FinTM2} (φ : M1.Γ M1.k₁ → M2.Γ M2.k₀)

abbrev CCfg (M1 M2 : FinTM2) : Type := TM2.Cfg (CΓ M1 M2) (CΛ M1 M2) (Cσ M1 M2)

theorem stepA_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (x : M1.Γ M1.k₁) (l : List (M1.Γ M1.k₁)) (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st (x :: l) t u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr false)), (v1, v2, some (φ x)), st l (φ x :: t) u⟩ := by
  simp only [TM2.step, prog, tA, TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some, Bool.cond_true,
    Option.getD_some]
  rw [st_set_fst, st_snd, st_set_snd]

theorem stepA_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st [] t u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, none), st [] t u⟩ := by
  simp only [TM2.step, prog, tA, TM2.stepAux]
  rw [st_fst]
  simp only [List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false]
  rw [st_set_fst]

theorem stepB_cons (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (x : M2.Γ M2.k₀) (t u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] (x :: t) u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, some x), st [] t (x :: u)⟩ := by
  simp only [TM2.step, prog, tB, TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [st_set_snd, st_thd, st_set_thd]

theorem stepB_nil (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (b : Option (M2.Γ M2.k₀))
    (u : List (M2.Γ M2.k₀)) :
    TM2.step (prog M1 M2 φ (some dd))
        (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] [] u⟩ : CCfg M1 M2) =
      some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none), st [] [] u⟩ := by
  simp only [TM2.step, prog, tB, TM2.stepAux]
  rw [st_snd]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [st_set_snd]

theorem loopA (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) (u : List (M2.Γ M2.k₀)) :
    ∀ (l : List (M1.Γ M1.k₁)) (t : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[l.length + 1]
          (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st l t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, none), st [] ((l.map φ).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact stepA_nil φ dd v1 v2 b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, b), st (x :: l) t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr false)), (v1, v2, some (φ x)), st l (φ x :: t) u⟩ :=
      stepA_cons φ dd v1 v2 b x l t u
    rw [e, ih]
    simp

theorem loopB (dd : M2.Γ M2.k₀) (v1 : M1.σ) (v2 : M2.σ) :
    ∀ (t u : List (M2.Γ M2.k₀)) (b : Option (M2.Γ M2.k₀)),
      (flip bind (TM2.step (prog M1 M2 φ (some dd))))^[t.length + 1]
          (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] t u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none), st [] [] (t.reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact stepB_nil φ dd v1 v2 b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (prog M1 M2 φ (some dd)))
        (some (⟨some (Sum.inr (Sum.inr true)), (v1, v2, b), st [] (x :: t) u⟩ : CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inr true)), (v1, v2, some x), st [] t (x :: u)⟩ :=
      stepB_cons φ dd v1 v2 b x t u
    rw [e, ih]
    simp

theorem transfer (d : Option (M2.Γ M2.k₀)) (hd : d = none → IsEmpty (M2.Γ M2.k₀))
    (v1 : M1.σ) (v2 : M2.σ) (o : List (M1.Γ M1.k₁)) :
    ∃ n, n ≤ 2 * o.length + 2 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n]
          (some (⟨some (Sum.inr (Sum.inr false)), (v1, v2, none),
            Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
            CCfg M1 M2)) =
        some ⟨some (Sum.inr (Sum.inl M2.main)), (v1, v2, none),
          Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀))
            (o.map φ)⟩ := by
  cases d with
  | none =>
    have := hd rfl
    have ho : o = [] := by
      cases o with
      | nil => rfl
      | cons x _ => exact (IsEmpty.false (φ x)).elim
    subst ho
    refine ⟨1, by omega, ?_⟩
    show some _ = some _
    simp only [prog, tA, TM2.stepAux, List.map_nil]
    rw [Function.update_eq_self_iff.mpr rfl, Function.update_eq_self_iff.mpr rfl]
  | some dd =>
    refine ⟨((o.map φ).reverse ++ []).length + 1 + (o.length + 1), by simp; omega, ?_⟩
    rw [Function.iterate_add_apply, ← st_start, loopA, loopB, ← st_end]
    simp

theorem emb1_init (d : Option (M2.Γ M2.k₀)) (i : List (M1.Γ M1.k₀)) :
    emb1 (M2.initialState, none) (initList M1 i) = initList (comp M1 M2 φ d) i := by
  rw [initList_eq]
  refine Eq.trans ?_ (initList_eq (comp M1 M2 φ d) i).symm
  show (⟨_, _, embStk1 _⟩ : CCfg M1 M2) = _
  rw [embStk1_update, embStk1_nil]
  rfl

theorem emb1_halt (w : M2.σ × Option (M2.Γ M2.k₀)) (o : List (M1.Γ M1.k₁)) :
    emb1 w (haltList M1 o) =
      (⟨some (Sum.inr (Sum.inr false)), (M1.initialState, w),
        Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inl M1.k₁)) o⟩ :
        CCfg M1 M2) := by
  rw [haltList_eq]
  show (⟨_, _, embStk1 _⟩ : CCfg M1 M2) = _
  rw [embStk1_update, embStk1_nil]
  rfl

theorem emb2_init (u : M1.σ) (i : List (M2.Γ M2.k₀)) :
    emb2 u none (initList M2 i) =
      (⟨some (Sum.inr (Sum.inl M2.main)), (u, M2.initialState, none),
        Function.update (fun _ => [] : ∀ k, List (CΓ M1 M2 k)) (some (Sum.inr M2.k₀)) i⟩ :
        CCfg M1 M2) := by
  rw [initList_eq]
  show (⟨_, _, embStk2 _⟩ : CCfg M1 M2) = _
  rw [embStk2_update, embStk2_nil]
  rfl

theorem emb2_halt (d : Option (M2.Γ M2.k₀)) (o : List (M2.Γ M2.k₁)) :
    emb2 M1.initialState none (haltList M2 o) = haltList (comp M1 M2 φ d) o := by
  rw [haltList_eq]
  refine Eq.trans ?_ (haltList_eq (comp M1 M2 φ d) o).symm
  show (⟨_, _, embStk2 _⟩ : CCfg M1 M2) = _
  rw [embStk2_update, embStk2_nil]
  rfl

theorem comp_run (d : Option (M2.Γ M2.k₀)) (hd : d = none → IsEmpty (M2.Γ M2.k₀))
    (i : List (M1.Γ M1.k₀)) (o1 : List (M1.Γ M1.k₁)) (o2 : List (M2.Γ M2.k₁)) (s1 s2 : ℕ)
    (h1 : (flip bind (TM2.step M1.m))^[s1] (some (initList M1 i)) = some (haltList M1 o1))
    (h2 : (flip bind (TM2.step M2.m))^[s2] (some (initList M2 (o1.map φ))) =
      some (haltList M2 o2)) :
    ∃ n, n ≤ s1 + (2 * o1.length + 2) + s2 ∧ o1.length ≤ i.length + maxPush M1 * s1 ∧
      (flip bind (TM2.step (prog M1 M2 φ d)))^[n] (some (initList (comp M1 M2 φ d) i)) =
        some (haltList (comp M1 M2 φ d) o2) := by
  have p1 := simulate (TM2.step M1.m) (TM2.step (prog M1 M2 φ d))
    (emb1 (M2.initialState, none)) (step1 φ d _) s1 _ _ h1
  rw [emb1_init φ d, emb1_halt] at p1
  obtain ⟨nt, hnt, pt⟩ := transfer φ d hd M1.initialState M2.initialState o1
  have p2 := simulate (TM2.step M2.m) (TM2.step (prog M1 M2 φ d))
    (emb2 M1.initialState none) (step2 φ d _ _) s2 _ _ h2
  rw [emb2_init, emb2_halt φ d] at p2
  refine ⟨s2 + (nt + s1), by omega, ?_, ?_⟩
  · have := run_length M1 M1.k₁ s1 _ _ h1
    rw [haltList_eq, initList_eq] at this
    simp only [Function.update_self] at this
    refine this.trans (Nat.add_le_add_right ?_ _)
    by_cases h : M1.k₁ = M1.k₀
    · rw [h, Function.update_self]
    · rw [Function.update_of_ne h]; simp
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, p1, pt, p2]
    rfl

theorem comp_polyTime {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (ec : γ → List γΓ) (f : α → β) (g : β → γ) (c1 : TM2ComputableInPolyTime ea eb f)
    (c2 : TM2ComputableInPolyTime eb ec g) :
    Nonempty (TM2ComputableInPolyTime ea ec (fun a => g (f a))) := by
  classical
  let φ : c1.tm.Γ c1.tm.k₁ → c2.tm.Γ c2.tm.k₀ :=
    fun x => c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d : Option (c2.tm.Γ c2.tm.k₀) :=
    if h : Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd : d = none → IsEmpty (c2.tm.Γ c2.tm.k₀) := by
    intro h
    by_cases hn : Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d, hn] at h
    · exact not_nonempty_iff.mp hn
  let T : Polynomial ℕ :=
    c1.time + (Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time) +
      Polynomial.C 2) +
      c2.time.comp (Polynomial.X + Polynomial.C (maxPush c1.tm) * c1.time)
  have key : ∀ a, ∃ n, n ≤ T.eval (ea a).length ∧
      (flip bind (TM2.step (prog c1.tm c2.tm φ d)))^[n]
          (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
        some (haltList (comp c1.tm c2.tm φ d)
          (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
    intro a
    have r1 := c1.outputsFun a
    have r2 := c2.outputsFun (f a)
    have hφ : (List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
        List.map c2.inputAlphabet.invFun (eb (f a)) := by
      rw [List.map_map]
      refine List.map_congr_left fun y _ => ?_
      show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y)) = _
      exact congrArg _ (c1.outputAlphabet.right_inv y)
    have h2 : (flip bind (TM2.step c2.tm.m))^[r2.steps]
        (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
        some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
      rw [hφ]; exact r2.evals_in_steps
    obtain ⟨n, hn, hlen, hrun⟩ := comp_run φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 := r1.steps_le_m
    have b2 := r2.steps_le_m
    simp only [List.length_map] at hlen
    have hmul : maxPush c1.tm * r1.steps ≤
        maxPush c1.tm * Polynomial.eval (ea a).length c1.time := Nat.mul_le_mul_left _ b1
    have b3 : Polynomial.eval (eb (f a)).length c2.time ≤
        Polynomial.eval ((ea a).length + maxPush c1.tm * Polynomial.eval (ea a).length c1.time)
          c2.time := eval_mono _ (by omega)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, List.length_map]
    omega
  exact ⟨{
    tm := comp c1.tm c2.tm φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := c2.outputAlphabet
    time := T
    outputsFun := fun a =>
      ⟨⟨Classical.choose (key a), (Classical.choose_spec (key a)).2⟩,
        (Classical.choose_spec (key a)).1⟩ }⟩

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

theorem comp_time {α β γ αΓ βΓ γΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (ec : γ → List γΓ) (f : α → β) (g : β → γ) (t₁ t₂ len : ℕ → ℕ)
    (h₁ : PEqualNP.Library.ComputableInTime ea eb f t₁)
    (h₂ : PEqualNP.Library.ComputableInTime eb ec g t₂)
    (hmono : Monotone t₂)
    (hlen : ∀ a, (eb (f a)).length ≤ len (ea a).length) :
    PEqualNP.Library.ComputableInTime ea ec (fun a => g (f a))
      (fun n => t₁ n + (2 * len n + 2) + t₂ (len n)) := by
  classical
  obtain ⟨c1, hc1⟩ := h₁
  obtain ⟨c2, hc2⟩ := h₂
  let φ : c1.tm.Γ c1.tm.k₁ → c2.tm.Γ c2.tm.k₀ :=
    fun x => c2.inputAlphabet.invFun (c1.outputAlphabet x)
  let d : Option (c2.tm.Γ c2.tm.k₀) :=
    if h : Nonempty (c2.tm.Γ c2.tm.k₀) then some (Classical.choice h) else none
  have hd : d = none → IsEmpty (c2.tm.Γ c2.tm.k₀) := by
    intro h
    by_cases hn : Nonempty (c2.tm.Γ c2.tm.k₀)
    · simp [d, hn] at h
    · exact not_nonempty_iff.mp hn
  let T : ℕ → ℕ := fun n => t₁ n + (2 * len n + 2) + t₂ (len n)
  have key : ∀ a, ∃ n, n ≤ T (ea a).length ∧
      (flip bind (TM2.step (prog c1.tm c2.tm φ d)))^[n]
          (some (initList (comp c1.tm c2.tm φ d) (List.map c1.inputAlphabet.invFun (ea a)))) =
        some (haltList (comp c1.tm c2.tm φ d)
          (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
    intro a
    have r1 := c1.outputsFun a
    have r2 := c2.outputsFun (f a)
    have hφ : (List.map c1.outputAlphabet.invFun (eb (f a))).map φ =
        List.map c2.inputAlphabet.invFun (eb (f a)) := by
      rw [List.map_map]
      refine List.map_congr_left fun y _ => ?_
      show c2.inputAlphabet.invFun (c1.outputAlphabet (c1.outputAlphabet.invFun y)) = _
      exact congrArg _ (c1.outputAlphabet.right_inv y)
    have h2 : (flip bind (TM2.step c2.tm.m))^[r2.steps]
        (some (initList c2.tm ((List.map c1.outputAlphabet.invFun (eb (f a))).map φ))) =
        some (haltList c2.tm (List.map c2.outputAlphabet.invFun (ec (g (f a))))) := by
      rw [hφ]; exact r2.evals_in_steps
    obtain ⟨n, hn, -, hrun⟩ := comp_run φ d hd _ _ _ r1.steps r2.steps r1.evals_in_steps h2
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 : r1.steps ≤ t₁ (ea a).length := r1.steps_le_m.trans (hc1 _)
    have b2 : r2.steps ≤ t₂ (len (ea a).length) :=
      (r2.steps_le_m.trans (hc2 _)).trans (hmono (hlen a))
    have b3 := hlen a
    simp only [T, List.length_map]
    omega
  exact ⟨{
    tm := comp c1.tm c2.tm φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := c2.outputAlphabet
    time := T
    outputsFun := fun a =>
      ⟨⟨Classical.choose (key a), (Classical.choose_spec (key a)).2⟩,
        (Classical.choose_spec (key a)).1⟩ }, fun _ => le_rfl⟩

theorem time_of_polyTime {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : PEqualNP.Library.ComputableInPolyTime ea eb f) :
    ∃ p : Polynomial ℕ, PEqualNP.Library.ComputableInTime ea eb f (fun n => p.eval n) := by
  obtain ⟨c⟩ := h
  exact ⟨c.time, ⟨{
    tm := c.tm
    inputAlphabet := c.inputAlphabet
    outputAlphabet := c.outputAlphabet
    time := fun n => c.time.eval n
    outputsFun := c.outputsFun }, fun _ => le_rfl⟩⟩

theorem time_mono {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    {t t' : ℕ → ℕ} (h : PEqualNP.Library.ComputableInTime ea eb f t) (ht : ∀ n, t n ≤ t' n) :
    PEqualNP.Library.ComputableInTime ea eb f t' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun n => (hc n).trans (ht n)⟩

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

variable {Γ₀ Γ₁ : Type}

abbrev FΓ (Γ₀ Γ₁ : Type) : Option Bool → Type
  | some false => Γ₀
  | none => Option Γ₀
  | some true => Γ₁

def fmProg (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) : Bool → TM2.Stmt (FΓ Γ₀ Γ₁) Bool (Option Γ₀)
  | false =>
    .pop (some false) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push none (fun s => s) (.goto fun _ => false))
        (.goto fun _ => true))
  | true =>
    .pop none (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.branch (fun s => (s.bind φ).isSome)
          (match d with
            | some dd => .push (some true) (fun s => (s.bind φ).getD dd) (.goto fun _ => true)
            | none => .goto fun _ => true)
          (.goto fun _ => true))
        .halt)

def fm [Fintype Γ₀] (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) : FinTM2 where
  K := Option Bool
  k₀ := some false
  k₁ := some true
  Γ := FΓ Γ₀ Γ₁
  Λ := Bool
  main := false
  σ := Option Γ₀
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := fmProg φ d

def fst3 (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) : ∀ k, List (FΓ Γ₀ Γ₁ k) :=
  Function.update (Function.update (Function.update (fun _ => [])
    (some false) l) none t) (some true) u

theorem fst3_fst (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u (some false) = l := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp), Function.update_self]

theorem fst3_snd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u none = t := by
  unfold fst3
  rw [Function.update_of_ne (by simp), Function.update_self]

theorem fst3_thd (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    fst3 l t u (some true) = u := by
  unfold fst3
  rw [Function.update_self]

theorem fst3_set_fst (l l' : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (fst3 l t u) (some false) l' = fst3 l' t u :=
  update3_fst _ (by simp) (by simp) _ _ _ _

theorem fst3_set_snd (l : List Γ₀) (t t' : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (fst3 l t u) none t' = fst3 l t' u :=
  update3_snd _ (by simp) _ _ _ _

theorem fst3_set_thd (l : List Γ₀) (t : List (Option Γ₀)) (u u' : List Γ₁) :
    Function.update (fst3 l t u) (some true) u' = fst3 l t u' :=
  Function.update_idem _ _ _

theorem fst3_start (l : List Γ₀) :
    (fst3 l [] [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) (some false) l := by
  unfold fst3
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]

theorem fst3_end (u : List Γ₁) :
    (fst3 [] [] u : ∀ k, List (FΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (FΓ Γ₀ Γ₁ k)) (some true) u := by
  unfold fst3
  congr 1
  rw [Function.update_eq_self_iff.mpr, Function.update_eq_self_iff.mpr]
  · rfl
  · rw [Function.update_of_ne (by simp)]

abbrev FCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (FΓ Γ₀ Γ₁) Bool (Option Γ₀)

variable (φ : Γ₀ → Option Γ₁) (d : Option Γ₁)

theorem fmA_cons (b : Option Γ₀) (x : Γ₀) (l : List Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some false, some x, fst3 l (some x :: t) u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true]
  rw [fst3_set_fst, fst3_snd, fst3_set_snd]

theorem fmA_nil (b : Option Γ₀) (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some false, b, fst3 [] t u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some true, none, fst3 [] t u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_fst]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [fst3_set_fst]

theorem fmB_cons (hd : d = none → ∀ x, φ x = none) (b : Option Γ₀) (x : Γ₀)
    (t : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true, b, fst3 [] (some x :: t) u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨some true, some x, fst3 [] t ((φ x).toList ++ u)⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_cons, List.tail_cons, Option.join_some, Option.isSome_some,
    Bool.cond_true, Option.bind_some]
  rw [fst3_set_snd]
  cases hφ : φ x with
  | none => simp
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp only [Option.isSome_some, Bool.cond_true, TM2.stepAux,
        Option.toList_some, List.singleton_append]
      rw [fst3_thd, fst3_set_thd]
      simp [hφ]

theorem fmB_nil (b : Option Γ₀) (u : List Γ₁) :
    TM2.step (fmProg φ d) (⟨some true, b, fst3 [] [] u⟩ : FCfg Γ₀ Γ₁) =
      some ⟨none, none, fst3 [] [] u⟩ := by
  simp only [TM2.step, fmProg, TM2.stepAux]
  rw [fst3_snd]
  simp only [List.head?_nil, List.tail_nil, Option.join_none, Option.isSome_none,
    Bool.cond_false]
  rw [fst3_set_snd]

theorem fmLoopA (u : List Γ₁) :
    ∀ (l : List Γ₀) (t : List (Option Γ₀)) (b : Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[l.length + 1]
          (some (⟨some false, b, fst3 l t u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some true, none, fst3 [] (l.reverse.map some ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t b; exact fmA_nil φ d b t u
  | cons x l ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ d))
        (some (⟨some false, b, fst3 (x :: l) t u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some false, some x, fst3 l (some x :: t) u⟩ := fmA_cons φ d b x l t u
    rw [e, ih]
    simp

theorem fmLoopB (hd : d = none → ∀ x, φ x = none) :
    ∀ (t : List Γ₀) (u : List Γ₁) (b : Option Γ₀),
      (flip bind (TM2.step (fmProg φ d)))^[t.length + 1]
          (some (⟨some true, b, fst3 [] (t.map some) u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨none, none, fst3 [] [] ((t.filterMap φ).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u b; exact fmB_nil φ d b u
  | cons x t ih =>
    intro u b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (fmProg φ d))
        (some (⟨some true, b, fst3 [] ((x :: t).map some) u⟩ : FCfg Γ₀ Γ₁)) =
        some ⟨some true, some x, fst3 [] (t.map some) ((φ x).toList ++ u)⟩ :=
      fmB_cons φ d hd b x (t.map some) u
    rw [e, ih]
    cases hφ : φ x <;> simp [hφ]

theorem fm_run [Fintype Γ₀] (hd : d = none → ∀ x, φ x = none) (l : List Γ₀) :
    (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
        (some (initList (fm φ d) l)) = some (haltList (fm φ d) (l.filterMap φ)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
    (some c)) (initList_eq (fm φ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (fm φ d) (l.filterMap φ))).symm)
  show (flip bind (TM2.step (fmProg φ d)))^[l.length + 1 + (l.length + 1)]
    (some (⟨some false, none, Function.update (fun _ => []) (some false) l⟩ : FCfg Γ₀ Γ₁)) =
    some (⟨none, none, Function.update (fun _ => []) (some true) (l.filterMap φ)⟩ : FCfg Γ₀ Γ₁)
  rw [Function.iterate_add_apply, ← fst3_start, fmLoopA, ← fst3_end]
  have := fmLoopB φ d hd l.reverse [] none
  rw [List.length_reverse] at this
  simpa [List.filterMap_reverse] using this

theorem filterMap_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ : αΓ → Option βΓ)
    (h : ∀ a, eb (f a) = (ea a).filterMap φ) :
    Nonempty (TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : d = none → ∀ x, φ x = none := by
    intro hdn x
    by_cases hn : Nonempty βΓ
    · simp [d, hn] at hdn
    · cases hφ : φ x with
      | none => rfl
      | some y => exact absurd ⟨y⟩ hn
  exact ⟨{
    tm := fm φ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 2
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := fm_run φ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (fmProg φ d)))^[(ea a).length + 1 +
            ((ea a).length + 1)] (some (initList (fm φ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (fm φ d) l)) ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

abbrev TPK : Type := Fin 5

abbrev TPL : Type := Fin 4

variable {Γ₀ Γ₁ : Type}

abbrev TPΓ (Γ₀ Γ₁ : Type) : TPK → Type
  | (0 : TPK) => Γ₀
  | (1 : TPK) => Option Γ₀
  | (2 : TPK) => Option Γ₀
  | (3 : TPK) => Option Γ₀
  | (4 : TPK) => Γ₁

def tpWrite (φ : Γ₀ → Option Γ₁) (d : Option Γ₁) (lbl : TPL) :
    TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀) :=
  .branch (fun s => (s.bind φ).isSome)
    (match d with
      | some dd => .push (4 : TPK) (fun s => (s.bind φ).getD dd) (.goto fun _ => lbl)
      | none => .goto fun _ => lbl)
    (.goto fun _ => lbl)

def tpProg (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁) :
    TPL → TM2.Stmt (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)
  | (0 : TPL) =>
    .pop (0 : TPK) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push (1 : TPK) (fun s => s) (.goto fun _ => (0 : TPL)))
        (.goto fun _ => (1 : TPL)))
  | (1 : TPL) =>
    .pop (1 : TPK) (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.push (2 : TPK) (fun s => s) (tpWrite φ₂ d (1 : TPL)))
        (.goto fun _ => (2 : TPL)))
  | (2 : TPL) =>
    .pop (2 : TPK) (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (.push (3 : TPK) (fun s => s) (.goto fun _ => (2 : TPL)))
        (.goto fun _ => (3 : TPL)))
  | (3 : TPL) =>
    .pop (3 : TPK) (fun _ o => o.join)
      (.branch (fun s => s.isSome)
        (tpWrite φ₁ d (3 : TPL))
        .halt)

def tp [Fintype Γ₀] (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁) : FinTM2 where
  K := TPK
  k₀ := (0 : TPK)
  k₁ := (4 : TPK)
  Γ := TPΓ Γ₀ Γ₁
  Λ := TPL
  main := (0 : TPL)
  σ := Option Γ₀
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := tpProg φ₁ φ₂ d

def st5 (l : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) : ∀ k, List (TPΓ Γ₀ Γ₁ k)
  | (0 : TPK) => l
  | (1 : TPK) => a
  | (2 : TPK) => b
  | (3 : TPK) => c
  | (4 : TPK) => u

theorem st5_set_inp (l l' : List Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) (0 : TPK) l' = st5 l' a b c u := by
  funext k; fin_cases k <;> simp [st5]

theorem st5_set_t1 (l : List Γ₀) (a a' b c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) (1 : TPK) a' = st5 l a' b c u := by
  funext k; fin_cases k <;> simp [st5]

theorem st5_set_t2 (l : List Γ₀) (a b b' c : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) (2 : TPK) b' = st5 l a b' c u := by
  funext k; fin_cases k <;> simp [st5]

theorem st5_set_t3 (l : List Γ₀) (a b c c' : List (Option Γ₀)) (u : List Γ₁) :
    Function.update (st5 l a b c u) (3 : TPK) c' = st5 l a b c' u := by
  funext k; fin_cases k <;> simp [st5]

theorem st5_set_out (l : List Γ₀) (a b c : List (Option Γ₀)) (u u' : List Γ₁) :
    Function.update (st5 l a b c u) (4 : TPK) u' = st5 l a b c u' := by
  funext k; fin_cases k <;> simp [st5]

theorem st5_start (l : List Γ₀) :
    (st5 l [] [] [] [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) (0 : TPK) l := by
  funext k; fin_cases k <;> simp [st5]

theorem st5_end (u : List Γ₁) :
    (st5 [] [] [] [] u : ∀ k, List (TPΓ Γ₀ Γ₁ k)) =
      Function.update (fun _ => [] : ∀ k, List (TPΓ Γ₀ Γ₁ k)) (4 : TPK) u := by
  funext k; fin_cases k <;> simp [st5]

abbrev TPCfg (Γ₀ Γ₁ : Type) : Type := TM2.Cfg (TPΓ Γ₀ Γ₁) TPL (Option Γ₀)

variable (φ₁ φ₂ : Γ₀ → Option Γ₁) (d : Option Γ₁)

theorem tpA_cons (s : Option Γ₀) (x : Γ₀) (l : List Γ₀) (a b c : List (Option Γ₀))
    (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some (0 : TPL), s, st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some (0 : TPL), some x, st5 l (some x :: a) b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_inp, st5_set_t1]

theorem tpA_nil (s : Option Γ₀) (a b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some (0 : TPL), s, st5 [] a b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some (1 : TPL), none, st5 [] a b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_inp]

theorem tpB_cons (hd : d = none → ∀ x, φ₂ x = none) (s : Option Γ₀) (x : Γ₀)
    (a b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some (1 : TPL), s, st5 [] (some x :: a) b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some (1 : TPL), some x, st5 [] a (some x :: b) c ((φ₂ x).toList ++ u)⟩ := by
  cases hφ : φ₂ x with
  | none =>
    cases d <;>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t1, st5_set_t2, hφ]
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t1, st5_set_t2,
        st5_set_out, hφ]

theorem tpB_nil (s : Option Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some (1 : TPL), s, st5 [] [] b c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some (2 : TPL), none, st5 [] [] b c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t1]

theorem tpC_cons (s : Option Γ₀) (x : Γ₀) (b c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some (2 : TPL), s, st5 [] [] (some x :: b) c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some (2 : TPL), some x, st5 [] [] b (some x :: c) u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t2, st5_set_t3]

theorem tpC_nil (s : Option Γ₀) (c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some (2 : TPL), s, st5 [] [] [] c u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some (3 : TPL), none, st5 [] [] [] c u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t2]

theorem tpE_cons (hd : d = none → ∀ x, φ₁ x = none) (s : Option Γ₀) (x : Γ₀)
    (c : List (Option Γ₀)) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some (3 : TPL), s, st5 [] [] [] (some x :: c) u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨some (3 : TPL), some x, st5 [] [] [] c ((φ₁ x).toList ++ u)⟩ := by
  cases hφ : φ₁ x with
  | none =>
    cases d <;>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t3, hφ]
  | some y =>
    cases d with
    | none => rw [hd rfl x] at hφ; exact absurd hφ (by simp)
    | some dd =>
      simp [TM2.step, tpProg, tpWrite, TM2.stepAux, st5, st5_set_t3, st5_set_out, hφ]

theorem tpE_nil (s : Option Γ₀) (u : List Γ₁) :
    TM2.step (tpProg φ₁ φ₂ d) (⟨some (3 : TPL), s, st5 [] [] [] [] u⟩ : TPCfg Γ₀ Γ₁) =
      some ⟨none, none, st5 [] [] [] [] u⟩ := by
  simp [TM2.step, tpProg, TM2.stepAux, st5, st5_set_t3]

theorem tpLoopA (b c : List (Option Γ₀)) (u : List Γ₁) :
    ∀ (l : List Γ₀) (a : List (Option Γ₀)) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
          (some (⟨some (0 : TPL), s, st5 l a b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some (1 : TPL), none, st5 [] (l.reverse.map some ++ a) b c u⟩ := by
  intro l
  induction l with
  | nil => intro a s; exact tpA_nil φ₁ φ₂ d s a b c u
  | cons x l ih =>
    intro a s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some (0 : TPL), s, st5 (x :: l) a b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some (0 : TPL), some x, st5 l (some x :: a) b c u⟩ := tpA_cons φ₁ φ₂ d s x l a b c u
    rw [e, ih]
    simp

theorem tpLoopB (hd : d = none → ∀ x, φ₂ x = none) (c : List (Option Γ₀)) :
    ∀ (t : List Γ₀) (b : List (Option Γ₀)) (u : List Γ₁) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some (1 : TPL), s, st5 [] (t.map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some (2 : TPL), none,
          st5 [] [] (t.reverse.map some ++ b) c ((t.filterMap φ₂).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro b u s; exact tpB_nil φ₁ φ₂ d s b c u
  | cons x t ih =>
    intro b u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some (1 : TPL), s, st5 [] ((x :: t).map some) b c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some (1 : TPL), some x, st5 [] (t.map some) (some x :: b) c ((φ₂ x).toList ++ u)⟩ :=
      tpB_cons φ₁ φ₂ d hd s x (t.map some) b c u
    rw [e, ih]
    cases hφ : φ₂ x <;> simp [hφ]

theorem tpLoopC (u : List Γ₁) :
    ∀ (t : List Γ₀) (c : List (Option Γ₀)) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some (2 : TPL), s, st5 [] [] (t.map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some (3 : TPL), none, st5 [] [] [] (t.reverse.map some ++ c) u⟩ := by
  intro t
  induction t with
  | nil => intro c s; exact tpC_nil φ₁ φ₂ d s c u
  | cons x t ih =>
    intro c s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some (2 : TPL), s, st5 [] [] ((x :: t).map some) c u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some (2 : TPL), some x, st5 [] [] (t.map some) (some x :: c) u⟩ :=
      tpC_cons φ₁ φ₂ d s x (t.map some) c u
    rw [e, ih]
    simp

theorem tpLoopE (hd : d = none → ∀ x, φ₁ x = none) :
    ∀ (t : List Γ₀) (u : List Γ₁) (s : Option Γ₀),
      (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[t.length + 1]
          (some (⟨some (3 : TPL), s, st5 [] [] [] (t.map some) u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨none, none, st5 [] [] [] [] ((t.filterMap φ₁).reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u s; exact tpE_nil φ₁ φ₂ d s u
  | cons x t ih =>
    intro u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (tpProg φ₁ φ₂ d))
        (some (⟨some (3 : TPL), s, st5 [] [] [] ((x :: t).map some) u⟩ : TPCfg Γ₀ Γ₁)) =
        some ⟨some (3 : TPL), some x, st5 [] [] [] (t.map some) ((φ₁ x).toList ++ u)⟩ :=
      tpE_cons φ₁ φ₂ d hd s x (t.map some) u
    rw [e, ih]
    cases hφ : φ₁ x <;> simp [hφ]

theorem tp_run [Fintype Γ₀] (hd₁ : d = none → ∀ x, φ₁ x = none)
    (hd₂ : d = none → ∀ x, φ₂ x = none) (l : List Γ₀) :
    (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 + (l.length + 1) + (l.length + 1) +
        (l.length + 1)]
        (some (initList (tp φ₁ φ₂ d) l)) =
      some (haltList (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 +
    (l.length + 1) + (l.length + 1) + (l.length + 1)]
    (some c)) (initList_eq (tp φ₁ φ₂ d) l)).trans
    (Eq.trans ?_ (congrArg some
      (haltList_eq (tp φ₁ φ₂ d) (l.filterMap φ₁ ++ l.filterMap φ₂))).symm)
  show (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1 + (l.length + 1) + (l.length + 1) +
      (l.length + 1)]
    (some (⟨some (0 : TPL), none, Function.update (fun _ => []) (0 : TPK) l⟩ : TPCfg Γ₀ Γ₁)) =
    some (⟨none, none, Function.update (fun _ => []) (4 : TPK)
      (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)
  have hA : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some (0 : TPL), none, st5 l [] [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some (1 : TPL), none, st5 [] (l.reverse.map some) [] [] []⟩ := by
    simpa using tpLoopA φ₁ φ₂ d [] [] [] l [] none
  have hB : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some (1 : TPL), none, st5 [] (l.reverse.map some) [] [] []⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some (2 : TPL), none, st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ := by
    have := tpLoopB φ₁ φ₂ d hd₂ [] l.reverse [] [] none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  have hC : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some (2 : TPL), none, st5 [] [] (l.map some) [] (l.filterMap φ₂)⟩ : TPCfg Γ₀ Γ₁)) =
      some ⟨some (3 : TPL), none, st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ := by
    simpa using tpLoopC φ₁ φ₂ d (l.filterMap φ₂) l [] none
  have hE : (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[l.length + 1]
      (some (⟨some (3 : TPL), none, st5 [] [] [] (l.reverse.map some) (l.filterMap φ₂)⟩ :
        TPCfg Γ₀ Γ₁)) =
      some ⟨none, none, st5 [] [] [] [] (l.filterMap φ₁ ++ l.filterMap φ₂)⟩ := by
    have := tpLoopE φ₁ φ₂ d hd₁ l.reverse (l.filterMap φ₂) none
    rw [List.length_reverse] at this
    simpa [List.filterMap_reverse] using this
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    ← st5_start, hA, hB, hC, hE, st5_end]

theorem twoPass_polyTime {α β αΓ βΓ : Type} [Fintype αΓ] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (φ₁ φ₂ : αΓ → Option βΓ)
    (h : ∀ a, eb (f a) = (ea a).filterMap φ₁ ++ (ea a).filterMap φ₂) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ φ : αΓ → Option βΓ, d = none → ∀ x, φ x = none := by
    intro φ hdn x
    by_cases hn : Nonempty βΓ
    · simp [d, hn] at hdn
    · cases hφ : φ x with
      | none => rfl
      | some y => exact absurd ⟨y⟩ hn
  exact ⟨{
    tm := tp φ₁ φ₂ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 4 * Polynomial.X + Polynomial.C 4
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + ((ea a).length + 1) + ((ea a).length + 1) +
          ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[(ea a).length + 1 +
            ((ea a).length + 1) + ((ea a).length + 1) + ((ea a).length + 1)]
            (some (initList (tp φ₁ φ₂ d) l))) (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (tp φ₁ φ₂ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

abbrev FX : Type := Fin 4

abbrev FL : Type := Fin 5

variable (M : FinTM2)

abbrev FstΓ : M.K ⊕ FX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr (0 : FX) => Bool ⊕ Bool
  | Sum.inr (1 : FX) => Bool
  | Sum.inr (2 : FX) => Bool
  | Sum.inr (3 : FX) => Bool ⊕ Bool

abbrev FstΛ : Type := M.Λ ⊕ FL

abbrev Fstσ : Type := M.σ × Option (Bool ⊕ Bool)

def bit : Option (Bool ⊕ Bool) → Bool
  | none => false
  | some (Sum.inl b) => b
  | some (Sum.inr b) => b

def isFst : Option (Bool ⊕ Bool) → Bool
  | some (Sum.inl _) => true
  | _ => false

variable {M}

def trF : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr (2 : FL))

variable (M)

def firstProg (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) :
    FstΛ M → TM2.Stmt (FstΓ M) (FstΛ M) (Fstσ M)
  | Sum.inl l => trF (M.m l)
  | Sum.inr (0 : FL) =>
    .pop (Sum.inr (0 : FX)) (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isFst s.2)
          (.push (Sum.inr (2 : FX)) (fun s => bit s.2) (.goto fun _ => Sum.inr (0 : FL)))
          (.push (Sum.inr (1 : FX)) (fun s => bit s.2) (.goto fun _ => Sum.inr (0 : FL))))
        (.goto fun _ => Sum.inr (1 : FL)))
  | Sum.inr (1 : FL) =>
    .pop (Sum.inr (2 : FX)) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (bit s.2)) (.goto fun _ => Sum.inr (1 : FL)))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr (2 : FL) =>
    .pop (Sum.inr (1 : FX)) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr (3 : FX)) (fun s => Sum.inr (bit s.2)) (.goto fun _ => Sum.inr (2 : FL)))
        (.goto fun _ => Sum.inr (3 : FL)))
  | Sum.inr (3 : FL) =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inl (e₁ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr (2 : FX)) (fun s => bit s.2) (.goto fun _ => Sum.inr (3 : FL)))
        (.goto fun _ => Sum.inr (4 : FL)))
  | Sum.inr (4 : FL) =>
    .pop (Sum.inr (2 : FX)) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr (3 : FX)) (fun s => Sum.inl (bit s.2)) (.goto fun _ => Sum.inr (4 : FL)))
        .halt)

def firstM (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ FX
    k₀ := Sum.inr (0 : FX)
    k₁ := Sum.inr (3 : FX)
    Γ := FstΓ M
    Λ := FstΛ M
    main := Sum.inr (0 : FL)
    σ := Fstσ M
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
    m := firstProg M e₀ e₁ }

variable {M}

def fstk (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) : ∀ k, List (FstΓ M k)
  | Sum.inl k => S k
  | Sum.inr (0 : FX) => i
  | Sum.inr (1 : FX) => w
  | Sum.inr (2 : FX) => t
  | Sum.inr (3 : FX) => o

section fstk

variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
  (o : List (Bool ⊕ Bool))

theorem fstk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (fstk S i w t o) (Sum.inl k) x = fstk (Function.update S k x) i w t o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; fin_cases j <;> rfl

theorem fstk_set_I (i' : List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr (0 : FX)) i' = fstk S i' w t o := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> rfl

theorem fstk_set_W (w' : List Bool) :
    Function.update (fstk S i w t o) (Sum.inr (1 : FX)) w' = fstk S i w' t o := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> rfl

theorem fstk_set_T (t' : List Bool) :
    Function.update (fstk S i w t o) (Sum.inr (2 : FX)) t' = fstk S i w t' o := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> rfl

theorem fstk_set_O (o' : List (Bool ⊕ Bool)) :
    Function.update (fstk S i w t o) (Sum.inr (3 : FX)) o' = fstk S i w t o' := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> rfl

end fstk

abbrev FCfg1 (M : FinTM2) : Type := TM2.Cfg (FstΓ M) (FstΛ M) (Fstσ M)

def embF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (c : TM2.Cfg M.Γ M.Λ M.σ) : FCfg1 M :=
  ⟨some (c.l.elim (Sum.inr (2 : FL)) Sum.inl), (c.var, b), fstk c.stk i w t o⟩

theorem simF (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trF q) ((v, b) : Fstσ M) (fstk S i w t o) =
      embF b i w t o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← fstk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← fstk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepF (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool) (b : Option (Bool ⊕ Bool))
    (i : List (Bool ⊕ Bool)) (w t : List Bool) (o : List (Bool ⊕ Bool))
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (firstProg M e₀ e₁) (embF b i w t o c) = some (embF b i w t o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w t o (M.m l) v S)

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

theorem iter_trans {σ : Type} (f : σ → Option σ) {a b : ℕ} {x y z : σ}
    (h₁ : (flip bind f)^[a] (some x) = some y) (h₂ : (flip bind f)^[b] (some y) = some z) :
    (flip bind f)^[b + a] (some x) = some z := by
  rw [Function.iterate_add_apply, h₁, h₂]

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool)

section fstk
variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
  (o : List (Bool ⊕ Bool))
@[simp] theorem fstk_M (k : M.K) : fstk S i w t o (Sum.inl k) = S k := rfl
@[simp] theorem fstk_I : fstk S i w t o (Sum.inr (0 : FX)) = i := rfl
@[simp] theorem fstk_W : fstk S i w t o (Sum.inr (1 : FX)) = w := rfl
@[simp] theorem fstk_T : fstk S i w t o (Sum.inr (2 : FX)) = t := rfl
@[simp] theorem fstk_O : fstk S i w t o (Sum.inr (3 : FX)) = o := rfl
end fstk

variable (v : M.σ) (S : ∀ k, List (M.Γ k)) (w : List Bool) (o : List (Bool ⊕ Bool))

theorem f1_inl (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr (0 : FL)), (v, b), fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr (0 : FL)), (v, some (Sum.inl a)), fstk S i w (a :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_T, isFst, bit]

theorem f1_inr (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr (0 : FL)), (v, b), fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr (0 : FL)), (v, some (Sum.inr a)), fstk S i (a :: w) t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_W, isFst, bit]

theorem f1_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr (0 : FL)), (v, b), fstk S [] w t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr (1 : FL)), (v, none), fstk S [] w t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I]

theorem loop1 : ∀ (i : List (Bool ⊕ Bool)) (w t : List Bool) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[i.length + 1]
        (some (⟨some (Sum.inr (0 : FL)), (v, b), fstk S i w t o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inr (1 : FL)), (v, none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
          ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩ := by
  intro i
  induction i with
  | nil => intro w t b; exact f1_nil e₀ e₁ v S w o b t
  | cons x i ih =>
    intro w t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : flip bind (TM2.step (firstProg M e₀ e₁))
          (some (⟨some (Sum.inr (0 : FL)), (v, b), fstk S (Sum.inl a :: i) w t o⟩ : FCfg1 M)) =
          some ⟨some (Sum.inr (0 : FL)), (v, some (Sum.inl a)), fstk S i w (a :: t) o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : flip bind (TM2.step (firstProg M e₀ e₁))
          (some (⟨some (Sum.inr (0 : FL)), (v, b), fstk S (Sum.inr a :: i) w t o⟩ : FCfg1 M)) =
          some ⟨some (Sum.inr (0 : FL)), (v, some (Sum.inr a)), fstk S i (a :: w) t o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t
      rw [e, ih]; simp [List.filterMap_cons]

theorem f2_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr (1 : FL)), (v, b), fstk S [] w (a :: t) o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr (1 : FL)), (v, some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_M, bit]

theorem f2_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr (1 : FL)), (v, b), fstk S [] w [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inl M.main), (v, none), fstk S [] w [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T]

theorem loop2 : ∀ (t : List Bool) (S : ∀ k, List (M.Γ k)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr (1 : FL)), (v, b), fstk S [] w t o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inl M.main), (v, none),
        fstk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) [] w [] o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List Bool).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr (1 : FL)), (v, b), fstk S [] w (a :: t) o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr (1 : FL)), (v, some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t o⟩ := f2_cons e₀ e₁ v S w o b a t
    rw [e, ih]; simp

theorem f3_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (w : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr (2 : FL)), (v, b), fstk S [] (a :: w) [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr (2 : FL)), (v, some (Sum.inl a)), fstk S [] w [] (Sum.inr a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W, fstk_set_O, bit]

theorem f3_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr (2 : FL)), (v, b), fstk S [] [] [] o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr (3 : FL)), (v, none), fstk S [] [] [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W]

theorem loop3 : ∀ (w : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[w.length + 1]
        (some (⟨some (Sum.inr (2 : FL)), (v, b), fstk S [] w [] o⟩ : FCfg1 M)) =
      some ⟨some (Sum.inr (3 : FL)), (v, none), fstk S [] [] [] (w.reverse.map Sum.inr ++ o)⟩ := by
  intro w
  induction w with
  | nil => intro o b; exact f3_nil e₀ e₁ v S o b
  | cons a w ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr (2 : FL)), (v, b), fstk S [] (a :: w) [] o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr (2 : FL)), (v, some (Sum.inl a)), fstk S [] w [] (Sum.inr a :: o)⟩ :=
      f3_cons e₀ e₁ v S o b a w
    rw [e, ih]; simp

theorem f4_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr (3 : FL)), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M) =
      some ⟨some (Sum.inr (3 : FL)), (v, some (Sum.inl (e₁ y))),
        fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_M, bit]

theorem f4_nil (b : Option (Bool ⊕ Bool)) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr (3 : FL)), (v, b), fstk (Function.update S M.k₁ []) [] [] t o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr (4 : FL)), (v, none), fstk (Function.update S M.k₁ []) [] [] t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_M]

theorem loop4 : ∀ (m : List (M.Γ M.k₁)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
        (some (⟨some (Sum.inr (3 : FL)), (v, b), fstk (Function.update S M.k₁ m) [] [] t o⟩ :
          FCfg1 M)) =
      some ⟨some (Sum.inr (4 : FL)), (v, none),
        fstk (Function.update S M.k₁ []) [] [] (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact f4_nil e₀ e₁ v S o b t
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr (3 : FL)), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] t o⟩ :
          FCfg1 M)) =
        some ⟨some (Sum.inr (3 : FL)), (v, some (Sum.inl (e₁ y))),
          fstk (Function.update S M.k₁ m) [] [] (e₁ y :: t) o⟩ := f4_cons e₀ e₁ v S o b y m t
    rw [e, ih]; simp

theorem f5_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (t : List Bool) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr (4 : FL)), (v, b), fstk S [] [] (a :: t) o⟩ : FCfg1 M) =
      some ⟨some (Sum.inr (4 : FL)), (v, some (Sum.inl a)), fstk S [] [] t (Sum.inl a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T, fstk_set_O, bit]

theorem f5_nil (b : Option (Bool ⊕ Bool)) :
    TM2.step (firstProg M e₀ e₁)
        (⟨some (Sum.inr (4 : FL)), (v, b), fstk S [] [] [] o⟩ : FCfg1 M) =
      some ⟨none, (v, none), fstk S [] [] [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_T]

theorem loop5 : ∀ (t : List Bool) (o : List (Bool ⊕ Bool)) (b : Option (Bool ⊕ Bool)),
    (flip bind (TM2.step (firstProg M e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr (4 : FL)), (v, b), fstk S [] [] t o⟩ : FCfg1 M)) =
      some ⟨none, (v, none), fstk S [] [] [] (t.reverse.map Sum.inl ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact f5_nil e₀ e₁ v S o b
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M e₀ e₁))
        (some (⟨some (Sum.inr (4 : FL)), (v, b), fstk S [] [] (a :: t) o⟩ : FCfg1 M)) =
        some ⟨some (Sum.inr (4 : FL)), (v, some (Sum.inl a)), fstk S [] [] t (Sum.inl a :: o)⟩ :=
      f5_cons e₀ e₁ v S o b a t
    rw [e, ih]; simp

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing PEqualNP.Library

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → Bool)

theorem fstk_nil : (fstk (fun _ => []) [] [] [] [] : ∀ k, List (FstΓ M k)) = fun _ => [] := by
  funext j; rcases j with j | j <;> [rfl; (fin_cases j <;> rfl)]

theorem fstk_nil_I (i : List (Bool ⊕ Bool)) :
    (fstk (fun _ => []) i [] [] [] : ∀ k, List (FstΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M k)) (Sum.inr (0 : FX)) i :=
  (fstk_set_I (fun _ => []) [] [] [] [] i).symm.trans (by rw [fstk_nil])

theorem fstk_nil_O (o : List (Bool ⊕ Bool)) :
    (fstk (fun _ => []) [] [] [] o : ∀ k, List (FstΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M k)) (Sum.inr (3 : FX)) o :=
  (fstk_set_O (fun _ => []) [] [] [] [] o).symm.trans (by rw [fstk_nil])

theorem embF_init (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (l : List (M.Γ M.k₀)) :
    embF b i w t o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₀ l) i w t o⟩ : FCfg1 M) := by
  rw [initList_eq]; rfl

theorem embF_halt (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (w t : List Bool)
    (o : List (Bool ⊕ Bool)) (m : List (M.Γ M.k₁)) :
    embF b i w t o (haltList M m) =
      (⟨some (Sum.inr (2 : FL)), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₁ m) i w t o⟩ : FCfg1 M) := by
  rw [haltList_eq]; rfl

theorem filterMap_const_none {γ δ : Type} (l : List γ) :
    l.filterMap (fun _ => (none : Option δ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem encodePair_left (x w : List Bool) :
    (encodePair (x, w)).filterMap Sum.getLeft? = x := by
  have h1 : (Sum.getLeft? ∘ (Sum.inl : Bool → Bool ⊕ Bool) : Bool → Option Bool) = some := rfl
  have h2 : (Sum.getLeft? ∘ (Sum.inr : Bool → Bool ⊕ Bool) : Bool → Option Bool) = fun _ => none := rfl
  simp only [encodePair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.append_nil]

theorem encodePair_right (x w : List Bool) :
    (encodePair (x, w)).filterMap Sum.getRight? = w := by
  have h1 : (Sum.getRight? ∘ (Sum.inl : Bool → Bool ⊕ Bool) : Bool → Option Bool) = fun _ => none := rfl
  have h2 : (Sum.getRight? ∘ (Sum.inr : Bool → Bool ⊕ Bool) : Bool → Option Bool) = some := rfl
  simp only [encodePair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.nil_append]

theorem encodePair_length (x w : List Bool) :
    (encodePair (x, w)).length = x.length + w.length := by
  simp [encodePair]

theorem first_run (x w0 : List Bool) (m : List (M.Γ M.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀))) = some (haltList M m)) :
    ∃ n, n ≤ s + 2 * x.length + 2 * w0.length + 2 * m.length + 5 ∧
      (flip bind (TM2.step (firstProg M e₀ e₁)))^[n]
          (some (initList (firstM M e₀ e₁) (encodePair (x, w0)))) =
        some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁, w0))) := by
  have q1 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(encodePair (x, w0)).length + 1]
      (some (initList (firstM M e₀ e₁) (encodePair (x, w0)))) =
      some (⟨some (Sum.inr (1 : FL)), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M) := by
    have := loop1 e₀ e₁ M.initialState (fun _ => []) [] (encodePair (x, w0)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, fstk_nil_I] at this
    exact (congrArg (fun c => (flip bind (TM2.step (firstProg M e₀ e₁)))^[
      (encodePair (x, w0)).length + 1] (some c))
      (initList_eq (firstM M e₀ e₁) (encodePair (x, w0)))).trans this
  have q2 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[x.reverse.length + 1]
      (some (⟨some (Sum.inr (1 : FL)), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse []⟩ : FCfg1 M)) =
      some (embF none [] w0.reverse [] [] (initList M (x.map e₀))) := by
    have := loop2 e₀ e₁ M.initialState w0.reverse [] x.reverse (fun _ => []) none
    rw [embF_init]
    simpa using this
  have q3 := simulate (TM2.step M.m) (TM2.step (firstProg M e₀ e₁))
    (embF none [] w0.reverse [] []) (stepF e₀ e₁ none [] w0.reverse [] []) s _ _ h
  rw [embF_halt] at q3
  have q4 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[w0.reverse.length + 1]
      (some (⟨some (Sum.inr (2 : FL)), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] w0.reverse [] []⟩ : FCfg1 M)) =
      some (⟨some (Sum.inr (3 : FL)), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M) := by
    have := loop3 e₀ e₁ M.initialState (Function.update (fun _ => []) M.k₁ m) w0.reverse [] none
    simpa using this
  have q5 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[m.length + 1]
      (some (⟨some (Sum.inr (3 : FL)), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] (w0.map Sum.inr)⟩ : FCfg1 M)) =
      some (⟨some (Sum.inr (4 : FL)), (M.initialState, none),
        fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M) := by
    have := loop4 e₀ e₁ M.initialState (fun _ => []) (w0.map Sum.inr) m [] none
    simpa using this
  have q6 : (flip bind (TM2.step (firstProg M e₀ e₁)))^[(m.reverse.map e₁).length + 1]
      (some (⟨some (Sum.inr (4 : FL)), (M.initialState, none),
        fstk (fun _ => []) [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg1 M)) =
      some (haltList (firstM M e₀ e₁) (encodePair (m.map e₁, w0))) := by
    have := loop5 e₀ e₁ M.initialState (fun _ => []) (m.reverse.map e₁) (w0.map Sum.inr) none
    rw [fstk_nil_O] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (haltList_eq (firstM M e₀ e₁) (encodePair (m.map e₁, w0)))).symm)
    simp [encodePair]
    rfl
  refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [encodePair_length, List.length_reverse, List.length_map]
  omega

theorem first_polyTime (f : List Bool → List Bool)
    (c : TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    Nonempty (TM2ComputableInPolyTime encodePair encodePair
      (fun p : List Bool × List Bool => (f p.1, p.2))) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let T : Polynomial ℕ :=
    c.time + Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  have key : ∀ p : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair p).length ∧
      (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[n]
          (some (initList (firstM c.tm e₀ e₁) (encodePair p))) =
        some (haltList (firstM c.tm e₀ e₁) (encodePair (f p.1, p.2))) := by
    rintro ⟨x, w⟩
    have hs : ∃ s, s ≤ Polynomial.eval x.length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (x.map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (f x))) :=
      ⟨(c.outputsFun x).steps, (c.outputsFun x).steps_le_m, (c.outputsFun x).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run e₀ e₁ x w _ s h
    have hm : (List.map c.outputAlphabet.invFun (f x)).map e₁ = f x := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (f x)]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have h' := h
    rw [haltList_eq, initList_eq] at h'
    have hlen := run_length c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self, List.length_map] at hlen
    have hin : ((Function.update (fun _ => [] : ∀ k, List (c.tm.Γ k)) c.tm.k₀ (x.map e₀))
        c.tm.k₁).length ≤ x.length := by
      by_cases hk : c.tm.k₁ = c.tm.k₀
      · rw [hk, Function.update_self, List.length_map]
      · rw [Function.update_of_ne hk]; simp
    have b2 : Polynomial.eval x.length c.time ≤ Polynomial.eval (x.length + w.length) c.time :=
      eval_mono _ (by omega)
    have hmul : maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval (x.length + w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, encodePair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm e₀ e₁) l)))
            (hm _ (encodePair p))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm e₀ e₁) l))
              (hm _ (encodePair (f p.1, p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }⟩

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open PEqualNP.Library

private theorem filterMap_map_some {α β γ : Type} (h : α → β) (φ : β → Option γ) (g : α → γ)
    (hφ : ∀ a, φ (h a) = some (g a)) (l : List α) : (l.map h).filterMap φ = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hφ, ih]

private theorem filterMap_map_none {α β γ : Type} (h : α → β) (φ : β → Option γ)
    (hφ : ∀ a, φ (h a) = none) (l : List α) : (l.map h).filterMap φ = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [hφ, ih]

theorem cpt_comp {α β γ αΓ βΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ}
    {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (hf : PEqualNP.Library.ComputableInPolyTime ea eb f)
    (hg : PEqualNP.Library.ComputableInPolyTime eb ec g) :
    PEqualNP.Library.ComputableInPolyTime ea ec (fun a => g (f a)) := by
  obtain ⟨c1⟩ := hf
  obtain ⟨c2⟩ := hg
  exact comp_polyTime ea eb ec f g c1 c2

theorem cpt_swap :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.2, p.1)) := by
  refine twoPass_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some (Sum.inl b)) s)
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some (Sum.inr b)) (fun _ => none) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_none Sum.inl _ (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ Sum.inl (fun _ => rfl) w,
    filterMap_map_some Sum.inl _ Sum.inr (fun _ => rfl) x,
    filterMap_map_none Sum.inr _ (fun _ => rfl) w]
  simp

theorem cpt_dup :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair (fun x : List Bool => (x, x)) := by
  refine twoPass_polyTime _ _ _
    (fun b : Bool => some (Sum.inl b)) (fun b : Bool => some (Sum.inr b)) ?_
  intro x
  have h1 := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some (Sum.inl (β := Bool) b))
    Sum.inl (fun _ => rfl) x
  have h2 := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some (Sum.inr (α := Bool) b))
    Sum.inr (fun _ => rfl) x
  simp only [List.map_id'] at h1 h2
  simp only [encodePair, h1, h2]

theorem cpt_fst :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun _ => none) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_some Sum.inl _ (fun b => b) (fun _ => rfl) x,
    filterMap_map_none Sum.inr _ (fun _ => rfl) w]
  simp

theorem cpt_snd :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.2) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun _ => none) (fun b => some b) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_none Sum.inl _ (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ (fun b => b) (fun _ => rfl) w]
  simp

theorem cpt_append :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1 ++ p.2) := by
  refine filterMap_polyTime _ _ _
    (fun s : Bool ⊕ Bool => Sum.elim (fun b => some b) (fun b => some b) s) ?_
  rintro ⟨x, w⟩
  simp only [encodePair, List.filterMap_append]
  rw [filterMap_map_some Sum.inl _ (fun b => b) (fun _ => rfl) x,
    filterMap_map_some Sum.inr _ (fun b => b) (fun _ => rfl) w]
  simp

theorem cpt_first {f : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (f p.1, p.2)) := by
  obtain ⟨c⟩ := hf
  exact first_polyTime f c

theorem cpt_second {g : List Bool → List Bool}
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair
      PEqualNP.Library.encodePair (fun p : List Bool × List Bool => (p.1, g p.2)) :=
  cpt_comp (cpt_comp cpt_swap (cpt_first hg)) cpt_swap

theorem cpt_pair {f g : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f)
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair (fun x : List Bool => (f x, g x)) :=
  cpt_comp (cpt_comp cpt_dup (cpt_second hg)) (cpt_first hf)

theorem cpt_id :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun x : List Bool => x) := by
  refine filterMap_polyTime _ _ _ (fun b : Bool => some b) ?_
  intro x
  have h := filterMap_map_some (fun b : Bool => b) (fun b : Bool => some b) (fun b => b)
    (fun _ => rfl) x
  simp only [List.map_id'] at h
  exact h.symm

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

abbrev MulK : Type := Fin 5

abbrev MulL : Type := Fin 5

abbrev MulΓ : MulK → Type
  | (0 : MulK) => Bool ⊕ Bool
  | (1 : MulK) => Bool
  | (2 : MulK) => Bool
  | (3 : MulK) => Bool
  | (4 : MulK) => Bool

def mulProg : MulL → TM2.Stmt MulΓ MulL (Option Bool)
  | (0 : MulL) =>
    .pop (0 : MulK) (fun _ o => o.map Sum.isLeft)
      (.branch (fun s => s.isSome)
        (.branch (fun s => s == some true)
          (.push (1 : MulK) (fun _ => true) (.goto fun _ => (0 : MulL)))
          (.push (2 : MulK) (fun _ => true) (.goto fun _ => (0 : MulL))))
        (.goto fun _ => (1 : MulL)))
  | (1 : MulL) =>
    .pop (1 : MulK) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.goto fun _ => (2 : MulL))
        (.goto fun _ => (4 : MulL)))
  | (2 : MulL) =>
    .pop (2 : MulK) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push (3 : MulK) (fun _ => true) (.push (4 : MulK) (fun _ => true) (.goto fun _ => (2 : MulL))))
        (.goto fun _ => (3 : MulL)))
  | (3 : MulL) =>
    .pop (3 : MulK) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push (2 : MulK) (fun _ => true) (.goto fun _ => (3 : MulL)))
        (.goto fun _ => (1 : MulL)))
  | (4 : MulL) =>
    .pop (2 : MulK) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.goto fun _ => (4 : MulL))
        .halt)

def mulTM : FinTM2 where
  K := MulK
  k₀ := (0 : MulK)
  k₁ := (4 : MulK)
  Γ := MulΓ
  Λ := MulL
  main := (0 : MulL)
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := mulProg

def mstk (i : List (Bool ⊕ Bool)) (a b c o : List Bool) : ∀ k, List (MulΓ k)
  | (0 : MulK) => i
  | (1 : MulK) => a
  | (2 : MulK) => b
  | (3 : MulK) => c
  | (4 : MulK) => o

@[simp] theorem mstk_I (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o (0 : MulK) = i := rfl
@[simp] theorem mstk_A (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o (1 : MulK) = a := rfl
@[simp] theorem mstk_B (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o (2 : MulK) = b := rfl
@[simp] theorem mstk_C (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o (3 : MulK) = c := rfl
@[simp] theorem mstk_O (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mstk i a b c o (4 : MulK) = o := rfl

@[simp] theorem mstk_set_I (i i' : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    Function.update (mstk i a b c o) (0 : MulK) i' = mstk i' a b c o := by
  funext k; fin_cases k <;> simp [mstk]
@[simp] theorem mstk_set_A (i : List (Bool ⊕ Bool)) (a a' b c o : List Bool) :
    Function.update (mstk i a b c o) (1 : MulK) a' = mstk i a' b c o := by
  funext k; fin_cases k <;> simp [mstk]
@[simp] theorem mstk_set_B (i : List (Bool ⊕ Bool)) (a b b' c o : List Bool) :
    Function.update (mstk i a b c o) (2 : MulK) b' = mstk i a b' c o := by
  funext k; fin_cases k <;> simp [mstk]
@[simp] theorem mstk_set_C (i : List (Bool ⊕ Bool)) (a b c c' o : List Bool) :
    Function.update (mstk i a b c o) (3 : MulK) c' = mstk i a b c' o := by
  funext k; fin_cases k <;> simp [mstk]
@[simp] theorem mstk_set_O (i : List (Bool ⊕ Bool)) (a b c o o' : List Bool) :
    Function.update (mstk i a b c o) (4 : MulK) o' = mstk i a b c o' := by
  funext k; fin_cases k <;> simp [mstk]

theorem mstk_start (i : List (Bool ⊕ Bool)) :
    mstk i [] [] [] [] = Function.update (fun _ => [] : ∀ k, List (MulΓ k)) (0 : MulK) i := by
  funext k; fin_cases k <;> simp [mstk]

theorem mstk_end (o : List Bool) :
    mstk [] [] [] [] o = Function.update (fun _ => [] : ∀ k, List (MulΓ k)) (4 : MulK) o := by
  funext k; fin_cases k <;> simp [mstk]

abbrev MulCfg : Type := TM2.Cfg MulΓ MulL (Option Bool)

abbrev mulStep : Option MulCfg → Option MulCfg := flip bind (TM2.step mulProg)

theorem split_inl (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some (0 : MulL), s, mstk (Sum.inl y :: i) a b c o⟩) =
      some ⟨some (0 : MulL), some true, mstk i (true :: a) b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem split_inr (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some (0 : MulL), s, mstk (Sum.inr y :: i) a b c o⟩) =
      some ⟨some (0 : MulL), some false, mstk i a (true :: b) c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem split_nil (s : Option Bool) (a b c o : List Bool) :
    mulStep (some ⟨some (0 : MulL), s, mstk [] a b c o⟩) =
      some ⟨some (1 : MulL), none, mstk [] a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem outer_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some (1 : MulL), s, mstk i (y :: a) b c o⟩) =
      some ⟨some (2 : MulL), some y, mstk i a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem outer_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (b c o : List Bool) :
    mulStep (some ⟨some (1 : MulL), s, mstk i [] b c o⟩) =
      some ⟨some (4 : MulL), none, mstk i [] b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem copy_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some (2 : MulL), s, mstk i a (y :: b) c o⟩) =
      some ⟨some (2 : MulL), some y, mstk i a b (true :: c) (true :: o)⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem copy_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a c o : List Bool) :
    mulStep (some ⟨some (2 : MulL), s, mstk i a [] c o⟩) =
      some ⟨some (3 : MulL), none, mstk i a [] c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem back_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some (3 : MulL), s, mstk i a b (y :: c) o⟩) =
      some ⟨some (3 : MulL), some y, mstk i a (true :: b) c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem back_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a b o : List Bool) :
    mulStep (some ⟨some (3 : MulL), s, mstk i a b [] o⟩) =
      some ⟨some (1 : MulL), none, mstk i a b [] o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem clean_cons (s : Option Bool) (y : Bool) (i : List (Bool ⊕ Bool)) (a b c o : List Bool) :
    mulStep (some ⟨some (4 : MulL), s, mstk i a (y :: b) c o⟩) =
      some ⟨some (4 : MulL), some y, mstk i a b c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

theorem clean_nil (s : Option Bool) (i : List (Bool ⊕ Bool)) (a c o : List Bool) :
    mulStep (some ⟨some (4 : MulL), s, mstk i a [] c o⟩) =
      some ⟨none, none, mstk i a [] c o⟩ := by
  simp [mulStep, flip, TM2.step, mulProg, TM2.stepAux]

abbrev rep (n : ℕ) : List Bool := List.replicate n true

theorem rep_succ (n : ℕ) : true :: rep n = rep (n + 1) := rfl

theorem splitLoopW (a : List Bool) :
    ∀ (w : List Bool) (b : ℕ) (s : Option Bool),
      mulStep^[w.length + 1] (some ⟨some (0 : MulL), s, mstk (w.map Sum.inr) a (rep b) [] []⟩) =
        some ⟨some (1 : MulL), none, mstk [] a (rep (w.length + b)) [] []⟩ := by
  intro w
  induction w with
  | nil => intro b s; simpa using split_nil s a (rep b) [] []
  | cons y w ih =>
    intro b s
    rw [List.length_cons, Function.iterate_succ_apply, List.map_cons, split_inr, rep_succ, ih]
    rw [show w.length + (b + 1) = w.length + 1 + b from by omega]

theorem splitLoopX (w : List Bool) :
    ∀ (x : List Bool) (a : ℕ) (s : Option Bool),
      mulStep^[x.length + (w.length + 1)]
          (some ⟨some (0 : MulL), s, mstk (x.map Sum.inl ++ w.map Sum.inr) (rep a) [] [] []⟩) =
        some ⟨some (1 : MulL), none, mstk [] (rep (x.length + a)) (rep w.length) [] []⟩ := by
  intro x
  induction x with
  | nil =>
    intro a s
    simpa using splitLoopW (rep a) w 0 s
  | cons y x ih =>
    intro a s
    rw [List.length_cons, show x.length + 1 + (w.length + 1) = (x.length + (w.length + 1)) + 1
      from by omega, Function.iterate_succ_apply, List.map_cons, List.cons_append, split_inl,
      rep_succ, ih]
    rw [show x.length + (a + 1) = x.length + 1 + a from by omega]

theorem copyLoop (a : List Bool) :
    ∀ (b c o : ℕ) (s : Option Bool),
      mulStep^[b + 1] (some ⟨some (2 : MulL), s, mstk [] a (rep b) (rep c) (rep o)⟩) =
        some ⟨some (3 : MulL), none, mstk [] a [] (rep (b + c)) (rep (b + o))⟩ := by
  intro b
  induction b with
  | zero => intro c o s; simpa using copy_nil s [] a (rep c) (rep o)
  | succ b ih =>
    intro c o s
    rw [Function.iterate_succ_apply, ← rep_succ b, copy_cons, rep_succ, rep_succ, ih]
    rw [show b + (c + 1) = b + 1 + c from by omega, show b + (o + 1) = b + 1 + o from by omega]

theorem backLoop (a o : List Bool) :
    ∀ (c b : ℕ) (s : Option Bool),
      mulStep^[c + 1] (some ⟨some (3 : MulL), s, mstk [] a (rep b) (rep c) o⟩) =
        some ⟨some (1 : MulL), none, mstk [] a (rep (c + b)) [] o⟩ := by
  intro c
  induction c with
  | zero => intro b s; simpa using back_nil s [] a (rep b) o
  | succ c ih =>
    intro b s
    rw [Function.iterate_succ_apply, ← rep_succ c, back_cons, rep_succ, ih]
    rw [show c + (b + 1) = c + 1 + b from by omega]

theorem outerLoop (b : ℕ) :
    ∀ (a o : ℕ) (s : Option Bool),
      mulStep^[a * (2 * b + 3) + 1] (some ⟨some (1 : MulL), s, mstk [] (rep a) (rep b) [] (rep o)⟩) =
        some ⟨some (4 : MulL), none, mstk [] [] (rep b) [] (rep (a * b + o))⟩ := by
  intro a
  induction a with
  | zero => intro o s; simpa using outer_nil s [] (rep b) [] (rep o)
  | succ a ih =>
    intro o s
    rw [show (a + 1) * (2 * b + 3) + 1 = (a * (2 * b + 3) + 1) + ((b + 1) + ((b + 1) + 1))
      from by ring, Function.iterate_add_apply mulStep (a * (2 * b + 3) + 1),
      Function.iterate_add_apply mulStep (b + 1) ((b + 1) + 1),
      Function.iterate_succ_apply mulStep (b + 1), ← rep_succ a, outer_cons]
    have h1 : mulStep^[b + 1]
        (some ⟨some (2 : MulL), some true, mstk [] (rep a) (rep b) [] (rep o)⟩) =
        some ⟨some (3 : MulL), none, mstk [] (rep a) [] (rep b) (rep (b + o))⟩ :=
      copyLoop (rep a) b 0 o (some true)
    rw [h1]
    have h2 : mulStep^[b + 1]
        (some ⟨some (3 : MulL), none, mstk [] (rep a) [] (rep b) (rep (b + o))⟩) =
        some ⟨some (1 : MulL), none, mstk [] (rep a) (rep b) [] (rep (b + o))⟩ :=
      backLoop (rep a) (rep (b + o)) b 0 none
    rw [h2, ih]
    rw [show a * b + (b + o) = (a + 1) * b + o from by ring]

theorem cleanLoop (o : List Bool) :
    ∀ (b : ℕ) (s : Option Bool),
      mulStep^[b + 1] (some ⟨some (4 : MulL), s, mstk [] [] (rep b) [] o⟩) =
        some ⟨none, none, mstk [] [] [] [] o⟩ := by
  intro b
  induction b with
  | zero => intro s; simpa using clean_nil s [] [] [] o
  | succ b ih =>
    intro s
    rw [Function.iterate_succ_apply, ← rep_succ b, clean_cons, ih]

def mulSteps (x w : ℕ) : ℕ := (w + 1) + ((x * (2 * w + 3) + 1) + (x + (w + 1)))

theorem mul_run (x w : List Bool) :
    (flip bind (TM2.step mulProg))^[mulSteps x.length w.length]
        (some (initList mulTM (x.map Sum.inl ++ w.map Sum.inr))) =
      some (haltList mulTM (rep (x.length * w.length))) := by
  refine (congrArg (fun c => (flip bind (TM2.step mulProg))^[mulSteps x.length w.length]
    (some c)) (initList_eq mulTM _)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq mulTM _)).symm)
  show mulStep^[mulSteps x.length w.length]
    (some (⟨some (0 : MulL), none, Function.update (fun _ => []) (0 : MulK)
      (x.map Sum.inl ++ w.map Sum.inr)⟩ : MulCfg)) =
    some (⟨none, none, Function.update (fun _ => []) (4 : MulK) (rep (x.length * w.length))⟩ : MulCfg)
  rw [← mstk_start, ← mstk_end, mulSteps, Function.iterate_add_apply mulStep (w.length + 1),
    Function.iterate_add_apply mulStep (x.length * (2 * w.length + 3) + 1)]
  have h1 : mulStep^[x.length + (w.length + 1)]
      (some ⟨some (0 : MulL), none, mstk (x.map Sum.inl ++ w.map Sum.inr) [] [] [] []⟩) =
      some ⟨some (1 : MulL), none, mstk [] (rep x.length) (rep w.length) [] []⟩ :=
    splitLoopX w x 0 none
  rw [h1]
  have h2 : mulStep^[x.length * (2 * w.length + 3) + 1]
      (some ⟨some (1 : MulL), none, mstk [] (rep x.length) (rep w.length) [] []⟩) =
      some ⟨some (4 : MulL), none, mstk [] [] (rep w.length) [] (rep (x.length * w.length))⟩ :=
    outerLoop w.length x.length 0 none
  rw [h2, cleanLoop]

theorem mul_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)) := by
  exact ⟨{
    tm := mulTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 5 * Polynomial.X + Polynomial.C 3
    outputsFun := fun p =>
      { steps := mulSteps p.1.length p.2.length
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := mul_run p.1 p.2
          exact (congrArg (fun l => (flip bind (TM2.step mulProg))^[mulSteps p.1.length
            p.2.length] (some (initList mulTM l))) (hm _ (encodePair p))).trans
            (this.trans (congrArg (fun l => some (haltList mulTM l)) (hm Bool _).symm))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X, Polynomial.eval_pow, encodePair, List.length_append,
            List.length_map, mulSteps]
          nlinarith [Nat.zero_le (p.1.length * p.1.length),
            Nat.zero_le (p.2.length * p.2.length), Nat.zero_le (p.1.length * p.2.length)] } }⟩

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open PEqualNP.Library

private theorem cpt_mul {f g : List Bool → List Bool}
    (hf : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) f)
    (hg : PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) g) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate ((f x).length * (g x).length) true) :=
  cpt_comp (cpt_pair hf hg) mul_polyTime

private theorem pow_polyTime
    (hconst : ∀ l : List Bool, PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (fun _ : List Bool => l))
    (n : ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (x.length ^ n) true) := by
  induction n with
  | zero => simpa using hconst [true]
  | succ n ih =>
    have h := cpt_mul cpt_id ih
    have e : (fun x : List Bool =>
        List.replicate (x.length * (List.replicate (x.length ^ n) true).length) true) =
        (fun x : List Bool => List.replicate (x.length ^ (n + 1)) true) := by
      funext x
      rw [List.length_replicate, pow_succ, Nat.mul_comm]
    rw [← e]
    exact h

theorem clock_polyTime
    (hconst : ∀ l : List Bool, PEqualNP.Library.ComputableInPolyTime
      (fun x : List Bool => x) (fun x : List Bool => x) (fun _ : List Bool => l))
    (p : Polynomial ℕ) :
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (p.eval x.length) true) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h := cpt_comp (cpt_pair hp hq) cpt_append
    have e : (fun x : List Bool => List.replicate (p.eval x.length) true ++
        List.replicate (q.eval x.length) true) =
        (fun x : List Bool => List.replicate ((p + q).eval x.length) true) := by
      funext x
      rw [Polynomial.eval_add, List.replicate_add]
    rw [← e]
    exact h
  | monomial n a =>
    have h := cpt_mul (hconst (List.replicate a true)) (pow_polyTime hconst n)
    have e : (fun x : List Bool => List.replicate ((List.replicate a true).length *
        (List.replicate (x.length ^ n) true).length) true) =
        (fun x : List Bool =>
          List.replicate ((Polynomial.monomial n a).eval x.length) true) := by
      funext x
      rw [List.length_replicate, List.length_replicate, Polynomial.eval_monomial]
    rw [← e]
    exact h

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing PEqualNP.Library

theorem clockPair_time : ∃ p : Polynomial ℕ, ∀ (t : ℕ → ℕ) (c : ℕ),
    PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (t x.length) true) (fun n => c * t n + c) →
    PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      PEqualNP.Library.encodePair
      (fun x : List Bool => (List.replicate (t x.length) true, x))
      (fun n => c * t n + c + 2 * t n + p.eval n) := by
  classical
  obtain ⟨pd, c1, hc1⟩ := time_of_polyTime cpt_dup
  refine ⟨pd + Polynomial.C 8 * Polynomial.X + Polynomial.C 7, ?_⟩
  rintro t c ⟨c2, hc2⟩
  let e₀ : Bool → c2.tm.Γ c2.tm.k₀ := c2.inputAlphabet.invFun
  let e₁ : c2.tm.Γ c2.tm.k₁ → Bool := c2.outputAlphabet
  let M2 : FinTM2 := firstM c2.tm e₀ e₁
  let φ : c1.tm.Γ c1.tm.k₁ → M2.Γ M2.k₀ := fun y => c1.outputAlphabet y
  let d : Option (M2.Γ M2.k₀) := some (Sum.inl true)
  have hd : d = none → IsEmpty (M2.Γ M2.k₀) := fun h => absurd h (Option.some_ne_none _)
  let T : ℕ → ℕ := fun n => c * t n + c + 2 * t n +
    (pd + Polynomial.C 8 * Polynomial.X + Polynomial.C 7).eval n
  have key : ∀ x : List Bool, ∃ n, n ≤ T x.length ∧
      (flip bind (TM2.step (prog c1.tm M2 φ d)))^[n]
          (some (initList (comp c1.tm M2 φ d) (List.map c1.inputAlphabet.invFun x))) =
        some (haltList (comp c1.tm M2 φ d)
          (encodePair (List.replicate (t x.length) true, x))) := by
    intro x
    have r1 := c1.outputsFun x
    have r2 := c2.outputsFun x
    obtain ⟨n2, hn2, hrun2⟩ := first_run e₀ e₁ x x _ r2.steps r2.evals_in_steps
    have hm : (List.map c2.outputAlphabet.invFun (List.replicate (t x.length) true)).map e₁ =
        List.replicate (t x.length) true := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (List.replicate (t x.length) true)]
      exact List.map_congr_left fun y _ => c2.outputAlphabet.right_inv y
    rw [hm] at hrun2
    have hφ : (List.map c1.outputAlphabet.invFun (encodePair (x, x))).map φ =
        encodePair (x, x) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (encodePair (x, x))]
      exact List.map_congr_left fun y _ => c1.outputAlphabet.right_inv y
    have h2 : (flip bind (TM2.step M2.m))^[n2]
        (some (initList M2 ((List.map c1.outputAlphabet.invFun (encodePair (x, x))).map φ))) =
        some (haltList M2 (encodePair (List.replicate (t x.length) true, x))) := by
      rw [hφ]; exact hrun2
    obtain ⟨n, hn, -, hrun⟩ := comp_run φ d hd _ _ _ r1.steps n2 r1.evals_in_steps h2
    refine ⟨n, hn.trans ?_, hrun⟩
    have b1 : r1.steps ≤ pd.eval x.length := r1.steps_le_m.trans (hc1 _)
    have b2 : r2.steps ≤ c * t x.length + c := r2.steps_le_m.trans (hc2 _)
    simp only [List.length_map, List.length_replicate, encodePair_length] at hn2 ⊢
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    omega
  exact ⟨{
    tm := comp c1.tm M2 φ d
    inputAlphabet := c1.inputAlphabet
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun x =>
      { steps := Classical.choose (key x)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (Classical.choose_spec (key x)).2.trans
            (congrArg (fun l => some (haltList (comp c1.tm M2 φ d) l))
              (hm _ (encodePair (List.replicate (t x.length) true, x))).symm)
        steps_le_m := (Classical.choose_spec (key x)).1 } }, fun _ => le_rfl⟩

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit.Iter

open PEqualNP.Library

open Turing

abbrev IX : Type := Fin 4

abbrev IL : Type := Fin 6

variable (M : FinTM2)

abbrev ItΓ : M.K ⊕ IX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr (0 : IX) => Bool ⊕ Bool
  | Sum.inr (1 : IX) => Bool
  | Sum.inr (2 : IX) => Bool
  | Sum.inr (3 : IX) => Bool

abbrev ItΛ : Type := M.Λ ⊕ IL

abbrev Itσ : Type := M.σ × Option (Bool ⊕ Bool)

variable {M}

def trI : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trI q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trI q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trI q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trI q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trI q₁) (trI q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr (3 : IL))

variable (M)

def iterProg (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool) :
    ItΛ M → TM2.Stmt (ItΓ M) (ItΛ M) (Itσ M)
  | Sum.inl l => trI (M.m l)
  | Sum.inr (0 : IL) =>
    .pop (Sum.inr (0 : IX)) (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isFst s.2)
          (.push (Sum.inr (2 : IX)) (fun s => bit s.2) (.goto fun _ => Sum.inr (0 : IL)))
          (.push (Sum.inr (1 : IX)) (fun s => bit s.2) (.goto fun _ => Sum.inr (0 : IL))))
        (.goto fun _ => Sum.inr (1 : IL)))
  | Sum.inr (1 : IL) =>
    .pop (Sum.inr (2 : IX)) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (bit s.2)) (.goto fun _ => Sum.inr (1 : IL)))
        (.goto fun _ => Sum.inr (2 : IL)))
  | Sum.inr (2 : IL) =>
    .pop (Sum.inr (1 : IX)) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.goto fun _ => Sum.inl M.main)
        (.goto fun _ => Sum.inr (4 : IL)))
  | Sum.inr (3 : IL) =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inl (e₁ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr (2 : IX)) (fun s => bit s.2) (.goto fun _ => Sum.inr (3 : IL)))
        (.goto fun _ => Sum.inr (1 : IL)))
  | Sum.inr (4 : IL) =>
    .pop (Sum.inl M.k₀) (fun s o => (s.1, o.map fun y => Sum.inl (d₀ y)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr (2 : IX)) (fun s => bit s.2) (.goto fun _ => Sum.inr (4 : IL)))
        (.goto fun _ => Sum.inr (5 : IL)))
  | Sum.inr (5 : IL) =>
    .pop (Sum.inr (2 : IX)) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr (3 : IX)) (fun s => bit s.2) (.goto fun _ => Sum.inr (5 : IL)))
        .halt)

def iterM (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ IX
    k₀ := Sum.inr (0 : IX)
    k₁ := Sum.inr (3 : IX)
    Γ := ItΓ M
    Λ := ItΛ M
    main := Sum.inr (0 : IL)
    σ := Itσ M
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
    m := iterProg M e₀ d₀ e₁ }

variable {M}

def istk (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    ∀ k, List (ItΓ M k)
  | Sum.inl k => S k
  | Sum.inr (0 : IX) => i
  | Sum.inr (1 : IX) => cn
  | Sum.inr (2 : IX) => t
  | Sum.inr (3 : IX) => o

section istk

variable (S : ∀ k, List (M.Γ k)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)

@[simp] theorem istk_M (k : M.K) : istk S i cn t o (Sum.inl k) = S k := rfl
@[simp] theorem istk_I : istk S i cn t o (Sum.inr (0 : IX)) = i := rfl
@[simp] theorem istk_C : istk S i cn t o (Sum.inr (1 : IX)) = cn := rfl
@[simp] theorem istk_T : istk S i cn t o (Sum.inr (2 : IX)) = t := rfl
@[simp] theorem istk_O : istk S i cn t o (Sum.inr (3 : IX)) = o := rfl

theorem istk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (istk S i cn t o) (Sum.inl k) x = istk (Function.update S k x) i cn t o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; fin_cases j <;> rfl

theorem istk_set_I (i' : List (Bool ⊕ Bool)) :
    Function.update (istk S i cn t o) (Sum.inr (0 : IX)) i' = istk S i' cn t o := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> rfl

theorem istk_set_C (cn' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr (1 : IX)) cn' = istk S i cn' t o := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> rfl

theorem istk_set_T (t' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr (2 : IX)) t' = istk S i cn t' o := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> rfl

theorem istk_set_O (o' : List Bool) :
    Function.update (istk S i cn t o) (Sum.inr (3 : IX)) o' = istk S i cn t o' := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> rfl

end istk

abbrev ICfg (M : FinTM2) : Type := TM2.Cfg (ItΓ M) (ItΛ M) (Itσ M)

def embI (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (c : TM2.Cfg M.Γ M.Λ M.σ) : ICfg M :=
  ⟨some (c.l.elim (Sum.inr (3 : IL)) Sum.inl), (c.var, b), istk c.stk i cn t o⟩

theorem simI (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trI q) ((v, b) : Itσ M) (istk S i cn t o) =
      embI b i cn t o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← istk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← istk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trI, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepI (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)
    (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (iterProg M e₀ d₀ e₁) (embI b i cn t o c) = some (embI b i cn t o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simI b i cn t o (M.m l) v S)

theorem embI_init (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (l : List (M.Γ M.k₀)) :
    embI b i cn t o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        istk (Function.update (fun _ => []) M.k₀ l) i cn t o⟩ : ICfg M) := by
  rw [initList_eq]; rfl

theorem embI_halt (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool)
    (m : List (M.Γ M.k₁)) :
    embI b i cn t o (haltList M m) =
      (⟨some (Sum.inr (3 : IL)), (M.initialState, b),
        istk (Function.update (fun _ => []) M.k₁ m) i cn t o⟩ : ICfg M) := by
  rw [haltList_eq]; rfl

theorem istk_nil : (istk (fun _ => []) [] [] [] [] : ∀ k, List (ItΓ M k)) = fun _ => [] := by
  funext j; rcases j with j | j <;> [rfl; (fin_cases j <;> rfl)]

theorem istk_nil_I (i : List (Bool ⊕ Bool)) :
    (istk (fun _ => []) i [] [] [] : ∀ k, List (ItΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (ItΓ M k)) (Sum.inr (0 : IX)) i :=
  (istk_set_I (fun _ => []) [] [] [] [] i).symm.trans (by rw [istk_nil])

theorem istk_nil_O (o : List Bool) :
    (istk (fun _ => []) [] [] [] o : ∀ k, List (ItΓ M k)) =
      Function.update (fun _ => [] : ∀ k, List (ItΓ M k)) (Sum.inr (3 : IX)) o :=
  (istk_set_O (fun _ => []) [] [] [] [] o).symm.trans (by rw [istk_nil])

end PEqualNP.Outside.Kit.Iter

namespace PEqualNP.Outside.Kit.Iter

open PEqualNP.Library

open Turing PEqualNP.Library

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)

variable (v : M.σ) (S : ∀ k, List (M.Γ k))

theorem i1_inl (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr (0 : IL)), (v, b), istk S (Sum.inl a :: i) cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr (0 : IL)), (v, some (Sum.inl a)), istk S i cn (a :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I, istk_set_T, isFst, bit]

theorem i1_inr (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr (0 : IL)), (v, b), istk S (Sum.inr a :: i) cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr (0 : IL)), (v, some (Sum.inr a)), istk S i (a :: cn) t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I, istk_set_C, isFst, bit]

theorem i1_nil (b : Option (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr (0 : IL)), (v, b), istk S [] cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr (1 : IL)), (v, none), istk S [] cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_I]

theorem iloop1 (o : List Bool) :
    ∀ (i : List (Bool ⊕ Bool)) (cn t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[i.length + 1]
        (some (⟨some (Sum.inr (0 : IL)), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨some (Sum.inr (1 : IL)), (v, none),
        istk S [] ((i.filterMap Sum.getRight?).reverse ++ cn)
          ((i.filterMap Sum.getLeft?).reverse ++ t) o⟩ := by
  intro i
  induction i with
  | nil => intro cn t b; exact i1_nil e₀ d₀ e₁ v S b cn t o
  | cons x i ih =>
    intro cn t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr (0 : IL)), (v, b), istk S (Sum.inl a :: i) cn t o⟩ : ICfg M)) =
          some ⟨some (Sum.inr (0 : IL)), (v, some (Sum.inl a)), istk S i cn (a :: t) o⟩ :=
        i1_inl e₀ d₀ e₁ v S b a i cn t o
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
          (some (⟨some (Sum.inr (0 : IL)), (v, b), istk S (Sum.inr a :: i) cn t o⟩ : ICfg M)) =
          some ⟨some (Sum.inr (0 : IL)), (v, some (Sum.inr a)), istk S i (a :: cn) t o⟩ :=
        i1_inr e₀ d₀ e₁ v S b a i cn t o
      rw [e, ih]; simp [List.filterMap_cons]

theorem i2_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr (1 : IL)), (v, b), istk S i cn (a :: t) o⟩ : ICfg M) =
      some ⟨some (Sum.inr (1 : IL)), (v, some (Sum.inl a)),
        istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]

theorem i2_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr (1 : IL)), (v, b), istk S i cn [] o⟩ : ICfg M) =
      some ⟨some (Sum.inr (2 : IL)), (v, none), istk S i cn [] o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T]

theorem iloop2 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (t : List Bool) (S : ∀ k, List (M.Γ k)) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[t.length + 1]
        (some (⟨some (Sum.inr (1 : IL)), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨some (Sum.inr (2 : IL)), (v, none),
        istk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) i cn [] o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List Bool).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact i2_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr (1 : IL)), (v, b), istk S i cn (a :: t) o⟩ : ICfg M)) =
        some ⟨some (Sum.inr (1 : IL)), (v, some (Sum.inl a)),
          istk (Function.update S M.k₀ (e₀ a :: S M.k₀)) i cn t o⟩ :=
      i2_cons e₀ d₀ e₁ v S b a i cn t o
    rw [e, ih]; simp

theorem i3_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr (2 : IL)), (v, b), istk S i (a :: cn) t o⟩ : ICfg M) =
      some ⟨some (Sum.inl M.main), (v, some (Sum.inl a)), istk S i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_C]

theorem i3_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr (2 : IL)), (v, b), istk S i [] t o⟩ : ICfg M) =
      some ⟨some (Sum.inr (4 : IL)), (v, none), istk S i [] t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_C]

theorem i4_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁))
    (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr (3 : IL)), (v, b), istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr (3 : IL)), (v, some (Sum.inl (e₁ y))),
        istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]

theorem i4_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr (3 : IL)), (v, b), istk (Function.update S M.k₁ []) i cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr (1 : IL)), (v, none), istk (Function.update S M.k₁ []) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_M]

theorem iloop4 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (m : List (M.Γ M.k₁)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[m.length + 1]
        (some (⟨some (Sum.inr (3 : IL)), (v, b), istk (Function.update S M.k₁ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr (1 : IL)), (v, none),
        istk (Function.update S M.k₁ []) i cn (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact i4_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr (3 : IL)), (v, b),
          istk (Function.update S M.k₁ (y :: m)) i cn t o⟩ : ICfg M)) =
        some ⟨some (Sum.inr (3 : IL)), (v, some (Sum.inl (e₁ y))),
          istk (Function.update S M.k₁ m) i cn (e₁ y :: t) o⟩ :=
      i4_cons e₀ d₀ e₁ v S b y m i cn t o
    rw [e, ih]; simp

theorem i5_cons (b : Option (Bool ⊕ Bool)) (y : M.Γ M.k₀) (m : List (M.Γ M.k₀))
    (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr (4 : IL)), (v, b), istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ :
          ICfg M) =
      some ⟨some (Sum.inr (4 : IL)), (v, some (Sum.inl (d₀ y))),
        istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_M, bit]

theorem i5_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr (4 : IL)), (v, b), istk (Function.update S M.k₀ []) i cn t o⟩ : ICfg M) =
      some ⟨some (Sum.inr (5 : IL)), (v, none), istk (Function.update S M.k₀ []) i cn t o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_M]

theorem iloop5 (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    ∀ (m : List (M.Γ M.k₀)) (t : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[m.length + 1]
        (some (⟨some (Sum.inr (4 : IL)), (v, b), istk (Function.update S M.k₀ m) i cn t o⟩ :
          ICfg M)) =
      some ⟨some (Sum.inr (5 : IL)), (v, none),
        istk (Function.update S M.k₀ []) i cn (m.reverse.map d₀ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact i5_nil e₀ d₀ e₁ v S b i cn t o
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr (4 : IL)), (v, b),
          istk (Function.update S M.k₀ (y :: m)) i cn t o⟩ : ICfg M)) =
        some ⟨some (Sum.inr (4 : IL)), (v, some (Sum.inl (d₀ y))),
          istk (Function.update S M.k₀ m) i cn (d₀ y :: t) o⟩ :=
      i5_cons e₀ d₀ e₁ v S b y m i cn t o
    rw [e, ih]; simp

theorem i6_cons (b : Option (Bool ⊕ Bool)) (a : Bool) (i : List (Bool ⊕ Bool))
    (cn t o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr (5 : IL)), (v, b), istk S i cn (a :: t) o⟩ : ICfg M) =
      some ⟨some (Sum.inr (5 : IL)), (v, some (Sum.inl a)), istk S i cn t (a :: o)⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T, istk_set_O, bit]

theorem i6_nil (b : Option (Bool ⊕ Bool)) (i : List (Bool ⊕ Bool)) (cn o : List Bool) :
    TM2.step (iterProg M e₀ d₀ e₁)
        (⟨some (Sum.inr (5 : IL)), (v, b), istk S i cn [] o⟩ : ICfg M) =
      some ⟨none, (v, none), istk S i cn [] o⟩ := by
  simp [TM2.step, iterProg, TM2.stepAux, istk_set_T]

theorem iloop6 (i : List (Bool ⊕ Bool)) (cn : List Bool) :
    ∀ (t o : List Bool) (b : Option (Bool ⊕ Bool)),
    ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[t.length + 1]
        (some (⟨some (Sum.inr (5 : IL)), (v, b), istk S i cn t o⟩ : ICfg M)) =
      some ⟨none, (v, none), istk S i cn [] (t.reverse ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact i6_nil e₀ d₀ e₁ v S b i cn o
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : (flip bind (TM2.step (iterProg M e₀ d₀ e₁)))
        (some (⟨some (Sum.inr (5 : IL)), (v, b), istk S i cn (a :: t) o⟩ : ICfg M)) =
        some ⟨some (Sum.inr (5 : IL)), (v, some (Sum.inl a)), istk S i cn t (a :: o)⟩ :=
      i6_cons e₀ d₀ e₁ v S b a i cn t o
    rw [e, ih]; simp

theorem update_nil_nil (k : M.K) :
    Function.update (fun _ => [] : ∀ k, List (M.Γ k)) k [] = fun _ => [] :=
  Function.update_eq_self k (fun _ => [] : ∀ k, List (M.Γ k))

theorem main_loop (g : List Bool → List Bool) (k : ℕ) (p : Polynomial ℕ)
    (hk : ∀ y : List Bool, (g y).length ≤ y.length + k)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z) :
    ∀ (cn z : List Bool) (L : ℕ) (b : Option (Bool ⊕ Bool)), z.length + k * cn.length ≤ L →
      ∃ n, n ≤ cn.length * (p.eval L + 2 * L + 3) + 2 * L + 3 ∧
        ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
            (some (⟨some (Sum.inr (2 : IL)), (M.initialState, b),
              istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] cn [] []⟩ : ICfg M)) =
          some ⟨none, (M.initialState, none),
            istk (fun _ => []) [] [] [] (g^[cn.length] z)⟩ := by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz : ((z.map e₀).reverse.map d₀).reverse = z := by
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      conv_rhs => rw [← List.map_id z]
      exact List.map_congr_left fun a _ => hd a
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr (2 : IL)), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ : ICfg M)) =
        some ⟨some (Sum.inr (4 : IL)), (M.initialState, none),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2 := iloop5 e₀ d₀ e₁ M.initialState (fun _ => []) [] [] [] (z.map e₀) [] none
    rw [update_nil_nil, List.append_nil] at q2
    have q3 := iloop6 e₀ d₀ e₁ M.initialState (fun _ => []) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil, hz] at q3
    refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3⟩
    simp only [List.length_reverse, List.length_map, List.length_nil] at hL ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s, m, hs, hm, hmg⟩ := hrun z
    rw [List.length_cons] at hL
    have hgz : (g z).length ≤ z.length + k := hk z
    have hkk : k * (cn.length + 1) = k * cn.length + k := Nat.mul_succ _ _
    have hml : m.length = (g z).length := by rw [← hmg, List.length_map]
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr (2 : IL)), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩ : ICfg M)) =
        some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))) := by
      rw [embI_init]
      exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2 := simulate (TM2.step M.m) (TM2.step (iterProg M e₀ d₀ e₁))
      (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
      s _ _ hm
    rw [embI_halt] at q2
    have q3 := iloop4 e₀ d₀ e₁ M.initialState (fun _ => []) [] cn [] m [] (some (Sum.inl a))
    rw [update_nil_nil, List.append_nil, List.map_reverse, hmg] at q3
    have q4 := iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ => []) none
    rw [List.append_nil, List.reverse_reverse] at q4
    obtain ⟨n, hn, q5⟩ := ih (g z) L none (by omega)
    have e : g^[(a :: cn).length] z = g^[cn.length] (g z) := Function.iterate_succ_apply g _ z
    rw [e]
    refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
    have hp : p.eval z.length ≤ p.eval L := eval_mono p (by omega)
    rw [List.length_reverse, List.length_cons, Nat.succ_mul]
    generalize cn.length * (p.eval L + 2 * L + 3) = A at hn ⊢
    omega

theorem iter_run (g : List Bool → List Bool) (k : ℕ) (p : Polynomial ℕ)
    (hk : ∀ y : List Bool, (g y).length ≤ y.length + k)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z)
    (y u : List Bool) (L : ℕ) (hL : y.length + k * u.length ≤ L) :
    ∃ n, n ≤ u.length * (p.eval L + 2 * L + 3) + 2 * L + 2 * y.length + u.length + 5 ∧
      ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) := by
  have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
      some (⟨some (Sum.inr (1 : IL)), (M.initialState, none),
        istk (fun _ => []) [] u.reverse y.reverse []⟩ : ICfg M) := by
    have := iloop1 e₀ d₀ e₁ M.initialState (fun _ => []) [] (encodePair (y, u)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, istk_nil_I] at this
    exact (congrArg (fun c => ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1] (some c))
      (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y, u)))).trans this
  have q2 := iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ => []) none
  rw [List.append_nil, List.reverse_reverse] at q2
  obtain ⟨n, hn, q3⟩ := main_loop e₀ d₀ e₁ g k p hk hd hrun u.reverse y L none
    (by rw [List.length_reverse]; exact hL)
  rw [List.length_reverse] at hn q3
  rw [istk_nil_O] at q3
  have q3' : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr (2 : IL)), (M.initialState, none),
        istk (Function.update (fun _ => []) M.k₀ (y.map e₀)) [] u.reverse [] []⟩ : ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3'⟩
  rw [encodePair_length, List.length_reverse]
  omega

theorem iter_polyTime (g : List Bool → List Bool)
    (c : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (k : ℕ) (hk : ∀ y : List Bool, (g y).length ≤ y.length + k) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x)
      (fun p : List Bool × List Bool => g^[p.2.length] p.1)) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let d₀ : c.tm.Γ c.tm.k₀ → Bool := c.inputAlphabet
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let W : Polynomial ℕ := Polynomial.X + Polynomial.C k * Polynomial.X
  let T : Polynomial ℕ :=
    Polynomial.X * (c.time.comp W + Polynomial.C 2 * W + Polynomial.C 3) +
      Polynomial.C 2 * W + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  have hd : ∀ a, d₀ (e₀ a) = a := fun a => c.inputAlphabet.right_inv a
  have hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (c.tm.Γ c.tm.k₁)),
      s ≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m) ∧ m.map e₁ = g z := by
    intro z
    refine ⟨(c.outputsFun z).steps, List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m, (c.outputsFun z).evals_in_steps, ?_⟩
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
  have key : ∀ q : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)) := by
    rintro ⟨y, u⟩
    have hku : k * u.length ≤ k * (y.length + u.length) := Nat.mul_le_mul_left _ (by omega)
    obtain ⟨n, hn, hr⟩ := iter_run e₀ d₀ e₁ g k c.time hk hd hrun y u
      (y.length + u.length + k * (y.length + u.length)) (by omega)
    refine ⟨n, hn.trans ?_, hr⟩
    simp only [T, W, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, encodePair_length]
    have hmul : u.length * (Polynomial.eval (y.length + u.length + k * (y.length + u.length))
          c.time + 2 * (y.length + u.length + k * (y.length + u.length)) + 3) ≤
        (y.length + u.length) * (Polynomial.eval
          (y.length + u.length + k * (y.length + u.length)) c.time +
            2 * (y.length + u.length + k * (y.length + u.length)) + 3) :=
      Nat.mul_le_mul_right _ (by omega)
    generalize k * (y.length + u.length) = B at hmul ⊢
    omega
  exact ⟨{
    tm := iterM c.tm e₀ d₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun q =>
      { steps := Classical.choose (key q)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l => some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m := (Classical.choose_spec (key q)).1 } }⟩

end PEqualNP.Outside.Kit.Iter

namespace PEqualNP.Outside.Kit.Iter

open PEqualNP.Library

open Turing PEqualNP.Library

variable {M : FinTM2} (e₀ : Bool → M.Γ M.k₀) (d₀ : M.Γ M.k₀ → Bool) (e₁ : M.Γ M.k₁ → Bool)

theorem main_loop_bdd (g : List Bool → List Bool) (p : Polynomial ℕ)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z) :
    ∀ (cn z : List Bool) (L : ℕ) (b : Option (Bool ⊕ Bool)),
      (∀ j ≤ cn.length, (g^[j] z).length ≤ L) →
      ∃ n, n ≤ cn.length * (p.eval L + 2 * L + 3) + 2 * L + 3 ∧
        ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
            (some (⟨some (Sum.inr (2 : IL)), (M.initialState, b),
              istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] cn [] []⟩ : ICfg M)) =
          some ⟨none, (M.initialState, none),
            istk (fun _ => []) [] [] [] (g^[cn.length] z)⟩ := by
  intro cn
  induction cn with
  | nil =>
    intro z L b hL
    have hz : ((z.map e₀).reverse.map d₀).reverse = z := by
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      conv_rhs => rw [← List.map_id z]
      exact List.map_congr_left fun a _ => hd a
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr (2 : IL)), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ : ICfg M)) =
        some ⟨some (Sum.inr (4 : IL)), (M.initialState, none),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] [] [] []⟩ :=
      i3_nil e₀ d₀ e₁ M.initialState _ b [] [] []
    have q2 := iloop5 e₀ d₀ e₁ M.initialState (fun _ => []) [] [] [] (z.map e₀) [] none
    rw [update_nil_nil, List.append_nil] at q2
    have q3 := iloop6 e₀ d₀ e₁ M.initialState (fun _ => []) [] []
      ((z.map e₀).reverse.map d₀) [] none
    rw [List.append_nil, hz] at q3
    refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3⟩
    have hz0 : z.length ≤ L := hL 0 (Nat.zero_le _)
    simp only [List.length_reverse, List.length_map, List.length_nil] at hz0 ⊢
    omega
  | cons a cn ih =>
    intro z L b hL
    obtain ⟨s, m, hs, hm, hmg⟩ := hrun z
    rw [List.length_cons] at hL
    have hz0 : z.length ≤ L := hL 0 (Nat.zero_le _)
    have hgz : (g z).length ≤ L := hL 1 (by omega)
    have hml : m.length = (g z).length := by rw [← hmg, List.length_map]
    have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[1]
        (some (⟨some (Sum.inr (2 : IL)), (M.initialState, b),
          istk (Function.update (fun _ => []) M.k₀ (z.map e₀)) [] (a :: cn) [] []⟩ : ICfg M)) =
        some (embI (some (Sum.inl a)) [] cn [] [] (initList M (z.map e₀))) := by
      rw [embI_init]
      exact i3_cons e₀ d₀ e₁ M.initialState _ b a [] cn [] []
    have q2 := simulate (TM2.step M.m) (TM2.step (iterProg M e₀ d₀ e₁))
      (embI (some (Sum.inl a)) [] cn [] []) (stepI e₀ d₀ e₁ (some (Sum.inl a)) [] cn [] [])
      s _ _ hm
    rw [embI_halt] at q2
    have q3 := iloop4 e₀ d₀ e₁ M.initialState (fun _ => []) [] cn [] m [] (some (Sum.inl a))
    rw [update_nil_nil, List.append_nil, List.map_reverse, hmg] at q3
    have q4 := iloop2 e₀ d₀ e₁ M.initialState [] cn [] (g z).reverse (fun _ => []) none
    rw [List.append_nil, List.reverse_reverse] at q4
    obtain ⟨n, hn, q5⟩ := ih (g z) L none (fun j hj => by
      have := hL (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    have e : g^[(a :: cn).length] z = g^[cn.length] (g z) := Function.iterate_succ_apply g _ z
    rw [e]
    refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3) q4) q5⟩
    have hp : p.eval z.length ≤ p.eval L := eval_mono p (by omega)
    rw [List.length_reverse, List.length_cons, Nat.succ_mul]
    generalize cn.length * (p.eval L + 2 * L + 3) = A at hn ⊢
    omega

theorem iter_run_bdd (g : List Bool → List Bool) (p : Polynomial ℕ)
    (hd : ∀ a, d₀ (e₀ a) = a)
    (hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (M.Γ M.k₁)), s ≤ p.eval z.length ∧
      (flip bind (TM2.step M.m))^[s] (some (initList M (z.map e₀))) = some (haltList M m) ∧
        m.map e₁ = g z)
    (y u : List Bool) (L : ℕ) (hL : ∀ j ≤ u.length, (g^[j] y).length ≤ L) :
    ∃ n, n ≤ u.length * (p.eval L + 2 * L + 3) + 2 * L + 2 * y.length + u.length + 5 ∧
      ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n] (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
        some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) := by
  have q1 : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1]
      (some (initList (iterM M e₀ d₀ e₁) (encodePair (y, u)))) =
      some (⟨some (Sum.inr (1 : IL)), (M.initialState, none),
        istk (fun _ => []) [] u.reverse y.reverse []⟩ : ICfg M) := by
    have := iloop1 e₀ d₀ e₁ M.initialState (fun _ => []) [] (encodePair (y, u)) [] [] none
    rw [encodePair_left, encodePair_right, List.append_nil, List.append_nil, istk_nil_I] at this
    exact (congrArg (fun c => ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[(encodePair (y, u)).length + 1] (some c))
      (initList_eq (iterM M e₀ d₀ e₁) (encodePair (y, u)))).trans this
  have q2 := iloop2 e₀ d₀ e₁ M.initialState [] u.reverse [] y.reverse (fun _ => []) none
  rw [List.append_nil, List.reverse_reverse] at q2
  obtain ⟨n, hn, q3⟩ := main_loop_bdd e₀ d₀ e₁ g p hd hrun u.reverse y L none
    (by rw [List.length_reverse]; exact hL)
  rw [List.length_reverse] at hn q3
  rw [istk_nil_O] at q3
  have q3' : ((flip bind (TM2.step (iterProg M e₀ d₀ e₁))))^[n]
      (some (⟨some (Sum.inr (2 : IL)), (M.initialState, none),
        istk (Function.update (fun _ => []) M.k₀ (y.map e₀)) [] u.reverse [] []⟩ : ICfg M)) =
      some (haltList (iterM M e₀ d₀ e₁) (g^[u.length] y)) :=
    q3.trans (congrArg some (haltList_eq (iterM M e₀ d₀ e₁) (g^[u.length] y))).symm
  refine ⟨_, ?_, iter_trans _ (iter_trans _ q1 q2) q3'⟩
  rw [encodePair_length, List.length_reverse]
  omega

theorem iterate_length_measure (g : List Bool → List Bool) (m : List Bool → ℕ)
    (hm : ∀ y : List Bool, m (g y) ≤ m y)
    (hg : ∀ y : List Bool, (g y).length ≤ y.length + m y) (y : List Bool) :
    ∀ j : ℕ, m (g^[j] y) ≤ m y ∧ (g^[j] y).length ≤ y.length + j * m y := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Nat.succ_mul]
    have h1 := hm (g^[j] y)
    have h2 := hg (g^[j] y)
    obtain ⟨i1, i2⟩ := ih
    generalize j * m y = A at i2 ⊢
    exact ⟨by omega, by omega⟩

theorem measure_arith (A B L V y u : ℕ) (hLV : L ≤ V) (hAB : A ≤ B) :
    A + 2 * L + 2 * y + u + 5 ≤ B + 2 * V + 3 * (y + u) + 5 := by
  omega

theorem iter_polyTime_measure (g : List Bool → List Bool)
    (c : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) g)
    (m : List Bool → ℕ) (a : ℕ)
    (hm : ∀ y : List Bool, m (g y) ≤ m y)
    (hg : ∀ y : List Bool, (g y).length ≤ y.length + m y)
    (ha : ∀ y : List Bool, m y ≤ a * y.length + a) :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      (fun x : List Bool => x) (fun p : List Bool × List Bool => g^[p.2.length] p.1)) := by
  let e₀ : Bool → c.tm.Γ c.tm.k₀ := c.inputAlphabet.invFun
  let d₀ : c.tm.Γ c.tm.k₀ → Bool := c.inputAlphabet
  let e₁ : c.tm.Γ c.tm.k₁ → Bool := c.outputAlphabet
  let W : Polynomial ℕ :=
    Polynomial.X + Polynomial.X * (Polynomial.C a * Polynomial.X + Polynomial.C a)
  let T : Polynomial ℕ :=
    Polynomial.X * (c.time.comp W + Polynomial.C 2 * W + Polynomial.C 3) +
      Polynomial.C 2 * W + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  have hd : ∀ a, d₀ (e₀ a) = a := fun a => c.inputAlphabet.right_inv a
  have hrun : ∀ z : List Bool, ∃ (s : ℕ) (m : List (c.tm.Γ c.tm.k₁)),
      s ≤ c.time.eval z.length ∧
      (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm (z.map e₀))) =
        some (haltList c.tm m) ∧ m.map e₁ = g z := by
    intro z
    refine ⟨(c.outputsFun z).steps, List.map c.outputAlphabet.invFun (g z),
      (c.outputsFun z).steps_le_m, (c.outputsFun z).evals_in_steps, ?_⟩
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (g z)]
    exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
  have key : ∀ q : List Bool × List Bool, ∃ n, n ≤ T.eval (encodePair q).length ∧
      (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[n]
          (some (initList (iterM c.tm e₀ d₀ e₁) (encodePair q))) =
        some (haltList (iterM c.tm e₀ d₀ e₁) (g^[q.2.length] q.1)) := by
    rintro ⟨y, u⟩
    have hL : ∀ j ≤ u.length,
        (g^[j] y).length ≤ y.length + u.length * (a * y.length + a) := by
      intro j hj
      have h1 := (iterate_length_measure g m hm hg y j).2
      have h2 : j * m y ≤ u.length * (a * y.length + a) := Nat.mul_le_mul hj (ha y)
      omega
    obtain ⟨n, hn, hr⟩ := iter_run_bdd e₀ d₀ e₁ g c.time hd hrun y u
      (y.length + u.length * (a * y.length + a)) hL
    have hLV : y.length + u.length * (a * y.length + a) ≤
        (y.length + u.length) + (y.length + u.length) * (a * (y.length + u.length) + a) :=
      Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega)
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _))
    have hp := eval_mono c.time hLV
    have hmul : u.length * (Polynomial.eval (y.length + u.length * (a * y.length + a)) c.time +
          2 * (y.length + u.length * (a * y.length + a)) + 3) ≤
        (y.length + u.length) * (Polynomial.eval
          ((y.length + u.length) + (y.length + u.length) * (a * (y.length + u.length) + a))
            c.time +
            2 * ((y.length + u.length) +
              (y.length + u.length) * (a * (y.length + u.length) + a)) + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine ⟨n, hn.trans ?_, hr⟩
    simp only [T, W, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_comp, encodePair_length]
    exact measure_arith _ _ _ _ _ _ hLV hmul
  exact ⟨{
    tm := iterM c.tm e₀ d₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun q =>
      { steps := Classical.choose (key q)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (iterProg c.tm e₀ d₀ e₁)))^[
            Classical.choose (key q)] (some (initList (iterM c.tm e₀ d₀ e₁) l)))
            (hm _ (encodePair q))).trans ((Classical.choose_spec (key q)).2.trans
            (congrArg (fun l => some (haltList (iterM c.tm e₀ d₀ e₁) l))
              (hm _ (g^[q.2.length] q.1)).symm))
        steps_le_m := (Classical.choose_spec (key q)).1 } }⟩

end PEqualNP.Outside.Kit.Iter

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

def pushList : List Bool → TM2.Stmt (fun _ : Unit => Bool) Unit Bool
  | [] => .halt
  | a :: l => .push () (fun _ => a) (pushList l)

def constListProg (l : List Bool) : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit Bool :=
  fun _ => .pop () (fun _ o => o.isSome)
    (.branch (fun s => s)
      (.load (fun _ => false) (.goto fun _ => ()))
      (pushList l.reverse))

def constList (l : List Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m := constListProg l

abbrev CLCfg : Type := TM2.Cfg (fun _ : Unit => Bool) Unit Bool

theorem update_unit (S T : List Bool) :
    Function.update (fun _ : Unit => S) () T = fun _ => T := by
  funext k
  simp

theorem pushList_stepAux (l : List Bool) (v : Bool) (S : List Bool) :
    TM2.stepAux (pushList l) v (fun _ : Unit => S) =
      (⟨none, v, fun _ => l.reverse ++ S⟩ : CLCfg) := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih =>
    simp only [pushList, TM2.stepAux]
    rw [update_unit, ih]
    simp

theorem constList_cons (l : List Bool) (x : Bool) (a : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => x :: a⟩ : CLCfg) =
      some ⟨some (), false, fun _ => a⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp

theorem constList_nil (l : List Bool) :
    TM2.step (constListProg l) (⟨some (), false, fun _ => []⟩ : CLCfg) =
      some ⟨none, false, fun _ => l⟩ := by
  simp only [TM2.step, constListProg, TM2.stepAux]
  rw [update_unit]
  simp only [List.head?_nil, Option.isSome_none, Bool.cond_false, List.tail_nil]
  rw [pushList_stepAux]
  simp

theorem constList_loop (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (⟨some (), false, fun _ => a⟩ : CLCfg)) =
      some ⟨none, false, fun _ => l⟩ := by
  induction a with
  | nil => exact constList_nil l
  | cons x a ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (constListProg l))
        (some (⟨some (), false, fun _ => x :: a⟩ : CLCfg)) =
        some ⟨some (), false, fun _ => a⟩ := constList_cons l x a
    rw [e, ih]

theorem constList_run (l : List Bool) (a : List Bool) :
    (flip bind (TM2.step (constListProg l)))^[a.length + 1]
        (some (initList (constList l) a)) = some (haltList (constList l) l) := by
  refine (congrArg (fun c => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some c)) (initList_eq (constList l) a)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (constList l) l)).symm)
  show (flip bind (TM2.step (constListProg l)))^[a.length + 1]
    (some (⟨some (), false, Function.update (fun _ => []) () a⟩ : CLCfg)) =
    some (⟨none, false, Function.update (fun _ => []) () l⟩ : CLCfg)
  rw [update_unit, update_unit]
  exact constList_loop l a

theorem constList_polyTime (l : List Bool) :
    Nonempty (Turing.TM2ComputableInPolyTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun _ : List Bool => l)) :=
  ⟨{
    tm := constList l
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.X + 1
    outputsFun := fun a =>
      { steps := a.length + 1
        evals_in_steps := by
          have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
          exact (congrArg (fun x => (flip bind (TM2.step (constListProg l)))^[a.length + 1]
            (some (initList (constList l) x))) (hm a)).trans
            ((constList_run l a).trans
              (congrArg (fun x => some (haltList (constList l) x)) (hm l).symm))
        steps_le_m := by simp } }⟩

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

def constBool (b : Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := TM2.Stmt.pop () (fun _ o => o.isSome)
    (TM2.Stmt.branch (fun s => s)
      (TM2.Stmt.load (fun _ => false) (TM2.Stmt.goto fun _ => ()))
      (TM2.Stmt.push () (fun _ => b) TM2.Stmt.halt))

theorem constBool_run (b : Bool) (l : List Bool) :
    (flip bind (constBool b).step)^[l.length + 1]
      (some (⟨some (), false, fun _ => l⟩ : (constBool b).Cfg)) =
      some (⟨none, false, fun _ => [b]⟩ : (constBool b).Cfg) := by
  induction l with
  | nil =>
    simp only [List.length_nil, Function.iterate_succ_apply, Function.iterate_zero_apply]
    show some _ = some _
    congr 1
  | cons a l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    rw [← ih]
    congr 1

noncomputable def constBoolComputable (b : Bool) :
    TM2ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun _ : List Bool => b) where
  tm := constBool b
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun a :=
    { steps := a.length + 1
      evals_in_steps := by
        have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
        have e1 : (some (initList (constBool b) (List.map (Equiv.refl Bool).invFun a)) :
            Option (constBool b).Cfg) = some ⟨some (), false, fun _ => a⟩ :=
          congrArg (fun l : List Bool =>
            (some (⟨some (), false, fun _ => l⟩ : (constBool b).Cfg))) (hm a)
        exact Eq.trans (congrArg ((flip bind (constBool b).step)^[a.length + 1]) e1)
          (constBool_run b a)
      steps_le_m := by simp }

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit.Rev

open PEqualNP.Library

open Turing

def prog : Unit → TM2.Stmt (fun _ : Bool => Bool) Unit (Option Bool)
  | () =>
    .pop false (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push true (fun s => s.getD false) (.load (fun _ => none) (.goto fun _ => ())))
        .halt)

def tm : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m := prog

abbrev RCfg : Type := TM2.Cfg (fun _ : Bool => Bool) Unit (Option Bool)

def st (l u : List Bool) : Bool → List Bool := fun k => cond k u l

theorem st_start (l : List Bool) :
    st l [] = Function.update (fun _ => ([] : List Bool)) false l := by
  funext k; cases k <;> simp [st]

theorem st_end (u : List Bool) :
    st [] u = Function.update (fun _ => ([] : List Bool)) true u := by
  funext k; cases k <;> simp [st]

theorem step_cons (x : Bool) (l u : List Bool) :
    TM2.step prog (⟨some (), none, st (x :: l) u⟩ : RCfg) =
      some ⟨some (), none, st l (x :: u)⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp only [st, Bool.cond_false, List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true,
    Option.getD_some, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
  funext k; cases k <;> simp [st]

theorem step_nil (u : List Bool) :
    TM2.step prog (⟨some (), none, st [] u⟩ : RCfg) = some ⟨none, none, st [] u⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp only [st, Bool.cond_false, List.head?_nil, List.tail_nil, Option.isSome_none,
    Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
  funext k; cases k <;> simp [st]

theorem loop : ∀ (l u : List Bool),
    (flip bind (TM2.step prog))^[l.length + 1] (some (⟨some (), none, st l u⟩ : RCfg)) =
      some ⟨none, none, st [] (l.reverse ++ u)⟩ := by
  intro l
  induction l with
  | nil => intro u; exact step_nil u
  | cons x l ih =>
    intro u
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step prog) (some (⟨some (), none, st (x :: l) u⟩ : RCfg)) =
        some ⟨some (), none, st l (x :: u)⟩ := step_cons x l u
    rw [e, ih]
    simp

theorem run (l : List Bool) :
    (flip bind (TM2.step prog))^[l.length + 1] (some (initList tm l)) =
      some (haltList tm l.reverse) := by
  refine (congrArg (fun c => (flip bind (TM2.step prog))^[l.length + 1] (some c))
    (initList_eq tm l)).trans (Eq.trans ?_ (congrArg some (haltList_eq tm l.reverse)).symm)
  show (flip bind (TM2.step prog))^[l.length + 1]
    (some (⟨some (), none, Function.update (fun _ => []) false l⟩ : RCfg)) =
    some (⟨none, none, Function.update (fun _ => []) true l.reverse⟩ : RCfg)
  rw [← st_start, loop, ← st_end]
  simp

noncomputable def reverseComputable :
    TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x.reverse) where
  tm := tm
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun a :=
    { steps := a.length + 1
      evals_in_steps := by
        have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
        exact (congrArg (fun l => (flip bind (TM2.step prog))^[a.length + 1]
          (some (initList tm l))) (hm a)).trans
          ((run a).trans (congrArg (fun l => some (haltList tm l)) (hm a.reverse).symm))
      steps_le_m := by simp }

end PEqualNP.Outside.Kit.Rev

namespace PEqualNP.Outside.Kit.LenCmp

open PEqualNP.Library

open Turing

abbrev LΓ : Bool × Bool → Type
  | (false, false) => Bool ⊕ Bool
  | (false, true) => Unit
  | (true, false) => Unit
  | (true, true) => Bool

abbrev LL : Type := Fin 4

def lenProg : LL → TM2.Stmt LΓ LL (Bool × Bool)
  | (0 : LL) =>
    .pop (false, false) (fun _ o => (o.isSome, (o.map Sum.isRight).getD false))
      (.branch (fun s => s.1)
        (.branch (fun s => s.2)
          (.push (true, false) (fun _ => ()) (.goto fun _ => (0 : LL)))
          (.push (false, true) (fun _ => ()) (.goto fun _ => (0 : LL))))
        (.goto fun _ => (1 : LL)))
  | (1 : LL) =>
    .pop (false, true) (fun s o => (o.isSome, s.2))
      (.pop (true, false) (fun s o => (s.1, o.isSome))
        (.branch (fun s => s.2)
          (.branch (fun s => s.1)
            (.goto fun _ => (1 : LL))
            (.load (fun _ => (false, false)) (.goto fun _ => (3 : LL))))
          (.load (fun _ => (false, false)) (.goto fun _ => (2 : LL)))))
  | (2 : LL) =>
    .pop (false, true) (fun s o => (o.isSome, s.2))
      (.branch (fun s => s.1)
        (.goto fun _ => (2 : LL))
        (.push (true, true) (fun _ => true) (.load (fun _ => (false, false)) .halt)))
  | (3 : LL) =>
    .pop (true, false) (fun s o => (o.isSome, s.2))
      (.branch (fun s => s.1)
        (.goto fun _ => (3 : LL))
        (.push (true, true) (fun _ => false) (.load (fun _ => (false, false)) .halt)))

def lenM : FinTM2 where
  K := Bool × Bool
  k₀ := (false, false)
  k₁ := (true, true)
  Γ := LΓ
  Λ := LL
  main := (0 : LL)
  σ := Bool × Bool
  initialState := (false, false)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := lenProg

def lst (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) : ∀ k, List (LΓ k)
  | (false, false) => l
  | (false, true) => List.replicate a ()
  | (true, false) => List.replicate b ()
  | (true, true) => o

theorem lst_in (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (false, false) = l := rfl

theorem lst_a (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (false, true) = List.replicate a () := rfl

theorem lst_b (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (true, false) = List.replicate b () := rfl

theorem lst_out (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    lst l a b o (true, true) = o := rfl

theorem lst_set_in (l l' : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (false, false) l' = lst l' a b o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_a (l : List (Bool ⊕ Bool)) (a a' b : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (false, true) (List.replicate a' ()) = lst l a' b o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_b (l : List (Bool ⊕ Bool)) (a b b' : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (true, false) (List.replicate b' ()) = lst l a b' o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_set_b0 (l : List (Bool ⊕ Bool)) (a b : ℕ) (o : List Bool) :
    Function.update (lst l a b o) (true, false) [] = lst l a 0 o :=
  lst_set_b l a b 0 o

theorem lst_set_out (l : List (Bool ⊕ Bool)) (a b : ℕ) (o o' : List Bool) :
    Function.update (lst l a b o) (true, true) o' = lst l a b o' := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_start (l : List (Bool ⊕ Bool)) :
    lst l 0 0 [] = Function.update (fun _ => [] : ∀ k, List (LΓ k)) (false, false) l := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

theorem lst_end (o : List Bool) :
    lst [] 0 0 o = Function.update (fun _ => [] : ∀ k, List (LΓ k)) (true, true) o := by
  funext ⟨x, y⟩
  cases x <;> cases y <;> simp [lst]

abbrev LCfg : Type := TM2.Cfg LΓ LL (Bool × Bool)

abbrev lenStep : Option LCfg → Option LCfg := flip bind (TM2.step lenProg)

theorem split_inl (s : Bool × Bool) (x : Bool) (l : List (Bool ⊕ Bool)) (a b : ℕ)
    (o : List Bool) :
    TM2.step lenProg (⟨some (0 : LL), s, lst (Sum.inl x :: l) a b o⟩ : LCfg) =
      some ⟨some (0 : LL), (true, false), lst l (a + 1) b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.map_some,
    Sum.isRight_inl, Option.getD_some, Bool.cond_true, Bool.cond_false]
  rw [lst_set_in, lst_a, ← List.replicate_succ, lst_set_a]

theorem split_inr (s : Bool × Bool) (x : Bool) (l : List (Bool ⊕ Bool)) (a b : ℕ)
    (o : List Bool) :
    TM2.step lenProg (⟨some (0 : LL), s, lst (Sum.inr x :: l) a b o⟩ : LCfg) =
      some ⟨some (0 : LL), (true, true), lst l a (b + 1) o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.map_some,
    Sum.isRight_inr, Option.getD_some, Bool.cond_true]
  rw [lst_set_in, lst_b, ← List.replicate_succ, lst_set_b]

theorem split_nil (s : Bool × Bool) (a b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some (0 : LL), s, lst [] a b o⟩ : LCfg) =
      some ⟨some (1 : LL), (false, false), lst [] a b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_in]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Option.map_none,
    Option.getD_none, Bool.cond_false]
  rw [lst_set_in]

theorem cmp_ss (s : Bool × Bool) (a b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some (1 : LL), s, lst [] (a + 1) (b + 1) o⟩ : LCfg) =
      some ⟨some (1 : LL), (true, true), lst [] a b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some]
  rw [lst_set_a, lst_b]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_b]

theorem cmp_b0 (s : Bool × Bool) (a : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some (1 : LL), s, lst [] a 0 o⟩ : LCfg) =
      some ⟨some (2 : LL), (false, false), lst [] (a - 1) 0 o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a, List.tail_replicate, lst_set_a, lst_b]
  simp only [List.replicate_zero, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false]
  rw [lst_set_b0]

theorem cmp_a0 (s : Bool × Bool) (b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some (1 : LL), s, lst [] 0 (b + 1) o⟩ : LCfg) =
      some ⟨some (3 : LL), (false, false), lst [] 0 b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a, List.tail_replicate, lst_set_a, lst_b]
  simp only [List.replicate_zero, List.replicate_succ, List.head?_nil, List.head?_cons,
    List.tail_cons, Option.isSome_none, Option.isSome_some, Bool.cond_false, Bool.cond_true]
  rw [lst_set_b]

theorem eraseA_s (s : Bool × Bool) (a : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some (2 : LL), s, lst [] (a + 1) 0 o⟩ : LCfg) =
      some ⟨some (2 : LL), (true, s.2), lst [] a 0 o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_a]

theorem eraseA_0 (s : Bool × Bool) (o : List Bool) :
    TM2.step lenProg (⟨some (2 : LL), s, lst [] 0 0 o⟩ : LCfg) =
      some ⟨none, (false, false), lst [] 0 0 (true :: o)⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_a, List.tail_replicate, lst_set_a]
  simp only [List.replicate_zero, List.head?_nil, Option.isSome_none, Bool.cond_false]
  rw [lst_out, lst_set_out]

theorem eraseB_s (s : Bool × Bool) (b : ℕ) (o : List Bool) :
    TM2.step lenProg (⟨some (3 : LL), s, lst [] 0 (b + 1) o⟩ : LCfg) =
      some ⟨some (3 : LL), (true, s.2), lst [] 0 b o⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_b]
  simp only [List.replicate_succ, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true]
  rw [lst_set_b]

theorem eraseB_0 (s : Bool × Bool) (o : List Bool) :
    TM2.step lenProg (⟨some (3 : LL), s, lst [] 0 0 o⟩ : LCfg) =
      some ⟨none, (false, false), lst [] 0 0 (false :: o)⟩ := by
  simp only [TM2.step, lenProg, TM2.stepAux]
  rw [lst_b, List.tail_replicate, lst_set_b]
  simp only [List.replicate_zero, List.head?_nil, Option.isSome_none, Bool.cond_false]
  rw [lst_out, lst_set_out]

theorem splitLoop :
    ∀ (l : List (Bool ⊕ Bool)) (a b : ℕ) (s : Bool × Bool),
      lenStep^[l.length + 1] (some (⟨some (0 : LL), s, lst l a b []⟩ : LCfg)) =
        some ⟨some (1 : LL), (false, false),
          lst [] (a + l.countP Sum.isLeft) (b + l.countP Sum.isRight) []⟩ := by
  intro l
  induction l with
  | nil => intro a b s; exact split_nil s a b []
  | cons x l ih =>
    intro a b s
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl x =>
      have e : lenStep (some (⟨some (0 : LL), s, lst (Sum.inl x :: l) a b []⟩ : LCfg)) =
          some ⟨some (0 : LL), (true, false), lst l (a + 1) b []⟩ := split_inl s x l a b []
      have h1 : a + 1 + l.countP Sum.isLeft =
          a + (Sum.inl x :: l : List (Bool ⊕ Bool)).countP Sum.isLeft := by
        rw [List.countP_cons_of_pos (by rfl)]; omega
      have h2 : l.countP Sum.isRight =
          (Sum.inl x :: l : List (Bool ⊕ Bool)).countP Sum.isRight := by
        rw [List.countP_cons_of_neg (by simp)]
      rw [e, ih, h1, h2]
    | inr x =>
      have e : lenStep (some (⟨some (0 : LL), s, lst (Sum.inr x :: l) a b []⟩ : LCfg)) =
          some ⟨some (0 : LL), (true, true), lst l a (b + 1) []⟩ := split_inr s x l a b []
      have h1 : b + 1 + l.countP Sum.isRight =
          b + (Sum.inr x :: l : List (Bool ⊕ Bool)).countP Sum.isRight := by
        rw [List.countP_cons_of_pos (by rfl)]; omega
      have h2 : l.countP Sum.isLeft =
          (Sum.inr x :: l : List (Bool ⊕ Bool)).countP Sum.isLeft := by
        rw [List.countP_cons_of_neg (by simp)]
      rw [e, ih, h1, h2]

theorem cmpLoopT :
    ∀ (b c : ℕ) (s : Bool × Bool),
      lenStep^[b + 1] (some (⟨some (1 : LL), s, lst [] (b + c) b []⟩ : LCfg)) =
        some ⟨some (2 : LL), (false, false), lst [] (c - 1) 0 []⟩ := by
  intro b
  induction b with
  | zero =>
    intro c s
    rw [Nat.zero_add c]
    exact cmp_b0 s c []
  | succ b ih =>
    intro c s
    rw [Function.iterate_succ_apply]
    have hbc : b + 1 + c = b + c + 1 := by omega
    have e : lenStep (some (⟨some (1 : LL), s, lst [] (b + 1 + c) (b + 1) []⟩ : LCfg)) =
        some ⟨some (1 : LL), (true, true), lst [] (b + c) b []⟩ := by
      rw [hbc]; exact cmp_ss s (b + c) b []
    rw [e, ih]

theorem cmpLoopF :
    ∀ (a d : ℕ) (s : Bool × Bool),
      lenStep^[a + 1] (some (⟨some (1 : LL), s, lst [] a (a + 1 + d) []⟩ : LCfg)) =
        some ⟨some (3 : LL), (false, false), lst [] 0 d []⟩ := by
  intro a
  induction a with
  | zero =>
    intro d s
    have h : 0 + 1 + d = d + 1 := by omega
    rw [h]
    exact cmp_a0 s d []
  | succ a ih =>
    intro d s
    rw [Function.iterate_succ_apply]
    have had : a + 1 + 1 + d = a + 1 + d + 1 := by omega
    have e : lenStep (some (⟨some (1 : LL), s, lst [] (a + 1) (a + 1 + 1 + d) []⟩ : LCfg)) =
        some ⟨some (1 : LL), (true, true), lst [] a (a + 1 + d) []⟩ := by
      rw [had]; exact cmp_ss s a (a + 1 + d) []
    rw [e, ih]

theorem eraseALoop :
    ∀ (n : ℕ) (s : Bool × Bool),
      lenStep^[n + 1] (some (⟨some (2 : LL), s, lst [] n 0 []⟩ : LCfg)) =
        some ⟨none, (false, false), lst [] 0 0 [true]⟩ := by
  intro n
  induction n with
  | zero => intro s; exact eraseA_0 s []
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply]
    have e : lenStep (some (⟨some (2 : LL), s, lst [] (n + 1) 0 []⟩ : LCfg)) =
        some ⟨some (2 : LL), (true, s.2), lst [] n 0 []⟩ := eraseA_s s n []
    rw [e, ih]

theorem eraseBLoop :
    ∀ (n : ℕ) (s : Bool × Bool),
      lenStep^[n + 1] (some (⟨some (3 : LL), s, lst [] 0 n []⟩ : LCfg)) =
        some ⟨none, (false, false), lst [] 0 0 [false]⟩ := by
  intro n
  induction n with
  | zero => intro s; exact eraseB_0 s []
  | succ n ih =>
    intro s
    rw [Function.iterate_succ_apply]
    have e : lenStep (some (⟨some (3 : LL), s, lst [] 0 (n + 1) []⟩ : LCfg)) =
        some ⟨some (3 : LL), (true, s.2), lst [] 0 n []⟩ := eraseB_s s n []
    rw [e, ih]

theorem len_run (l : List (Bool ⊕ Bool)) (a b : ℕ) (ha : l.countP Sum.isLeft = a)
    (hb : l.countP Sum.isRight = b) (hab : a + b ≤ l.length) :
    ∃ n, n ≤ 2 * l.length + 3 ∧
      lenStep^[n] (some (initList lenM l)) = some (haltList lenM [decide (b ≤ a)]) := by
  have hs := splitLoop l 0 0 (false, false)
  rw [Nat.zero_add, Nat.zero_add, ha, hb] at hs
  have key : ∀ n : ℕ,
      lenStep^[n] (some (⟨some (0 : LL), (false, false), lst l 0 0 []⟩ : LCfg)) =
        some (⟨none, (false, false), lst [] 0 0 [decide (b ≤ a)]⟩ : LCfg) →
      lenStep^[n] (some (initList lenM l)) = some (haltList lenM [decide (b ≤ a)]) := by
    intro n h
    refine (congrArg (fun c => lenStep^[n] (some c)) (initList_eq lenM l)).trans
      (Eq.trans ?_ (congrArg some (haltList_eq lenM [decide (b ≤ a)])).symm)
    show lenStep^[n]
      (some (⟨some (0 : LL), (false, false), Function.update (fun _ => []) (false, false) l⟩ :
        LCfg)) =
      some (⟨none, (false, false),
        Function.update (fun _ => []) (true, true) [decide (b ≤ a)]⟩ : LCfg)
    rw [← lst_start, ← lst_end]
    exact h
  by_cases h : b ≤ a
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    refine ⟨(c - 1 + 1) + ((b + 1) + (l.length + 1)), by omega, key _ ?_⟩
    have hd : decide (b ≤ b + c) = true := by simp
    rw [Function.iterate_add_apply _ (c - 1 + 1) _, Function.iterate_add_apply _ (b + 1) _, hs,
      cmpLoopT, eraseALoop, hd]
  · obtain ⟨d, rfl⟩ : ∃ d, b = a + 1 + d := ⟨b - a - 1, by omega⟩
    refine ⟨(d + 1) + ((a + 1) + (l.length + 1)), by omega, key _ ?_⟩
    have hd : decide (a + 1 + d ≤ a) = false := decide_eq_false h
    rw [Function.iterate_add_apply _ (d + 1) _, Function.iterate_add_apply _ (a + 1) _, hs,
      cmpLoopF, eraseBLoop, hd]

theorem countP_isLeft_encodePair (p : List Bool × List Bool) :
    (PEqualNP.Library.encodePair p).countP Sum.isLeft = p.1.length := by
  have h1 : ∀ l : List Bool, (l.map Sum.inl : List (Bool ⊕ Bool)).countP Sum.isLeft =
      l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_pos (by rfl), ih, List.length_cons]
  have h2 : ∀ l : List Bool, (l.map Sum.inr : List (Bool ⊕ Bool)).countP Sum.isLeft = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_neg (by simp), ih]
  unfold PEqualNP.Library.encodePair
  rw [List.countP_append, h1, h2, Nat.add_zero]

theorem countP_isRight_encodePair (p : List Bool × List Bool) :
    (PEqualNP.Library.encodePair p).countP Sum.isRight = p.2.length := by
  have h1 : ∀ l : List Bool, (l.map Sum.inr : List (Bool ⊕ Bool)).countP Sum.isRight =
      l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_pos (by rfl), ih, List.length_cons]
  have h2 : ∀ l : List Bool, (l.map Sum.inl : List (Bool ⊕ Bool)).countP Sum.isRight = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.countP_cons_of_neg (by simp), ih]
  unfold PEqualNP.Library.encodePair
  rw [List.countP_append, h1, h2, Nat.zero_add]

theorem lenLE_run (p : List Bool × List Bool) :
    ∃ n, n ≤ 2 * (PEqualNP.Library.encodePair p).length + 3 ∧
      lenStep^[n] (some (initList lenM (PEqualNP.Library.encodePair p))) =
        some (haltList lenM [decide (p.2.length ≤ p.1.length)]) :=
  len_run (PEqualNP.Library.encodePair p) p.1.length p.2.length
    (countP_isLeft_encodePair p) (countP_isRight_encodePair p)
    (by simp [PEqualNP.Library.encodePair])

theorem lenLE_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length))) :=
  ⟨{
    tm := lenM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
    outputsFun := fun p =>
      { steps := Classical.choose (lenLE_run p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have hout : [decide (p.2.length ≤ p.1.length)] =
              List.map (Equiv.refl Bool).invFun
                (Computability.encodeBool (decide (p.2.length ≤ p.1.length))) := by
            rw [hm]
            rfl
          exact (congrArg (fun x => lenStep^[Classical.choose (lenLE_run p)]
            (some (initList lenM x))) (hm _ (PEqualNP.Library.encodePair p))).trans
            ((Classical.choose_spec (lenLE_run p)).2.trans
              (congrArg (fun x => some (haltList lenM x)) hout))
        steps_le_m := by
          have h := (Classical.choose_spec (lenLE_run p)).1
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          exact h } }⟩

end PEqualNP.Outside.Kit.LenCmp

namespace PEqualNP.Outside.Kit

open PEqualNP.Library
open Turing PEqualNP.Library

theorem output_length_poly (f : List Bool → List Bool)
    (hf : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f) :
    ∃ q : Polynomial ℕ, ∀ x : List Bool, (f x).length ≤ q.eval x.length := by
  obtain ⟨c⟩ := hf
  refine ⟨Polynomial.X + Polynomial.C (maxPush c.tm) * c.time, fun x => ?_⟩
  obtain ⟨⟨steps, hev⟩, hle⟩ := c.outputsFun x
  have hev' : (flip bind (TM2.step c.tm.m))^[steps]
      (some (⟨some c.tm.main, c.tm.initialState, Function.update (fun _ => []) c.tm.k₀
        (List.map c.inputAlphabet.invFun x)⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ)) =
      some (⟨none, c.tm.initialState, Function.update (fun _ => []) c.tm.k₁
        (List.map c.outputAlphabet.invFun (f x))⟩ : TM2.Cfg c.tm.Γ c.tm.Λ c.tm.σ) := by
    rw [← initList_eq, ← haltList_eq]; exact hev
  have key := run_length c.tm c.tm.k₁ steps _ _ hev'
  simp only [Function.update_self, List.length_map] at key
  have hin : ((Function.update (fun _ => ([] : List _)) c.tm.k₀
      (List.map c.inputAlphabet.invFun x) : ∀ k, List (c.tm.Γ k)) c.tm.k₁).length ≤ x.length := by
    by_cases hk : c.tm.k₁ = c.tm.k₀
    · rw [hk]; simp
    · rw [Function.update_of_ne hk]; simp
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  calc (f x).length ≤ x.length + maxPush c.tm * steps := key.trans (by omega)
    _ ≤ x.length + maxPush c.tm * c.time.eval x.length :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hle) _

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

abbrev AΓ : Bool → Type
  | false => Bool ⊕ Bool
  | true => Bool

def aval : Bool ⊕ Bool → Bool := Sum.elim id id

def atProg : Unit → TM2.Stmt AΓ Unit (Bool × Bool) :=
  fun _ => .pop false (fun s o => (s.1 && (o.map aval).getD true, o.isSome))
    (.branch (fun s => s.2)
      (.goto fun _ => ())
      (.push true (fun s => s.1) (.load (fun _ => (true, false)) .halt)))

def atM : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := AΓ
  Λ := Unit
  main := ()
  σ := Bool × Bool
  initialState := (true, false)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := atProg

def ast (l : List (Bool ⊕ Bool)) (u : List Bool) : ∀ k, List (AΓ k)
  | false => l
  | true => u

theorem ast_in (l : List (Bool ⊕ Bool)) (u : List Bool) : ast l u false = l := rfl

theorem ast_out (l : List (Bool ⊕ Bool)) (u : List Bool) : ast l u true = u := rfl

theorem ast_set_in (l l' : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (ast l u) false l' = ast l' u := by
  funext k
  cases k <;> simp [ast]

theorem ast_set_out (l : List (Bool ⊕ Bool)) (u u' : List Bool) :
    Function.update (ast l u) true u' = ast l u' := by
  funext k
  cases k <;> simp [ast]

theorem ast_start (l : List (Bool ⊕ Bool)) :
    ast l [] = Function.update (fun _ => [] : ∀ k, List (AΓ k)) false l := by
  funext k
  cases k <;> simp [ast]

theorem ast_end (u : List Bool) :
    ast [] u = Function.update (fun _ => [] : ∀ k, List (AΓ k)) true u := by
  funext k
  cases k <;> simp [ast]

abbrev ACfg : Type := TM2.Cfg AΓ Unit (Bool × Bool)

theorem at_cons (s : Bool × Bool) (x : Bool ⊕ Bool) (l : List (Bool ⊕ Bool)) (u : List Bool) :
    TM2.step atProg (⟨some (), s, ast (x :: l) u⟩ : ACfg) =
      some ⟨some (), (s.1 && aval x, true), ast l u⟩ := by
  simp [TM2.step, atProg, TM2.stepAux, ast_in, ast_set_in]

theorem at_nil (s : Bool × Bool) (u : List Bool) :
    TM2.step atProg (⟨some (), s, ast [] u⟩ : ACfg) =
      some ⟨none, (true, false), ast [] (s.1 :: u)⟩ := by
  simp [TM2.step, atProg, TM2.stepAux, ast_in, ast_out, ast_set_in, ast_set_out]

theorem at_loop :
    ∀ (l : List (Bool ⊕ Bool)) (s : Bool × Bool),
      (flip bind (TM2.step atProg))^[l.length + 1]
          (some (⟨some (), s, ast l []⟩ : ACfg)) =
        some ⟨none, (true, false), ast [] [s.1 && l.all aval]⟩ := by
  intro l
  induction l with
  | nil =>
    intro s
    have h : (s.1 && ([] : List (Bool ⊕ Bool)).all aval) = s.1 := by simp
    rw [h]
    exact at_nil s []
  | cons x l ih =>
    intro s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step atProg)
        (some (⟨some (), s, ast (x :: l) []⟩ : ACfg)) =
        some ⟨some (), (s.1 && aval x, true), ast l []⟩ := at_cons s x l []
    rw [e, ih]
    simp [Bool.and_assoc]

theorem at_run (l : List (Bool ⊕ Bool)) :
    (flip bind (TM2.step atProg))^[l.length + 1]
        (some (initList atM l)) = some (haltList atM [l.all aval]) := by
  refine (congrArg (fun c => (flip bind (TM2.step atProg))^[l.length + 1]
    (some c)) (initList_eq atM l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq atM [l.all aval])).symm)
  show (flip bind (TM2.step atProg))^[l.length + 1]
    (some (⟨some (), (true, false), Function.update (fun _ => []) false l⟩ : ACfg)) =
    some (⟨none, (true, false), Function.update (fun _ => []) true [l.all aval]⟩ : ACfg)
  rw [← ast_start, at_loop, ← ast_end]
  simp

theorem all_aval_encodePair (p : List Bool × List Bool) :
    (PEqualNP.Library.encodePair p).all aval = (p.1 ++ p.2).all id := by
  have h1 : ∀ l : List Bool, (l.map Sum.inl : List (Bool ⊕ Bool)).all aval = l.all id := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => simp [aval]
  have h2 : ∀ l : List Bool, (l.map Sum.inr : List (Bool ⊕ Bool)).all aval = l.all id := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => simp [aval]
  unfold PEqualNP.Library.encodePair
  rw [List.all_append, List.all_append, h1, h2]

theorem allTrue_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun p : List Bool × List Bool => (p.1 ++ p.2).all id)) :=
  ⟨{
    tm := atM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.X + 1
    outputsFun := fun p =>
      { steps := (PEqualNP.Library.encodePair p).length + 1
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have hout : [(PEqualNP.Library.encodePair p).all aval] =
              List.map (Equiv.refl Bool).invFun
                (Computability.encodeBool ((p.1 ++ p.2).all id)) := by
            rw [hm, all_aval_encodePair]
            rfl
          exact (congrArg (fun x => (flip bind (TM2.step atProg))^[
            (PEqualNP.Library.encodePair p).length + 1]
            (some (initList atM x))) (hm _ (PEqualNP.Library.encodePair p))).trans
            ((at_run (PEqualNP.Library.encodePair p)).trans
              (congrArg (fun x => some (haltList atM x)) hout))
        steps_le_m := by simp } }⟩

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

theorem dup_time :
    PEqualNP.Library.ComputableInTime (fun x : List Bool => x) PEqualNP.Library.encodePair
      (fun x : List Bool => (x, x)) (fun n : ℕ => 4 * n + 4) := by
  let φ₁ : Bool → Option (Bool ⊕ Bool) := fun b => some (Sum.inl b)
  let φ₂ : Bool → Option (Bool ⊕ Bool) := fun b => some (Sum.inr b)
  let d : Option (Bool ⊕ Bool) := some (Sum.inl true)
  have hd : ∀ φ : Bool → Option (Bool ⊕ Bool), d = none → ∀ x, φ x = none :=
    fun φ h => by simp [d] at h
  have hid : ∀ x : List Bool, PEqualNP.Library.encodePair (x, x) =
      x.filterMap φ₁ ++ x.filterMap φ₂ := by
    intro x
    have h1 : x.filterMap φ₁ = x.map Sum.inl := by
      simp [φ₁]
    have h2 : x.filterMap φ₂ = x.map Sum.inr := by
      simp [φ₂]
    rw [h1, h2]; rfl
  exact ⟨{
    tm := tp φ₁ φ₂ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun n => 4 * n + 4
    outputsFun := fun a =>
      { steps := a.length + 1 + (a.length + 1) + (a.length + 1) + (a.length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := tp_run φ₁ φ₂ d (hd φ₁) (hd φ₂) a
          exact (congrArg (fun l => (flip bind (TM2.step (tpProg φ₁ φ₂ d)))^[a.length + 1 +
            (a.length + 1) + (a.length + 1) + (a.length + 1)]
            (some (initList (tp φ₁ φ₂ d) l))) (hm Bool a)).trans
            (this.trans (congrArg (fun l => some (haltList (tp φ₁ φ₂ d) l))
              ((hid a).symm.trans (hm _ (PEqualNP.Library.encodePair (a, a))).symm)))
        steps_le_m := by
          show _ ≤ 4 * a.length + 4
          omega } }, fun _ => le_rfl⟩

theorem mul_time :
    PEqualNP.Library.ComputableInTime PEqualNP.Library.encodePair (fun x : List Bool => x)
      (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)
      (fun m : ℕ => 2 * m ^ 2 + 5 * m + 3) := by
  exact ⟨{
    tm := mulTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun m => 2 * m ^ 2 + 5 * m + 3
    outputsFun := fun p =>
      { steps := mulSteps p.1.length p.2.length
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := mul_run p.1 p.2
          exact (congrArg (fun l => (flip bind (TM2.step mulProg))^[mulSteps p.1.length
            p.2.length] (some (initList mulTM l))) (hm _ (PEqualNP.Library.encodePair p))).trans
            (this.trans (congrArg (fun l => some (haltList mulTM l)) (hm Bool _).symm))
        steps_le_m := by
          simp only [PEqualNP.Library.encodePair, List.length_append, List.length_map, mulSteps]
          nlinarith [Nat.zero_le (p.1.length * p.1.length),
            Nat.zero_le (p.2.length * p.2.length), Nat.zero_le (p.1.length * p.2.length)] } },
    fun _ => le_rfl⟩

theorem square_time :
    PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (x.length ^ 2) true)
      (fun n : ℕ => 27 * n ^ 2 + 27) := by
  have h := comp_time (fun x : List Bool => x) PEqualNP.Library.encodePair
    (fun x : List Bool => x) (fun x : List Bool => (x, x))
    (fun p : List Bool × List Bool => List.replicate (p.1.length * p.2.length) true)
    (fun n : ℕ => 4 * n + 4) (fun m : ℕ => 2 * m ^ 2 + 5 * m + 3) (fun n : ℕ => 2 * n)
    dup_time mul_time
    (fun a b hab => by
      have := Nat.pow_le_pow_left hab 2
      show 2 * a ^ 2 + 5 * a + 3 ≤ 2 * b ^ 2 + 5 * b + 3
      omega)
    (fun a => by simp [PEqualNP.Library.encodePair]; omega)
  have h' : PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (x.length ^ 2) true)
      (fun n : ℕ => 4 * n + 4 + (2 * (2 * n) + 2) + (2 * (2 * n) ^ 2 + 5 * (2 * n) + 3)) := by
    simpa only [sq] using h
  refine time_mono h' fun n => ?_
  nlinarith [Nat.zero_le (n * n), Nat.le_mul_self n]

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit

open PEqualNP.Library

open Turing

def fstRun {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.toList ++ fstRun δ fin (δ q a).1 l

def fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q → List Γ₀ → List Γ₁
  | q, [] => (fin q).toList
  | q, a :: l => (δ q a).2.1.toList ++ (δ q a).2.2.toList ++ fstRun2 δ fin (δ q a).1 l

theorem fstRun_eq_fstRun2 {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁) (fin : Q → Option Γ₁)
    (q : Q) (l : List Γ₀) :
    fstRun δ fin q l = fstRun2 (fun q a => ((δ q a).1, (δ q a).2, none)) fin q l := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [fstRun, fstRun2, ih]

abbrev TrK : Type := Fin 3

variable {Γ₀ Γ₁ Q : Type}

abbrev TrΓ (Γ₀ Γ₁ Q : Type) : TrK → Type
  | (0 : TrK) => Γ₀
  | (1 : TrK) => Q × Option Γ₀
  | (2 : TrK) => Γ₁

abbrev TrS (Γ₀ Q : Type) : Type := Q × Option Γ₀ × Bool

def trO1 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) :
    Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.1
  | (q, none) => fin q

def trO2 (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q × Option Γ₀ → Option Γ₁
  | (q, some a) => (δ q a).2.2
  | (_, none) => none

def trOut (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁)
    (e : Q × Option Γ₀) : List Γ₁ :=
  (trO1 δ fin e).toList ++ (trO2 δ e).toList

def trTrace (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) : Q → List Γ₀ → List (Q × Option Γ₀)
  | q, [] => [(q, none)]
  | q, a :: l => (q, some a) :: trTrace δ (δ q a).1 l

theorem trTrace_length (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (q : Q) (l : List Γ₀) :
    (trTrace δ q l).length = l.length + 1 := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simp [trTrace, ih]

theorem trTrace_out (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q : Q)
    (l : List Γ₀) : (trTrace δ q l).flatMap (trOut δ fin) = fstRun2 δ fin q l := by
  induction l generalizing q with
  | nil => simp [trTrace, trOut, trO1, trO2, fstRun2]
  | cons a l ih => simp [trTrace, trOut, trO1, trO2, fstRun2, ih]

def trWrite (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) :
    TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q) :=
  .branch (fun s => (o s).isSome)
    (match d with
      | some dd => .push (2 : TrK) (fun s => (o s).getD dd) next
      | none => next)
    next

def trProg (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
    (d : Option Γ₁) : Bool → TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)
  | false =>
    .pop (0 : TrK) (fun s o => (s.1, o, o.isSome))
      (.branch (fun s => s.2.2)
        (.push (1 : TrK) (fun s => (s.1, s.2.1))
          (.load (fun s => (match s.2.1 with
              | some a => (δ s.1 a).1
              | none => s.1, none, false))
            (.goto fun _ => false)))
        (.push (1 : TrK) (fun s => (s.1, none))
          (.load (fun _ => (q₀, none, false)) (.goto fun _ => true))))
  | true =>
    .pop (1 : TrK) (fun _ o => match o with
        | some e => (e.1, e.2, true)
        | none => (q₀, none, false))
      (.branch (fun s => s.2.2)
        (trWrite (fun s => trO2 δ (s.1, s.2.1)) d
          (trWrite (fun s => trO1 δ fin (s.1, s.2.1)) d (.goto fun _ => true)))
        .halt)

def trM [Fintype Γ₀] [Fintype Q] (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁)
    (fin : Q → Option Γ₁) (q₀ : Q) (d : Option Γ₁) : FinTM2 where
  K := TrK
  k₀ := (0 : TrK)
  k₁ := (2 : TrK)
  Γ := TrΓ Γ₀ Γ₁ Q
  Λ := Bool
  main := false
  σ := TrS Γ₀ Q
  initialState := (q₀, none, false)
  Γk₀Fin := inferInstanceAs (Fintype Γ₀)
  m := trProg δ fin q₀ d

def trSt (l : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)
  | (0 : TrK) => l
  | (1 : TrK) => t
  | (2 : TrK) => u

theorem trSt_set_inp (l l' : List Γ₀) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) (0 : TrK) l' = trSt l' t u := by
  funext k; fin_cases k <;> simp [trSt]

theorem trSt_set_tmp (l : List Γ₀) (t t' : List (Q × Option Γ₀)) (u : List Γ₁) :
    Function.update (trSt l t u) (1 : TrK) t' = trSt l t' u := by
  funext k; fin_cases k <;> simp [trSt]

theorem trSt_set_out (l : List Γ₀) (t : List (Q × Option Γ₀)) (u u' : List Γ₁) :
    Function.update (trSt l t u) (2 : TrK) u' = trSt l t u' := by
  funext k; fin_cases k <;> simp [trSt]

theorem trSt_start (l : List Γ₀) :
    (trSt l [] [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) (0 : TrK) l := by
  funext k; fin_cases k <;> simp [trSt]

theorem trSt_end (u : List Γ₁) :
    (trSt [] [] u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) =
      Function.update (fun _ => [] : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) (2 : TrK) u := by
  funext k; fin_cases k <;> simp [trSt]

abbrev TrCfg (Γ₀ Γ₁ Q : Type) : Type := TM2.Cfg (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)

theorem trWrite_stepAux (o : TrS Γ₀ Q → Option Γ₁) (d : Option Γ₁) (hd : ∀ _ : Γ₁, d ≠ none)
    (next : TM2.Stmt (TrΓ Γ₀ Γ₁ Q) Bool (TrS Γ₀ Q)) (s : TrS Γ₀ Q) (l : List Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.stepAux (trWrite o d next) s (trSt l t u) =
      TM2.stepAux next s (trSt l t ((o s).toList ++ u)) := by
  cases ho : o s with
  | none => cases d <;> simp [trWrite, TM2.stepAux, ho]
  | some y =>
    cases d with
    | none => exact absurd rfl (hd y)
    | some dd => simp [trWrite, TM2.stepAux, ho, trSt, trSt_set_out]

variable (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁) (fin : Q → Option Γ₁) (q₀ : Q)
  (d : Option Γ₁)

theorem trA_cons (s : TrS Γ₀ Q) (a : Γ₀) (l : List Γ₀) (t : List (Q × Option Γ₀))
    (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]

theorem trA_nil (s : TrS Γ₀ Q) (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some false, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (q₀, none, false), trSt [] ((s.1, none) :: t) u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_inp, trSt_set_tmp]

theorem trB_cons (hd : ∀ _ : Γ₁, d ≠ none) (s : TrS Γ₀ Q) (e : Q × Option Γ₀)
    (t : List (Q × Option Γ₀)) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ := by
  simp only [TM2.step, trProg, TM2.stepAux]
  have e1 : (trSt [] (e :: t) u : ∀ k, List (TrΓ Γ₀ Γ₁ Q k)) (1 : TrK) = e :: t := rfl
  rw [e1]
  simp only [List.head?_cons, List.tail_cons, Bool.cond_true]
  rw [trSt_set_tmp, trWrite_stepAux _ _ hd, trWrite_stepAux _ _ hd]
  simp [TM2.stepAux, trOut]

theorem trB_nil (s : TrS Γ₀ Q) (u : List Γ₁) :
    TM2.step (trProg δ fin q₀ d) (⟨some true, s, trSt [] [] u⟩ : TrCfg Γ₀ Γ₁ Q) =
      some ⟨none, (q₀, none, false), trSt [] [] u⟩ := by
  simp [TM2.step, trProg, TM2.stepAux, trSt, trSt_set_tmp]

theorem trLoopA (u : List Γ₁) :
    ∀ (l : List Γ₀) (t : List (Q × Option Γ₀)) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
          (some (⟨some false, s, trSt l t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (q₀, none, false), trSt [] ((trTrace δ s.1 l).reverse ++ t) u⟩ := by
  intro l
  induction l with
  | nil => intro t s; exact trA_nil δ fin q₀ d s t u
  | cons a l ih =>
    intro t s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some false, s, trSt (a :: l) t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some false, ((δ s.1 a).1, none, false), trSt l ((s.1, some a) :: t) u⟩ :=
      trA_cons δ fin q₀ d s a l t u
    rw [e, ih]
    simp [trTrace]

theorem trLoopB (hd : ∀ _ : Γ₁, d ≠ none) :
    ∀ (t : List (Q × Option Γ₀)) (u : List Γ₁) (s : TrS Γ₀ Q),
      (flip bind (TM2.step (trProg δ fin q₀ d)))^[t.length + 1]
          (some (⟨some true, s, trSt [] t u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨none, (q₀, none, false), trSt [] [] (t.reverse.flatMap (trOut δ fin) ++ u)⟩ := by
  intro t
  induction t with
  | nil => intro u s; exact trB_nil δ fin q₀ d s u
  | cons e t ih =>
    intro u s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e' : flip bind (TM2.step (trProg δ fin q₀ d))
        (some (⟨some true, s, trSt [] (e :: t) u⟩ : TrCfg Γ₀ Γ₁ Q)) =
        some ⟨some true, (e.1, e.2, true), trSt [] t (trOut δ fin e ++ u)⟩ :=
      trB_cons δ fin q₀ d hd s e t u
    rw [e', ih]
    simp [List.flatMap_append]

theorem trM_run [Fintype Γ₀] [Fintype Q] (hd : ∀ _ : Γ₁, d ≠ none) (l : List Γ₀) :
    (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
        (some (initList (trM δ fin q₀ d) l)) =
      some (haltList (trM δ fin q₀ d) (fstRun2 δ fin q₀ l)) := by
  refine (congrArg (fun c => (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 +
    (l.length + 1)] (some c)) (initList_eq (trM δ fin q₀ d) l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq (trM δ fin q₀ d) (fstRun2 δ fin q₀ l))).symm)
  show (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1 + (l.length + 1)]
    (some (⟨some false, (q₀, none, false), Function.update (fun _ => []) (0 : TrK) l⟩ :
      TrCfg Γ₀ Γ₁ Q)) =
    some (⟨none, (q₀, none, false), Function.update (fun _ => []) (2 : TrK) (fstRun2 δ fin q₀ l)⟩ :
      TrCfg Γ₀ Γ₁ Q)
  have hA : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1]
      (some (⟨some false, (q₀, none, false), trSt l [] []⟩ : TrCfg Γ₀ Γ₁ Q)) =
      some ⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ := by
    have := trLoopA δ fin q₀ d [] l [] (q₀, none, false)
    rw [List.append_nil] at this
    exact this
  have hB : (flip bind (TM2.step (trProg δ fin q₀ d)))^[l.length + 1 + 1]
      (some (⟨some true, (q₀, none, false), trSt [] (trTrace δ q₀ l).reverse []⟩ :
        TrCfg Γ₀ Γ₁ Q)) =
      some ⟨none, (q₀, none, false), trSt [] [] (fstRun2 δ fin q₀ l)⟩ := by
    have := trLoopB δ fin q₀ d hd (trTrace δ q₀ l).reverse [] (q₀, none, false)
    rw [List.length_reverse, trTrace_length, List.reverse_reverse, trTrace_out,
      List.append_nil] at this
    exact this
  rw [Function.iterate_add_apply, ← trSt_start, hA, hB, trSt_end]

theorem fst2_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ × Option βΓ)
    (fin : Q → Option βΓ) (q₀ : Q) (h : ∀ a, eb (f a) = fstRun2 δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ _ : βΓ, d ≠ none := by
    intro y
    have hn : Nonempty βΓ := ⟨y⟩
    simp [d, hn]
  exact ⟨{
    tm := trM δ fin q₀ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 2 * Polynomial.X + Polynomial.C 3
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := trM_run δ fin q₀ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (trProg δ fin q₀ d)))^[(ea a).length +
            1 + 1 + ((ea a).length + 1)] (some (initList (trM δ fin q₀ d) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (trM δ fin q₀ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          omega } }⟩

theorem fst_polyTime {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ) (fin : Q → Option βΓ) (q₀ : Q)
    (h : ∀ a, eb (f a) = fstRun δ fin q₀ (ea a)) :
    Nonempty (Turing.TM2ComputableInPolyTime ea eb f) :=
  fst2_polyTime ea eb f (fun q a => ((δ q a).1, (δ q a).2, none)) fin q₀
    (fun a => (h a).trans (fstRun_eq_fstRun2 δ fin q₀ (ea a)))

end PEqualNP.Outside.Kit

namespace PEqualNP.Outside.Kit.Gen

open PEqualNP.Library

open Turing PEqualNP.Outside.Kit

def gpair {A C : Type} (p : List A × List C) : List (A ⊕ C) :=
  p.1.map Sum.inl ++ p.2.map Sum.inr

abbrev FX : Type := Fin 5

abbrev FL : Type := Fin 5

variable (M : FinTM2) (A B C : Type)

abbrev FstΓ : M.K ⊕ FX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr (0 : FX) => A ⊕ C
  | Sum.inr (1 : FX) => C
  | Sum.inr (2 : FX) => A
  | Sum.inr (3 : FX) => B
  | Sum.inr (4 : FX) => B ⊕ C

abbrev FstΛ : Type := M.Λ ⊕ FL

abbrev Fstσ : Type := M.σ × Option (A ⊕ B ⊕ C)

variable {A B C}

def getA [Inhabited A] : Option (A ⊕ B ⊕ C) → A
  | some (Sum.inl a) => a
  | _ => default

def getB [Inhabited B] : Option (A ⊕ B ⊕ C) → B
  | some (Sum.inr (Sum.inl b)) => b
  | _ => default

def getC [Inhabited C] : Option (A ⊕ B ⊕ C) → C
  | some (Sum.inr (Sum.inr c)) => c
  | _ => default

def isA : Option (A ⊕ B ⊕ C) → Bool
  | some (Sum.inl _) => true
  | _ => false

def ofI : A ⊕ C → A ⊕ B ⊕ C
  | Sum.inl a => Sum.inl a
  | Sum.inr c => Sum.inr (Sum.inr c)

variable {M}
variable (A B C)

def trF : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr (2 : FL))

variable (M) {A B}
variable [Inhabited A] [Inhabited B] [Inhabited C]

def firstProg (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B) :
    FstΛ M → TM2.Stmt (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)
  | Sum.inl l => trF A B C (M.m l)
  | Sum.inr (0 : FL) =>
    .pop (Sum.inr (0 : FX)) (fun s o => (s.1, o.map ofI))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isA s.2)
          (.push (Sum.inr (2 : FX)) (fun s => getA s.2) (.goto fun _ => Sum.inr (0 : FL)))
          (.push (Sum.inr (1 : FX)) (fun s => getC s.2) (.goto fun _ => Sum.inr (0 : FL))))
        (.goto fun _ => Sum.inr (1 : FL)))
  | Sum.inr (1 : FL) =>
    .pop (Sum.inr (2 : FX)) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (getA s.2)) (.goto fun _ => Sum.inr (1 : FL)))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr (2 : FL) =>
    .pop (Sum.inr (1 : FX)) (fun s o => (s.1, o.map fun c => Sum.inr (Sum.inr c)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr (4 : FX)) (fun s => Sum.inr (getC s.2)) (.goto fun _ => Sum.inr (2 : FL)))
        (.goto fun _ => Sum.inr (3 : FL)))
  | Sum.inr (3 : FL) =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inr (Sum.inl (e₁ y))))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr (3 : FX)) (fun s => getB s.2) (.goto fun _ => Sum.inr (3 : FL)))
        (.goto fun _ => Sum.inr (4 : FL)))
  | Sum.inr (4 : FL) =>
    .pop (Sum.inr (3 : FX)) (fun s o => (s.1, o.map fun b => Sum.inr (Sum.inl b)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr (4 : FX)) (fun s => Sum.inl (getB s.2)) (.goto fun _ => Sum.inr (4 : FL)))
        .halt)

def firstM [Fintype A] [Fintype B] [Fintype C] (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B) :
    FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ FX
    k₀ := Sum.inr (0 : FX)
    k₁ := Sum.inr (4 : FX)
    Γ := FstΓ M A B C
    Λ := FstΛ M
    main := Sum.inr (0 : FL)
    σ := Fstσ M A B C
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (A ⊕ C))
    m := firstProg M C e₀ e₁ }

omit [Inhabited A] [Inhabited B] [Inhabited C]
variable {M} {C}

def fstk (S : ∀ k, List (M.Γ k)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
    (o : List (B ⊕ C)) : ∀ k, List (FstΓ M A B C k)
  | Sum.inl k => S k
  | Sum.inr (0 : FX) => i
  | Sum.inr (1 : FX) => w
  | Sum.inr (2 : FX) => ta
  | Sum.inr (3 : FX) => tb
  | Sum.inr (4 : FX) => o

section fstk

variable (S : ∀ k, List (M.Γ k)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
  (o : List (B ⊕ C))

@[simp] theorem fstk_M (k : M.K) : fstk S i w ta tb o (Sum.inl k) = S k := rfl
@[simp] theorem fstk_I : fstk S i w ta tb o (Sum.inr (0 : FX)) = i := rfl
@[simp] theorem fstk_W : fstk S i w ta tb o (Sum.inr (1 : FX)) = w := rfl
@[simp] theorem fstk_TA : fstk S i w ta tb o (Sum.inr (2 : FX)) = ta := rfl
@[simp] theorem fstk_TB : fstk S i w ta tb o (Sum.inr (3 : FX)) = tb := rfl
@[simp] theorem fstk_O : fstk S i w ta tb o (Sum.inr (4 : FX)) = o := rfl

theorem fstk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (fstk S i w ta tb o) (Sum.inl k) x =
      fstk (Function.update S k x) i w ta tb o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; fin_cases j <;> rfl

theorem fstk_set_I (i' : List (A ⊕ C)) :
    Function.update (fstk S i w ta tb o) (Sum.inr (0 : FX)) i' = fstk S i' w ta tb o := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_W (w' : List C) :
    Function.update (fstk S i w ta tb o) (Sum.inr (1 : FX)) w' = fstk S i w' ta tb o := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_TA (ta' : List A) :
    Function.update (fstk S i w ta tb o) (Sum.inr (2 : FX)) ta' = fstk S i w ta' tb o := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_TB (tb' : List B) :
    Function.update (fstk S i w ta tb o) (Sum.inr (3 : FX)) tb' = fstk S i w ta tb' o := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> rfl

theorem fstk_set_O (o' : List (B ⊕ C)) :
    Function.update (fstk S i w ta tb o) (Sum.inr (4 : FX)) o' = fstk S i w ta tb o' := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · fin_cases j <;> rfl

end fstk

variable (M A B C) in

abbrev FCfg : Type := TM2.Cfg (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)

def embF (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
    (o : List (B ⊕ C)) (c : TM2.Cfg M.Γ M.Λ M.σ) : FCfg M A B C :=
  ⟨some (c.l.elim (Sum.inr (2 : FL)) Sum.inl), (c.var, b), fstk c.stk i w ta tb o⟩

theorem simF (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ)
    (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trF A B C q) ((v, b) : Fstσ M A B C) (fstk S i w ta tb o) =
      embF b i w ta tb o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← fstk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← fstk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepF [Inhabited A] [Inhabited B] [Inhabited C] (e₀ : A → M.Γ M.k₀)
    (e₁ : M.Γ M.k₁ → B) (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C)
    (ta : List A) (tb : List B) (o : List (B ⊕ C))
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (firstProg M C e₀ e₁) (embF b i w ta tb o c) = some (embF b i w ta tb o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w ta tb o (M.m l) v S)

end PEqualNP.Outside.Kit.Gen

namespace PEqualNP.Outside.Kit.Gen

open PEqualNP.Library

open Turing PEqualNP.Outside.Kit

theorem iter_trans {σ : Type} (f : σ → Option σ) {a b : ℕ} {x y z : σ}
    (h₁ : (flip bind f)^[a] (some x) = some y) (h₂ : (flip bind f)^[b] (some y) = some z) :
    (flip bind f)^[b + a] (some x) = some z := by
  rw [Function.iterate_add_apply, h₁, h₂]

variable {M : FinTM2} {A B C : Type} [Inhabited A] [Inhabited B] [Inhabited C]
  (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B)

variable (v : M.σ) (S : ∀ k, List (M.Γ k)) (w : List C) (o : List (B ⊕ C))

theorem f1_inl (b : Option (A ⊕ B ⊕ C)) (a : A) (i : List (A ⊕ C)) (t : List A)
    (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr (0 : FL)), (v, b), fstk S (Sum.inl a :: i) w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr (0 : FL)), (v, some (Sum.inl a)), fstk S i w (a :: t) tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_TA, isA, getA, ofI]

theorem f1_inr (b : Option (A ⊕ B ⊕ C)) (a : C) (i : List (A ⊕ C)) (t : List A)
    (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr (0 : FL)), (v, b), fstk S (Sum.inr a :: i) w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr (0 : FL)), (v, some (Sum.inr (Sum.inr a))),
        fstk S i (a :: w) t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_W, isA, getC, ofI]

theorem f1_nil (b : Option (A ⊕ B ⊕ C)) (t : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr (0 : FL)), (v, b), fstk S [] w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr (1 : FL)), (v, none), fstk S [] w t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I]

theorem loop1 (tb : List B) : ∀ (i : List (A ⊕ C)) (w : List C) (t : List A)
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[i.length + 1]
        (some (⟨some (Sum.inr (0 : FL)), (v, b), fstk S i w t tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inr (1 : FL)), (v, none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
          ((i.filterMap Sum.getLeft?).reverse ++ t) tb o⟩ := by
  intro i
  induction i with
  | nil => intro w t b; exact f1_nil e₀ e₁ v S w o b t tb
  | cons x i ih =>
    intro w t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : flip bind (TM2.step (firstProg M C e₀ e₁))
          (some (⟨some (Sum.inr (0 : FL)), (v, b), fstk S (Sum.inl a :: i) w t tb o⟩ :
            FCfg M A B C)) =
          some ⟨some (Sum.inr (0 : FL)), (v, some (Sum.inl a)), fstk S i w (a :: t) tb o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t tb
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : flip bind (TM2.step (firstProg M C e₀ e₁))
          (some (⟨some (Sum.inr (0 : FL)), (v, b), fstk S (Sum.inr a :: i) w t tb o⟩ :
            FCfg M A B C)) =
          some ⟨some (Sum.inr (0 : FL)), (v, some (Sum.inr (Sum.inr a))),
            fstk S i (a :: w) t tb o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t tb
      rw [e, ih]; simp [List.filterMap_cons]

theorem f2_cons (b : Option (A ⊕ B ⊕ C)) (a : A) (t : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr (1 : FL)), (v, b), fstk S [] w (a :: t) tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr (1 : FL)), (v, some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TA, fstk_set_M, getA]

theorem f2_nil (b : Option (A ⊕ B ⊕ C)) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr (1 : FL)), (v, b), fstk S [] w [] tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inl M.main), (v, none), fstk S [] w [] tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TA]

theorem loop2 (tb : List B) : ∀ (t : List A) (S : ∀ k, List (M.Γ k))
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr (1 : FL)), (v, b), fstk S [] w t tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inl M.main), (v, none),
        fstk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) [] w [] tb o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List A).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b tb
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr (1 : FL)), (v, b), fstk S [] w (a :: t) tb o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr (1 : FL)), (v, some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t tb o⟩ :=
      f2_cons e₀ e₁ v S w o b a t tb
    rw [e, ih]; simp

theorem f3_cons (b : Option (A ⊕ B ⊕ C)) (a : C) (w : List C) (ta : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr (2 : FL)), (v, b), fstk S [] (a :: w) ta tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr (2 : FL)), (v, some (Sum.inr (Sum.inr a))),
        fstk S [] w ta tb (Sum.inr a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W, fstk_set_O, getC]

theorem f3_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr (2 : FL)), (v, b), fstk S [] [] ta tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr (3 : FL)), (v, none), fstk S [] [] ta tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W]

theorem loop3 (ta : List A) (tb : List B) : ∀ (w : List C) (o : List (B ⊕ C))
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[w.length + 1]
        (some (⟨some (Sum.inr (2 : FL)), (v, b), fstk S [] w ta tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inr (3 : FL)), (v, none),
        fstk S [] [] ta tb (w.reverse.map Sum.inr ++ o)⟩ := by
  intro w
  induction w with
  | nil => intro o b; exact f3_nil e₀ e₁ v S o b ta tb
  | cons a w ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr (2 : FL)), (v, b), fstk S [] (a :: w) ta tb o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr (2 : FL)), (v, some (Sum.inr (Sum.inr a))),
          fstk S [] w ta tb (Sum.inr a :: o)⟩ :=
      f3_cons e₀ e₁ v S o b a w ta tb
    rw [e, ih]; simp

theorem f4_cons (b : Option (A ⊕ B ⊕ C)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁)) (ta : List A)
    (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr (3 : FL)), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] ta t o⟩ :
          FCfg M A B C) =
      some ⟨some (Sum.inr (3 : FL)), (v, some (Sum.inr (Sum.inl (e₁ y)))),
        fstk (Function.update S M.k₁ m) [] [] ta (e₁ y :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB, fstk_set_M, getB]

theorem f4_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr (3 : FL)), (v, b), fstk (Function.update S M.k₁ []) [] [] ta t o⟩ :
          FCfg M A B C) =
      some ⟨some (Sum.inr (4 : FL)), (v, none),
        fstk (Function.update S M.k₁ []) [] [] ta t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_M]

theorem loop4 (ta : List A) : ∀ (m : List (M.Γ M.k₁)) (t : List B) (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[m.length + 1]
        (some (⟨some (Sum.inr (3 : FL)), (v, b), fstk (Function.update S M.k₁ m) [] [] ta t o⟩ :
          FCfg M A B C)) =
      some ⟨some (Sum.inr (4 : FL)), (v, none),
        fstk (Function.update S M.k₁ []) [] [] ta (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact f4_nil e₀ e₁ v S o b ta t
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr (3 : FL)), (v, b),
          fstk (Function.update S M.k₁ (y :: m)) [] [] ta t o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr (3 : FL)), (v, some (Sum.inr (Sum.inl (e₁ y)))),
          fstk (Function.update S M.k₁ m) [] [] ta (e₁ y :: t) o⟩ :=
      f4_cons e₀ e₁ v S o b y m ta t
    rw [e, ih]; simp

theorem f5_cons (b : Option (A ⊕ B ⊕ C)) (a : B) (ta : List A) (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr (4 : FL)), (v, b), fstk S [] [] ta (a :: t) o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr (4 : FL)), (v, some (Sum.inr (Sum.inl a))),
        fstk S [] [] ta t (Sum.inl a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB, fstk_set_O, getB]

theorem f5_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr (4 : FL)), (v, b), fstk S [] [] ta [] o⟩ : FCfg M A B C) =
      some ⟨none, (v, none), fstk S [] [] ta [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB]

theorem loop5 (ta : List A) : ∀ (t : List B) (o : List (B ⊕ C)) (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr (4 : FL)), (v, b), fstk S [] [] ta t o⟩ : FCfg M A B C)) =
      some ⟨none, (v, none), fstk S [] [] ta [] (t.reverse.map Sum.inl ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact f5_nil e₀ e₁ v S o b ta
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr (4 : FL)), (v, b), fstk S [] [] ta (a :: t) o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr (4 : FL)), (v, some (Sum.inr (Sum.inl a))),
          fstk S [] [] ta t (Sum.inl a :: o)⟩ :=
      f5_cons e₀ e₁ v S o b a ta t
    rw [e, ih]; simp

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil :
    (fstk (fun _ => []) [] [] [] [] [] : ∀ k, List (FstΓ M A B C k)) = fun _ => [] := by
  funext j; rcases j with j | j <;> [rfl; (fin_cases j <;> rfl)]

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil_I (i : List (A ⊕ C)) :
    (fstk (fun _ => []) i [] [] [] [] : ∀ k, List (FstΓ M A B C k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M A B C k)) (Sum.inr (0 : FX)) i :=
  (fstk_set_I (fun _ => []) [] [] [] [] [] i).symm.trans (by rw [fstk_nil])

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil_O (o : List (B ⊕ C)) :
    (fstk (fun _ => []) [] [] [] [] o : ∀ k, List (FstΓ M A B C k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M A B C k)) (Sum.inr (4 : FX)) o :=
  (fstk_set_O (fun _ => []) [] [] [] [] [] o).symm.trans (by rw [fstk_nil])

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem embF_init (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (l : List (M.Γ M.k₀)) :
    embF b i w ta tb o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₀ l) i w ta tb o⟩ : FCfg M A B C) := by
  rw [initList_eq]; rfl

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem embF_halt (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (m : List (M.Γ M.k₁)) :
    embF b i w ta tb o (haltList M m) =
      (⟨some (Sum.inr (2 : FL)), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₁ m) i w ta tb o⟩ : FCfg M A B C) := by
  rw [haltList_eq]; rfl

theorem filterMap_const_none {γ δ : Type} (l : List γ) :
    l.filterMap (fun _ => (none : Option δ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem gpair_left {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).filterMap Sum.getLeft? = x := by
  have h1 : (Sum.getLeft? ∘ (Sum.inl : A → A ⊕ C) : A → Option A) = some := rfl
  have h2 : (Sum.getLeft? ∘ (Sum.inr : C → A ⊕ C) : C → Option A) = fun _ => none := rfl
  simp only [gpair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.append_nil]

theorem gpair_right {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).filterMap Sum.getRight? = w := by
  have h1 : (Sum.getRight? ∘ (Sum.inl : A → A ⊕ C) : A → Option C) = fun _ => none := rfl
  have h2 : (Sum.getRight? ∘ (Sum.inr : C → A ⊕ C) : C → Option C) = some := rfl
  simp only [gpair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.nil_append]

theorem gpair_length {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).length = x.length + w.length := by
  simp [gpair]

theorem first_run [Fintype A] [Fintype B] [Fintype C] (x : List A) (w0 : List C)
    (m : List (M.Γ M.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀))) = some (haltList M m)) :
    ∃ n, n ≤ s + 2 * x.length + 2 * w0.length + 2 * m.length + 5 ∧
      (flip bind (TM2.step (firstProg M C e₀ e₁)))^[n]
          (some (initList (firstM M C e₀ e₁) (gpair (x, w0)))) =
        some (haltList (firstM M C e₀ e₁) (gpair (m.map e₁, w0))) := by
  have q1 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[(gpair (x, w0)).length + 1]
      (some (initList (firstM M C e₀ e₁) (gpair (x, w0)))) =
      some (⟨some (Sum.inr (1 : FL)), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse [] []⟩ : FCfg M A B C) := by
    have := loop1 e₀ e₁ M.initialState (fun _ => []) [] [] (gpair (x, w0)) [] [] none
    rw [gpair_left, gpair_right, List.append_nil, List.append_nil, fstk_nil_I] at this
    exact (congrArg (fun c => (flip bind (TM2.step (firstProg M C e₀ e₁)))^[
      (gpair (x, w0)).length + 1] (some c))
      (initList_eq (firstM M C e₀ e₁) (gpair (x, w0)))).trans this
  have q2 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[x.reverse.length + 1]
      (some (⟨some (Sum.inr (1 : FL)), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse [] []⟩ : FCfg M A B C)) =
      some (embF none [] w0.reverse [] [] [] (initList M (x.map e₀))) := by
    have := loop2 e₀ e₁ M.initialState w0.reverse ([] : List (B ⊕ C)) [] x.reverse
      (fun _ => []) none
    rw [embF_init]
    simpa using this
  have q3 := simulate (TM2.step M.m) (TM2.step (firstProg M C e₀ e₁))
    (embF none [] w0.reverse [] [] []) (stepF e₀ e₁ none [] w0.reverse [] [] []) s _ _ h
  rw [embF_halt] at q3
  have q4 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[w0.reverse.length + 1]
      (some (⟨some (Sum.inr (2 : FL)), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] w0.reverse [] [] []⟩ : FCfg M A B C)) =
      some (⟨some (Sum.inr (3 : FL)), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] [] (w0.map Sum.inr)⟩ :
          FCfg M A B C) := by
    have := loop3 e₀ e₁ M.initialState (Function.update (fun _ => []) M.k₁ m) ([] : List A)
      ([] : List B) w0.reverse [] none
    simpa using this
  have q5 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[m.length + 1]
      (some (⟨some (Sum.inr (3 : FL)), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] [] (w0.map Sum.inr)⟩ :
          FCfg M A B C)) =
      some (⟨some (Sum.inr (4 : FL)), (M.initialState, none),
        fstk (fun _ => []) [] [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg M A B C) := by
    have := loop4 e₀ e₁ M.initialState (fun _ => []) (w0.map Sum.inr) ([] : List A) m [] none
    simpa using this
  have q6 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[(m.reverse.map e₁).length + 1]
      (some (⟨some (Sum.inr (4 : FL)), (M.initialState, none),
        fstk (fun _ => []) [] [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg M A B C)) =
      some (haltList (firstM M C e₀ e₁) (gpair (m.map e₁, w0))) := by
    have := loop5 e₀ e₁ M.initialState (fun _ => []) ([] : List A) (m.reverse.map e₁)
      (w0.map Sum.inr) none
    rw [fstk_nil_O] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (haltList_eq (firstM M C e₀ e₁) (gpair (m.map e₁, w0)))).symm)
    simp [gpair]
    rfl
  refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [gpair_length, List.length_reverse, List.length_map]
  omega

theorem first_polyTime {α β A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [Inhabited A] [Inhabited B] [Inhabited C]
    (ea : α → List A) (eb : β → List B) (f : α → β)
    (c : Turing.TM2ComputableInPolyTime ea eb f) :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun p : α × List C => gpair (ea p.1, p.2))
      (fun p : β × List C => gpair (eb p.1, p.2))
      (fun p : α × List C => (f p.1, p.2))) := by
  let e₀ : A → c.tm.Γ c.tm.k₀ := fun a => c.inputAlphabet.invFun a
  let e₁ : c.tm.Γ c.tm.k₁ → B := fun y => c.outputAlphabet y
  let T : Polynomial ℕ :=
    c.time + Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  have key : ∀ p : α × List C, ∃ n, n ≤ T.eval (gpair (ea p.1, p.2)).length ∧
      (flip bind (TM2.step (firstProg c.tm C e₀ e₁)))^[n]
          (some (initList (firstM c.tm C e₀ e₁) (gpair (ea p.1, p.2)))) =
        some (haltList (firstM c.tm C e₀ e₁) (gpair (eb (f p.1), p.2))) := by
    rintro ⟨a, w⟩
    have hs : ∃ s, s ≤ Polynomial.eval (ea a).length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm ((ea a).map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (eb (f a)))) :=
      ⟨(c.outputsFun a).steps, (c.outputsFun a).steps_le_m, (c.outputsFun a).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run (C := C) e₀ e₁ (ea a) w _ s h
    have hm : (List.map c.outputAlphabet.invFun (eb (f a))).map e₁ = eb (f a) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (eb (f a))]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have h' := h
    rw [haltList_eq, initList_eq] at h'
    have hlen := run_length c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self, List.length_map] at hlen
    have hin : ((Function.update (fun _ => [] : ∀ k, List (c.tm.Γ k)) c.tm.k₀ ((ea a).map e₀))
        c.tm.k₁).length ≤ (ea a).length := by
      by_cases hk : c.tm.k₁ = c.tm.k₀
      · rw [hk, Function.update_self, List.length_map]
      · rw [Function.update_of_ne hk]; simp
    have b2 : Polynomial.eval (ea a).length c.time ≤
        Polynomial.eval ((ea a).length + w.length) c.time :=
      eval_mono _ (by omega)
    have hmul : maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval ((ea a).length + w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, gpair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm C e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm C e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm C e₀ e₁) l)))
            (hm _ (gpair (ea p.1, p.2)))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm C e₀ e₁) l))
              (hm _ (gpair (eb (f p.1), p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }⟩

end PEqualNP.Outside.Kit.Gen

namespace PEqualNP.Outside.Kit.ExpPad

open PEqualNP.Library

open Turing

def expPad (x : List Bool) : List Bool := List.replicate (2 ^ x.length) true ++ false :: x

abbrev PadK : Type := Fin 5

abbrev PadL : Type := Fin 6

abbrev PadΓ : PadK → Type
  | (0 : PadK) => Bool
  | (1 : PadK) => Bool
  | (2 : PadK) => Bool
  | (3 : PadK) => Bool
  | (4 : PadK) => Bool

def padProg : PadL → TM2.Stmt PadΓ PadL (Option Bool)
  | (0 : PadL) => .push (2 : PadK) (fun _ => true) (.goto fun _ => (1 : PadL))
  | (1 : PadL) =>
    .pop (0 : PadK) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push (1 : PadK) (fun s => s.getD false) (.goto fun _ => (2 : PadL)))
        (.goto fun _ => (4 : PadL)))
  | (2 : PadL) =>
    .pop (2 : PadK) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push (3 : PadK) (fun _ => true) (.push (3 : PadK) (fun _ => true) (.goto fun _ => (2 : PadL))))
        (.goto fun _ => (3 : PadL)))
  | (3 : PadL) =>
    .pop (3 : PadK) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push (2 : PadK) (fun _ => true) (.goto fun _ => (3 : PadL)))
        (.goto fun _ => (1 : PadL)))
  | (4 : PadL) =>
    .pop (1 : PadK) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push (4 : PadK) (fun s => s.getD false) (.goto fun _ => (4 : PadL)))
        (.push (4 : PadK) (fun _ => false) (.goto fun _ => (5 : PadL))))
  | (5 : PadL) =>
    .pop (2 : PadK) (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push (4 : PadK) (fun _ => true) (.goto fun _ => (5 : PadL)))
        .halt)

def padTM : FinTM2 where
  K := PadK
  k₀ := (0 : PadK)
  k₁ := (4 : PadK)
  Γ := PadΓ
  Λ := PadL
  main := (0 : PadL)
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := padProg

def pstk (i s a b o : List Bool) : ∀ k, List (PadΓ k)
  | (0 : PadK) => i
  | (1 : PadK) => s
  | (2 : PadK) => a
  | (3 : PadK) => b
  | (4 : PadK) => o

@[simp] theorem pstk_I (i s a b o : List Bool) : pstk i s a b o (0 : PadK) = i := rfl
@[simp] theorem pstk_S (i s a b o : List Bool) : pstk i s a b o (1 : PadK) = s := rfl
@[simp] theorem pstk_A (i s a b o : List Bool) : pstk i s a b o (2 : PadK) = a := rfl
@[simp] theorem pstk_B (i s a b o : List Bool) : pstk i s a b o (3 : PadK) = b := rfl
@[simp] theorem pstk_O (i s a b o : List Bool) : pstk i s a b o (4 : PadK) = o := rfl

@[simp] theorem pstk_set_I (i i' s a b o : List Bool) :
    Function.update (pstk i s a b o) (0 : PadK) i' = pstk i' s a b o := by
  funext k; fin_cases k <;> simp [pstk]
@[simp] theorem pstk_set_S (i s s' a b o : List Bool) :
    Function.update (pstk i s a b o) (1 : PadK) s' = pstk i s' a b o := by
  funext k; fin_cases k <;> simp [pstk]
@[simp] theorem pstk_set_A (i s a a' b o : List Bool) :
    Function.update (pstk i s a b o) (2 : PadK) a' = pstk i s a' b o := by
  funext k; fin_cases k <;> simp [pstk]
@[simp] theorem pstk_set_B (i s a b b' o : List Bool) :
    Function.update (pstk i s a b o) (3 : PadK) b' = pstk i s a b' o := by
  funext k; fin_cases k <;> simp [pstk]
@[simp] theorem pstk_set_O (i s a b o o' : List Bool) :
    Function.update (pstk i s a b o) (4 : PadK) o' = pstk i s a b o' := by
  funext k; fin_cases k <;> simp [pstk]

theorem pstk_start (i : List Bool) :
    pstk i [] [] [] [] = Function.update (fun _ => [] : ∀ k, List (PadΓ k)) (0 : PadK) i := by
  funext k; fin_cases k <;> simp [pstk]

theorem pstk_end (o : List Bool) :
    pstk [] [] [] [] o = Function.update (fun _ => [] : ∀ k, List (PadΓ k)) (4 : PadK) o := by
  funext k; fin_cases k <;> simp [pstk]

abbrev PadCfg : Type := TM2.Cfg PadΓ PadL (Option Bool)

abbrev padStep : Option PadCfg → Option PadCfg := flip bind (TM2.step padProg)

theorem start_step (st : Option Bool) (i s a b o : List Bool) :
    padStep (some ⟨some (0 : PadL), st, pstk i s a b o⟩) =
      some ⟨some (1 : PadL), st, pstk i s (true :: a) b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem outer_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some (1 : PadL), st, pstk (y :: i) s a b o⟩) =
      some ⟨some (2 : PadL), some y, pstk i (y :: s) a b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem outer_nil (st : Option Bool) (s a b o : List Bool) :
    padStep (some ⟨some (1 : PadL), st, pstk [] s a b o⟩) =
      some ⟨some (4 : PadL), none, pstk [] s a b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem dbl_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some (2 : PadL), st, pstk i s (y :: a) b o⟩) =
      some ⟨some (2 : PadL), some y, pstk i s a (true :: true :: b) o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem dbl_nil (st : Option Bool) (i s b o : List Bool) :
    padStep (some ⟨some (2 : PadL), st, pstk i s [] b o⟩) =
      some ⟨some (3 : PadL), none, pstk i s [] b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem back_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some (3 : PadL), st, pstk i s a (y :: b) o⟩) =
      some ⟨some (3 : PadL), some y, pstk i s (true :: a) b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem back_nil (st : Option Bool) (i s a o : List Bool) :
    padStep (some ⟨some (3 : PadL), st, pstk i s a [] o⟩) =
      some ⟨some (1 : PadL), none, pstk i s a [] o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem unsave_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some (4 : PadL), st, pstk i (y :: s) a b o⟩) =
      some ⟨some (4 : PadL), some y, pstk i s a b (y :: o)⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem unsave_nil (st : Option Bool) (i a b o : List Bool) :
    padStep (some ⟨some (4 : PadL), st, pstk i [] a b o⟩) =
      some ⟨some (5 : PadL), none, pstk i [] a b (false :: o)⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem fin_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some (5 : PadL), st, pstk i s (y :: a) b o⟩) =
      some ⟨some (5 : PadL), some y, pstk i s a b (true :: o)⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem fin_nil (st : Option Bool) (i s b o : List Bool) :
    padStep (some ⟨some (5 : PadL), st, pstk i s [] b o⟩) =
      some ⟨none, none, pstk i s [] b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

abbrev rep (n : ℕ) : List Bool := List.replicate n true

theorem rep_succ (n : ℕ) : true :: rep n = rep (n + 1) := rfl

theorem dblLoop (i s o : List Bool) :
    ∀ (a b : ℕ) (st : Option Bool),
      padStep^[a + 1] (some ⟨some (2 : PadL), st, pstk i s (rep a) (rep b) o⟩) =
        some ⟨some (3 : PadL), none, pstk i s [] (rep (2 * a + b)) o⟩ := by
  intro a
  induction a with
  | zero => intro b st; simpa using dbl_nil st i s (rep b) o
  | succ a ih =>
    intro b st
    rw [Function.iterate_succ_apply, ← rep_succ a, dbl_cons, rep_succ, rep_succ, ih]
    rw [show 2 * a + (b + 1 + 1) = 2 * (a + 1) + b from by omega]

theorem backLoop (i s o : List Bool) :
    ∀ (b a : ℕ) (st : Option Bool),
      padStep^[b + 1] (some ⟨some (3 : PadL), st, pstk i s (rep a) (rep b) o⟩) =
        some ⟨some (1 : PadL), none, pstk i s (rep (b + a)) [] o⟩ := by
  intro b
  induction b with
  | zero => intro a st; simpa using back_nil st i s (rep a) o
  | succ b ih =>
    intro a st
    rw [Function.iterate_succ_apply, ← rep_succ b, back_cons, rep_succ, ih]
    rw [show b + (a + 1) = b + 1 + a from by omega]

def outerSteps : ℕ → ℕ → ℕ
  | _, 0 => 1
  | a, n + 1 => outerSteps (2 * a) n + ((2 * a + 1) + ((a + 1) + 1))

theorem outerSteps_eq : ∀ (n a : ℕ), outerSteps a n + 3 * a = 3 * a * 2 ^ n + 3 * n + 1 := by
  intro n
  induction n with
  | zero => intro a; simp [outerSteps]; omega
  | succ n ih =>
    intro a
    have h := ih (2 * a)
    have e : 3 * a * 2 ^ (n + 1) = 3 * (2 * a) * 2 ^ n := by ring
    rw [outerSteps, e]
    omega

theorem outerLoop :
    ∀ (x s : List Bool) (a : ℕ) (st : Option Bool),
      padStep^[outerSteps a x.length] (some ⟨some (1 : PadL), st, pstk x s (rep a) [] []⟩) =
        some ⟨some (4 : PadL), none, pstk [] (x.reverse ++ s) (rep (a * 2 ^ x.length)) [] []⟩ := by
  intro x
  induction x with
  | nil => intro s a st; simpa [outerSteps] using outer_nil st s (rep a) [] []
  | cons y x ih =>
    intro s a st
    rw [List.length_cons, outerSteps,
      Function.iterate_add_apply padStep (outerSteps (2 * a) x.length),
      Function.iterate_add_apply padStep (2 * a + 1) ((a + 1) + 1),
      Function.iterate_succ_apply padStep (a + 1), outer_cons]
    have h1 : padStep^[a + 1]
        (some ⟨some (2 : PadL), some y, pstk x (y :: s) (rep a) [] []⟩) =
        some ⟨some (3 : PadL), none, pstk x (y :: s) [] (rep (2 * a)) []⟩ :=
      dblLoop x (y :: s) [] a 0 (some y)
    rw [h1]
    have h2 : padStep^[2 * a + 1]
        (some ⟨some (3 : PadL), none, pstk x (y :: s) [] (rep (2 * a)) []⟩) =
        some ⟨some (1 : PadL), none, pstk x (y :: s) (rep (2 * a)) [] []⟩ :=
      backLoop x (y :: s) [] (2 * a) 0 none
    rw [h2, ih]
    rw [show 2 * a * 2 ^ x.length = a * 2 ^ (x.length + 1) from by ring]
    simp

theorem unsaveLoop (a : List Bool) :
    ∀ (s o : List Bool) (st : Option Bool),
      padStep^[s.length + 1] (some ⟨some (4 : PadL), st, pstk [] s a [] o⟩) =
        some ⟨some (5 : PadL), none, pstk [] [] a [] (false :: (s.reverse ++ o))⟩ := by
  intro s
  induction s with
  | nil => intro o st; simpa using unsave_nil st [] a [] o
  | cons y s ih =>
    intro o st
    rw [List.length_cons, Function.iterate_succ_apply, unsave_cons, ih]
    simp

theorem finLoop :
    ∀ (a : ℕ) (o : List Bool) (st : Option Bool),
      padStep^[a + 1] (some ⟨some (5 : PadL), st, pstk [] [] (rep a) [] o⟩) =
        some ⟨none, none, pstk [] [] [] [] (rep a ++ o)⟩ := by
  intro a
  induction a with
  | zero => intro o st; simpa using fin_nil st [] [] [] o
  | succ a ih =>
    intro o st
    rw [Function.iterate_succ_apply, ← rep_succ a, fin_cons, ih]
    rw [show rep a ++ true :: o = true :: rep a ++ o from by
      simp [rep, ← List.replicate_succ, List.replicate_succ']]

def padSteps (n : ℕ) : ℕ := (2 ^ n + 1) + ((n + 1) + (outerSteps 1 n + 1))

theorem padSteps_eq (n : ℕ) : padSteps n = 4 * 2 ^ n + 4 * n + 1 := by
  have h := outerSteps_eq n 1
  unfold padSteps
  omega

theorem pad_run (x : List Bool) :
    (flip bind (TM2.step padProg))^[padSteps x.length] (some (initList padTM x)) =
      some (haltList padTM (expPad x)) := by
  refine (congrArg (fun c => (flip bind (TM2.step padProg))^[padSteps x.length]
    (some c)) (initList_eq padTM _)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq padTM _)).symm)
  show padStep^[padSteps x.length]
    (some (⟨some (0 : PadL), none, Function.update (fun _ => []) (0 : PadK) x⟩ : PadCfg)) =
    some (⟨none, none, Function.update (fun _ => []) (4 : PadK) (expPad x)⟩ : PadCfg)
  rw [← pstk_start, ← pstk_end, padSteps, Function.iterate_add_apply padStep (2 ^ x.length + 1),
    Function.iterate_add_apply padStep (x.length + 1),
    Function.iterate_succ_apply padStep (outerSteps 1 x.length), start_step]
  have h1 : padStep^[outerSteps 1 x.length]
      (some ⟨some (1 : PadL), none, pstk x [] [true] [] []⟩) =
      some ⟨some (4 : PadL), none, pstk [] x.reverse (rep (2 ^ x.length)) [] []⟩ := by
    simpa using outerLoop x [] 1 none
  have h2 : padStep^[x.length + 1]
      (some ⟨some (4 : PadL), none, pstk [] x.reverse (rep (2 ^ x.length)) [] []⟩) =
      some ⟨some (5 : PadL), none, pstk [] [] (rep (2 ^ x.length)) [] (false :: x)⟩ := by
    simpa using unsaveLoop (rep (2 ^ x.length)) x.reverse [] none
  rw [h1, h2, finLoop]
  rfl

theorem expPad_time : PEqualNP.Library.ComputableInTime
    (fun x : List Bool => x) (fun x : List Bool => x) expPad
    (fun n : ℕ => 8 * 2 ^ n + 8 * n + 8) := by
  refine ⟨{
    tm := padTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := padSteps
    outputsFun := fun x =>
      { steps := padSteps x.length
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := pad_run x
          exact (congrArg (fun l => (flip bind (TM2.step padProg))^[padSteps x.length]
            (some (initList padTM l))) (hm _ x)).trans
            (this.trans (congrArg (fun l => some (haltList padTM l)) (hm Bool _).symm))
        steps_le_m := le_refl _ } }, fun n => ?_⟩
  show padSteps n ≤ 8 * 2 ^ n + 8 * n + 8
  rw [padSteps_eq]
  omega

end PEqualNP.Outside.Kit.ExpPad
