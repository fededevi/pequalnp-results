import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_238 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasBinarySize 2 (fun x : Fin 2 → Bool => xor (x 0) (x 1)) s ↔ 1 ≤ s := by
  intro s
  constructor
  · rintro ⟨C, hC, h⟩
    by_contra hs
    have h0 : C.gates = [] := by
      simp [PEqualNP.MetaComplexity.BinaryCircuit.size] at hC
      exact List.eq_nil_of_length_eq_zero (by omega)
    have h1 := h ![true, true]
    have h2 := h ![true, false]
    have h3 := h ![false, true]
    simp [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires, h0, List.ofFn_succ] at h1 h2 h3
    rcases C with ⟨g, o⟩
    rcases o with _ | _ | o <;> simp_all
  · intro hs
    refine ⟨⟨[⟨xor, 0, 1⟩], 2⟩, by simp [PEqualNP.MetaComplexity.BinaryCircuit.size]; omega, fun x => ?_⟩
    simp [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires, List.ofFn_succ]
