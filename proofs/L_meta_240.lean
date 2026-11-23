import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_240 : ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => true) s ↔ 1 ≤ s := by
  intro n s
  constructor
  · rintro ⟨C, hC, h⟩
    by_contra hs
    have h0 : C.gates = [] := by
      simp [PEqualNP.MetaComplexity.BinaryCircuit.size] at hC
      exact List.eq_nil_of_length_eq_zero (by omega)
    have := h (fun _ => false)
    simp [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires, h0] at this
  · intro hs
    refine ⟨⟨[⟨fun _ _ => true, 0, 0⟩], n⟩, by simp [PEqualNP.MetaComplexity.BinaryCircuit.size]; omega, fun x => ?_⟩
    simp [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires]
