import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

def tC : Circuit := ⟨[⟨GateOp.or, [1,5]⟩, ⟨GateOp.or, [8,6]⟩, ⟨GateOp.and, [0,9]⟩, ⟨GateOp.or, [2,7]⟩,
  ⟨GateOp.and, [1,11]⟩, ⟨GateOp.or, [2,4]⟩, ⟨GateOp.and, [3,13]⟩, ⟨GateOp.and, [4,5]⟩,
  ⟨GateOp.or, [10,12]⟩, ⟨GateOp.or, [14,15]⟩, ⟨GateOp.or, [16,17]⟩], 18⟩

lemma ofFn8 (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

theorem tC_eval : ∀ x : Fin 8 → Bool, tC.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)) := by
  intro x
  rw [ofFn8]
  generalize x 0 = a0, x 1 = a1, x 2 = a2, x 3 = a3, x 4 = a4, x 5 = a5, x 6 = a6, x 7 = a7
  revert a0 a1 a2 a3 a4 a5 a6 a7
  decide
