import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_491 : ∀ (E k u v p : ℕ), u < v → v < 3 * (E + 1) → p < 2 * k → 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + p < 3 * (E + 1) + 18 * k * (E + 1) ^ 2 ∧ 3 * (E + 1) + 2 * k * (3 * (E + 1)) ^ 2 = 3 * (E + 1) + 18 * k * (E + 1) ^ 2 := by
  intro E k u v p huv hv hp
  refine ⟨?_, by ring⟩
  have hu : u + 1 ≤ 3 * (E + 1) := by omega
  have hv1 : v + 1 ≤ 3 * (E + 1) := by omega
  have h1 : u * (3 * (E + 1)) + v + 1 ≤ 9 * (E + 1) ^ 2 := by
    nlinarith [Nat.mul_le_mul_right (3 * (E + 1)) hu]
  have h2 : 2 * k * (u * (3 * (E + 1)) + v + 1) ≤ 2 * k * (9 * (E + 1) ^ 2) :=
    Nat.mul_le_mul_left _ h1
  nlinarith
