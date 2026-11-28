import Mathlib

theorem Conjectures.Cuts.Refute51c05dd90eec360519ea8b7f : ¬ (have x1 : ℕ → ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | Nat.Prime x2 ∧ Nat.Prime (x1 - x2)}.card; ∀ x2 ≤ (10 : ℕ) ^ (12 : ℕ), Even x2 → ∃ (x5 : ℕ), (2 : ℕ) ≤ x5 ∧ ((2 : ℕ) ^ x5) ^ (2 : ℕ) ≤ x2 ∧ (0 : ℕ) < x1 (x2 - (2 : ℕ) ^ x5) ∧ (0 : ℕ) < x1 (x2 + (2 : ℕ) - (2 : ℕ) ^ x5)) := by
  intro h
  obtain ⟨x5, hx5, hle, _⟩ := h 0 (Nat.zero_le _) ⟨0, rfl⟩
  have hpow : 2 ^ 2 ≤ 2 ^ x5 := Nat.pow_le_pow_right (by omega) hx5
  have hsq : 16 ≤ ((2 : ℕ) ^ x5) ^ 2 := by nlinarith
  omega
