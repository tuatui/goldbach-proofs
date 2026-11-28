import Mathlib

theorem Conjectures.Cuts.Task0e20cec561428d099e05d319 : (have x1 : (ℕ → Bool) → ℕ → ℕ := fun (x1 : ℕ → Bool) (x2 : ℕ) => {x3 ∈ Finset.Icc (1 : ℕ) x2 | x1 x3 = Bool.true ∧ Nat.Prime (x2 - x3)}.card; have x2 : (ℕ → Bool) → ℕ → ℕ → ℝ → ℕ := fun (x2 : ℕ → Bool) (x3 x4 : ℕ) (x5 : ℝ) => {x6 ∈ Finset.Ioc x3 (x3 + x4) | Even x6 ∧ ↑(x1 x2 x6) < x5}.card; ∀ (x3 x4 : ℕ → Bool) (x5 x6 : ℕ) (x7 : ℝ), (∀ x8 ≤ x5 + x6, x3 x8 = x4 x8) → {x9 ∈ Finset.Icc (1 : ℕ) x5 | x3 x9 = Bool.true}.card = {x9 ∈ Finset.Icc (1 : ℕ) x5 | x4 x9 = Bool.true}.card ∧ x2 x3 x5 x6 x7 = x2 x4 x5 x6 x7) := by
  dsimp only
  intro m₁ m₂ K H thr hm
  refine ⟨?_, ?_⟩
  · congr 1
    refine Finset.filter_congr ?_
    intro a ha
    have haKH : a ≤ K + H := le_trans (Finset.mem_Icc.mp ha).2 (Nat.le_add_right K H)
    rw [hm a haKH]
  · congr 1
    refine Finset.filter_congr ?_
    intro n hn
    have hnKH : n ≤ K + H := (Finset.mem_Ioc.mp hn).2
    have hcount :
        {x3 ∈ Finset.Icc 1 n | m₁ x3 = Bool.true ∧ Nat.Prime (n - x3)}.card =
          {x3 ∈ Finset.Icc 1 n | m₂ x3 = Bool.true ∧ Nat.Prime (n - x3)}.card := by
      congr 1
      refine Finset.filter_congr ?_
      intro a ha
      have haKH : a ≤ K + H := le_trans (Finset.mem_Icc.mp ha).2 hnKH
      rw [hm a haKH]
    rw [hcount]
