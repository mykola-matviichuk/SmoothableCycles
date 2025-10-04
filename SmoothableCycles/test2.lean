import Mathlib


lemma lll (i1 : ℕ) : (i1 + 2) / 2 * 2 = i1 / 2 * 2 + 2 := by
  -- (i1 + 2) / 2 = i1 / 2 + 1 because 2 = 1 * 2
  simp only [Nat.ofNat_pos, Nat.add_div_right]
  rw [Nat.right_distrib]
