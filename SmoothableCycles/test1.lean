import Mathlib

open Matrix

variable {α : Type*} {n n': ℕ}

example : ![1,2,3] 1 = 2 := rfl


lemma not_ge_eq : ∀ {a b : Fin n}, ¬ (a ≥ b) → a < b := by
  intros a b
  simp only [ge_iff_le, not_le, imp_self]

lemma le_or_gt' : ∀ {a b : Fin n}, (a ≤ b) ∨ (a > b) := by
  intros a b
  by_cases h : a ≤ b
  · left; exact h
  right; exact Nat.lt_of_not_ge h

lemma le_ge : ∀ {a b : Fin n}, a < b → b > a := by
  intros a b
  simp only [gt_iff_lt]
  simp only [imp_self]

lemma le_fin_nat : ∀ {a b : Fin n}, (a ≤ b) ↔ (a.val ≤ b.val) := by
  intros a b
  simp only [Fin.le_iff_val_le_val]

lemma lt_fin_nat : ∀ {a b : Fin n}, (a < b) ↔ (a.val < b.val) := by
  intros a b
  simp only [Fin.lt_iff_val_lt_val]

lemma le_or_gt_fin_nat (a b : Fin n): (a ≤ b) ∨ (a > b) := by
  rw [le_fin_nat]
  by_cases h : a.val ≤ b.val
  · left; exact h
  right; exact Nat.lt_of_not_ge h

lemma zero_le_fin (a : Fin n.succ) : (0 : Fin n.succ) ≤ a := by
  rw [le_fin_nat]
  exact Nat.zero_le a.val

lemma fin_le_last (a : Fin n.succ) : a ≤ Fin.last n := by
  rw [le_fin_nat]
  simp [Fin.last]
  exact Nat.le_of_lt_succ a.is_lt

lemma plus_one_gt {k:ℕ } (a : Fin k.succ) : ¬ (a = Fin.last k) → a + 1 > a := by
  rw [gt_iff_lt]
  intro h
  simp only [Nat.succ_eq_add_one, Fin.lt_add_one_iff]
  rw [@Fin.lt_last_iff_ne_last]
  exact h

lemma fin_add_comm {k : ℕ} (a b : Fin k.succ): a + b = b + a := by
  rw [Fin.add_def, Fin.add_def]
  simp only [Nat.add_comm]

lemma not_last_lt_last {k : ℕ} (a : Fin k.succ) : ¬ (a = Fin.last k) → a < Fin.last k := by
  intro h
  rw [Fin.lt_last_iff_ne_last]
  exact h

lemma fin_lt_nat (a : Fin n) (m : ℕ) : (a < m) ↔ (a.val < m) := by
  simp only [Fin.lt_iff_val_lt_val]

lemma le_ne (a b : Fin n.succ) : (a < b) → ¬ (a = b)  := by
  intro h
  rw [Fin.lt_iff_le_and_ne] at h
  exact h.2

lemma fin_val_plus_one (a : Fin n.succ) : ¬a = Fin.last n → (a + 1).val = a.val + 1 := by
  intro h
  have h1 : a.val + 1 < n.succ := by
    have h2 : a < Fin.last n := not_last_lt_last a h
    have h3 : a.val < n := by
      rw [Fin.lt_iff_val_lt_val] at h2
      simp [Fin.last] at h2
      exact h2
    exact Nat.succ_lt_succ h3
  rw [Fin.val_add]
  simp only [Nat.succ_eq_add_one, Fin.val_one', Nat.add_mod_mod, Nat.mod_succ_eq_iff_lt,
    add_lt_add_iff_right, gt_iff_lt]
  have h2 : a.val +1 < n +1 := by
    simp [h1]
  exact Nat.lt_of_succ_lt_succ h2


def system_of_intervals {n k : ℕ} (f g : Fin k.succ → Fin n.succ) : Prop :=
  (f (0:Fin k.succ) = (0: Fin n.succ)) ∧ (g (Fin.last k) = (Fin.last n)) ∧ StrictMono f ∧ StrictMono g ∧ (∀ i : Fin k.succ, f i ≤ g i) ∧ (∀ i: Fin k.succ, ¬i = Fin.last k → (g i)+1 = f (i+1))

lemma interval_split {n k : ℕ} : ∀ f g : Fin k.succ → Fin n.succ, system_of_intervals f g → ∀ i : Fin n.succ, ∃ j : Fin k.succ, f j ≤ i ∧ i ≤ g j := by
  intros f g h_system i
  have h_f0 : f (0:Fin k.succ) = (0: Fin n.succ) := h_system.1
  have h_fk : g (Fin.last k) = (Fin.last n) := h_system.2.1
  have _ : StrictMono f := h_system.2.2.1
  have h_g_mono : StrictMono g := h_system.2.2.2.1
  have _ : ∀ i : Fin k.succ, f i ≤ g i := h_system.2.2.2.2.1
  have h_interval : ∀ i : Fin k.succ, ¬i = Fin.last k → (g i)+1 = f (i+1) := h_system.2.2.2.2.2
  let set := Finset.univ.filter (fun j => f j ≤ i)
  have h_set_nonempty : set.Nonempty := by
    use 0
    rw [@Finset.mem_filter]
    constructor
    · simp
    · rw [h_f0]
      exact zero_le_fin i
  let jmax : Fin k.succ := set.max' (h_set_nonempty)
  use jmax
  constructor
  · have h1: jmax ∈ set := by
      exact Finset.max'_mem set h_set_nonempty
    rw [@Finset.mem_filter] at h1
    exact h1.2
  · by_cases h_eq : jmax = Fin.last k
    · rw [h_eq]
      rw [h_fk]
      exact fin_le_last i
    · have h1 : f (jmax + 1) > i := by
        have h2 : ¬ (jmax + 1 ∈ set) := by
          have h4 : jmax +1 >  jmax := by
            exact plus_one_gt jmax h_eq
          have h4' : jmax < jmax + 1 := by
            exact le_ge h4
          rw [set.max'_lt_iff] at h4'
          by_contra h_in
          let h3 := h4' (jmax + 1) h_in
          exact lt_irrefl (jmax+1) h3
        have h6 : jmax + 1 ∈ Finset.univ := by
          simp
        have h5 : f (jmax + 1) > i := by
          rw [@Finset.mem_filter] at h2
          rw [not_and] at h2
          have h26 : ¬ (f (jmax + 1) ≤ i) := by
            exact h2 h6
          simp only [Nat.succ_eq_add_one, gt_iff_lt]
          simp only [not_le] at h26
          exact h26
        exact h5
      have h2 : i < g jmax + 1:= by
        have h3 : f (jmax + 1) > i := by
          exact h1
        have h4 : g jmax + 1 = f (jmax + 1) := by
          exact h_interval jmax h_eq
        rw [h4]
        exact h3
      have h3 : g jmax < Fin.last n := by
        have _: jmax ≤ Fin.last k := by
          exact fin_le_last (jmax)
        have h5: jmax < Fin.last k := by
          exact not_last_lt_last jmax h_eq
        let h6 := h_g_mono h5
        rw [←h_fk]
        exact h6
      have h4: ¬ g jmax =Fin.last n := by
        exact le_ne (g jmax) (Fin.last n) h3
      have h5 : (g jmax + 1).val = (g jmax).val + 1 := by
        exact fin_val_plus_one (g jmax) h4
      let h6 := Fin.lt_iff_val_lt_val.mp h2
      rw [h5] at h6
      have h6' : i.val < 1 + (g jmax).val := by
        rw [Nat.add_comm]
        exact h6
      have h7 : i.val ≤  (g jmax).val := by
        exact Nat.lt_one_add_iff.mp h6'
      exact Fin.le_iff_val_le_val.mpr h7


#eval (2:Fin 5) ≥ (-2:Fin 5)


def Y'caseA (i : Fin n) := i.val % 2 = 0
def Y'caseB (i : Fin n) := i.val % 2 = 1

lemma Y'AorB (i: Fin n) : Y'caseA i ∨ Y'caseB i := by
  unfold Y'caseA Y'caseB
  exact Nat.mod_two_eq_zero_or_one i.val

def Y'case1 (l : ℕ) (i j : Fin (4 * l + 6)) : Prop := (j-i % (4 * l + 6)) = 1
def Y'case2 (l : ℕ) (i j : Fin (4 * l + 6)) : Prop := (j-i % (4 * l + 6)) = -1
def Y'case3 (l : ℕ) (i j : Fin (4 * l + 6)) : Prop := (j-i % (4 * l + 6)) ≥ 2 ∧ (j-i % (4 * l + 6)) ≤ 2*l+2
def Y'case4 (l : ℕ) (i j : Fin (4 * l + 6)) : Prop := (j-i % (4 * l + 6)) ≤ -2 ∧ (j-i % (4 * l + 6)) ≥ -(2*l+2)
def Y'case5 (l : ℕ) (i j : Fin (4 * l + 6)) : Prop := (j-i % (4 * l + 6)) = 2*l+3
def Y'case6 (l : ℕ) (i j : Fin (4 * l + 6)) : Prop := (j-i % (4 * l + 6)) = 0

def Y'cases_ij (l : ℕ) (i j : Fin (4 * l + 6)) : (Fin 6 → Prop) :=
  ![Y'case1 l i j, Y'case2 l i j, Y'case3 l i j, Y'case4 l i j, Y'case5 l i j, Y'case6 l i j]

def Y'f (l : ℕ): (Fin 6) → Fin (4*l + 6)  :=
  ![0, 1, 2, 2*l+3, 2*l+4, 2*l+5]

lemma Y'f_values (l : ℕ) :
  Y'f l 0 = 0 ∧ Y'f l 1 = 1 ∧ Y'f l 2 = 2 ∧
  Y'f l 3 = 2*l+3 ∧ Y'f l 4 = 2*l+4 ∧ Y'f l 5 = 2*l+5 := by
    simp [Y'f]
    norm_cast

def Y'g (l : ℕ): (Fin 6) →  Fin (4*l + 6) :=
  ![0, 1,  2*l+2, 2*l+3, 4*l+4, 2*l+5]

lemma Y'fStrictMono (l : ℕ) : StrictMono (Y'f l) := by
  unfold Y'f StrictMono
  intro i j h_ij
  -- The sequence is [0, 1, 2, 2*l+3, 2*l+4, 2*l+5]
  -- All consecutive terms satisfy: 0 < 1 < 2 < 2*l+3 < 2*l+4 < 2*l+5
  have vals := Y'f_values l
  fin_cases i <;> fin_cases j <;> (simp_all)
  norm_cast
  have h:  ![0, 1, 2, 2 * l + 3, 2 * l + 4, 2 * l + 5] 5 = 2 * l + 5 := by
    rfl
  simp [Fin.lt_iff_val_lt_val.mpr]
  all_goals norm_num
  rw [Fin.lt_iff_val_lt_val.mp]
  rw [h]
  omega
  have h:  ![0, 1, 2, 2 * l + 3, 2 * l + 4, 2 * l + 5] 5 = 2 * l + 5 := by
    rfl
  rw [h]
  omega
  have h:  ![0, 1, 2, 2 * l + 3, 2 * l + 4, 2 * l + 5] 5 = 2 * l + 5 := by
    rfl
  rw [h]
  omega
  have h:  ![0, 1, 2, 2 * l + 3, 2 * l + 4, 2 * l + 5] 5 = 2 * l + 5 := by
    rfl
  rw [h]
  omega
  have h:  ![0, 1, 2, 2 * l + 3, 2 * l + 4, 2 * l + 5] 5 = 2 * l + 5 := by
    rfl
  rw [h]
  omega

lemma interval_split_Y' (l : ℕ) : system_of_intervals (Y'f l) (Y'g l) := by
  unfold Y'f Y'g system_of_intervals
  let l' := (l : Fin (4*l + 6))
  constructor
  · simp [Y'f]
  constructor
  · simp only [Nat.succ_eq_add_one]
    have h : ![0, 1, 2 * l' + 2, 2 * l' + 3, -2, -1] (Fin.last 5) = -1 := by
      rfl
    simp [h]
    have h2 : (-1:Fin (4*l + 6)) = (4*l+5: Fin (4*l + 6)) := by
      rw [@neg_eq_iff_add_eq_zero]
      rw [@fin_add_comm]
      simp only [Nat.succ_eq_add_one]
      norm_cast
      simp
    have h3 : (4*l +5 : Fin (4*l +6)) = Fin.last (4*l +5) := by
      norm_cast
      rw [Fin.natCast_eq_last]
    rw [h2, h3]
  constructor
  · unfold StrictMono
    intro i j h_ij
    simp [Y'f]
    fin_cases i <;> fin_cases j <;> simp [h_ij]

  constructor
  · simp [Y'g]
  constructor
  · intro i
    simp [Y'f, Y'g]
    have h : ∀ m : Fin 6, (Y'f l m) ≤ (Y'g l m) := by
      intro m
      fin_cases m <;> simp
    exact h i
  intro i h_ne
  simp [Y'f, Y'g]
  fin_cases i <;> simp [h_ne]

lemma Y'case1or6 (l : ℕ) (i j : Fin (4 * l + 6)) : Y'case1 l i j ∨ Y'case6 l i j ∨ Y'case2 l i j ∨ Y'case3 l i j ∨ Y'case4 l i j ∨ Y'case5 l i j := by
  unfold Y'case1 Y'case2 Y'case3 Y'case4 Y'case5 Y'case6
  have h1 : ∀ k : Fin (4 * l + 6), (k ≤ 2*l+3) ∨ (k > 2*l+3) := by
    intro k
    exact le_or_gt_fin_nat k (2*l+3 : Fin (4*l+6))
  have h2 : ∀ k : Fin (4 * l + 6), (k≤ 2*l + 3) → (k = 1 ∨ k = 0 ∨ k = -1 ∨ (k ≥ 2 ∧ k ≤ 2*l+2)) := by
    intro k hle
    by_cases h1 : k = 1
    · left; exact h1
    by_cases h0 : k = 0
    · right; left; exact h0
    by_cases h_neg1 : k = -1
    · right; right; left; exact h_neg1
    by_cases h_range_pos : (k ≥ 2 ∧ k ≤ 2*l+2)
    · right; right; right; left; exact h_range_pos
    right; right; right; right; left;
    have hk : k < 2*l+3 := by
      rw [Nat.lt_iff_add_one_le]
      apply Nat.le_of_lt_succ
      rw [Fin.le_iff_val_le_val] at *
      exact hle
    have h_all : ¬ (k = 1) ∧ ¬ (k = 0) ∧ ¬ (k = -1) ∧ ¬ (k ≥ 2 ∧ k ≤ 2*l+2) := by
      simp only [not_or_distrib]
      constructor
      · exact not_eq_of_ne h1
      constructor
      · exact not_eq_of_ne h0
      constructor
      · exact not_eq_of_ne h_neg1
      exact not_eq_of_ne h_range_pos

    have hk_ge : ¬ (k ≥ 2) := by
      intro hk_ge'
      have hk_le : k ≤ 2*l+2 := by
        rw [Fin.le_iff_val_le_val] at *
        rw [Nat.le_iff_add_one_le]
        apply Nat.le_of_lt_succ
        exact hk
      exact h_all.3 ⟨hk_ge', hk_le⟩

    have hk_lt_2 : k < 2 := by
      rw [Nat.lt_iff_add_one_le]
      apply Nat.le_of_lt_succ
      rw [Fin.le_iff_val_le_val]
      apply Nat.le_of_not_ge
      exact hk_ge

    have hk_eq : k = 1 ∨ k = 0 ∨ k = -1 := by
      cases

  have h2 : ∀ k : Fin (4 * l + 6), (k ≤ 2*l+3) ∨ (k ≥ 2*l+4) := by
    intro k
    by_cases h : k ≤ 2*l+3
    · left; exact h
    right;
    have h3 : (2*l + 3 : Fin (4*l+6)) < (k: Fin (4*l+6)) := by
      simp only [ge_iff_le, not_le, imp_self] at *
      simp only [gt_iff_lt] at *
      exact h
    have h4 : 2*l + 3 < k := by
      rw [Fin.le_iff_val_le_val] at *

      apply Nat.lt_of_not_ge
      rw [Fin.le_iff_val_le_val]
      rw [Nat.lt_iff_add_one_le]
      apply Nat.le_of_lt_succ
      exact h3

    have h1': k > 2*l+3 := by
      simp only [ge_iff_le, not_le, imp_self] at *
      simp only [gt_iff_lt] at *
      exact h

    rw [Nat.lt_iff_add_one_le] at h

    exact Nat.le_of_lt (Nat.lt_of_not_ge h)
  have h : ∀ k : Fin (4 * l + 6), k = 1 ∨ k = 0 ∨ k = -1 ∨ (k ≥ 2 ∧ k ≤ 2*l+2) ∨ (k ≤ -2 ∧ k ≥ -(2*l+2)) ∨ k = 2*l+3 := by
    intro k
    by_cases h1 : k = 1
    · left; exact h1
    by_cases h0 : k = 0
    · right; left; exact h0
    by_cases h_neg1 : k = -1
    · right; right; left; exact h_neg1
    by_cases h_range_pos : (k ≥ 2 ∧ k ≤ 2*l+2)
    · right; right; right; left; exact h_range_pos
    by_cases h_range_neg : (k ≤ -2 ∧ k ≥ -(2*l+2))
    · right; right; right; right; left; exact h_range_neg
    right; right; right; right; right; exact Nat.lt_of_not_ge (h1 k)


    exact Or.inr Or.inr Or.inr Or.inr Or.inr Or.inl rfl
  apply h



def Y' (l : ℕ) : Matrix (Fin (4 * l + 6)) (Fin (4 * l + 6)) ℚ :=
  let n := 4 * l + 6
  Matrix.of fun i j =>
    if (j-i % n) = 1 then
      if i % 2 = 0 then 2 else 1
    else if (j-i % n) = -1 then
      if i % 2 = 0 then -1 else -2
    else if ((j-i % n) ≥  2 ∧ (j-i % n) ≤ 2*l+2) then 1
    else if (j-i % n) ≤ -2 ∧ (j-i % n) ≥ -(2*l+2) then -1
    else if (j-i % n) = 2*l+3 then
      if i % 2 = 0 then -1 else 1
    else 0

#eval Y' 0
#eval Y' 1
