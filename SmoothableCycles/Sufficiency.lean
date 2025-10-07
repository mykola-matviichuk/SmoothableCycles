import Mathlib

open Matrix

section shift

variable {α : Type*} {n n': ℕ}

def shift (v : Fin n → α) : Fin n → α := v ∘ (finRotate n).symm

def prev (i : Fin n) : Fin n := (finRotate n).symm i

def next (i : Fin n) : Fin n := finRotate n i

lemma prev_next (i : Fin n) : prev (next i) = i := by
  rw [prev, next]
  exact Equiv.symm_apply_apply (finRotate n) i

lemma shift_prev_eq (v : Fin n → α) (i : Fin n) : shift v i = v (prev i) := by
  dsimp [shift, prev]

lemma shift_succ_eq (v : Fin n → α) (i : Fin n) : shift v (next i) = v i := by
  rw [@shift_prev_eq]
  rw [@prev_next]

lemma shift_prev_iter (k:ℕ) : ∀ (v : Fin n → α) (i: Fin n) , shift^[k] v i = v (prev^[k] i) := by
  induction' k with k ih
  · intro v i
    rfl
  · intro v i
    calc
      shift^[k + 1] v i = shift (shift^[k] v) i := by
        rw [Function.iterate_succ']
        rw [Function.comp_apply]
      _ = shift^[k] v (prev i) := by rfl
      _ = v (prev^[k] (prev i)) := by rw [ih]
      _ = v (prev^[k + 1] i) := by
        simp only [Function.iterate_succ, Function.comp_apply]

lemma next_add_one (i: Fin (n'+1)) (ineqn : i ≠ Fin.last n') : (next i : ℕ ) = i + 1 := by
  let h := coe_finRotate_of_ne_last ineqn
  unfold next
  rw [h]

lemma finRotate_pred_apply (i : Fin (n + 1)) : (finRotate (n + 1)).symm i = i - 1 := by
  rw [@Equiv.symm_apply_eq]
  simp only [finRotate_succ_apply, sub_add_cancel]

lemma prev_sub_one (i: Fin (n'+1)) (in0 : i ≠ 0) : (prev i:ℕ) = i - 1 := by
  unfold prev
  rw [@finRotate_pred_apply]
  rw [@Fin.coe_sub_one]
  simp only [ite_eq_else]
  have : ¬ i= 0 := by
    exact in0
  intro h1
  contradiction

lemma prev_sub_iter  (k:ℕ) : ∀ (i: Fin (n'+1)),  (k ≤ i) →  (prev^[k] i : ℕ) = (i:ℕ) - k := by
  induction' k with k ih
  · intro i _
    rfl
  · intro i klei
    rw [@Function.iterate_add_apply]
    let j := prev^[1] i
    let h1 := ih j
    have ine0: i ≠ 0 := by
      intro h1
      rw [h1] at klei
      norm_num at klei
    have jei1: (j:ℕ) = (i:ℕ) - 1 := by
      let h2 := prev_sub_one i ine0
      have h3: j = prev i := by rfl
      rw [h3.symm] at h2
      exact h2
    have klej: k ≤ (j:ℕ) := by
      have klei1: k ≤ i -1 := by
        have : (k + 1) ≤ i := by omega
        have : (k + 1) - 1 ≤ i - 1 := by omega
        exact this
      rw [jei1.symm] at klei1
      exact klei1
    have : ((prev^[k] j) :ℕ)  = (j:ℕ) - k := by
      exact h1 klej
    rw [this]
    rw [jei1]
    rw [Nat.sub_sub]
    omega

lemma shift_property (v : Fin n → α) (i: Fin n): shift v i = v (prev i) := by
  rfl

lemma shift_iter_property (k:ℕ) : ∀ (v : Fin n → α) (i: Fin n) , shift^[k] v i = v (prev^[k] i) := by
  induction' k with k ih
  · intro v i
    rfl
  · intro v i
    calc
      shift^[k + 1] v i = shift (shift^[k] v) i := by
        rw [Function.iterate_succ']
        rw [Function.comp_apply]
      _ = shift^[k] v (prev i) := by rfl
      _ = v (prev^[k] (prev i)) := by rw [ih]
      _ = v (prev^[k + 1] i) := by
        simp only [Function.iterate_succ, Function.comp_apply]

--lemma shift_eq (v : Fin n → α) (i : Fin n) : shift v i = v ((finRotate n).symm i) := by
--  dsimp [shift]

end shift

lemma skewSymm_iff {n α : Type*} [Neg α] (M : Matrix n n α) :
    (∀ i j, M i j = - M j i) ↔ M = -Mᵀ := by
  simp [← Matrix.ext_iff]

variable (R : Type*) [CommRing R]

section X4

def X4 : Matrix (Fin 4) (Fin 4) R :=
  !![ 0,  2, -1, -1;
     -2,  0,  3, -1;
      1, -3,  0,  2;
      1,  1, -2,  0]

lemma row_sum_X4 (i : Fin 4) : ∑ j, X4 R i j = 0 := by
  fin_cases i <;> norm_num [Fin.sum_univ_four, X4]

end X4

section Y

def Y_top (l : ℕ) : Matrix (Fin 2) (Fin (4 * l + 6)) ℚ :=
  ![vecCons 0 <| vecCons 2 <|
      vecAppend (m := 2 * l + 1) (n := 2 * l + 3) (by omega) (fun _ => 1) (fun _ => -1),
    vecCons (-2) <| vecCons 0 <|
      vecAppend (m := 2 * l + 3) (n := 2 * l + 1) (by omega) (fun _ => 1) (fun _ => -1) ]

def Y (l : ℕ) : Matrix (Fin (4 * l + 6)) (Fin (4 * l + 6)) ℚ :=
  Matrix.of fun i => shift^[(i / 2) * 2] (Y_top l i)

lemma Y_is_nonempty (l : ℕ) : (4 * l + 6) > 0 := by omega

#eval Y 0
#eval Y 1
#eval Y 2

def Y' (l : ℕ) : Matrix (Fin (4 * l + 6)) (Fin (4 * l + 6)) ℚ :=
  let n := 4 * l + 6
  Matrix.of fun i j =>
    if (j-i % n) == 1 then
      if i % 2 == 0 then 2 else 1
    else if (j-i % n) == -1 then
      if i % 2 == 0 then -1 else -2
    else if ((j-i % n) ≥  2 ∧ (j-i % n) ≤ 2*l+2) then 1
    else if (j-i % n) ≤ -2 ∧ (j-i % n) ≥ -(2*l+2) then -1
    else if (j-i % n) == 2*l+3 then
      if i % 2 == 0 then -1 else 1
    else 0

#eval Y' 0  - Y 0
#eval Y' 1  - Y 1
#eval Y' 2  - Y 2



--def periodic_2_2 {n : ℕ} {α : Type*} (A : Matrix (Fin n) (Fin n) α) (nn0:n>0): Prop :=
--  ∀ (i : Fin n) (j : Fin n), A i j = A (i + Fin.ofNat' 2 nn0) j

def periodic_matrix {n : ℕ} {α : Type*} (A : Matrix (Fin n) (Fin n) α) (d : ℕ): Prop :=
  ∀ (i j : Fin n), A i j = A (prev^[d] i) (prev^[d] j)

lemma Y_is_2_periodic : ∀ (l : ℕ), periodic_matrix (Y l)  (2) := by
  intro l
  unfold periodic_matrix
  intro i j
  unfold Y
  simp only [of_apply]
  cases Nat.lt_or_ge (↑i) 2 with
  | inl hlt =>
    sorry
  | inr hge =>
    sorry


  simp only [of_apply, Fin.val_two, Function.iterate_succ, Function.iterate_one,
    Function.comp_apply]

  have shift_property : ∀ (x : Fin (4 * l + 6)) (k : ℕ),
  shift^[k + 2] (Y_top l x) = shift^[k] (Y_top l (x-(2: Fin (4 * l + 6)))) := by
    intro x k
    induction' k with m IH
    · rfl
    · simp [IH, pow_succ, shift, Function.comp]






/--/
def periodic_matrix {n : ℕ} {α : Type*} (A : Matrix (Fin n) (Fin n) α) (nn0 : n > 0) (d : ℕ): Prop :=
  ∀ (i j : Fin n), A i j = A (i + Fin.ofNat' d nn0) (j + Fin.ofNat' d nn0)



lemma Y_is_2_periodic : ∀ (l : ℕ), periodic_matrix (Y l) (Y_is_nonempty l) (2) := by
  intro l i j
  let i1 : ℕ := ↑ i
  let n := 4 * l + 6
  let d := Fin.ofNat' 2 (Y_is_nonempty l)
  --let d := 2
  have h1 : Y l i j = Y l (i + d) (j + d) := by
    dsimp [Y, shift]
    have h1 : (i1+2) / 2 * 2 = i1 / 2 *2  + 2 := by
      -- (i1 + 2) / 2 = i1 / 2 + 1 because 2 = 1 * 2
      simp only [Nat.ofNat_pos, Nat.add_div_right]
      rw [Nat.right_distrib]
    sorry

    have h2 : ((i + d) / 2) * 2 = (i + d) - (i + d) % 2 := by
      rw [Nat.mul_comm, Nat.mul_div_cancel_left ((i + d) / 2) two_ne_zero, Nat.sub_add_cancel]
      exact Nat.le_of_lt (Fin.isLt (i + d))
    rw [h1, h2]
    fin_cases (i % 2) <;> fin_cases ((i + d) % 2) <;> fin_cases (j - (i - i % 2) % n) <;> fin_cases ((j + d) - ((i + d) - (i + d) % 2) % n)
    all_goals
      simp [vecCons, vecAppend, if_pos, if_neg, Nat.mod_eq_of_lt (Fin.isLt j), Nat.mod_eq_of_lt (Fin.isLt i), Nat.mod_eq_of_lt (Fin.isLt (i + d)), Nat.mod_eq_of_lt (Fin.isLt (j + d))]
    all_goals
      try {ring}
    all_goals
      try {exact rfl}
  exact h1







lemma Y_eq_Y' (l : ℕ) : Y  l = Y' l := by
  ext i j
  let n := 4 * l + 6
  dsimp [Y, Y']
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.vecMul_apply, Matrix.vecCons, Matrix.vecAppend]
  rw [Matrix.of_apply, Matrix.of_apply]
  dsimp [Y_top, shift]
  have h1 : (i / 2) * 2 = i - i % 2 := by
    rw [Nat.mul_comm, Nat.mul_div_cancel_left (i / 2) two_ne_zero, Nat.sub_add_cancel]
    exact Nat.le_of_lt (Fin.isLt i)
  rw [h1]
  fin_cases (i % 2) <;> fin_cases (j - (i - i % 2) % n) <;> simp [vecCons, vecAppend, if_pos, if_neg, Nat.mod_eq_of_lt (Fin.isLt j), Nat.mod_eq_of_lt (Fin.isLt i)]

end Y
