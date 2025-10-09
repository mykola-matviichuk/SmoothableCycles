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

lemma shift_iter_double_property (m k : ℕ) (v : Fin n → α) (i : Fin n) : shift^[m+k] (v) i = shift^[m] (v) (prev^[k] i) := by
  rw [@shift_prev_iter]
  rw [@shift_prev_iter]
  rw [Function.iterate_add_apply]

lemma next_add_one (i: Fin (n'+1)) (ineqn : i ≠ Fin.last n') : (next i : ℕ ) = i + 1 := by
  let h := coe_finRotate_of_ne_last ineqn
  unfold next
  rw [h]

lemma finRotate_pred_apply (i : Fin (n + 1)) : (finRotate (n + 1)).symm i = i - 1 := by
  rw [@Equiv.symm_apply_eq]
  simp only [finRotate_succ_apply, sub_add_cancel]

lemma prev_sub_one' (i: Fin (n'+1)) : prev i = i - 1 := by
  unfold prev
  rw [@finRotate_pred_apply]

lemma prev_power_sub  (k : ℕ) :∀ (i: Fin (n'+1)), prev^[k] i  = i - k := by
  induction' k with k ih
  · intro i
    have h: (prev^[0] i) = i := by rfl
    simp [h]
  · intro i
    let ih' := ih i
    rw [Function.iterate_succ_apply']
    rw [ih']
    rw [prev_sub_one']
    simp only [Nat.cast_add, Nat.cast_one]
    have  : - (k:Fin (n'+1)) - (1: Fin (n'+1)) = - ((k:Fin (n'+1)) + (1: Fin (n'+1))) := by
      simp only [neg_add_rev]
      rw [@neg_add_eq_sub]
    rw [@sub_sub]

lemma prev_idemp (i : Fin (n'+1)) : prev^[n'+1] i = i := by
  let h := prev_power_sub (n'+1) i
  have h': (((n':ℕ)+(1:ℕ)) : Fin (n'+1)) = 0 := by
    simp only [Fin.natCast_eq_last, Fin.last_add_one]
    simp only [Nat.cast_one, Fin.last_add_one]
  simp [h, h']

lemma prev_sub_one (i: Fin (n'+1)) (in0 : i ≠ 0) : (prev i:ℕ) = i - 1 := by
  unfold prev
  rw [@finRotate_pred_apply]
  rw [@Fin.coe_sub_one]
  simp only [ite_eq_else]
  have : ¬ i= 0 := by
    exact in0
  intro h1
  contradiction

lemma next_last (n : ℕ) : next (Fin.last n)  = 0 := by
  unfold next
  rw [finRotate_last]

lemma prev_zero : prev (0 : Fin (n'+1) ) = Fin.last n' := by
  let h := prev_next (Fin.last (n'))
  let h' := next_last n'
  rw [h'] at h
  rw [h]

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

lemma prev_sub_iter'  (k:ℕ) : ∀ (i: Fin (n'+1)),  ((i:ℕ) < k) → (k ≤ n') →  (prev^[k] i : ℕ) = (i:ℕ) + (n'+1) - k := by
  intro i inik klen
  have h: (k:ℕ) = (k - (i:ℕ) - (1:ℕ)) + (1:ℕ) + (i:ℕ) := by
    rw [Nat.add_comm]
    rw [Nat.add_left_comm]
    rw [Nat.sub_sub]
    omega
  rw [h]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply]
  have h1: ((prev^[i] i):ℕ) = ((0:Fin (n'+1)):ℕ) := by
    let h2 := prev_sub_iter i i
    have h3: i ≤ i := by omega
    let h4 := h2 h3
    have h5: (i:ℕ) - (i:ℕ) = (0:ℕ) := by
      rw [Nat.sub_self]
    rw [h5] at h4
    exact h4
  have h2: (prev^[i] i) = 0 := by
    let h3 := (Fin.ext_iff.mpr) h1
    exact h3
  rw [h2]
  have h3: (prev^[1] 0) = Fin.last n' := by
    exact prev_zero
  rw [h3]
  have h4: (prev^[k - (i:ℕ) - (1:ℕ)] (Fin.last n') : ℕ) = (n') - (k - (i:ℕ) - (1:ℕ)) := by
    let h5 := prev_sub_iter (k - (i:ℕ) - (1:ℕ)) (Fin.last n')
    have h6: (k - (i:ℕ) - (1:ℕ)) ≤ n' := by
      have : k ≤ n' := by omega
      have h8: k - (i:ℕ) - (1:ℕ) ≤ k := by omega
      omega
    have : (Fin.last n':ℕ) = n' := by
      rfl
    rw [this] at h5
    exact h5 h6
  rw [h4]
  omega

/- divisibility lemmas -/
lemma div_trans (a b c : ℕ): (a % b = 0) → (b % c = 0) → (a % c = 0) := by
  intro h1 h2
  have h: (b∣a) := by
    let h3 := Nat.dvd_iff_mod_eq_zero b a
    exact h3.mpr h1
  have h': (c∣b) := by
    let h4 := Nat.dvd_iff_mod_eq_zero c b
    exact h4.mpr h2
  have : (c∣a) := by
    exact Nat.dvd_trans h' h
  let h5 := Nat.dvd_iff_mod_eq_zero c a
  exact h5.mp this

lemma eq_rem_eq_fin (a b n : ℕ) (h : a % n.succ = b % n.succ) :
  (a:Fin n.succ) = (b:Fin n.succ) := by
  simp [Fin.ext_iff]
  rw [h]

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
  let n := 4 * l + 6
  cases Nat.lt_or_ge (↑i) 2 with
  | inl hlt =>
    have h0: (i:ℕ)/2 * 2 = 0 := by
      have h1: (i:ℕ) < 2 := by omega
      have h2: (i:ℕ)/2 = 0 := by
        apply Nat.div_eq_of_lt h1
      rw [h2]
    simp [h0]
    have h1: (prev^[2] i : ℕ) = (i:ℕ) + 4 * l + 4 := by
      have h2: 2 ≤ 4 * l + 5 := by omega
      exact prev_sub_iter' 2 i hlt h2
    have h2: (prev^[2] i : ℕ) / 2 * 2 = 4 * l + 4 := by
      rw [h1]
      have : (i:ℕ)/2 = 0 := by
        have h4: (i:ℕ) < 2 := by omega
        exact Nat.div_eq_of_lt h4
      omega
    have h3: ((prev (prev i)):ℕ) / 2 * 2 = 4 * l + 4 := by
      rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply] at h2
      exact h2
    have h4 : ((prev (prev i)):ℕ) / 2 * 2 = n -2 := by
      rw [h3]
      omega
    simp [h4]
    have h5 : (((prev (prev i)):ℕ): Fin 2) = (i : Fin 2) := by
      have h6 : ((prev (prev i)):ℕ) = (i:ℕ) + 4 * l + 4 := by
        exact h1
      have h7 : ((prev (prev i)):ℕ) % 2 = (i:ℕ) % 2 := by
        rw [h6]
        rw [Nat.add_mod]
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [Nat.reduceMod, add_zero]
        rw [Nat.add_mod]
        rw [Nat.mod_eq_of_lt (by omega)]
        simp only [add_right_eq_self]
        have h8 : 4 * l % 4 = 0 := by
          exact Nat.mul_mod_right 4 l
        have h9 : 4 * l  % 2 = 0 := by
          have h10: 4 % 2 = 0 := by norm_num
          exact div_trans (4 * l) 4 2 h8 h10
        exact h9
      exact eq_rem_eq_fin ((prev (prev i)):ℕ) (i:ℕ) 1 h7
    rw [h5]
    let h6 := shift_prev_iter (4*l+4) (Y_top l (i:Fin 2)) (prev (prev j) )
    have h7: 4*l+4 = n-2 := by omega
    rw [h7] at h6
    rw [h6]
    have h8: prev (prev j) = prev^[2] j := by rfl
    rw [h8]
    have h8: prev^[n-2] (prev^[2]  j) = prev^[n] j := by
      rw [←Function.iterate_add_apply]
      rw [Nat.sub_add_cancel (by omega : 2 ≤ n)]
    rw [h8]
    have h9: prev^[n] j = j := by
      exact prev_idemp j
    rw [h9]
  | inr hge =>
    let k:= (prev^[2] i : ℕ)
    have h1: (i:ℕ) = (prev^[2] i : ℕ) + 2 := by
      rw [prev_sub_iter 2 i hge]
      omega
    have : (i:ℕ) = k + 2 := by
      omega
    have : k < 4 * l + 4 := by
      have : (i:ℕ) < 4 * l + 6 := by
        exact Nat.lt_of_lt_of_le (Fin.isLt i) (by omega)
      omega
    have h4: ((i / 2) :ℕ) = (k/2)+1 := by
      omega
    have : ((i) / 2 * 2 :ℕ) = (k/2)*2 + 2 := by
      rw [h4]
      rw [Nat.right_distrib]
    rw [h1]
    have h6:(k+2)/2 * 2 = (k/2)*2 + 2 := by
      rw [Nat.add_div_right]
      rw [Nat.right_distrib]
      simp only [Nat.ofNat_pos]
    have h7: (↑(prev^[2] i) +2 ) / 2 * 2 = (↑(prev^[2] i) :ℕ) / 2 * 2 + 2 := by
      exact h6
    rw [h7]
    have h8 : ((k + 2) : Fin 2) = (k : Fin 2) := by
      omega
    have : ((((prev^[2] i):ℕ) + (2:ℕ)) : Fin 2) = (((prev^[2] i) : ℕ ): Fin 2) := by
      exact h8
    have h8'' : ((((prev^[2] i):ℕ) + (2:ℕ):ℕ) : Fin 2) = (((prev^[2] i) : ℕ ): Fin 2) := by
      simp only [Function.iterate_succ, Function.iterate_one, Function.comp_apply, Nat.cast_add,
        Nat.cast_ofNat, Fin.isValue, add_right_eq_self, Fin.reduceEq]
    rw [←h8'']
    let hh := shift_iter_double_property (↑(prev^[2] i) / 2 * 2) 2 (Y_top l ((((prev^[2] i):ℕ) + (2:ℕ):ℕ) : Fin 2) ) (j)
    exact hh


end Y



/-
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
-/
