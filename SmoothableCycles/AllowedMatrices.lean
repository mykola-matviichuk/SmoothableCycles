import Mathlib

open Matrix

section shift

variable {α : Type*} {n : ℕ}

def shift (v : Fin n → α) : Fin n → α := v ∘ (finRotate n).symm

lemma shift_apply (v : Fin n → α) (i : Fin n) : shift v i = v ((finRotate n).symm i) := rfl

lemma iterate_shift_apply (v : Fin n → α) {m : ℕ} (i : Fin n) :
    shift^[m] v i = v ((finRotate n).symm ^[m] i) := by
  induction m generalizing i
  case zero => simp
  case succ m ih =>
    rw [Function.iterate_succ_apply', shift_apply, ih, Function.iterate_succ_apply]

lemma sum_shift [AddCommMonoid α] {v : Fin n → α} : ∑ i, shift v i = ∑ i, v i := by
  simp only [shift_apply, (finRotate _).symm.sum_comp]

lemma sum_iterate_shift [AddCommMonoid α] {m : ℕ} {v : Fin n → α} :
    ∑ i, shift^[m] v i = ∑ i, v i := by
  induction m with
  | zero => simp
  | succ m ih => simpa only [Function.iterate_succ_apply', sum_shift]

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

def Y_top (l : ℕ) : Matrix (Fin 2) (Fin (4 * l + 6)) R :=
  ![vecCons 0 <| vecCons 2 <|
      vecAppend (m := 2 * l + 1) (n := 2 * l + 3) (by omega) (fun _ => 1) (fun _ => -1),
    vecCons (-2) <| vecCons 0 <|
      vecAppend (m := 2 * l + 3) (n := 2 * l + 1) (by omega) (fun _ => 1) (fun _ => -1) ]

def Y (l : ℕ) : Matrix (Fin (4 * l + 6)) (Fin (4 * l + 6)) R :=
  Matrix.of fun i => shift^[(i / 2) * 2] (Y_top R l i)

lemma univ_eq_union {m n : ℕ} :
    (Finset.univ : Finset (Fin (m + n))) =
      Finset.disjUnion
        (Finset.map (Fin.castAddEmb _) Finset.univ)
        (Finset.map (Fin.natAddEmb _) Finset.univ)
      (by simp [Finset.disjoint_left, Fin.ext_iff]; omega) := by
  ext i
  simp only [Finset.mem_univ, Finset.disjUnion_eq_union, Finset.mem_union, Finset.mem_map,
    Fin.castAddEmb_apply, true_and, Fin.natAddEmb_apply, true_iff]
  induction i using Fin.addCases <;>
  simp [Fin.castAdd]

@[simp] lemma Fin.castAddEmb_apply' {m n : ℕ} {i : Fin n} : Fin.castAddEmb m i = Fin.castAdd m i :=
  rfl

lemma sum_vecAppend {α : Type*} [AddCommMonoid α] {m n o : ℕ} (v : Fin m → α) (w : Fin n → α)
    (ho : o = m + n) :
    ∑ i : Fin o, vecAppend ho v w i = (∑ i : Fin m, v i) + (∑ i : Fin n, w i) := by
  cases ho
  rw [univ_eq_union]
  rw [Finset.sum_disjUnion]
  simp only [vecAppend]
  simp [Fin.cast_refl, Function.comp_apply, id_eq, Finset.sum_map, Fin.natAddEmb_apply,
    Fin.append_right, Fin.castAddEmb_apply', -Fin.castAddEmb_apply]

lemma row_sum_Y_top (l : ℕ) : ∀ i : Fin 2, ∑ j, Y_top R l i j = 0 := by
  rw [Fin.forall_fin_two]
  simp only [Y_top, Fin.isValue, cons_val', empty_val', cons_val_fin_one, cons_val_zero,
    cons_val_one, head_fin_const]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [cons_val_succ, sum_vecAppend, Finset.sum_const]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [sum_vecAppend]
  ring_nf
  simp

lemma row_sum_Y (l : ℕ) (i : Fin (4 * l + 6)) : ∑ j, Y R l i j = 0 := by
  simp only [Y, of_apply, sum_iterate_shift]
  simp [row_sum_Y_top]

lemma Y_apply {l : ℕ} {i j} : Y R l i j = sorry := by
  sorry
  -- simp only [Y, of_apply]

lemma skew_symm_Y (l : ℕ) (i j) : Y R l i j = -Y R l j i := by
  sorry
  -- fin_cases i; fin_cases j; simp [Y, Y_top, shift_apply, vecCons, vecAppend, Matrix.of, Matrix.map, Matrix.read, Matrix.vec]

end Y

section Y'

def Y'_vec (l : ℕ) (i : ℕ) : Matrix (Fin 2) (Fin 2) R :=
  if i = 0 then !![0, 2;
                  -2, 0]
  else if i < l + 1 then Matrix.of (-1)
  else if i = l + 1 then !![-1, -1;
                             1, -1]
  else if i = l + 2 then !![ 1, -1;
                             1,  1]
  else Matrix.of 1

variable {l : ℕ}

lemma Y'_vec_zero : Y'_vec R l 0 = !![0, 2; -2, 0] := rfl

lemma Y'_vec_small {i : Fin (2 * l + 3)} (hi : (i : ℕ) ≠ 0) (hi' : (i : ℕ) < l + 1) :
    Y'_vec R l i = Matrix.of (-1) := by
  rwa [Y'_vec, if_neg, if_pos hi']

lemma Y'_vec_left {i : Fin (2 * l + 3)} (hi : (i : ℕ) = l + 1) :
    Y'_vec R l i = !![-1, -1; 1, -1] := by
  rw [Y'_vec, if_neg (by omega), if_neg hi.not_lt, if_pos hi]

lemma Y'_vec_right {i : Fin (2 * l + 3)} (hi : (i : ℕ) = l + 2) :
    Y'_vec R l i = !![1, -1; 1, 1] := by
  rw [Y'_vec, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hi]

lemma Y'_vec_large {i : Fin (2 * l + 3)} (hi : l + 2 < (i : ℕ)) :
    Y'_vec R l i = Matrix.of 1 := by
  rw [Y'_vec, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

example {n : ℕ} (i : Fin (n + 1)) : i = 0 ↔ (i : ℕ) = 0 := by
  rw [Fin.ext_iff]
  simp only [Fin.val_zero]

lemma coe_neg' {n : ℕ} {i : Fin (n + 1)} (hi : (i : ℕ) ≠ 0) :
    ((-i : Fin (n + 1)) : ℕ) = n + 1 - (i : ℕ) := by
  rw [Fin.coe_neg, Nat.mod_eq_of_lt]
  omega

lemma Y'_vec_spin {l : ℕ} {i : Fin (2 * l + 3)} :
    (Y'_vec R l (-i : Fin (2 * l + 3)))ᵀ = - Y'_vec R l i := by
  by_cases (i : ℕ) = 0
  case pos h₁ =>
    have : i = 0 := Fin.ext_iff.2 h₁
    rw [this, neg_zero, Fin.val_zero, Y'_vec_zero, ← ext_iff]
    simp [Fin.forall_fin_two]
  case neg h₁ =>
  have : ((-i : Fin (2 * l + 3)) : ℕ) = 2 * l + 3 - (i : ℕ) := coe_neg' h₁
  rcases lt_or_le (i : ℕ) (l + 1)
  case inl h₂ =>
    rw [Y'_vec_large, Y'_vec_small _ h₁ h₂]
    · ext i j
      rw [transpose_apply, of_apply, neg_apply]
      simp
    omega
  case inr h₁ =>
  rcases eq_or_lt_of_le h₁ with h₁ | h₁
  case inl =>
    rw [Y'_vec_right, Y'_vec_left _ h₁.symm]
    · rw [← Matrix.ext_iff]
      simp [Fin.forall_fin_two]
    omega
  case inr h₁ =>
  rcases eq_or_lt_of_le h₁ with h₁ | h₁
  case inl =>
    rw [Y'_vec_left, Y'_vec_right _ h₁.symm]
    · rw [← Matrix.ext_iff]
      simp [Fin.forall_fin_two]
    omega
  case inr =>
    rw [Y'_vec_small, Y'_vec_large _ h₁]
    · rw [← Matrix.ext_iff]
      simp only [transpose_apply, of_apply, neg_apply]
      simp
    · omega
    · omega

def fin_mul_test {l : ℕ} : Fin (2 * l + 3) × Fin 2 ≃ Fin (4 * l + 6) :=
  finProdFinEquiv.trans (Fin.castOrderIso (by omega)).toEquiv

def Y''' (l : ℕ) :=
    circulant fun i : Fin (2 * l + 3) ↦ Y'_vec R l i

def Y'' (l : ℕ) : Matrix (Fin (2 * l + 3) × Fin 2) (Fin (2 * l + 3) × Fin 2) R :=
  Matrix.comp _ _ _ _ _
    <| circulant fun i : Fin (2 * l + 3) ↦ Y'_vec R l i

def Y' (l : ℕ) : Matrix (Fin (4 * l + 6)) (Fin (4 * l + 6)) R :=
  Matrix.reindex fin_mul_test fin_mul_test (Y'' R l)

lemma comp_transpose {I J K L R : Type*} (M : Matrix I J (Matrix K L R)) :
    (Matrix.comp _ _ _ _ _ M)ᵀ = Matrix.comp _ _ _ _ _ (Mᵀ.map (·ᵀ)) := by
  ext ⟨j, l⟩ ⟨i, k⟩
  simp

lemma circulant_neg' {α n : Type*} [Neg α] [Sub n] (v : n → α) :
    circulant (fun i ↦ - v i) = - circulant v :=
  circulant_neg _

lemma comp_neg {I J K L R : Type*} [Neg R] (M : Matrix I J (Matrix K L R)) :
    Matrix.comp _ _ _ _ _ (-M) = - Matrix.comp _ _ _ _ _ M :=
  rfl

lemma reindex_neg {I J K L R : Type*} [Neg R] (f : I ≃ J) (g : K ≃ L) (M : Matrix I K R) :
    Matrix.reindex f g (-M) = - Matrix.reindex f g M :=
  rfl

lemma Y'_transpose (l : ℕ) : (Y' R l)ᵀ = -Y' R l := by
  rw [Y', transpose_reindex, Y'', comp_transpose, transpose_circulant, map_circulant]
  simp only [Y'_vec_spin]
  rw [circulant_neg']
  rw [comp_neg]
  rw [reindex_neg]

lemma finRotate_succ_iterate_apply {n : ℕ} {i : Fin (n + 1)} {m : ℕ} :
    (finRotate _)^[m] i = i + m := by
  induction m
  case zero => simp
  case succ m ih =>
    rw [Function.iterate_succ_apply', ih, finRotate_succ_apply, Nat.cast_add_one, add_assoc]

lemma finRotate_succ_symm_iterate_apply {n : ℕ} {i : Fin (n + 1)} {m : ℕ} :
    (finRotate _).symm^[m] i = i - m := by
  rw [Equiv.Perm.iterate_eq_pow, ← Equiv.Perm.inv_def, inv_pow, Equiv.Perm.inv_def,
    Equiv.symm_apply_eq, ← Equiv.Perm.iterate_eq_pow, finRotate_succ_iterate_apply]
  simp

lemma Y''_explicit (l : ℕ) (i j : Fin (2 * l + 3) × Fin 2) :
    Y'' R l i j = Y'_vec R l ((i.1 - j.1 : Fin (2 * l + 3))) i.2 j.2 := by
  rw [Y'', comp_apply, circulant_apply]

lemma Y'_explicit (l : ℕ) (i j) :
    Y' R l i j =
      Y'_vec R l (⟨i / 2, by omega⟩ - ⟨j / 2, by omega⟩ : Fin (2 * l + 3))
        ⟨i % 2, by omega⟩ ⟨j % 2, by omega⟩ := by
  rw [Y', reindex_apply, submatrix_apply, Y''_explicit]
  simp [fin_mul_test]
  simp [fin_mul_test, Fin.modNat, Fin.divNat, Fin.coe_cast]

lemma Y'_explicit_rotate (l : ℕ) (i j) :
    Y' R l i j =
      Y'_vec R l ((finRotate (2 * l + 3))^[i / 2] (- ⟨j / 2, by omega⟩))
        ⟨i % 2, by omega⟩ ⟨j % 2, by omega⟩ := by
  rw [Y'_explicit, finRotate_succ_iterate_apply, neg_add_eq_sub]
  congr 2
  rw [sub_left_inj, Fin.ext_iff, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]

lemma Y'_explicit_above (l : ℕ) (i j) (hi : j / 2 ≤ i / 2) :
    Y' R l i j = Y'_vec R l (i / 2 - j / 2) ⟨i % 2, by omega⟩ ⟨j % 2, by omega⟩ := by
  rw [Y'_explicit, Fin.sub_val_of_le]
  exact hi

lemma Y'_explicit_below (l : ℕ) (i j) (hi : i / 2 < j / 2) :
    Y' R l i j = Y'_vec R l (2 * l + 3 + i / 2 - j / 2) ⟨i % 2, by omega⟩ ⟨j % 2, by omega⟩ := by
  rw [Y'_explicit, Fin.coe_sub_iff_lt.2]
  exact hi

open Real

lemma Y'_shift (l : ℕ) {i} :
    Y' R l i = shift^[i / 2 * 2] (Y' R l (i % 2)) := by
  ext1 j
  rw [Y'_explicit_rotate, iterate_shift_apply, finRotate_succ_symm_iterate_apply,
    Y'_explicit_rotate, finRotate_succ_iterate_apply, finRotate_succ_iterate_apply]
  have h₁ : (i : ℕ) / 2 * 2 < 4 * l + 5 + 1 := by sorry -- omega
  have h₂ : (i : ℕ) / 2 < 2 * l + 2 + 1 := by sorry -- omega
  simp only [Fin.natCast_def]
  simp only [Fin.mod_val, Fin.val_two, Nat.mod_div_self, Nat.zero_mod, Fin.zero_eta, add_zero,
    dvd_refl, Nat.mod_mod_of_dvd, Nat.mod_eq_of_lt, h₁, h₂]
  congr 2
  next =>
    rw [neg_add_eq_sub, eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, sub_eq_zero]
    ext1
    rw [Fin.val_add]
    simp only [Fin.val_mk]
    rcases le_or_lt ⟨(i : ℕ) / 2 * 2, by omega⟩ j
    case inl h₃ =>
      rw [Fin.sub_val_of_le h₃]
      rw [Fin.le_def, Fin.val_mk] at h₃
      rw [Fin.val_mk h₁, mul_comm (i / 2 : ℕ) 2, Nat.sub_mul_div _ _ _ (by omega),
        add_tsub_cancel_of_le]
      sorry
      sorry


    case inr =>
      sorry
    -- rw [Fin.coe_sub]
    -- simp only [Fin.val_mk]


  next => sorry






#exit

end Y'

#exit

section Z

def Z_top (l : ℕ) : Matrix (Fin 5) (Fin (10 * l + 15)) R :=
  ![vecAppend (n := 10 * l + 10) (by omega) ![ 0,  1,  1,  1,  1] <|
      vecAppend (m := 5 * l + 3) (n := 5 * l + 7) (by omega) (fun _ => 1) (fun _ => -1),
    vecAppend (n := 10 * l + 10) (by omega) ![-1,  0,  2,  2,  1] <|
      vecAppend (m := 5 * l + 3) (n := 5 * l + 7) (by omega) (fun _ => 1) (fun _ => -1),
    vecAppend (n := 10 * l + 10) (by omega) ![-1, -2,  0,  2,  1] <|
      vecAppend (m := 5 * l + 5) (n := 5 * l + 5) (by omega) (fun _ => 1) (fun _ => -1),
    vecAppend (n := 10 * l + 10) (by omega) ![-1, -2, -2,  0,  1] <|
      vecAppend (m := 5 * l + 7) (n := 5 * l + 3) (by omega) (fun _ => 1) (fun _ => -1),
    vecAppend (n := 10 * l + 10) (by omega) ![-1, -1, -1, -1,  0] <|
      vecAppend (m := 5 * l + 7) (n := 5 * l + 3) (by omega) (fun _ => 1) (fun _ => -1) ]


def Z (l : ℕ) : Matrix (Fin (10 * l + 15)) (Fin (10 * l + 15)) R :=
  Matrix.of fun i => shift^[(i / 5) * 5] (Z_top R l (Fin.ofNat'' i))

end Z
