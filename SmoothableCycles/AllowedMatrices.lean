import Mathlib

section shift

variable {α : Type*} {n : ℕ}

def shift (v : Fin n → α) : Fin n → α := v ∘ (finRotate n).symm

lemma shift_apply (v : Fin n → α) (i : Fin n) : shift v i = v ((finRotate n).symm i) := rfl

end shift

variable (R : Type*) [CommRing R]

section X4

def X4 : Fin 4 → Fin 4 → R :=
  !![ 0,  2, -1, -1;
     -2,  0,  3, -1;
      1, -3,  0,  2;
      1,  1, -2,  0]

def test : Fin 4 → R := ![1, 1, -2, 0]

lemma row_sum_X4 (i : Fin 4) : ∑ j, X4 R i j = 0 := by
  fin_cases i <;> norm_num [Fin.sum_univ_four, X4]

end X4
