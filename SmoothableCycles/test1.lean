import Mathlib

variable {α : Type*} {n n': ℕ}

def shift (v : Fin n → α) : Fin n → α := v ∘ (finRotate n).symm

def prev (i : Fin n) : Fin n := (finRotate n).symm i

def next (i : Fin n) : Fin n := finRotate n i

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
