import Mathlib

variable {α : Type*} {n n': ℕ}

def shift (v : Fin n → α) : Fin n → α := v ∘ (finRotate n).symm

def prev (i : Fin n) : Fin n := (finRotate n).symm i

def next (i : Fin n) : Fin n := finRotate n i
