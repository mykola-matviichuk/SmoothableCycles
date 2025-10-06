import Mathlib

open Matrix

variable {α : Type*} {m n : ℕ}

def shift (v : Fin n → α) : Fin n → α :=
  v ∘ (finRotate n).symm

def shift_left (v : Fin n → α) : Fin n → α :=
  v ∘ (finRotate n)

def shiftRow (M : Matrix (Fin m) (Fin n) α) : Matrix (Fin m) (Fin n) α :=
  fun i j => (shift (M i)) j

def shiftRow_left (M : Matrix (Fin m) (Fin n) α) : Matrix (Fin m) (Fin n) α :=
  fun i j => (shift_left (M i)) j

def shiftCol  (M : Matrix (Fin m) (Fin n) α) : Matrix (Fin m) (Fin n) α :=
  fun i j => (shift (fun k => M k j)) i

def shiftCol_left  (M : Matrix (Fin m) (Fin n) α) : Matrix (Fin m) (Fin n) α :=
  fun i j => (shift_left (fun k => M k j)) i



#eval shiftRow ![![1,2,3],![4,5,6],![7,8,9]]
#eval shiftCol ![![1,2,3],![4,5,6],![7,8,9]]
#eval shiftRow  (shiftCol  !![ 0,  2, -1, -1; -2,  0,  3, -1; 1, -3,  0,  2;   1,  1, -2,  0])
#eval shiftRow_left  (shiftCol_left  !![ 0,  2, -1, -1; -2,  0,  3, -1; 1, -3,  0,  2;   1,  1, -2,  0])



#eval shift_left ![1,2,3,4]

example : shift ![1,2,3] = ![3,1,2] := by
  decide

#eval Function.comp List.reverse (List.drop 2) [3, 2, 4, 1]
#eval shift ![1,2,3]
#eval shift^[2] ![1,2,3,4]

section Y
variable (R : Type*) [CommRing R]

def Y_top (l : ℕ) : Matrix (Fin 2) (Fin (4 * l + 6)) R :=
  ![vecCons 0 <| vecCons 2 <|
      vecAppend (m := 2 * l + 1) (n := 2 * l + 3) (by omega) (fun _ => 1) (fun _ => -1),
    vecCons (-2) <| vecCons 0 <|
      vecAppend (m := 2 * l + 3) (n := 2 * l + 1) (by omega) (fun _ => 1) (fun _ => -1) ]

def Y (l : ℕ) : Matrix (Fin (4 * l + 6)) (Fin (4 * l + 6)) R :=
  Matrix.of fun i => shift^[(i / 2) * 2] (Y_top R l i)

#eval Y ℚ 0
#eval Y ℚ 1
#eval Odd (3 : ℤ)

#eval abs (3 : ℚ)

def IsSkewSymmetric {k : ℕ} (A : Matrix (Fin k) (Fin k) R) : Prop :=
  ∀ i j , A i j = -A j i

lemma Y_equiv_def {i j l : ℕ } :  Y ℚ l i j == (if abs (i-j : ℤ) < 2 then 1 else 0) := by sorry

lemma Y_skew_symmetric : ∀ l i j, Y ℚ l i j == Y ℚ l j i := by
  intro l i j
  set Y' := Y ℚ l
  show Y' i j == Y' j i
  set indicator : ℚ := if abs (i - j) < 3 then 1 else 0

  sorry


--lemma Y_skew_symmetric : IsSkewSymmetric Y1 := by sorry

end Y
