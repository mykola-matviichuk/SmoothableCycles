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

-- to be removed
lemma lt_iff_gt_fin : ∀ {a b : Fin n}, a < b → b > a := by
  intros a b
  simp only [gt_iff_lt]
  simp only [imp_self]

-- to be removed
lemma lt_iff_gt_nat {a b : ℕ} : a < b → b > a := by
  simp only [gt_iff_lt]
  simp only [imp_self]

lemma lt_iff_gt {a b : α} [LT α] : a < b ↔ b > a := by
  simp only [gt_iff_lt]


lemma le_fin_nat : ∀ {a b : Fin n}, (a ≤ b) ↔ (a.val ≤ b.val) := by
  intros a b
  simp only [Fin.le_iff_val_le_val]

lemma ge_fin_nat : ∀ {a b : Fin n}, (a ≥ b) ↔ (a.val ≥ b.val) := by
  intros a b
  simp only [ge_iff_le]
  simp only [le_fin_nat]

lemma lt_fin_nat : ∀ {a b : Fin n}, (a < b) ↔ (a.val < b.val) := by
  intros a b
  simp only [Fin.lt_iff_val_lt_val]

lemma lt_nat_fin (n:ℕ) (a b : ℕ): (a < b) → (b < n+1) → (a:Fin n.succ) < (b:Fin n.succ) := by
  intro h1 h2
  have h3: a < n + 1 := by
    exact Nat.lt_trans h1 h2
  simp only [Fin.lt_iff_val_lt_val]
  rw [Fin.val_cast_of_lt h2]
  rw [Fin.val_cast_of_lt h3]
  exact h1

lemma lt_nat_fin' (l:ℕ) (a b : ℕ): (a < b) → (b < 4*l+6) → (a:Fin (4*l+6)) < (b:Fin (4*l+6)) := by
  intro h1 h2
  have h3: a < 4*l+6  := by
    exact Nat.lt_trans h1 h2
  simp only [Fin.lt_iff_val_lt_val]
  rw [Fin.val_cast_of_lt h2]
  rw [Fin.val_cast_of_lt h3]
  exact h1

lemma le_nat_fin (n:ℕ) (a b : ℕ): (a ≤ b) → (b < n+1) → (a:Fin n.succ) ≤ (b:Fin n.succ) := by
  intro h1 h2
  have h3: a < n+1 := by
    exact Nat.lt_of_le_of_lt h1 h2
  simp only [Fin.le_iff_val_le_val]
  rw [Fin.val_cast_of_lt h2]
  rw [Fin.val_cast_of_lt h3]
  exact h1

lemma le_nat_fin' (l:ℕ) (a b : ℕ): (a ≤ b) → (b < 4*l+6) → (a:Fin (4*l+6)) ≤ (b:Fin (4*l+6)) := by
  intro h1 h2
  have h3: a < 4*l+6  := by
    exact Nat.lt_of_le_of_lt h1 h2
  simp only [Fin.le_iff_val_le_val]
  rw [Fin.val_cast_of_lt h2]
  rw [Fin.val_cast_of_lt h3]
  exact h1

lemma gt_fin_nat : ∀ {a b : Fin n}, (a > b) ↔ (a.val > b.val) := by
  intros a b
  simp only [gt_iff_lt]
  simp only [Fin.val_fin_lt]



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

lemma fin_trans_lt {a b c : Fin n} : (a < b) → (b < c) → (a < c) := by
  intros h_ab h_bc
  rw [Fin.lt_iff_val_lt_val] at *
  simp only [Fin.val_fin_lt]
  exact Nat.lt_trans h_ab h_bc

lemma fin_lt_le_imp_lt {a b c : Fin n} : (a < b) → (b ≤ c) → (a < c) := by
  intros h_ab h_bc
  rw [Fin.lt_iff_val_lt_val] at *
  simp only [Fin.val_fin_lt, Fin.le_iff_val_le_val] at *
  exact Nat.lt_of_lt_of_le h_ab h_bc

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

lemma gt_iff_ge_plus_one (a b : Fin n.succ) : ¬ (b=Fin.last n) → (a > b ↔ a ≥ b + 1) := by
  intro h
  have h1: (b + 1).val = b.val + 1 := by
    exact fin_val_plus_one b h
  constructor
  · intro h_gt
    rw [ge_fin_nat]
    rw [h1]
    have h5: a.val > b.val := by
      exact h_gt
    have h6: b.val  < a.val := by
      exact h5
    have h7: b.val + 1 ≤ a.val := by
      exact Nat.add_one_le_of_lt h6
    exact h7
  intro h_ge
  rw [gt_fin_nat]
  have h2: a.val ≥ (b + 1).val := by
    exact ge_fin_nat.mp h_ge
  rw [h1] at h2
  have h3 : b.val + 1 ≤ a.val := by
    exact h2
  exact Nat.lt_of_succ_le h3

lemma lt_iff_plus_one_le (k:ℕ ) (a b : Fin k.succ) : ¬ (a=Fin.last k) → (a < b ↔ a + 1 ≤ b) := by
  intro h
  have h1: (a + 1).val = a.val + 1 := by
    exact fin_val_plus_one a h
  constructor
  · intro h_lt
    rw [le_fin_nat]
    rw [h1]
    have h5: a.val < b.val := by
      exact h_lt
    have h6: a.val + 1 ≤ b.val := by
      exact Nat.succ_le_of_lt h5
    exact h6
  intro h_le
  rw [lt_fin_nat]
  have h2: (a + 1).val ≤ b.val := by
    exact le_fin_nat.mp h_le
  rw [h1] at h2
  have h3 : a.val + 1 ≤ b.val := by
    exact h2
  exact Nat.lt_of_succ_le h3


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
            exact lt_iff_gt_fin h4
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

lemma intervals_disjoint' {n k : ℕ}: ∀ f g : Fin k.succ → Fin n.succ, system_of_intervals f g → ∀ i : Fin n.succ, ∀ j1 j2 : Fin k.succ, (j1 < j2) → (f j1 ≤ i ∧ i ≤ g j1) → (f j2 ≤ i ∧ i ≤ g j2) → False := by
  intros f g h_system i j1 j2 h_lt h_j1 h_j2
  unfold system_of_intervals at h_system
  have h2 : j2≤  Fin.last k := by
      exact fin_le_last j2
  have h3: j1 < Fin.last k := by
    exact fin_lt_le_imp_lt h_lt h2
  have h4: ¬ (j1 = Fin.last k) := by
    rw [Fin.lt_iff_le_and_ne] at h3
    exact h3.2
  have h2' : g j2 ≤ Fin.last n := by
    exact fin_le_last (g j2)
  have h3': g j1 < Fin.last n := by
    have h5 : g j1 < g j2 := by
      let h8:= h_system.2.2.2.1
      exact h8 h_lt
    exact fin_lt_le_imp_lt h5 h2'
  have h4': ¬ (g j1 = Fin.last n) := by
    exact le_ne (g j1) (Fin.last n) h3'
  have h1: j1 + 1 ≤ j2 := by
    let h2 := lt_iff_plus_one_le k j1 j2
    let h5:= h2 h4
    exact h5.mp h_lt
  have h5 : g j1 < f j2 := by
    have h6 : g j1 + 1 = f (j1 + 1) := by
      exact h_system.2.2.2.2.2 j1 h4
    have h7 : f (j1 + 1) ≤ f j2 := by
      let h8:= h_system.2.2.1
      let h9:= StrictMono.monotone h8
      exact h9 h1
    rw [←h6] at h7
    let h8:= lt_iff_plus_one_le n (g j1) (f j2) h4'
    exact h8.mpr h7
  have not_h5 : f j2 ≤ g j1 := by
    let h6 := h_j2.1
    let h7 := h_j1.2
    exact le_trans h6 h7
  exact lt_irrefl (g j1) (lt_fin_nat.mpr (Nat.lt_of_lt_of_le h5 not_h5))



lemma intervals_disjoint {n k :ℕ}: ∀ f g : Fin k.succ → Fin n.succ, system_of_intervals f g → ∀ i : Fin n.succ, ∀ j1 j2 : Fin k.succ, (f j1 ≤ i ∧ i ≤ g j1) → (f j2 ≤ i ∧ i ≤ g j2) → j1 = j2 := by
  intros f g h_system i j1 j2 h_j1 h_j2
  unfold system_of_intervals at h_system
  by_contra h_neq
  have h1: j1 < j2 ∨ j2 < j1 := by
    let h2 := le_or_gt_fin_nat j1 j2
    cases h2 with
    | inl h_le =>
      left;
      rw [le_iff_eq_or_lt] at h_le
      simp [h_neq] at h_le
      exact h_le
    | inr h_gt => right; exact h_gt
  cases h1 with
  | inl h_lt =>
    exact intervals_disjoint' f g h_system i j1 j2 h_lt h_j1 h_j2
  | inr h_gt =>
    exact intervals_disjoint' f g h_system i j2 j1 h_gt h_j2 h_j1


#eval (2:Fin 5) ≥ (-2:Fin 5)



def Y'caseA (l:ℕ) (i : Fin (4*l + 6)) := i.val % 2 = 0
def Y'caseB (l:ℕ) (i : Fin (4*l + 6)) := i.val % 2 = 1

lemma Y'AorB (l:ℕ) (i: Fin (4*l + 6)) : Y'caseA l i ∨ Y'caseB l i := by
  unfold Y'caseA Y'caseB
  exact Nat.mod_two_eq_zero_or_one i.val

lemma Y'notA_impliesB (l:ℕ) (i: Fin (4*l + 6)) : ¬ Y'caseA l i → Y'caseB l i := by
  intro h_notA
  let h:= Y'AorB l i
  simp [h_notA] at h
  exact h

def Y'f (l : ℕ): (Fin 6) → Fin (4*l + 6)  :=
  ![0, 1, 2, 2*l+3, 2*l+4, 4*l+5]

def Y'f_nat (l : ℕ): (Fin 6) → ℕ  :=
  ![0, 1, 2, 2*l+3, 2*l+4, 4*l+5]

lemma Y'f_values (l : ℕ) :
  Y'f l 0 = 0 ∧ Y'f l 1 = 1 ∧ Y'f l 2 = 2 ∧
  Y'f l 3 = 2*l+3 ∧ Y'f l 4 = 2*l+4 ∧ Y'f l 5 = 4*l+5 := by
    simp [Y'f]
    norm_cast

def Y'g (l : ℕ): (Fin 6) →  Fin (4*l + 6) :=
  ![0, 1,  2*l+2, 2*l+3, 4*l+4, 4*l+5]

def Y'g_nat (l : ℕ): (Fin 6) → ℕ  :=
  ![0, 1, 2*l+2, 2*l+3, 4*l+4, 4*l+5]

lemma Y'g_values (l : ℕ) :
  Y'g l 0 = 0 ∧ Y'g l 1 = 1 ∧ Y'g l 2 = 2*l+2 ∧
  Y'g l 3 = 2*l+3 ∧ Y'g l 4 = 4*l+4 ∧ Y'g l 5 = 4*l+5 := by
    simp [Y'g]
    norm_cast

def Y'case1 (l : ℕ) (i j : Fin (4 * l + 6)) : Prop := (j-i) = 1
def Y'case5 (l : ℕ) (i j : Fin (4 * l + 6)) : Prop := (j-i) = -1
def Y'case2 (l : ℕ) (i j : Fin (4 * l + 6)) : Prop := (j-i) ≥ 2 ∧ (j-i) ≤ 2*l+2
def Y'case4 (l : ℕ) (i j : Fin (4 * l + 6)) : Prop := (j-i) ≤ -2 ∧ (j-i) ≥ -(2*l+2)
def Y'case3 (l : ℕ) (i j : Fin (4 * l + 6)) : Prop := (j-i) = 2*l+3
def Y'case0 (l : ℕ) (i j : Fin (4 * l + 6)) : Prop := (j-i) = 0




lemma Y'f_natStrictMono (l : ℕ) : StrictMono (Y'f_nat l) := by
  unfold Y'f_nat StrictMono
  intro i j h_ij
  have h : ![0, 1, 2, 2 * l + 3, 2 * l + 4, 4 * l + 5] 5 = 4*l+5 := by
    norm_cast
  fin_cases i <;> fin_cases j <;> (simp_all)
  omega
  omega

lemma Y'g_natStrictMono (l : ℕ) : StrictMono (Y'g_nat l) := by
  unfold Y'g_nat StrictMono
  intro i j h_ij
  have h : ![0, 1, 2*l+2, 2 * l + 3, 4 * l + 4, 4 * l + 5] 5 = 4*l+5 := by
    norm_cast
  fin_cases i <;> fin_cases j <;> (simp_all)
  omega
  omega
  omega
  omega

lemma Y'f_Y'f_nat (l : ℕ) : ∀ (i: Fin 6), Y'f l i = ((Y'f_nat l i) : Fin (4*l+6)) := by
  intro i
  have h : ![0, 1, 2, 2 * l + 3, 2 * l + 4, 4 * l + 5] 5 = 4*l+5 := by
    norm_cast
  unfold Y'f Y'f_nat
  fin_cases i <;> (simp_all)
  norm_cast

lemma Y'g_Y'g_nat (l : ℕ) : ∀ (i: Fin 6), Y'g l i = ((Y'g_nat l i) : Fin (4*l+6)) := by
  intro i
  have h : ![0, 1, 2*l+2, 2 * l + 3, 4 * l + 4, 4 * l + 5] 5 = 4*l+5 := by
    norm_cast
  unfold Y'g Y'g_nat
  fin_cases i <;> (simp_all)
  norm_cast

lemma StrictMonoFinVsNat (k:ℕ) (f: Fin k → Fin n.succ) (f_nat: Fin k → ℕ): (∀ (i:Fin k), f_nat i < n+1) → (∀ (i:Fin k), f i = ((f_nat i): Fin n.succ )) → StrictMono f_nat → StrictMono f := by
  intro bound rel
  unfold StrictMono
  intro mono_nat
  intro i j i_lt_j
  let ineq_nat := mono_nat i_lt_j
  let h:= lt_nat_fin n (f_nat i) (f_nat j) ineq_nat (bound j)
  rw [rel i, rel j]
  exact h

lemma Y'f_nat_bound (l:ℕ) : ∀ (i:Fin 6), (Y'f_nat l i) < 4*l+6 := by
  intro i
  unfold Y'f_nat
  have h : ![0, 1, 2, 2 * l + 3, 2 * l + 4, 4 * l + 5] 5 = 4*l + 5 := by
    norm_cast
  fin_cases i <;> simp [lt_fin_nat]
  omega
  omega
  simp [h]

lemma Y'g_nat_bound (l:ℕ) : ∀ (i:Fin 6), (Y'g_nat l i) < 4*l+6 := by
  intro i
  unfold Y'g_nat
  have h : ![0, 1, 2*l+2, 2 * l + 3, 4 * l + 4, 4 * l + 5] 5 = 4*l+5 := by
    norm_cast
  fin_cases i <;> simp [lt_fin_nat]
  omega
  omega
  simp [h]


lemma Y'fStrictMono (l : ℕ) : StrictMono (Y'f l) := by
  have bound : ∀ (i:Fin 6), (Y'f_nat l i) < 4*l + 5 +1 := by
    exact Y'f_nat_bound l
  exact StrictMonoFinVsNat 6 (Y'f l) (Y'f_nat l) bound (Y'f_Y'f_nat l) (Y'f_natStrictMono l)

lemma Y'gStrictMono (l : ℕ) : StrictMono (Y'g l) := by
  have bound : ∀ (i:Fin 6), (Y'g_nat l i) < 4*l + 5 +1 := by
    exact Y'g_nat_bound l
  exact StrictMonoFinVsNat 6 (Y'g l) (Y'g_nat l) bound (Y'g_Y'g_nat l) (Y'g_natStrictMono l)


lemma interval_split_Y' (l : ℕ) : system_of_intervals (Y'f l) (Y'g l) := by
  unfold system_of_intervals
  let l' := (l : Fin (4*l + 6))
  constructor
  · simp [Y'f]
  constructor
  · simp only [Nat.succ_eq_add_one]
    have h : ![0, 1, 2 * l' + 2, 2 * l' + 3, 4*l'+4, 4*l'+5] (Fin.last 5) = 4*l'+5 := by
      rfl
    unfold Y'g
    simp [h]
    have h2 : (4*l'+5:Fin (4*l + 6)) = (4*l+5: Fin (4*l + 6)) := by
      rw [@fin_add_comm]
    have h3 : (4*l +5 : Fin (4*l +6)) = Fin.last (4*l +5) := by
      norm_cast
      rw [Fin.natCast_eq_last]
    rw [h2, h3]
  constructor
  · exact Y'fStrictMono l
  constructor
  · exact Y'gStrictMono l
  constructor
  · intro i
    simp [Y'f, Y'g]
    have h : ∀ m : Fin 6, (Y'f l m) ≤ (Y'g l m) := by
      intro m
      unfold Y'f Y'g
      fin_cases m <;> simp
      norm_cast
      have h1: 2 ≤ 2*l+2 := by
        omega
      have h2 : 2*l+2 < 4*l+6 := by
        omega
      exact le_nat_fin' l 2 (2*l+2) h1 h2
      norm_cast
      have h1 : 2*l+4 ≤ 4*l+4 := by
        omega
      have h2 : 4*l+4 < 4*l+6 := by
        omega
      exact le_nat_fin' l (2*l+4) (4*l+4) h1 h2
      exact le_refl (![0, 1, 2, 2 * l' + 3, 2 * l' + 4, 4 * l' + 5] 5)
    exact h i
  intro i h_ne
  simp [Y'f, Y'g]
  fin_cases i <;> simp [h_ne]
  norm_num
  simp [add_assoc]
  norm_num
  simp [add_assoc]
  norm_num
  rw [@fin_add_comm]
  have h1: ![0, 1, 2, 2*l'+3, 2*l'+4, 4*l'+5] 5 = 4*l'+5 := by
    rfl
  simp [h1]
  rw [@fin_add_comm]
  have h2 : (l:Fin (4*l + 6)) = l' := by
    rfl
  rw [h2]
  simp only  [add_assoc]
  have h3: (4:Fin (4*l + 6)) + (1: Fin (4*l + 6)) = (5: Fin (4*l + 6)) := by
    norm_num
  rw [h3]
  have h1: ![0, 1, 2*l'+2, 2*l'+3, 4*l'+4, 4*l'+5] 5 = 4*l'+5 := by
    rfl
  rw [h1]
  simp only [add_assoc]
  norm_num
  have h2 : (l:Fin (4*l + 6)) = l' := by
    rfl
  rw [← h2]
  norm_cast


def Y'cases_ij (l : ℕ) (i j : Fin (4 * l + 6)) : (Fin 6 → Prop) :=
  fun k => j-i ≥ Y'f l k ∧ j-i ≤ Y'g l k

lemma Y'cases1to6_exhaustive (l : ℕ) (i j : Fin (4 * l + 6)) : ∃ k: Fin 6, Y'cases_ij l i j k  := by
  unfold Y'cases_ij
  have h: system_of_intervals (Y'f l) (Y'g l) := by
    exact interval_split_Y' l
  let h1:= interval_split (Y'f l) (Y'g l) h (j-i)
  obtain ⟨k, hk⟩ := h1
  use k


def Y' (l : ℕ) : Matrix (Fin (4 * l + 6)) (Fin (4 * l + 6)) ℚ :=
  Matrix.of fun i j =>
    if (j-i) = 1 then
      if i % 2 = 0 then 2 else 1
    else if (j-i) = -1 then
      if i % 2 = 0 then -1 else -2
    else if ((j-i) ≥  2 ∧ (j-i) ≤ 2*l+2) then 1
    else if (j-i ) ≤ -2 ∧ (j-i) ≥ -(2*l+2) then -1
    else if (j-i) = 2*l+3 then
      if i % 2 = 0 then -1 else 1
    else if (j-i) = 0 then 0
    else 0

lemma Y'case0_iff (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 0 ↔ j-i = 0 := by
  unfold Y'cases_ij
  unfold Y'f Y'g
  have h1 : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 0 = 0 := by
    norm_cast
  rw [h1]
  have h2 : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 0 = 0 := by
    norm_cast
  rw [h2]
  constructor
  · intro h_case
    let h1:= h_case
    have h2 : (j - i) ≥ 0 := by
      exact h1.1
    have h3 : (j - i) ≤ 0 := by
      exact h1.2
    exact le_antisymm h3 h2
  intro h_ji
  rw [h_ji]
  constructor
  · norm_num
  norm_num
lemma Y'case1_iff (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 1 ↔ j-i = 1 := by
  unfold Y'cases_ij
  unfold Y'f Y'g
  have h1 : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 1 = 1 := by
    norm_cast
  rw [h1]
  have h2 : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 1 = 1 := by
    norm_cast
  rw [h2]
  constructor
  · intro h_case
    let h1:= h_case
    have h2 : (j - i) ≥ 1 := by
      exact h1.1
    have h3 : (j - i) ≤ 1 := by
      exact h1.2
    exact le_antisymm h3 h2
  intro h_ji
  rw [h_ji]
  constructor
  · norm_num
  norm_num
lemma Y'case2_iff (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 2 ↔ (j-i) ≥ 2 ∧ (j-i) ≤ 2*l+2 := by
  unfold Y'cases_ij
  unfold Y'f Y'g
  have h1 : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 2 = 2 := by
    norm_cast
  rw [h1]
  have h2 : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 2 = 2*l + 2 := by
    norm_cast
  rw [h2]
lemma Y'case3_iff (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 3 ↔ (j-i) = 2*l+3 := by
  unfold Y'cases_ij
  unfold Y'f Y'g
  have h1 : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 3 = 2*l + 3 := by
    norm_cast
  rw [h1]
  have h2 : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 3 = 2*l + 3 := by
    norm_cast
  rw [h2]
  constructor
  · intro h_case
    let h1:= h_case
    have h2 : (j - i) ≥ 2*l + 3 := by
      exact h1.1
    have h3 : (j - i) ≤ 2*l + 3 := by
      exact h1.2
    exact le_antisymm h3 h2
  intro h_ji
  rw [h_ji]
  constructor
  · norm_num
  norm_num
lemma Y'case4_iff (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 4 ↔ (j-i) ≤ -2 ∧ (j-i) ≥ -(2*l+2) := by
  unfold Y'cases_ij
  unfold Y'f Y'g
  have h1 : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 4 = 2*l + 4 := by
    norm_cast
  rw [h1]
  have h2 : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 4 = 4*l + 4 := by
    norm_cast
  rw [h2]
  have h3 : (4*(l : Fin (4*l + 6)) + 4) = (-2 : Fin (4*l + 6)) := by
    norm_cast
  have h4 : (2*l +4 : Fin (4*l + 6)) = (-(2*l +2) : Fin (4*l + 6)) := by
    rw [←add_eq_zero_iff_eq_neg]
    rw [←add_assoc]
    norm_cast
    have h6: 2*l+4+2*l+2 = 4*l+6 := by
      omega
    rw [h6]
    have h7 : ((4*l+6:ℕ) : Fin (4*l + 6)) = (0 : Fin (4*l + 6)) := by
      have h8 (k l : ℕ): (k%(4*l+6)) = (k: Fin (4*l+6)) := by
        norm_cast
      let h9:= h8 (4*l+6) l
      simp only [Fin.ext_iff, Nat.mod_self]
      rw [←h9]
      simp only [Fin.ext_iff, Nat.mod_self]
      norm_cast
    rw [h7]
  rw [h3]
  rw [h4]
  rw [and_comm]
lemma Y'case5_iff (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 5 ↔ j-i = -1 := by
  unfold Y'cases_ij
  unfold Y'f Y'g
  have h1 : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 5 = 4*l + 5 := by
    norm_cast
  rw [h1]
  have h2 : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 5 = 4*l + 5 := by
    norm_cast
  rw [h2]
  have h3 : (4*(l : Fin (4*l + 6)) + 5) = (-1 : Fin (4*l + 6)) := by
    norm_cast
  rw [h3]
  constructor
  · intro h_case
    let h1:= h_case
    have h2 : (j - i) ≥ -1 := by
      exact h1.1
    have h3 : (j - i) ≤ -1 := by
      exact h1.2
    exact le_antisymm h3 h2
  intro h_ji
  rw [h_ji]
  constructor
  · norm_num
  norm_num


lemma fin_neg_le_neg (a b : Fin (n + 1)) (ha : a ≠ 0) : a ≤ b → (-b : Fin (n + 1)) ≤ -a := by
  intro hab
  -- unpack the Fin's to access the nat values
  rcases a with ⟨k, hk⟩
  rcases b with ⟨l, hl⟩
  -- a ≠ 0 gives k ≠ 0, hence k ≥ 1; from k ≤ l we get l ≥ 1 as well
  have k_ne : k ≠ 0 := by
    intro hk0
    dsimp at ha
    apply ha
    simp [hk0]
  have k_pos : 0 < k := Nat.pos_of_ne_zero k_ne
  have k_le_l : k ≤ l := by simpa using Fin.le_iff_val_le_val.mp hab
  have : l ≠ 0 := by
    intro hl0
    -- if l = 0 then k ≤ 0, so k = 0 contradicts k_ne
    have : k ≤ 0 := by simpa [hl0] using k_le_l
    exact absurd (Nat.le_zero.1 this) k_ne
  -- now both n+1 - l and n+1 - k are < n+1, so the `%` in the definition of neg is redundant
  let N := n + 1
  have h1 : (N - l) % N = N - l := Nat.mod_eq_of_lt (by omega)
  have h2 : (N - k) % N = N - k := Nat.mod_eq_of_lt (by omega)
  -- convert the goal to nat inequalities on the `.val` fields
  show (N - l) % N ≤ (N - k) % N
  -- rewrite using the two `mod` facts and finish by the nat inequality coming from k ≤ l
  rw [h1, h2]
  omega
lemma fin_neg_le_neg'  (l:ℕ) (a b : Fin (4*l +6)) (ha: a≠ 0): a ≤ b → (-b : Fin (4*l +6)) ≤ -a := by
  intro hab
  exact fin_neg_le_neg a b ha hab
lemma fin_ij_ge_neg (l:ℕ) (i j a : Fin (4*l +6)) (ha:a≠ 0):  j-i ≥ a → i - j ≤ -a := by
    intro h_ji
    have h_ji' : a≤ j-i:= by
      exact h_ji
    let h4 := fin_neg_le_neg' l a (j - i) ha h_ji'
    rw [neg_sub] at h4
    exact h4
lemma fin_ij_le_neg (l:ℕ) (i j a : Fin (4*l +6)) (hij:j-i≠ 0):  j-i ≤ a → i - j ≥ -a := by
    intro h_ji
    let h4 := fin_neg_le_neg' l (j - i) a hij h_ji
    rw [neg_sub] at h4
    exact h4
lemma fin_ij_int_neg (l:ℕ) (i j a b: Fin (4*l +6)) (ha:a≠ 0) : (j-i ≥ a ∧  j-i ≤ b) → (i - j ≤ -a ∧ i - j ≥ -b) := by
    intro h_ji
    let h_ji_ge := h_ji.1
    let h_ji_le := h_ji.2
    let h1 := fin_ij_ge_neg l i j a ha h_ji_ge
    have h2 : j-i ≠ 0 := by
      intro h0
      rw [h0] at h_ji_ge
      have h3 : a≤ 0 := by
        exact h_ji_ge
      have h2: a<0 := by
        exact  lt_of_le_of_ne h3 ha
      exact Nat.not_lt_zero a.val h2
    let h2 := fin_ij_le_neg l i j b h2 h_ji_le
    constructor
    · exact h1
    exact h2
lemma fin_ij_eq_neg (l:ℕ) (i j a : Fin (4*l +6)) :  j-i = a → i - j = -a := by
    intro h_ji
    have h1 (b c: Fin (4*l +6)) : b = c →  -c = -b := by
      intro h_bc
      rw [h_bc]
    rw [h1 _ _ h_ji]
    rw [neg_sub]


lemma Y'skewCase0 (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 0 → Y'cases_ij l j i 0 := by
  unfold Y'cases_ij
  intro h_case
  let h1:= h_case
  unfold Y'f Y'g at h1
  let l' := (l : Fin (4*l + 6))
  have h2 : ![0, 1, 2, 2 * l' + 3, 2 * l' + 4, 4 * l' + 5] 0 = 0 := by
    norm_cast
  rw [h2] at h1
  have h3 : ![0, 1, 2 * l' + 2, 2 * l' + 3, 4 * l' + 4, 4 * l' + 5] 0 = 0 := by
    norm_cast
  rw [h3] at h1
  have h5 : (j - i) = 0 := by
    have h5' : (j - i) ≥ 0 := by
      exact h1.1
    have h5'' : (j - i) ≤ 0 := by
      exact h1.2
    exact le_antisymm h5'' h5'
  have h7 : (j-i) = - (i-j) := by
    rw [neg_sub]
  have h6 : j-i = 0 ↔ i - j = 0 := by
    constructor
    · intro h_ji
      rw [h7] at h_ji
      exact neg_eq_zero.mp h_ji
    intro h_ij
    rw [h7]
    exact neg_eq_zero.mpr h_ij
  unfold Y'f Y'g
  rw [h2]
  rw [h3]
  constructor
  · norm_num
  norm_num
  rw [h7] at h5
  exact neg_eq_zero.mp h5
lemma Y'skewCase1 (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 1 → Y'cases_ij l j i 5 := by
  unfold Y'cases_ij
  intro h_case
  let h1:= h_case
  unfold Y'f Y'g at h1
  let l' := (l : Fin (4*l + 6))
  have h2 : ![0, 1, 2, 2 * l' + 3, 2 * l' + 4, 4 * l' + 5] 1 = 1 := by
    norm_cast
  rw [h2] at h1
  have h3 : ![0, 1, 2 * l' + 2, 2 * l' + 3, 4 * l' + 4, 4 * l' + 5] 1 = 1 := by
    norm_cast
  rw [h3] at h1
  have h5 : (j - i) = 1 := by
    have h5' : (j - i) ≥ 1 := by
      exact h1.1
    have h5'' : (j - i) ≤ 1 := by
      exact h1.2
    exact le_antisymm h5'' h5'
  have h6 : j-i = 1 ↔ i - j = -1 := by
    constructor
    · intro _
      rw [← h5]
      simp [Eq.symm]
    intro _
    rw [← h5]
  unfold Y'f Y'g
  have h2' : ![0, 1, 2, 2 * l' + 3, 2 * l' + 4, 4 * l' + 5] 5 = 4*l'+5 := by
    rfl
  rw [h2']
  have h3' : ![0, 1, 2 * l' + 2, 2 * l' + 3, 4 * l' + 4, 4 * l' + 5] 5 = 4*l'+5 := by
    rfl
  rw [h3']
  have h5' : (4*(l : Fin (4*l + 6)) + 5) = (-1 : Fin (4*l + 6)) := by
    norm_cast
  rw [h5']
  let h8:= h6.mp h5
  rw [h8]
  rw [← @Fin.le_antisymm_iff]
lemma Y'skewCase2 (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 2 → Y'cases_ij l j i 4 := by
  rw [Y'case2_iff]
  rw [Y'case4_iff]
  intro h_case
  have h2ne0 : (2 : Fin (4*l + 6)) ≠ 0 := by
      have h0lt2: 0 < 2 := by omega
      have h0lt2fin : (0 : Fin (4*l + 6)) < (2 : Fin (4*l + 6)) := by
        exact lt_nat_fin' l 0 2 h0lt2 (by omega)
      have h0ne2 : (0 : Fin (4*l + 6)) ≠ (2 : Fin (4*l + 6)) := by
        exact ne_of_lt h0lt2fin
      exact h0ne2.symm
  exact fin_ij_int_neg l i j (2 : Fin (4*l +6)) (2*(l : Fin (4*l +6)) +2) h2ne0 h_case
lemma Y'skewCase3 (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 3 → Y'cases_ij l j i 3 := by
  rw [Y'case3_iff]
  rw [Y'case3_iff]
  intro h_case
  let h1:= fin_ij_eq_neg l i j (2*l +3) h_case
  have h2: (2*l +3 : Fin (4*l +6)) = -(2*l +3 : Fin (4*l +6)) := by
    rw [←add_eq_zero_iff_eq_neg]
    rw [←add_assoc]
    norm_cast
    have h6: 2*l+3+2*l+3 = 4*l+6 := by
      omega
    rw [h6]
    have h7 : ((4*l+6:ℕ) : Fin (4*l + 6)) = (0 : Fin (4*l + 6)) := by
      have h8 (k l : ℕ): (k%(4*l+6)) = (k: Fin (4*l+6)) := by
        norm_cast
      let h9:= h8 (4*l+6) l
      simp only [Fin.ext_iff, Nat.mod_self]
      rw [←h9]
      simp only [Fin.ext_iff, Nat.mod_self]
      norm_cast
    rw [h7]
  rw [h2] at h1
  rw [neg_neg] at h1
  exact h1
lemma Y'skewCase4 (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 4 → Y'cases_ij l j i 2 := by
  rw [Y'case4_iff]
  rw [Y'case2_iff]
  intro h_case
  have h2ne0 : -(2 * (l:Fin (4*l + 6)) + 2) ≠ 0 := by
    have h0lt2l2: 0 < 2*((l:Fin (4*l + 6)):ℕ) +2 := by omega
    have h3: ((l:Fin (4*l + 6)):ℕ) = l := by
      have h : l < 4 * l + 6 := by
        linarith
      rw [Fin.val_cast_of_lt h]
    have h1: 2*((l:Fin (4*l + 6)):ℕ) +2 < 4*l +6 := by
      rw [h3]
      omega
    have h0lt2l2fin : (0 : Fin (4*l + 6)) < (2*l +2 : Fin (4*l + 6)) := by
      let h2:= lt_nat_fin' l 0 (2*(l:Fin (4*l + 6)) +2) h0lt2l2 h1
      norm_cast
      rw [h3] at h2
      exact h2
    have h0ne2l2 : (0 : Fin (4*l + 6)) ≠ (2*l +2 : Fin (4*l + 6)) := by
      exact ne_of_lt h0lt2l2fin
    have h_neg_ne : -(2*l +2 : Fin (4*l + 6)) ≠ 0 := by
      intro h0
      rw [neg_eq_zero] at h0
      exact h0ne2l2 h0.symm
    exact h_neg_ne
  let h1:= fin_ij_int_neg l i j (-(2*(l : Fin (4*l +6)) +2)) (-2 : Fin (4*l +6)) h2ne0 h_case.symm
  rw [neg_neg] at h1
  rw [neg_neg] at h1
  exact h1.symm
lemma Y'skewCase5 (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 5 → Y'cases_ij l j i 1 := by
  rw [Y'case5_iff]
  rw [Y'case1_iff]
  intro h_case
  let h1:= fin_ij_eq_neg l i j (-1) h_case
  rw [neg_neg] at h1
  exact h1



lemma add_mod_mod_div (l:ℕ) (a b: Fin (4*l +6)) : (((a + b):Fin (4*l+6)):Fin 2) = (a:Fin 2) + (b:Fin 2) := by
  rw [@Fin.val_add_eq_ite]
  split_ifs with h
  · -- Case 1: 4*l+6 ≤ a.val + b.val
    have h1 (a': ℕ) (b': ℕ): (b'≤ a') →(((a' - b'):ℕ):Fin 2) = (a': Fin 2) - (b': Fin 2) := by
      intro h_le
      -- Add (b':Fin 2) to both sides of the equality
      have (A B C: Fin 2): A = B - C ↔ A + C = B := by
        omega
      rw [this]
      --rw [←h3]
      simp only [←Nat.cast_add]
      rw [Nat.sub_add_cancel h_le]
    let h2 := h1 (a + b) (4*l +6) h
    rw [h2]
    have h4 : (((4*l +6):ℕ ):Fin 2)  = 0 := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Fin.isValue, zero_mul, add_zero]
    rw [h4]
    simp only [Nat.cast_add, Fin.isValue, sub_zero]
  · -- Case 2: ¬(4*l+6 ≤ a.val + b.val), i.e., a.val + b.val < 4*l+6
    have h1 (a' b': ℕ): (((a' + b'):ℕ):Fin 2) = (a': Fin 2) + (b': Fin 2) := by
      rw [Nat.cast_add]
    exact h1 a.val b.val


lemma Y'skewCase1A (l:ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 1 ∧ Y'caseA l i → Y'cases_ij l j i 5 ∧ Y'caseB l j:= by
  intro h_case
  constructor
  · exact Y'skewCase1 l i j h_case.1
  unfold Y'caseA at h_case
  unfold Y'caseB
  unfold Y'cases_ij at h_case
  unfold Y'f Y'g at h_case
  have  : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 1 = 1 := by
    norm_cast
  rw [this] at h_case
  have  : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 1 = 1 := by
    norm_cast
  rw [this] at h_case
  have h5 : (j - i) = 1 := by
    exact le_antisymm h_case.1.2 h_case.1.1
  have h6: (i:Fin 2) =0 → (j:Fin 2) =1 := by
    intro  hi_even
    have h1 : j = i + 1 := by
      simp [h5.symm]
    rw [h1]
    let h4:= add_mod_mod_div l i 1
    rw [h4]
    rw [hi_even]
    norm_num
  have hi_even : (i:Fin 2) = 0 := by
    have h7 (A:ℕ): A%2=0 → (A:Fin 2) =0 := by
      intro h_even
      rw [@Fin.natCast_eq_zero]
      exact Nat.dvd_of_mod_eq_zero h_even
    exact h7 i.val h_case.2
  let h7:= h6 hi_even
  rw [← @Nat.odd_iff]
  rw [← @ZMod.eq_one_iff_odd]
  exact h7

lemma Y'skewCase1B (l:ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 1 ∧ Y'caseB l i → Y'cases_ij l j i 5 ∧ Y'caseA l j:= by
  intro h_case
  constructor
  · exact Y'skewCase1 l i j h_case.1
  unfold Y'caseB at h_case
  unfold Y'caseA
  unfold Y'cases_ij at h_case
  unfold Y'f Y'g at h_case
  have  : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 1 = 1 := by
    norm_cast
  rw [this] at h_case
  have  : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 1 = 1 := by
    norm_cast
  rw [this] at h_case
  have h5 : (j - i) = 1 := by
    exact le_antisymm h_case.1.2 h_case.1.1
  have h6: (i:Fin 2) =1 → (j:Fin 2) =0 := by
    intro hi_odd
    have h1 : j = i + 1 := by
      simp [h5.symm]
    rw [h1]
    let h4:= add_mod_mod_div l i 1
    rw [h4]
    rw [hi_odd]
    norm_num
    norm_cast
  have hi_odd : (i:Fin 2) = 1 := by
    have h7 (A:ℕ): A%2=1 → (A:Fin 2) =1 := by
      intro h_odd
      have h8: Odd A := by
        exact Nat.odd_iff.mpr h_odd
      simp [h8]
      rw [@Fin.natCast_def]
      simp [h_odd]
    exact h7 i.val h_case.2
  let h7:= h6 hi_odd
  rw [@Fin.natCast_eq_zero] at h7
  exact Nat.mod_eq_zero_of_dvd h7




lemma Y'skewCase3A (l:ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 3 ∧ Y'caseA l i → Y'cases_ij l j i 3 ∧ Y'caseB l j:= by
  intro h_case
  constructor
  · exact Y'skewCase3 l i j h_case.1
  unfold Y'caseA at h_case
  unfold Y'caseB
  unfold Y'cases_ij at h_case
  unfold Y'f Y'g at h_case
  have  : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 3 = 2*l +3 := by
    norm_cast
  rw [this] at h_case
  have  : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 3 = 2*l +3 := by
    norm_cast
  rw [this] at h_case
  have h5 : (j - i) = 2*l +3 := by
    exact le_antisymm h_case.1.2 h_case.1.1
  have h6 : j = i + (2*l +3) := by
    simp [h5.symm]
  have h6': (j:Fin 2) = (i:Fin 2) + (((2*l +3):Fin (4*l +6)):Fin 2) := by
    have h7 (a b: Fin (4*l +6)): a=b → (a:Fin 2) = (b:Fin 2) := by
      intro h_eq
      rw [@Fin.natCast_def]
      rw [@Fin.natCast_def]
      simp [h_eq]
    let h8:= h7 j (i + (2*l +3)) h6
    rw [h8]
    let h9:= add_mod_mod_div l i (2*l +3)
    exact h9
  have h7:  (((2*l+3):Fin (4*l+6)):Fin 2) = (1:Fin 2) := by
    have h8: ((2*l +3):ℕ)%2 =1 := by
      have h9: Odd (2*l +3) := by
        exact Nat.odd_iff.mpr (by omega)
      exact Nat.odd_iff.mp h9
    have h10 (A:ℕ): A%2=1 → (A:Fin 2) =1 := by
      intro h_mod
      rw [@Fin.natCast_def]
      simp [h_mod]
    let h11:= h10 (2*l +3) h8
    have h12: ((2*l + 3): Fin (4*l+6)).val = 2*l +3 := by
      norm_cast
      have h13: 2*l +3 < 4*l +6 := by
        omega
      let h14:= Fin.val_cast_of_lt h13
      exact h14
    rw [h12]
    exact h11
  rw [h7] at h6'
  have h8: (i:Fin 2) = 0 := by
    have h9 (A:ℕ): A%2=0 → (A:Fin 2) =0 := by
      intro h_mod
      rw [@Fin.natCast_eq_zero]
      exact Nat.dvd_of_mod_eq_zero h_mod
    exact h9 i.val h_case.2
  have h9: (j:Fin 2) =1 := by
    rw [h6']
    rw [h8]
    norm_num
  rw [← @Nat.odd_iff]
  rw [← @ZMod.eq_one_iff_odd]
  exact h9

lemma Y'skewCase3B (l:ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 3 ∧ Y'caseB l i → Y'cases_ij l j i 3 ∧ Y'caseA l j:= by
  intro h_case
  constructor
  · exact Y'skewCase3 l i j h_case.1
  unfold Y'caseB at h_case
  unfold Y'caseA
  unfold Y'cases_ij at h_case
  unfold Y'f Y'g at h_case
  have  : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 3 = 2*l +3 := by
    norm_cast
  rw [this] at h_case
  have  : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 3 = 2*l +3 := by
    norm_cast
  rw [this] at h_case
  have h5 : (j - i) = 2*l +3 := by
    exact le_antisymm h_case.1.2 h_case.1.1
  have h6 : j = i + (2*l +3) := by
    simp [h5.symm]
  have h6': (j:Fin 2) = (i:Fin 2) + (((2*l +3):Fin (4*l +6)):Fin 2) := by
    have h7 (a b: Fin (4*l +6)): a=b → (a:Fin 2) = (b:Fin 2) := by
      intro h_eq
      rw [@Fin.natCast_def]
      rw [@Fin.natCast_def]
      simp [h_eq]
    let h8:= h7 j (i + (2*l +3)) h6
    rw [h8]
    let h9:= add_mod_mod_div l i (2*l +3)
    exact h9
  have h7:  (((2*l+3):Fin (4*l+6)):Fin 2) = (1:Fin 2) := by
    have h8: ((2*l +3):ℕ)%2 =1 := by
      have h9: Odd (2*l +3) := by
        exact Nat.odd_iff.mpr (by omega)
      exact Nat.odd_iff.mp h9
    have h10 (A:ℕ): A%2=1 → (A:Fin 2) =1 := by
      intro h_mod
      rw [@Fin.natCast_def]
      simp [h_mod]
    let h11:= h10 (2*l +3) h8
    have h12: ((2*l + 3): Fin (4*l+6)).val = 2*l +3 := by
      norm_cast
      have h13: 2*l +3 < 4*l +6 := by
        omega
      let h14:= Fin.val_cast_of_lt h13
      exact h14
    rw [h12]
    exact h11
  rw [h7] at h6'
  have h8: (i:Fin 2) = 1 := by
    let h9 := Nat.odd_iff.mpr h_case.2
    rw [← @ZMod.eq_one_iff_odd] at h9
    exact h9
  rw [h8] at h6'
  have h9: (j:Fin 2) =0 := by
    rw [h6']
    norm_cast
  simp only [@Fin.natCast_eq_zero] at h9
  exact Nat.mod_eq_zero_of_dvd h9

lemma Y'skewCase5A (l:ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 5 ∧ Y'caseA l i → Y'cases_ij l j i 1 ∧ Y'caseB l j:= by
  intro h_case
  constructor
  · exact Y'skewCase5 l i j h_case.1
  unfold Y'caseA at h_case
  unfold Y'caseB
  unfold Y'cases_ij at h_case
  unfold Y'f Y'g at h_case
  have  : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 5 = 4*l +5 := by
    norm_cast
  rw [this] at h_case
  have  : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 5 = 4*l +5 := by
    norm_cast
  rw [this] at h_case
  have h5 : (j - i) = 4*l +5 := by
    exact le_antisymm h_case.1.2 h_case.1.1
  have h6: (i:Fin 2) =0 → (j:Fin 2) =1 := by
    intro  hi_even
    have h1 : j = i + (4*l +5) := by
      simp [h5.symm]
    rw [h1]
    let h4:= add_mod_mod_div l i (4*l +5)
    rw [h4]
    rw [hi_even]
    have h7 : (((4*l +5):Fin (4*l+6)):Fin 2) =1 := by
      have h8: (4*l +5)%2 =1 := by
        have h9: Odd (4*l +5) := by
          exact Nat.odd_iff.mpr (by omega)
        exact Nat.odd_iff.mp h9
      have h10 (A:ℕ): A%2=1 → (A:Fin 2) =1 := by
        intro h_mod
        rw [@Fin.natCast_def]
        simp [h_mod]
      let h11:=  h10 (4*l +5) h8
      have h12: ((4*l + 5): Fin (4*l+6)).val = 4*l +5 := by
        norm_cast
        have h13: 4*l +5 < 4*l +6 := by
          omega
        let h14:= Fin.val_cast_of_lt h13
        exact h14
      rw [h12]
      exact h11
    rw [h7]
    norm_num
  have hi_even : (i:Fin 2) = 0 := by
    have h7 (A:ℕ): A%2=0 → (A:Fin 2) =0 := by
      intro h_even
      rw [@Fin.natCast_eq_zero]
      exact Nat.dvd_of_mod_eq_zero h_even
    exact h7 i.val h_case.2
  let h7:= h6 hi_even
  rw [← @Nat.odd_iff]
  rw [@ZMod.eq_one_iff_odd] at h7
  exact h7

lemma Y'skewCase5B (l:ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 5 ∧ Y'caseB l i → Y'cases_ij l j i 1 ∧ Y'caseA l j:= by
  intro h_case
  constructor
  · exact Y'skewCase5 l i j h_case.1
  unfold Y'caseB at h_case
  unfold Y'caseA
  unfold Y'cases_ij at h_case
  unfold Y'f Y'g at h_case
  have  : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 5 = 4*l +5 := by
    norm_cast
  rw [this] at h_case
  have  : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 5 = 4*l +5 := by
    norm_cast
  rw [this] at h_case
  have h5 : (j - i) = 4*l +5 := by
    exact le_antisymm h_case.1.2 h_case.1.1
  have h6: (i:Fin 2) =1 → (j:Fin 2) =0 := by
    intro hi_odd
    have h1 : j = i + (4*l +5) := by
      simp [h5.symm]
    rw [h1]
    let h4:= add_mod_mod_div l i (4*l +5)
    rw [h4]
    rw [hi_odd]
    have h7 : (((4*l +5):Fin (4*l+6)):Fin 2) =1 := by
      have h8: (4*l +5)%2 =1 := by
        have h9: Odd (4*l +5) := by
          exact Nat.odd_iff.mpr (by omega)
        exact Nat.odd_iff.mp h9
      have h10 (A:ℕ): A%2=1 → (A:Fin 2) =1 := by
        intro h_mod
        rw [@Fin.natCast_def]
        simp [h_mod]
      let h11:=  h10 (4*l +5) h8
      have h12: ((4*l + 5): Fin (4*l+6)).val = 4*l +5 := by
        norm_cast
        have h13: 4*l +5 < 4*l +6 := by
          omega
        let h14:= Fin.val_cast_of_lt h13
        exact h14
      rw [h12]
      exact h11
    rw [h7]
    norm_cast
  have hi_odd : (i:Fin 2) = 1 := by
    let h9 := Nat.odd_iff.mpr h_case.2
    rw [← @ZMod.eq_one_iff_odd] at h9
    exact h9
  let h7:= h6 hi_odd
  rw [h7] at h6
  have h9: (j:Fin 2) =0 := by
    rw [h6]
    exact h7
    exact hi_odd
  simp only [@Fin.natCast_eq_zero] at h9
  exact Nat.mod_eq_zero_of_dvd h9




lemma Y'cases_exclusive (l:ℕ) (i j : Fin (4 * l + 6)) : ∀ (k1 k2 : Fin 6), k1 ≠ k2 → (Y'cases_ij l i j k1) → ¬ (Y'cases_ij l i j k2) := by
  intros k1 k2 h_neq h_case1 h_case2
  unfold Y'cases_ij at h_case1 h_case2
  have h_system : system_of_intervals (Y'f l) (Y'g l) := by
    exact interval_split_Y' l
  let h1 := intervals_disjoint (Y'f l) (Y'g l) h_system (j - i) k1 k2 h_case1 h_case2
  exact h_neq h1


#eval Y' 0
#eval Y' 1

--def Y'f (l : ℕ): (Fin 6) → Fin (4*l + 6)  :=
  --![0, 1, 2, 2*l+3, 2*l+4, 4*l+5]


lemma fin_ne_zero (k l : ℕ) : (k≠ 0) → (k<4*l+6) → (k : Fin (4*l+6)) ≠ (0 : Fin (4*l+6)) := by
  intro h1 h2
  rw [@Fin.ne_iff_vne]
  rw [Fin.val_cast_of_lt h2]
  exact h1


lemma Y'value_case0 (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 0  → Y' l i j = 0 := by
  unfold Y'cases_ij
  intro h_case
  let h1:= h_case
  unfold Y'f Y'g at h1
  let l' := (l : Fin (4*l + 6))
  have h3 : ![0, 1, 2, 2 * l' + 3, 2 * l' + 4, 4 * l' + 5] 0 = 0 := by
    norm_cast
  rw [h3] at h1
  have h4 : ![0, 1, 2 * l' + 2, 2 * l' + 3, 4 * l' + 4, 4 * l' + 5] 0 = 0 := by
    norm_cast
  rw [h4] at h1
  have h5 : (j - i) = 0 := by
    have h5' : (j - i) ≥ 0 := by
      exact h1.1
    have h5'' : (j - i) ≤ 0 := by
      exact h1.2
    exact le_antisymm h5'' h5'
  unfold Y'
  have h6 : j-i = 0 → Y' l i j = 0 := by
    intro h_ji
    unfold Y'
    simp only [ge_iff_le, neg_add_rev, ite_self, of_apply]
    rw [h_ji]
    norm_num
    have hh: ((2:Fin (4*l + 6))=(0:Fin (4*l + 6))) = False := by
      norm_num
      rw [Fin.ext_iff]
      norm_num
    simp [hh]
    have hh: ((-(2:Fin (4*l+6)) + -(2 * (l:Fin (4*l+6))))= (0:Fin (4*l + 6))) = False := by
      norm_num
      have h1: -(2:Fin (4*l+6)) + -(2 * (l:Fin (4*l+6))) = -(2 + 2 * (l:Fin (4*l+6))) := by
        rw [neg_add_rev]
        rw [@fin_add_comm]
      rw [h1]
      rw [@neg_eq_zero]
      simp only [ne_eq]
      have h6 : ((2*l + 2 : ℕ) : Fin (4*l + 6)) ≠ (0 : Fin (4*l + 6)) := by
        have h1 : (2*l + 2) < (4*l + 6) := by
          omega
        have h2 : 2*l+2 ≠ 0 := by
          omega
        let h3 := fin_ne_zero (2*l + 2) l h2 h1
        exact h3
      have h7 : ((2*l + 2 : ℕ) : Fin (4*l + 6)) = ((2+ 2*l ) : Fin (4*l + 6)) := by
        norm_num
        rw [@fin_add_comm]
      rw [h7] at h6
      exact h6
    simp [hh]
    have h8: ¬(2*(l:Fin (4*l+6)) + 3 = 0) := by
      let h9:= fin_ne_zero (2*l + 3) l (by omega) (by omega)
      have h10 : (2*(l:Fin (4*l+6)) + 3) = ((2*l + 3: ℕ) : Fin (4*l + 6)) := by
        norm_num
      norm_num
      rw [←h10] at h9
      exact h9
    have h9 : ¬( 0 = (2*(l:Fin (4*l+6)) + 3)) := by
      rw [eq_comm]
      exact h8
    have h_imp {A B : Prop}: ¬A → (A → B) := by
      intros h_notA hA
      contradiction
    exact h_imp h9
  have h_imp{A B : Prop} : A → (A → B) → B := by
    intros hA hAimpB
    exact hAimpB hA
  let h' := h_imp h5 h6
  exact h'
lemma Y'value_case1A (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 1 ∧ Y'caseA l i → Y' l i j = 2 := by
  unfold Y'cases_ij
  intro h_case
  let h1:= h_case.1
  let h2:= h_case.2
  have h_caseA : i.val % 2 = 0 := by
      exact h2
  unfold Y'f Y'g at h1
  let l' := (l : Fin (4*l + 6))
  have h3 : ![0, 1, 2, 2 * l' + 3, 2 * l' + 4, 4 * l' + 5] 1 = 1 := by
    norm_cast
  rw [h3] at h1
  have h4 : ![0, 1, 2 * l' + 2, 2 * l' + 3, 4 * l' + 4, 4 * l' + 5] 1 = 1 := by
    norm_cast
  rw [h4] at h1
  have h5 : (j - i) = 1 := by
    have h5' : (j - i) ≥ 1 := by
      exact h1.1
    have h5'' : (j - i) ≤ 1 := by
      exact h1.2
    exact le_antisymm h5'' h5'
  have h6 : j-i = 1 → Y' l i j = 2 := by
    intro h_ji
    unfold Y'
    simp only [ge_iff_le, neg_add_rev, ite_self, of_apply]
    rw [h_ji]
    norm_num
    unfold Y'caseA at h_caseA
    rw [Fin.ext_iff]
    exact h_caseA
  have h_imp{A B : Prop} : A → (A → B) → B := by
    intros hA hAimpB
    exact hAimpB hA
  let h' := h_imp h5 h6
  exact h'
lemma Y'value_case1B (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 1 ∧ Y'caseB l i → Y' l i j = 1 := by
  unfold Y'cases_ij
  intro h_case
  let h1:= h_case.1
  let h2:= h_case.2
  have h_caseB : i.val % 2 = 1 := by
      exact h2
  unfold Y'f Y'g at h1
  let l' := (l : Fin (4*l + 6))
  have h3 : ![0, 1, 2, 2 * l' + 3, 2 * l' + 4, 4 * l' + 5] 1 = 1 := by
    norm_cast
  rw [h3] at h1
  have h4 : ![0, 1, 2 * l' + 2, 2 * l' + 3, 4 * l' + 4      , 4 * l' + 5] 1 = 1 := by
    norm_cast
  rw [h4] at h1
  have h5 : (j - i) = 1 := by
    have h5' : (j - i) ≥ 1 := by
      exact h1.1
    have h5'' : (j - i) ≤ 1 := by
      exact h1.2
    exact le_antisymm h5'' h5'
  have h6 : j-i = 1 → Y' l i j = 1 := by
    intro h_ji
    unfold Y'
    simp only [ge_iff_le, neg_add_rev, ite_self, of_apply]
    rw [h_ji]
    norm_num
    unfold Y'caseB at h_caseB
    rw [Fin.ext_iff]
    have h_ne : i.val % 2 ≠ 0 := by
      rw [h_caseB]
      norm_num
    exact h_ne
  have h_imp{A B : Prop} : A → (A → B) → B := by
    intros hA hAimpB
    exact hAimpB hA
  let h' := h_imp h5 h6
  exact h'
lemma Y'value_case2 (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 2 → Y' l i j = 1 := by
  unfold Y'cases_ij
  intro h_case
  let h1:= h_case
  unfold Y'f Y'g at h1
  let l' := (l : Fin (4*l + 6))
  have h3 : ![0, 1, 2, 2 * l' + 3, 2 * l' + 4, 4 * l' + 5] 2 = 2 := by
    norm_cast
  rw [h3] at h1
  have h4 : ![0, 1, 2 * l' + 2, 2 * l' + 3, 4 * l' + 4, 4 * l' + 5] 2 = 2*l'+2 := by
    norm_cast
  rw [h4] at h1
  have h5 : (j - i) ≥ 2 ∧ (j - i) ≤ 2*l+2 := by
    exact h1
  have h6 : (j - i) ≥ 2 ∧ (j - i) ≤ 2*l+2 → Y' l i j = 1 := by
    intro h_ji
    unfold Y'
    simp only [ge_iff_le, neg_add_rev, ite_self, of_apply]
    have h8 : ¬ ((j - i) = 1) := by
      have h9 : (j - i) ≥ 2 := by
        exact h_ji.1
      by_contra h_lt2
      rw [h_lt2] at h9
      have not_h9 : ¬ (1 ≥ 2) := by
        omega
      exact not_h9 h9
    simp [h8]
    have h9 : ¬ ((j - i) = -1) := by
      have h10 : (j - i) ≤  2*l + 2 := by
        exact h_ji.2
      by_contra h_lt0
      rw [h_lt0] at h10
      have not_h10 : ¬ (-1:Fin (4*l+6)) ≤ 2*l + 2 := by
        have h11 : (-1:Fin (4*l+6)) = (4*l + 5 : Fin (4*l +6)) := by
          norm_cast
        rw [h11]
        rw [le_fin_nat]
        norm_cast
        have h12 : 2*l + 2 < 4*l + 5  := by
          omega
        have h13 : (2*l + 2 : Fin (4*l+6)) <((4*l+5):Fin (4*l+6) ) := by
          let h14:= lt_nat_fin' l (2*l+2) (4*l+5) h12 (by omega)
          norm_cast
        simp [←le_fin_nat]
        exact h13
      exact not_h10 h10
    simp [h9]
    simp [h5.1]
    have not_h5right : ¬ ((j - i) > 2*l + 2) := by
      have h10 : (j - i) ≤ 2*l + 2 := by
        exact h_ji.2
      by_contra h_gt
      have not_h10 : ¬ ( (j - i) ≤ 2*l + 2) := by
        omega
      exact not_h10 h10
    simp [not_h5right]
  let h' := h6 h5
  exact h'
lemma Y'value_case3 (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 3 → Y' l i j = if i.val % 2 = 0 then -1 else 1 := by
  unfold Y'cases_ij
  intro h_case
  unfold Y'f Y'g at h_case
  unfold Y'
  --let l' := (l : Fin (4*l + 6))
  have h3 : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 3 = 2*(l : Fin (4*l + 6))+3 := by
    norm_cast
  rw [h3] at h_case
  have h4 : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 3 = 2*(l : Fin (4*l + 6))+3 := by
    norm_cast
  rw [h4] at h_case
  have h3: j-i = 2*l+3 := by
    have h_eq : (j - i) ≤ 2*l+3 := by
      exact h_case.2
    have h_ge : (j - i) ≥ 2*l+3 := by
      exact h_case.1
    exact le_antisymm h_eq h_ge
  have h3': Y'cases_ij l i j 3 := by
    exact (Y'case3_iff l i j).mpr h3
  have not_h1 : ¬ ((j - i) = 1) := by
    have not_h1' : ¬ Y'cases_ij l i j 1 := by
      let hh:= Y'cases_exclusive l i j 3 1
      have h_neq : (3:Fin 6) ≠ (1:Fin 6) := by
        norm_cast
      exact hh h_neq h3'
    by_contra h1'
    exact not_h1' ((Y'case1_iff l i j).mpr h1')
  simp [not_h1]
  have not_h5 : ¬ ((j - i) = -1) := by
    have not_h2' : ¬ Y'cases_ij l i j 5 := by
      let hh:= Y'cases_exclusive l i j 3 5
      have h_neq : (3:Fin 6) ≠ (5:Fin 6) := by
        norm_cast
      exact hh h_neq h3'
    by_contra h2'
    exact not_h2' ((Y'case5_iff l i j).mpr h2')
  simp [not_h5]
  have not_h2 : ¬ ((j - i) ≥ 2 ∧ (j - i) ≤ 2*l+2) := by
    have not_h3' : ¬ Y'cases_ij l i j 2 := by
      let hh:= Y'cases_exclusive l i j 3 2
      have h_neq : (3:Fin 6) ≠ (2:Fin 6) := by
        norm_cast
      exact hh h_neq h3'
    by_contra h3'
    exact not_h3' ((Y'case2_iff l i j).mpr h3')
  simp [not_h2]
  have not_h4 : ¬ ((j - i) ≤ -2 ∧ (j - i) ≥ -(2*l+2)) := by
    have not_h4' : ¬ Y'cases_ij l i j 4 := by
      let hh:= Y'cases_exclusive l i j 3 4
      have h_neq : (3:Fin 6) ≠ (4:Fin 6) := by
        norm_cast
      exact hh h_neq h3'
    by_contra h4'
    exact not_h4' ((Y'case4_iff l i j).mpr h4')
  have not_h4'': ¬ ((j - i) ≤ -2 ∧ -(2:Fin (4*l + 6)) + -(2*l) ≤ (j - i) ) := by
    have hh: -(2*(l:Fin (4*l + 6)) +2) = (-(2:Fin (4*l + 6)) + -(2*l)) := by
      rw [←neg_add_rev]
    rw [←hh]
    have hhh: (j-i≥ -(2*(l:Fin (4*l + 6)) +2)) ↔ (-(2*(l:Fin (4*l + 6)) +2) ≤ (j - i) ) := by
      rw [ge_iff_le]
    rw [←hhh]
    exact not_h4
  simp [not_h4'']
  simp [h3]
  have hh: i%2 = 0 ↔ i.val % 2 = 0 := by
    rw [Fin.ext_iff]
    norm_cast
  simp [hh]
lemma Y'value_case3A (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 3 ∧ Y'caseA l i → Y' l i j = -1 := by
  intro h_case
  let h1:= h_case.1
  let h2:= h_case.2
  have h_caseA : i.val % 2 = 0 := by
      exact h2
  let h_y3 := Y'value_case3 l i j h1
  rw [h_y3]
  simp [h_caseA]
lemma Y'value_case3B (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 3 ∧ Y'caseB l i → Y' l i j = 1 := by
  intro h_case
  let h1:= h_case.1
  let h2:= h_case.2
  have h_caseB : i.val % 2 = 1 := by
      exact h2
  let h_y3 := Y'value_case3 l i j h1
  rw [h_y3]
  simp [h_caseB]
lemma Y'value_case4 (l:ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 4 → Y' l i j = -1 := by
  unfold Y'cases_ij
  intro h_case
  unfold Y'
  let h1:= h_case
  unfold Y'f Y'g at h1
  let l' := (l : Fin (4*l + 6))
  have h3 : ![0, 1, 2, 2 * l' + 3, 2 * l' + 4, 4 * l' + 5] 4 = 2*l'+4 := by
    norm_cast
  rw [h3] at h1
  have h4 : ![0, 1, 2 * l' + 2, 2 * l' + 3, 4 * l' + 4, 4 * l' + 5] 4 = 4*l'+4 := by
    norm_cast
  rw [h4] at h1
  have h7': l' = (l: Fin (4*l + 6)) := by
        rfl
  have h6: 4*l'+4 = -2 := by
      rw [h7']
      norm_cast
  have h7: 2*l'+4 = -(2*l+2) := by
    have h8: l' = (l: Fin (4*l + 6)) := by
      rfl
    rw [h8]
    rw [←add_eq_zero_iff_eq_neg]
    norm_cast
    rw [Nat.add_add_add_comm]
    simp only [Nat.reduceAdd, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    norm_cast
    rw [← Nat.left_distrib]
    have h9 : 2*(l+l) = 4*l := by omega
    rw [h9]
    norm_num
  have h8 : (j - i) ≤ -2 ∧ (j - i) ≥ -(2*l+2) := by
    rw [h6, h7] at h1
    exact (And.comm.mp h1)
  have h9 : ¬ (j-i = 1) := by
    have h10 : (j - i) ≥ -(2*l+2) := by
      exact h8.2
    have h11: (j - i) ≥ 2*l'+4 := by
      rw [←h7] at h10
      exact h10
    by_contra h_eq
    rw [h_eq] at h11
    have not_h7 : ¬ (1≥ 2*l'+4) := by
      norm_num
      have h12: ((2*l+4:ℕ):Fin (4*l+6))=2*l'+4  := by
        --norm_num
        simp [h7']
      let h13 := lt_nat_fin' l 1 (2*l+4) (by omega) (by omega)
      rw [h12] at h13
      exact h13
    exact not_h7 h11
  simp [h9]
  have h10: ¬ (j-i = -1) := by
    have h11 : (j - i) ≤ -2 := by
      exact h8.1
    have h12: (j - i) ≤ 4*l'+4 := by
      rw [←h6] at h11
      exact h11
    by_contra h_eq
    rw [h_eq] at h12
    have not_h7 : ¬ (-1 ≤ 4*l'+4) := by
      norm_num
      have h13: ((4*l+4:ℕ):Fin (4*l+6))=4*l'+4  := by
        simp [h7']
      let h14 := lt_nat_fin' l (4*l+4) (4*l+5) (by omega) (by omega)
      rw [h13] at h14
      exact h14
    exact not_h7 h12
  simp [h10]
  have h11: ¬ ( (j - i) ≤ 2*l+2) := by
    by_contra h_eq
    have h12 : (j - i) ≥  2*l+4 := by
      have h12:  2*(l:Fin (4*l+6))+4 = -(2*l+2) := by
        rw [←add_eq_zero_iff_eq_neg]
        norm_cast
        rw [Nat.add_add_add_comm]
        simp only [Nat.reduceAdd, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        norm_cast
        rw [← Nat.left_distrib]
        have h13 : 2*(l+l) = 4*l := by omega
        rw [h13]
        norm_num
      let h82 := h8.2
      rw [←h12] at h82
      exact h82
    have h13 : 2*(l:Fin (4*l+6))+4 ≤  2*l+2  := by
      let h14 := Nat.le_trans (Fin.le_iff_val_le_val.mp h12) (Fin.le_iff_val_le_val.mp h_eq)
      exact h14
    have not_h13 : ¬ (2*(l:Fin (4*l+6))+4 ≤ 2*l+2) := by
      let h16 := lt_nat_fin' l (2*l+2) (2*l+4) (by omega) (by omega)
      norm_cast at h16
      norm_num at h16
      simp only [not_le, gt_iff_lt]
      exact h16
    exact not_h13 h13
  simp [h11]
  simp [h8.1]
  have h12 : ¬ ((j-i) < -2 + -(2*(l:Fin (4*l+6)))) := by
    have h13 : (j - i) ≥ -(2*l+2) := by
      exact h8.2
    simp [not_le.mpr]
    have h14: -(2*(l:Fin (4*l+6))+2) = -2  + - (2*l) := by
      rw [neg_add_rev]
    rw [h14] at h13
    exact h13
  simp [h12]
lemma Y'value_case5A (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 5 ∧ Y'caseA l i → Y' l i j = -1 := by
  unfold Y'cases_ij
  intro h_case5A
  let h_case:= h_case5A.1
  unfold Y'
  unfold Y'f Y'g at h_case
  have h3 : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 5 = 4*(l : Fin (4*l + 6))+5 := by
    norm_cast
  rw [h3] at h_case
  have h4 : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 5 = 4*(l : Fin (4*l + 6))+5 := by
    norm_cast
  rw [h4] at h_case
  have h5: j-i = 4*(l : Fin (4*l + 6))+5 := by
    have h_eq : (j - i) ≤ 4*(l : Fin (4*l + 6))+5 := by
      exact h_case.2
    have h_ge : (j - i) ≥ 4*(l : Fin (4*l + 6))+5 := by
      exact h_case.1
    exact le_antisymm h_eq h_ge
  have h6: 4*(l : Fin (4*l + 6))+5 = -1 := by
      rw [←add_eq_zero_iff_eq_neg]
      norm_cast
      have h7: 4*l+5 +1 = 4*l+6 := by
        omega
      simp [h7]
  simp [h6] at h5
  have h5': Y'cases_ij l i j 5 := by
    exact (Y'case5_iff l i j).mpr h5
  have not_h1 : ¬ ((j - i) = 1) := by
    have not_h1' : ¬ Y'cases_ij l i j 1 := by
      let hh:= Y'cases_exclusive l i j 5 1
      have h_neq : (5:Fin 6) ≠ (1:Fin 6) := by
        norm_cast
      exact hh h_neq h5'
    by_contra h1'
    exact not_h1' ((Y'case1_iff l i j).mpr h1')
  simp [not_h1]
  simp [h5]
  let h2:= h_case5A.2
  unfold Y'caseA at h2
  rw [Fin.ext_iff]
  simp [h2]
lemma Y'value_case5B (l : ℕ) (i j : Fin (4 * l + 6)) : Y'cases_ij l i j 5 ∧ Y'caseB l i → Y' l i j = -2 := by
  unfold Y'cases_ij
  intro h_case5B
  let h_case:= h_case5B.1
  unfold Y'
  unfold Y'f Y'g at h_case
  have h3 : ![0, 1, 2, 2 * (l : Fin (4*l + 6)) + 3, 2 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 5 = 4*(l : Fin (4*l + 6))+5 := by
    norm_cast
  rw [h3] at h_case
  have h4 : ![0, 1, 2 * (l : Fin (4*l + 6)) + 2, 2 * (l : Fin (4*l + 6)) + 3, 4 * (l : Fin (4*l + 6)) + 4, 4 * (l : Fin (4*l + 6)) + 5] 5 = 4*(l : Fin (4*l + 6))+5 := by
    norm_cast
  rw [h4] at h_case
  have h5: j-i = 4*(l : Fin (4*l + 6))+5 := by
    have h_eq : (j - i) ≤ 4*(l : Fin (4*l + 6))+5 := by
      exact h_case.2
    have h_ge : (j - i) ≥ 4*(l : Fin (4*l + 6))+5 := by
      exact h_case.1
    exact le_antisymm h_eq h_ge
  have h6: 4*(l : Fin (4*l + 6))+5 = -1 := by
      rw [←add_eq_zero_iff_eq_neg]
      norm_cast
      have h7: 4*l+5 +1 = 4*l+6 := by
        omega
      simp [h7]
  simp [h6] at h5
  have h5': Y'cases_ij l i j 5 := by
    exact (Y'case5_iff l i j).mpr h5
  have not_h1 : ¬ ((j - i) = 1) := by
    have not_h1' : ¬ Y'cases_ij l i j 1 := by
      let hh:= Y'cases_exclusive l i j 5 1
      have h_neq : (5:Fin 6) ≠ (1:Fin 6) := by
        norm_cast
      exact hh h_neq h5'
    by_contra h1'
    exact not_h1' ((Y'case1_iff l i j).mpr h1')
  simp [not_h1]
  simp [h5]
  let h2:= h_case5B.2
  unfold Y'caseB at h2
  rw [Fin.ext_iff]
  simp [h2]

lemma Y'skew_symmetric (l:ℕ): ∀ (i j : Fin (4 * l + 6)), Y' l i j = - (Y' l j i) := by
  intros i j
  obtain ⟨k, h⟩ := Y'cases1to6_exhaustive l i j
  fin_cases k
  · have hij: Y' l i j = 0 := by
      exact Y'value_case0 l i j h
    rw [hij]
    have h' : Y'cases_ij l j i 0 := by
      exact Y'skewCase0 l i j h
    have hji: Y' l j i = 0 := by
      exact Y'value_case0 l j i h'
    rw [hji]
    norm_num
  · by_cases h_caseA : Y'caseA l i
    · have hij: Y' l i j = 2 := by
        exact Y'value_case1A l i j ⟨h, h_caseA⟩
      rw [hij]
      have hji: Y' l j i = -2 := by
        have h_case5B : Y'cases_ij l j i 5 ∧ Y'caseB l j := by
          exact Y'skewCase1A l i j ⟨h, h_caseA⟩
        exact Y'value_case5B l j i h_case5B
      rw [hji]
      norm_num
    · let h_caseB := Y'notA_impliesB l i h_caseA
      have hij: Y' l i j = 1 := by
        exact Y'value_case1B l i j ⟨h, h_caseB⟩
      rw [hij]
      have hji: Y' l j i = -1 := by
        have h_case5A : Y'cases_ij l j i 5 ∧ Y'caseA l j := by
          exact Y'skewCase1B l i j ⟨h, h_caseB⟩
        exact Y'value_case5A l j i h_case5A
      rw [hji]
      norm_num
  · have hij: Y' l i j = 1 := by
      exact Y'value_case2 l i j h
    rw [hij]
    have hji: Y' l j i = -1 := by
      have h_case4 : Y'cases_ij l j i 4 := by
        exact Y'skewCase2 l i j h
      exact Y'value_case4 l j i h_case4
    rw [hji]
    norm_num
  · by_cases h_caseA : Y'caseA l i
    · have hij: Y' l i j = -1 := by
        exact Y'value_case3A l i j ⟨h, h_caseA⟩
      rw [hij]
      have hji: Y' l j i = 1 := by
        have h_case3B : Y'cases_ij l j i 3 ∧ Y'caseB l j := by
          exact Y'skewCase3A l i j ⟨h, h_caseA⟩
        exact Y'value_case3B l j i h_case3B
      rw [hji]
    · let h_caseB := Y'notA_impliesB l i h_caseA
      have hij: Y' l i j = 1 := by
        exact Y'value_case3B l i j ⟨h, h_caseB⟩
      rw [hij]
      have hji: Y' l j i = -1 := by
        have h_case3A : Y'cases_ij l j i 3 ∧ Y'caseA l j := by
          exact Y'skewCase3B l i j ⟨h, h_caseB⟩
        exact Y'value_case3A l j i h_case3A
      rw [hji]
      norm_num
  · have hij: Y' l i j = -1 := by
      exact Y'value_case4 l i j h
    rw [hij]
    have hji: Y' l j i = 1 := by
      have h_case2 : Y'cases_ij l j i 2 := by
        exact Y'skewCase4 l i j h
      exact Y'value_case2 l j i h_case2
    rw [hji]
  · by_cases h_caseA : Y'caseA l i
    · have hij: Y' l i j = -1 := by
        exact Y'value_case5A l i j ⟨h, h_caseA⟩
      rw [hij]
      have hji: Y' l j i = 1 := by
        have h_case1B : Y'cases_ij l j i 1 ∧ Y'caseB l j := by
          exact Y'skewCase5A l i j ⟨h, h_caseA⟩
        exact Y'value_case1B l j i h_case1B
      rw [hji]
    · let h_caseB := Y'notA_impliesB l i h_caseA
      have hij: Y' l i j = -2 := by
        exact Y'value_case5B l i j ⟨h, h_caseB⟩
      rw [hij]
      have hji: Y' l j i = 2 := by
        have h_case1A : Y'cases_ij l j i 1 ∧ Y'caseA l j := by
          exact Y'skewCase5B l i j ⟨h, h_caseB⟩
        exact Y'value_case1A l j i h_case1A
      rw [hji]
