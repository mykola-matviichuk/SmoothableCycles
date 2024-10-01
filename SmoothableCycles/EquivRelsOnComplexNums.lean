import Mathlib.Analysis.Complex.Basic

def rational_ratio (a b: ℂ ) : Prop := ∃ q : ℚ, a= q*b


lemma rational_ratio_trans  (a b c : ℂ ) :
  (rational_ratio a b) → (rational_ratio b c) → (rational_ratio a c) :=
  by
    intros h₁ h₂
    obtain ⟨q₁, hq₁⟩ := h₁
    obtain ⟨q₂, hq₂⟩ := h₂
    use q₁ * q₂
    simp only [Rat.cast_mul]
    simp_all only
    exact Eq.symm (mul_assoc (↑q₁) (↑q₂) c)

lemma cancel_inv_left (b : ℂ) (p : ℚ) (left : p≠ 0) : b = ↑p * ((↑p)⁻¹* b) := by
  rw [mul_inv_cancel_left₀ ]
  exact Rat.cast_ne_zero.mpr left

lemma cancel_left_inv (b : ℂ) (p : ℚ) (left : p≠ 0) : b = (↑p)⁻¹ * (↑p * b) := by
  rw [← mul_assoc]
  simp_all only [ne_eq, isUnit_iff_ne_zero, Rat.cast_eq_zero, not_false_eq_true, IsUnit.inv_mul_cancel, one_mul]

lemma rational_ratio_symm (a b : ℂ) (an0: a≠ 0) :
  (rational_ratio a b) → (rational_ratio b a) := by
    intros h
    obtain ⟨q, s⟩ := h
    use 1/q
    have qn0: q≠ 0 := by
      simp_all only [ne_eq, mul_eq_zero, Rat.cast_eq_zero, not_or, not_false_eq_true]
    simp_all only [one_div, Rat.cast_inv]
    exact cancel_left_inv b q qn0

lemma zero_rational_ratio (a b : ℂ) (a0:a=0): rational_ratio a b := by
  use 0
  simp_all only [Rat.cast_zero, zero_mul]

def positive_ratio (a b: ℂ ) : Prop := ∃ q : ℚ, q>0 ∧ a= q*b



theorem positive_ratio_symm (a b: ℂ) :
  (positive_ratio a b) → (positive_ratio b a) := by
    intro h
    obtain ⟨ p, hp ⟩ := h
    use 1/p
    constructor
    . case h.left => simp only [one_div, gt_iff_lt, inv_pos]; linarith
    . { case h.right =>
        rw [hp.2]
        simp_all only [gt_iff_lt, one_div, Rat.cast_inv]
        apply cancel_left_inv
        linarith
        }

theorem positive_ratio_trans  (a b c : ℂ ) :
  (positive_ratio a b) → (positive_ratio b c) → (positive_ratio a c) :=
  by
    intros h₁ h₂
    obtain ⟨q₁, hq₁⟩ := h₁
    obtain ⟨q₂, hq₂⟩ := h₂
    use q₁ * q₂
    constructor
    . case h.left => simp_all only [gt_iff_lt, mul_pos_iff_of_pos_left]
    . case h.right =>
     simp_all only [gt_iff_lt, Rat.cast_mul]
     exact Eq.symm (mul_assoc (↑q₁) (↑q₂) c)



def negative_ratio (a b: ℂ ) : Prop := ∃ q : ℚ, q<0 ∧ a= q*b

theorem cancel_one_vs_notone (b : ℂ) (bn0 : b≠0) : (∃ pr : ℚ, pr<0 ∧  b = ↑pr * b) → False := by
  simp_all only [ne_eq, not_false_eq_true, right_eq_mul₀, imp_false, not_exists, not_and]
  by_contra!
  obtain ⟨ x, x1 ⟩ := this
  have xeq1 : x=1 := by
    obtain heq11 := x1.right
    norm_cast at heq11
  linarith

theorem positive_ratio_negative_ratio_gives_false (a b : ℂ) (bn0 : b≠0)  :
  (positive_ratio a b) → (negative_ratio a b) → False := by
    intros hpos hneg
    obtain hposrev := positive_ratio_symm a b hpos
    obtain ⟨ p, hb ⟩ := hposrev
    obtain ⟨ r, hc ⟩ := hneg
    have prb: ∃ pr : ℚ, pr<0 ∧  b = ↑pr * b := by
      use p*r
      constructor
      · obtain tt := mul_neg_of_pos_of_neg hb.left hc.left; exact tt
      · simp only [Rat.cast_mul]; rw [mul_assoc]; rw [hc.right.symm]; exact hb.right
    apply cancel_one_vs_notone b bn0 prb


theorem negative_ratio_negative_ratio_gives_positive_ratio  (a b c : ℂ ) :
  (negative_ratio a b) → (negative_ratio b c) → (positive_ratio a c) := by
    intros h₁ h₂
    obtain ⟨q₁, hq₁⟩ := h₁
    obtain ⟨q₂, hq₂⟩ := h₂
    use q₁ * q₂
    constructor
    · obtain negq₁ := hq₁.left
      obtain negq₂ := hq₂.left
      exact mul_pos_of_neg_of_neg negq₁ negq₂
    · simp_all only [gt_iff_lt]
      simp_all only [Rat.cast_mul]
      exact Eq.symm (mul_assoc (↑q₁) (↑q₂) c)

theorem negative_ratio_trans (a b c : ℂ ) (cn0 : c≠0) :
  (negative_ratio a b) → (negative_ratio b c) → (negative_ratio a c) → False :=
  by
    intros h₁ h₂ h₃
    obtain prac := negative_ratio_negative_ratio_gives_positive_ratio a b c h₁ h₂
    exact positive_ratio_negative_ratio_gives_false a c cn0 prac h₃

----------some lemmas on complex numbers------
lemma mult_zero_right (a : ℂ) : a*0=0 := by
  exact CommMonoidWithZero.mul_zero a

lemma mult_zero_left (a : ℂ) : 0*a=0 := by
  exact zero_mul a

lemma coersionDistrSubtractLeft  (r₁ r₂:ℚ)(c:ℂ): ↑(r₁-r₂)*c = ↑r₁*c-↑r₂*c := by
  simp_all only [Rat.cast_sub]
  exact sub_mul (↑r₁) (↑r₂) c

lemma manipulation1 : ∀ (x y z: ℂ), (-x+y=z) → (x = y - z):= by
  simp_all only [forall_eq', sub_add_cancel_right, neg_neg, implies_true]

lemma Nminus1LessThanN (n: Nat)(nn0:n≠ 0): n-1 < n := by
  omega
