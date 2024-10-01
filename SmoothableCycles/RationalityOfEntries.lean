
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Analysis.Complex.Basic
import SmoothableCycles.Basic
import SmoothableCycles.EquivRelsOnComplexNums


variable {V : Type*}
variable {B : V → V → ℂ}

def Path (V) := List V

def validPath (hB: ∀ i j, B i j = - B j i) (p : Path V) : Prop :=
  ∀ (i : Nat), (hl: i < p.length - 1) →
    (smoothableGraph B hB).Adj (p.get ⟨i, by omega⟩) (p.get ⟨i+1, by omega⟩)



def pathConnectsVertices (hB: ∀ i j, B i j = - B j i) (p: Path V) (i j: V): Prop :=
   ∃ (hl : p.length > 0), validPath hB p ∧ p.get ⟨0, by omega⟩ = i ∧ p.get ⟨p.length-1, by omega⟩ = j

def verticesConnected_n (hB: ∀ i j, B i j = - B j i) (i j: V) (n:ℕ): Prop :=
  ∃ (p : Path V), (p.length = n) ∧ pathConnectsVertices hB p i j

def verticesConnected (hB: ∀ i j, B i j = - B j i) (i j: V): Prop :=
  ∃ n : ℕ, verticesConnected_n hB i j (n+1)

lemma pathLength1HeadEqTail (hB: ∀ i j, B i j = - B j i): ∀ (p: Path V) (i j : V),
  pathConnectsVertices hB p i j → p.length=1 → i=j := by
    intro p i j  pij pl1
    obtain ⟨ hl, pdef⟩ := pij
    obtain hh := pdef.left
    obtain h4 := pdef.right.right
    simp_all only [List.get_eq_getElem, le_refl, tsub_eq_zero_of_le, true_and]


def graphConnected (hB: ∀ i j, B i j = - B j i) : Prop :=
  ∀ (i j : V), verticesConnected hB i j

lemma BiiZero (hB : ∀ i j, B i j = - B j i) (k:V): B k k = 0 := by
  exact CharZero.eq_neg_self_iff.mp (hB k k)

lemma existenceOfColoredEdge (hB) (i j: V) : graphConnected hB → B i j ≠ 0 →
  ∃ (k l : V), (smoothableGraph B hB).Adj k l := by
    intro hc bijn0
    obtain ⟨ n, pconn⟩ := hc i j
    obtain ⟨ p, pdef⟩ := pconn
    have nn0: n≠ 0 := by
      by_contra! n0
      have pl1: p.length =1 := by linarith
      have iej: i=j := pathLength1HeadEqTail hB p i j pdef.right pl1
      have bij0 : B i j = 0 := by
        have hh := BiiZero hB i
        exact (AddSemiconjBy.eq_zero_iff (B i i) (congrFun (congrArg HAdd.hAdd (congrArg (B i) iej)) (B i i))).mp hh
      exact bijn0 bij0
    use (p.get ⟨0,by omega⟩)
    use (p.get ⟨1, by omega⟩ )
    obtain ⟨hl, h3⟩ := pdef.right
    have hl' : 0 < p.length -1 := by omega
    exact h3.left 0 hl'




lemma rationalityAdjacentColoredEdges (hB) :
  ∀ (i j k : V), (smoothableGraph B hB).Adj i j → (smoothableGraph B hB).Adj j k →
  rational_ratio (B i j)  (B j k) := by
  intros i j k hij hjk
  by_cases h : i=k
  · use -1
    rw [h, hB]
    exact Mathlib.Tactic.Ring.neg_one_mul rfl
  · obtain ⟨ q, rat⟩:= lem_3point1_part2 hB h hij hjk
    use q
    rw [←rat.right]
    exact Eq.symm (Rat.cast_comm q (B j k))

lemma rationalityColoredEdgesMatching (hB) :
  ∀ (i j₁ j₂ k : V), (h12: j₁=j₂) → (smoothableGraph B hB).Adj i j₁ → (smoothableGraph B hB).Adj j₂ k →
  rational_ratio (B i j₁)  (B j₂ k) := by
    intro i j₁ j₂ k h12 hij₁ hj₂k
    --have be: (B j₁ k) = (B j₂ k):= by
    --  exact congrFun (congrArg B h12) k
    obtain h : rational_ratio (B i j₁) (B j₁ k) := by
      obtain hh := rationalityAdjacentColoredEdges hB i j₁ k hij₁
      obtain hj₁k : (smoothableGraph B hB).Adj j₁ k := by
        rw [h12]
        exact hj₂k
      exact hh hj₁k
    rw [←h12]
    exact h

lemma rationalExtendByOneColoredEdge (hB) :
  ∀ (i j k: V) (b: ℂ), rational_ratio (B i j) b → (smoothableGraph B hB).Adj j k →
  rational_ratio (B j k) b → rational_ratio (B i k) b := by
    intro i j k b hbij hjk hbjk
    obtain h := (smoothableGraph_adj hB).mp hjk
    obtain hjkne := h.left
    --match
    by_cases ije : i=j
    · rw [ije]
      exact hbjk
    · obtain hh := h.right i ije
      by_cases ike: i=k
      · have bik0: B i k = 0 := by
          have bii0: B i i = 0 := CharZero.eq_neg_self_iff.mp (hB i i)
          rw [←ike]
          exact bii0
        use 0
        rw [bik0]
        simp only [Rat.cast_zero, zero_mul]
      · obtain ⟨ n, hhh⟩ := hh ike
        obtain ⟨p, ijbeq⟩ := hbij
        obtain ⟨q, jkbeq⟩ := hbjk
        use p - n*q
        have bikskew : B k i = - B i k := hB k i
        have eq: B i k = ↑(p - ↑n * q) * b := by
          have eq1 : (B k i + ↑p * b) / (↑q * b) = ↑n := by
            rw [←ijbeq, ←jkbeq]
            exact hhh
          have eq2 : B k i + ↑p * b = ↑n * (↑q * b) := by
            rw [←eq1]
            have eq2' : (↑q*b)≠ 0 := by
              exact Ne.symm (ne_of_ne_of_eq (id (Ne.symm hjkne)) jkbeq)
            have eq2'': ∀ (x y:ℂ) (yn0:y≠ 0), x = x/y*y := by
              exact fun x y yn0 ↦ Eq.symm (div_mul_cancel₀ x yn0)
            obtain eq3 := eq2'' (B k i + ↑p * b) (↑q*b) eq2'
            exact eq3
          obtain eq3 := coersionDistrSubtractLeft p (↑n*q) b
          rw [eq3]
          simp only [Rat.cast_mul, Rat.cast_natCast]
          rw [bikskew] at eq2
          have eq4: B i k = ↑p*b -↑n*(↑q*b):= manipulation1 (B i k) (↑p*b) (↑n*(↑q*b)) eq2
          rw [eq4]
          simp only [sub_right_inj]
          exact Eq.symm (mul_assoc (↑n) (↑q) b)
        exact eq


lemma rationalityColoredEdges (hB) :
  graphConnected hB → ∀ (i₁ j₁ i₂ j₂ : V), (smoothableGraph B hB).Adj i₁ j₁
  → (smoothableGraph B hB).Adj i₂ j₂ → rational_ratio (B i₁ j₁)  (B i₂ j₂) := by
    intros hc i₁ j₁ i₂ j₂ hi₁j₁ hi₂j₂
    obtain ⟨ n, p, h⟩   := hc j₁ i₂
    match nv:n with
    | 0 =>
      have j1i2 : j₁=i₂ := by
        obtain ⟨ plpos, hh⟩ := h.right
        have pl0: p.length=1 := by linarith
        simp_all only [zero_add, true_and, List.get_eq_getElem, le_refl, tsub_eq_zero_of_le]
        obtain hhl := hh.left
        obtain hhm := hh.right.left
        simp_all only [true_and]
      have hj₁j₂ : (smoothableGraph B hB).Adj j₁ j₂ := by
        simp_all only [zero_add]
      obtain hhh := rationalityAdjacentColoredEdges hB i₁ j₁ j₂ hi₁j₁ hj₁j₂
      rw [←j1i2]
      exact hhh
    | n'+1 =>
      have ind: ∀ k:ℕ, (kbound:k<n'+1) →
      rational_ratio (B i₁ j₁) (B (p.get ⟨k, by omega⟩) (p.get ⟨k+1,by omega⟩ ))
      := by
        intro k
        induction k with
        | zero =>
          intro kbound
          obtain ⟨ _, hh⟩  := h.right
          have hj₁pk : j₁ = p.get ⟨0, by omega⟩ := by rw [hh.right.left]
          obtain hhh := rationalityAdjacentColoredEdges hB i₁ j₁ (p.get ⟨1,by omega⟩ ) hi₁j₁
          have hl: 0<p.length-1 := by omega
          obtain smp0p1 := hh.left 0 hl
          rw [←hj₁pk] at smp0p1
          rw [←hj₁pk]
          exact hhh smp0p1
        | succ k' ih =>
          intro kbound
          have kbound': k'<n'+1 := by omega
          obtain ih' := ih kbound'
          have ih'' : rational_ratio (B (p.get ⟨k', by omega⟩) (p.get ⟨k'+1,by omega⟩ )) (B (p.get ⟨k'+1, by omega⟩) (p.get ⟨k'+1+1,by omega⟩ )) :=
          by
            obtain h4 := rationalityAdjacentColoredEdges hB (p.get ⟨k', by omega⟩) (p.get ⟨k'+1,by omega⟩ ) (p.get ⟨k'+1+1, by omega⟩)
            have smkk1: (smoothableGraph B hB).Adj (List.get p ⟨k',by omega⟩) (List.get p ⟨k' + 1, by omega⟩) :=
              by
                have kpbound : k'< List.length p - 1 := by omega
                obtain ⟨ hl, h5 ⟩ := h.right
                exact h5.left k' kpbound
            have smk1k2: (smoothableGraph B hB).Adj (List.get p ⟨k'+1,by omega⟩) (List.get p ⟨k' + 1+1, by omega⟩) :=
              by
                have kpbound : k'+1 < List.length p - 1 := by omega
                obtain ⟨ hl, h5 ⟩ := h.right
                exact h5.left (k'+1) kpbound
            exact h4 smkk1 smk1k2
          obtain h7 := rational_ratio_trans (B i₁ j₁) (B (List.get p ⟨k', by omega⟩) (List.get p ⟨k' + 1, by omega ⟩)) (B (List.get p ⟨k' + 1, by omega⟩) (List.get p ⟨k' + 1 + 1, by omega ⟩))--(List.get p ⟨k',by omega⟩) (List.get p ⟨k' + 1, by omega⟩) (List.get p ⟨k'+1+1,by omega⟩)
          exact h7 ih' ih''
      obtain le : ∃ ell, ell=p.get ⟨ n', by omega⟩ := by
        use p.get ⟨n', by omega⟩
      obtain ⟨ ell, elldef⟩ := le
      have i₂e :i₂=p.get ⟨ n'+1, by omega⟩ := by
        obtain ⟨_,hh⟩ := h.right
        obtain hhh:= hh.right.right
        obtain hl: n'+1 =p.length -1 := by omega
        obtain hll: p.get ⟨n'+1, by omega⟩ = p.get ⟨ p.length-1, by omega⟩ := by
          simp only [List.get_eq_getElem]
          exact getElem_congr hl
        rw [hll]
        exact id (Eq.symm hhh)
      have kbound:n'<n'+1 := by omega
      obtain hi₁j₁li₂ := ind n' kbound
      rw [←i₂e,←elldef] at hi₁j₁li₂
      have hli₂j₂ : rational_ratio (B ell i₂) (B i₂ j₂) := by
        obtain hh:= rationalityAdjacentColoredEdges hB ell i₂ j₂
        have helli₂ : (smoothableGraph B hB).Adj ell i₂ := by
          rw [i₂e,elldef]
          obtain ⟨hl,hhh⟩  := h.right
          have hl' : n' < p.length - 1 := by omega
          exact hhh.left n' hl'
        exact hh helli₂ hi₂j₂
      exact rational_ratio_trans (B i₁ j₁) (B ell i₂) (B i₂ j₂) hi₁j₁li₂ hli₂j₂


lemma rationalityRelativeToColoredEdge (hB) :
  graphConnected hB → ∀ (i₁ j₁ i₂ j₂ : V),
  (smoothableGraph B hB).Adj i₁ j₁ → rational_ratio (B i₂ j₂) (B i₁ j₁) :=
  by
    intro hc i₁ j₁ i₂ j₂ hi₁j₁
    obtain ⟨ n, hh⟩  := hc i₂ j₂
    obtain ⟨ p, hhh⟩ := hh
    obtain pl := hhh.left
    obtain pj₁j₂ := hhh.right
    obtain ⟨hl, h4⟩ := pj₁j₂
    obtain pv := h4.left
    have aux : ∀ k:ℕ, (kn:k<n) →
    rational_ratio (B (p.get ⟨0,by omega⟩) (p.get ⟨k+1,by omega⟩)) (B i₁ j₁) :=
    by
      intro k kn
      induction k with
      | zero =>
        obtain h5 := rationalityColoredEdges hB hc (p.get ⟨0,by omega⟩) (p.get ⟨0+1,by omega⟩) i₁ j₁
        have hl' : 0 < p.length-1 := by omega
        have h6 := pv 0 hl'
        exact h5 h6 hi₁j₁
      | succ k' ih =>
        have kn':  k' < n := by omega
        obtain hp0pk1i₁j₁ := ih kn'
        have hk1k11: (smoothableGraph B hB).Adj (p.get ⟨k'+1,by omega⟩) (p.get ⟨k'+1+1,by omega⟩) := by
          have hl' : k' + 1 < List.length p - 1 := by omega
          exact pv (k'+1) hl'
        have hk1k11i₁j₁: rational_ratio (B (List.get p ⟨k' + 1,by omega⟩) (List.get p ⟨k' + 1 + 1, by omega⟩)) (B i₁ j₁) :=
          by exact rationalityColoredEdges hB hc (List.get p ⟨k' + 1,by omega⟩) (List.get p ⟨k' + 1 + 1, by omega⟩) i₁ j₁ hk1k11 hi₁j₁
        exact rationalExtendByOneColoredEdge hB (p.get ⟨0,by omega⟩) (p.get ⟨k'+1,by omega⟩) (p.get ⟨k'+1+1,by omega⟩) (B i₁ j₁) hp0pk1i₁j₁ hk1k11 hk1k11i₁j₁
    by_cases i₂ej₂ : i₂=j₂
    · have bi₂j₂zero : B i₂ j₂ = 0 := by
        rw [i₂ej₂]
        exact CharZero.eq_neg_self_iff.mp (hB j₂ j₂)
      use 0
      rw [bi₂j₂zero]
      simp only [Rat.cast_zero, zero_mul]
    · have npos : n≠ 0 := by
        by_contra!
        obtain h5 := h4.right.right
        have i₂eqj₂: i₂ = j₂ := by
          aesop
        exact i₂ej₂ i₂eqj₂
      have kn : n-1 < n := by omega
      obtain h5:= aux (n-1) kn
      have p0i₂ : p.get ⟨0,by omega⟩ = i₂ := h4.right.left
      have pnj₂ : p.get ⟨n-1+1,by omega⟩ = j₂ := by
        obtain h6:= h4.right.right
        have h7: ∀ (p1 p2 : Nat), (p1b: p1<p.length) → (p2b: p2<p.length)→ (p1=p2) → p.get ⟨p1,by omega⟩ = p.get ⟨p2, by omega⟩ :=
          by
            intro p1 p2 p1b p2b p1p2
            simp only [List.get_eq_getElem]
            exact getElem_congr p1p2
        have pl' : n-1+1 = p.length -1 := by omega
        have p1b : n-1+1<p.length := by omega
        have p2b : p.length -1 < p.length := by omega
        obtain h8 := h7 (n-1+1) (p.length-1) p1b p2b pl'
        rw [h8]
        exact h6
      rw [pnj₂,p0i₂] at h5
      exact h5




theorem rationalityEdges (hB: ∀ i j, B i j = - B j i) :
  graphConnected hB → ∀ (i₁ j₁ i₂ j₂ : V),
  (hi₂j₂: B i₂ j₂ ≠ 0) →  rational_ratio  (B i₁ j₁)  (B i₂ j₂) :=
  by
    intro hc i₁ j₁ i₂ j₂ hi₂j₂
    by_cases bi₁j₁e0 : B i₁ j₁ = 0
    · exact zero_rational_ratio (B i₁ j₁) (B i₂ j₂) bi₁j₁e0
    · obtain ⟨ k,l,hkl⟩ := existenceOfColoredEdge hB i₁ j₁ hc bi₁j₁e0
      have hi₁j₁kl : rational_ratio (B i₁ j₁) (B k l) := rationalityRelativeToColoredEdge hB hc k l i₁ j₁ hkl
      have hi₂j₂kl : rational_ratio (B i₂ j₂) (B k l) := rationalityRelativeToColoredEdge hB hc k l i₂ j₂ hkl
      have hkli₂j₂ : rational_ratio (B k l) (B i₂ j₂)  := rational_ratio_symm (B i₂ j₂) (B k l) hi₂j₂ hi₂j₂kl
      exact rational_ratio_trans (B i₁ j₁) (B k l) (B i₂ j₂) hi₁j₁kl hkli₂j₂
