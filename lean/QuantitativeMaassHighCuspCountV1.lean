module

public import QuantitativeMaassHighCuspDisplacementV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels QuantitativeArithmeticMaassOverlap
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- Upper-triangular actual projective elements are counted by one bounded
integer parameter and their diagonal sign. The harmless factor three keeps
the finite encoding in an ordinary integer interval. -/
theorem gamma_upper_triangular_card_bound (N B : ℕ) (S : Finset (gamma N))
    (hc : ∀ g∈S,(representative g) 1 0=0)
    (hb : ∀ g∈S,|(representative g) 0 1|≤(B:ℤ)) :
    S.card≤3*(2*B+1) := by
  classical
  let D : Finset ℤ := Finset.Icc (-1) 1
  let J : Finset ℤ := Finset.Icc (-(B:ℤ)) B
  have hd (g : gamma N) (hg : g∈S) :
      (representative g) 1 1=(representative g) 0 0 ∧ (representative g) 0 0∈D := by
    rcases integral_upper_triangular_diagonal (representative g) (hc g hg) with ⟨ha,he⟩ | ⟨ha,he⟩
    · simp only [ha,he,D,Finset.mem_Icc]
      norm_num
    · simp only [ha,he,D,Finset.mem_Icc]
      norm_num
  let enc : S → D × J := fun g =>
    (⟨(representative g.val) 0 0,(hd g.val g.property).2⟩,
     ⟨(representative g.val) 0 1,Finset.mem_Icc.mpr (abs_le.mp (hb g.val g.property))⟩)
  have hinj : Function.Injective enc := by
    intro g h he
    have ha : (representative g.val) 0 0=(representative h.val) 0 0 :=
      congrArg (fun q : D × J => q.1.val) he
    have hb' : (representative g.val) 0 1=(representative h.val) 0 1 :=
      congrArg (fun q : D × J => q.2.val) he
    apply Subtype.ext
    apply representative_injective N
    apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j
    · exact ha
    · exact hb'
    · exact (hc g.val g.property).trans (hc h.val h.property).symm
    · exact (hd g.val g.property).1.trans (ha.trans (hd h.val h.property).1.symm)
  have hD : Fintype.card D=3 := by norm_num [D,Int.card_Icc]
  have hJ : Fintype.card J=2*B+1 := by
    simp only [Fintype.card_coe,J,Int.card_Icc]
    omega
  have hh := Fintype.card_le_of_injective enc hinj
  simpa only [Fintype.card_coe,Fintype.card_prod,hD,hJ] using hh

/-- The actual short-return count grows only linearly in height above the
fixed propagation threshold, uniformly in the congruence level. -/
theorem diagonalOrbitSet_high_cusp_card (N : ℕ) (z : ℍ) (R : ℝ)
    (hz : Real.exp (R/2)<z.im) :
    (diagonalOrbitSet N z R).card≤3*(2*⌈z.im*(Real.exp R-1)⌉₊+1) := by
  apply gamma_upper_triangular_card_bound
  · intro g hg
    have hd := (mem_diagonalOrbitSet N z R g).mp hg
    have he : representative g•z=g•z := by
      rw [← integralLabel_action,representative_label]
      rfl
    exact integral_high_cusp_lowerleft_zero (representative g) z R (he ▸ hd) hz
  · intro g hg
    have hd := (mem_diagonalOrbitSet N z R g).mp hg
    have he : representative g•z=g•z := by
      rw [← integralLabel_action,representative_label]
      rfl
    have hh := (integral_high_cusp_upperright_bound (representative g) z R (he ▸ hd) hz).trans
      (Nat.le_ceil (z.im*(Real.exp R-1)))
    exact_mod_cast hh

/-- A real-valued linear-height majorant, ready for integration against the
hyperbolic cusp measure. -/
theorem diagonalOrbitSet_high_cusp_card_real (N : ℕ) (z : ℍ) (R : ℝ)
    (hR : 0≤R) (hz : Real.exp (R/2)<z.im) :
    ((diagonalOrbitSet N z R).card:ℝ)≤6*z.im*(Real.exp R-1)+9 := by
  have h := diagonalOrbitSet_high_cusp_card N z R hz
  have hh : ((diagonalOrbitSet N z R).card:ℝ)≤3*(2*(⌈z.im*(Real.exp R-1)⌉₊:ℝ)+1) := by
    exact_mod_cast h
  have hn : 0≤z.im*(Real.exp R-1) :=
    mul_nonneg z.im_pos.le (sub_nonneg.mpr (Real.one_le_exp hR))
  have hb := Nat.ceil_lt_add_one hn
  nlinarith

#print axioms gamma_upper_triangular_card_bound
#print axioms diagonalOrbitSet_high_cusp_card
#print axioms diagonalOrbitSet_high_cusp_card_real

end QuantitativeMaass
