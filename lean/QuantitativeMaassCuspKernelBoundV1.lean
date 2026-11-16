module

public import QuantitativeMaassCuspSingularWeightV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped Topology MatrixGroups

namespace QuantitativeMaass

/-- Cusp conjugation preserves the identity projective element. -/
theorem cuspConjugateFull_one (N : ℕ) (A : SL(2,ℤ)) : cuspConjugateFull N A 1=1 := by
  apply Subtype.ext
  simp [cuspConjugateFull]

/-- The singular displacement bound holds in every actual integral cusp chart. -/
theorem congruence_chart_singular_weight (N : ℕ) (A : SL(2,ℤ)) (g : gamma N) (hg : g≠1)
    (z : ℍ) (R : ℝ) (hd : dist (g•(A•z)) (A•z)≤R) (hz : Real.exp (R/2)<z.im) :
    0<dist (g•(A•z)) (A•z) ∧
      1/Real.sqrt (Real.sinh (dist (g•(A•z)) (A•z)))≤Real.sqrt z.im := by
  have hn : cuspConjugateFull N A g≠1 := by
    intro hh
    apply hg
    exact cuspConjugateFull_injective N A (hh.trans (cuspConjugateFull_one N A).symm)
  have hh := congruence_high_cusp_singular_weight 1 (cuspConjugateFull N A g) hn z R
    (by simpa only [cuspConjugateFull_displacement] using hd) hz
  simpa only [cuspConjugateFull_displacement] using hh

/-- The actual nonidentity radial kernel has a height^(3/2) majorant in
all high-cusp charts. Its profile assumption is the checked off-diagonal
square-root decay bound, ready to instantiate with the moving window. -/
theorem radialNonidentity_high_cusp_bound (N : ℕ) (A : SL(2,ℤ))
    (g : ℝ → ℂ) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R))
    (C : ℝ) (hC : 0≤C) (hb : ∀ d : ℝ,0<d → ‖g (Real.cosh d)‖≤C/Real.sqrt (Real.sinh d))
    (z : ℍ) (hz : Real.exp (R/2)<z.im) :
    ‖radialNonidentity N g (A•z)‖≤(6*z.im*(Real.exp R-1)+9)*C*Real.sqrt z.im := by
  classical
  have he := radialNonidentity_eq_finite N g R hR hs (A•z) (A•z) 0 (by simp)
  simp only [mul_zero,add_zero] at he
  have he' : radialNonidentity N g (A•z)=
      ∑ γ∈(diagonalOrbitSet N (A•z) R).erase 1,g (Real.cosh (dist (γ•(A•z)) (A•z))) := by
    rw [he]
    apply Finset.sum_congr
    · ext γ
      simp
    · intro γ _
      rfl
  rw [he']
  have hsummand (γ : gamma N) (hγ : γ∈(diagonalOrbitSet N (A•z) R).erase 1) :
      ‖g (Real.cosh (dist (γ•(A•z)) (A•z)))‖≤C*Real.sqrt z.im := by
    have hm := Finset.mem_erase.mp hγ
    have hw := congruence_chart_singular_weight N A γ hm.1 z R
      ((mem_diagonalOrbitSet N (A•z) R γ).mp hm.2) hz
    calc
      _ ≤ C/Real.sqrt (Real.sinh (dist (γ•(A•z)) (A•z))) := hb _ hw.1
      _ = C*(1/Real.sqrt (Real.sinh (dist (γ•(A•z)) (A•z)))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hw.2 hC
  have hc : (((diagonalOrbitSet N (A•z) R).erase 1).card:ℝ)≤6*z.im*(Real.exp R-1)+9 := by
    have hh := Finset.card_erase_le (s := diagonalOrbitSet N (A•z) R) (a := 1)
    have hj := diagonalOrbitSet_integral_chart_card N A z R
    have hk : (((diagonalOrbitSet N (A•z) R).erase 1).card:ℝ)≤(diagonalOrbitSet 1 z R).card := by
      exact_mod_cast hh.trans hj
    exact hk.trans (diagonalOrbitSet_high_cusp_card_real 1 z R hR hz)
  calc
    _ ≤ ∑ γ∈(diagonalOrbitSet N (A•z) R).erase 1,‖g (Real.cosh (dist (γ•(A•z)) (A•z)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _γ∈(diagonalOrbitSet N (A•z) R).erase 1,C*Real.sqrt z.im :=
      Finset.sum_le_sum hsummand
    _ = (((diagonalOrbitSet N (A•z) R).erase 1).card:ℝ)*(C*Real.sqrt z.im) := by simp
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg hC (Real.sqrt_nonneg z.im))
      simpa only [mul_assoc] using hh

#print axioms cuspConjugateFull_one
#print axioms congruence_chart_singular_weight
#print axioms radialNonidentity_high_cusp_bound

end QuantitativeMaass
