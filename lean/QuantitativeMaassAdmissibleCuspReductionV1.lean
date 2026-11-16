module

public import QuantitativeMaassDyadicCuspArithmeticV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix UpperHalfPlane AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticRationalGroup AsymptoticRationalBranches AsymptoticRationalFreeness
open AsymptoticIntegralSubgroup
open scoped MatrixGroups

namespace QuantitativeMaass

theorem dilationLabel_one : dilationLabel 1 (by decide)=1 := by
  apply Subtype.ext
  apply Subtype.ext
  change rationalMap (dilationGL 1 (by decide))=1
  have h : dilationGL 1 (by decide)=1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dilationGL,GeneralLinearGroup.mkOfDetNeZero]
  rw [h,map_one]

theorem dilationLabel_height (p : ℕ) (hp : 0<p) (z : ℍ) :
    (dilationLabel p hp • z).im=(p:ℝ)*z.im := by
  rw [dilationLabel,ofMatrix_action,UpperHalfPlane.im_smul_eq_div_normSq]
  have hd : (realMatrix (dilationGL p hp)).det.val=(p:ℝ) := by
    change ((!![(p:ℚ),0;0,1]).map (algebraMap ℚ ℝ)).det=(p:ℝ)
    simp [Matrix.det_fin_two]
  rw [hd,abs_of_nonneg (Nat.cast_nonneg p)]
  simp [UpperHalfPlane.denom,realMatrix,dilationGL,
    GeneralLinearGroup.map,GeneralLinearGroup.mkOfDetNeZero]

/-- A half-translation or one integral lower normalizer suffices to
make the dyadic part of a cusp denominator full at every admissible level.
The exact residual right factor is a positive dilation. -/
theorem admissible_cusp_reduction (N : ℕ) (hN : GridAdmissibleGap.Admissible N)
    (a : SL(2,ℤ)) :
    ∃ g : AsymptoticRationalGroup.Group,
      (∀ b∈gamma N,g*b*g⁻¹∈gamma N) ∧ (∀ b∈gamma N,g⁻¹*b*g∈gamma N) ∧
      ∃ a' : SL(2,ℤ),fullDyadicDenominator N (a' 1 0).natAbs ∧
      ∃ d : ℕ,∃ hd : 0<d,g*integralLabel a=integralLabel a'*dilationLabel d hd := by
  by_cases hfull : fullDyadicDenominator N (a 1 0).natAbs
  · refine ⟨1,?_,?_,a,hfull,1,by decide,?_⟩
    · intro b hb; simpa using hb
    · intro b hb; simpa using hb
    · rw [dilationLabel_one,one_mul,mul_one]
  have hc2 : (2:ℤ)∣a 1 0 := by
    by_contra h
    exact hfull (fullDyadicDenominator_of_odd N (a 1 0) h)
  have hN4 : 4∣N := by
    by_contra h
    exact hfull (fullDyadicDenominator_of_level N h (a 1 0))
  by_cases hc4 : (4:ℤ)∣a 1 0
  · have hN8 : 8∣N := by
      by_contra h
      exact hfull (fullDyadicDenominator_of_four N h (a 1 0) hc4)
    have hc8 : ¬(8:ℤ)∣a 1 0 := by
      intro h
      exact hfull (fullDyadicDenominator_of_eight N (a 1 0) h)
    obtain ⟨M,rfl⟩ := hN8
    have h4 : 4*(2*M)=8*M := by omega
    have h2 : 2*(2*M)=4*M := by omega
    refine ⟨integralLabel (lowerSL (4*M) 1),?_,?_,lowerSL (4*M) 1*a,?_,1,by decide,?_⟩
    · intro b hb
      have hb' : b∈gamma (4*(2*M)) := by simpa only [h4] using hb
      simpa only [h4,h2] using lowerHalfLabel_conj_mem (2*M) 1 hb'
    · intro b hb
      have hb' : b∈gamma (4*(2*M)) := by simpa only [h4] using hb
      simpa only [h4,h2] using lowerHalfLabel_inv_conj_mem (2*M) 1 hb'
    · exact fullDyadicDenominator_of_eight (8*M) _ (lowerHalf_cusp_eight M hN.2.1 a hc4 hc8)
    · rw [dilationLabel_one,mul_one,map_mul]
  · obtain ⟨c,u,hc,hu,hco⟩ := halfCuspReduction_exists a hc2 hc4
    refine ⟨translationLabel (1/2),?_,?_,halfCuspReduction a c u hc hu,?_,4,by decide,?_⟩
    · intro b hb
      simpa only [Int.cast_one] using halfTranslation_conj_mem N hN4 1 hb
    · intro b hb
      simpa only [Int.cast_one] using halfTranslation_inv_conj_mem N hN4 1 hb
    · exact fullDyadicDenominator_of_odd N c hco
    · exact halfCuspReduction_label a c u hc hu

#print axioms dilationLabel_one
#print axioms dilationLabel_height
#print axioms admissible_cusp_reduction

end QuantitativeMaass
