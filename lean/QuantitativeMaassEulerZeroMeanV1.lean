module

public import QuantitativeMaassEulerCoefficientV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory

namespace QuantitativeMaass

theorem eulerParityPhase_mean_zero (σ n : ℕ) (hn : 0<n) :
    (∫ x in Ioc (0:ℝ) 1,eulerParityPhase σ n x)=0 := by
  simp_rw [eulerParityPhase_characters]
  rw [integral_add
    ((eulerCharacter_continuous _).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (((eulerCharacter_continuous _).const_mul _).integrableOn_Icc.mono_set Ioc_subset_Icc_self),
    integral_const_mul,eulerCharacter_integral,eulerCharacter_integral]
  have hpos : (n:ℤ)≠0 := by omega
  have hneg : -(n:ℤ)≠0 := neg_ne_zero.mpr hpos
  simp only [ite_eq_right hpos,ite_eq_right hneg,mul_zero,add_zero]

theorem principalEulerTerm_mean_zero (b : ℕ → ℂ) (r : ℝ) (σ n : ℕ) (y : ℝ) :
    (∫ x in Ioc (0:ℝ) 1,principalEulerTerm b r σ n (x,y))=0 := by
  unfold principalEulerTerm
  dsimp only
  rw [integral_const_mul,eulerParityPhase_mean_zero σ (n+1) (by omega),mul_zero]

/-- The literal Fourier--Bessel reconstruction has zero constant term at
every positive height. Integration through the infinite series is justified
by the checked absolute majorant, with individual polynomial growth only. -/
theorem principalEulerWave_mean_zero {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (y : ℝ) (hy : 0<y) :
    (∫ x in Ioc (0:ℝ) 1,principalEulerWave b r σ (x,y))=0 := by
  have hh := principalEulerCore_coefficient_hasSum hb r σ 0 y hy
  simp only [Nat.cast_zero,neg_zero,eulerCharacter,Int.cast_zero,mul_zero,zero_mul,
    Complex.ofReal_zero,Complex.exp_zero,one_mul] at hh
  have he : (∫ x in Ioc (0:ℝ) 1,principalEulerCore b r σ (x,y))=0 := by
    rw [←hh.tsum_eq]
    simp only [principalEulerTerm_mean_zero,tsum_zero]
  unfold principalEulerWave
  dsimp only
  rw [integral_const_mul,he,mul_zero]

#print axioms eulerParityPhase_mean_zero
#print axioms principalEulerTerm_mean_zero
#print axioms principalEulerWave_mean_zero

end QuantitativeMaass
