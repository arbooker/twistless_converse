module

public import QuantitativeMaassPoincareUnfoldV1
public import AsymptoticClassicalPeterssonMeasureV1
public import QuantitativeMaassTranslationQuotientV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticCongruenceWeight AsymptoticClassicalPetersson
open AsymptoticCompactBranch AsymptoticMassTransport
open scoped ENNReal

namespace QuantitativeMaass

/-- Exact unfolding of the literal capped translation-cylinder norm to
the unweighted level quotient. The orbit weight is the actual convergent
sum, not an unspecified comparison density. -/
theorem weighted_quotient_energy (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (f : ℍ → ℂ) (hf : Measurable f)
    (hinv : ∀ g : gamma N,∀ z,f (g.val • z)=f z) :
    (∫⁻ z,ENNReal.ofReal (‖(cap ε v z:ℂ)*f z‖^2) ∂quotientMeasure 0)=
      ∫⁻ z,ENNReal.ofReal (weight N ε v z)*ENNReal.ofReal (‖f z‖^2)
        ∂quotientMeasure N := by
  let F : ℍ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖(cap ε v z:ℂ)*f z‖^2)
  have hF : Measurable F :=
    (((Complex.measurable_ofReal.comp (cap_continuous ε v).measurable).mul hf).norm.pow_const 2).ennreal_ofReal
  have he (z : ℍ) : (∑' g : gamma N,strip.indicator F (g.val • z))=
      ENNReal.ofReal (weight N ε v z)*ENNReal.ofReal (‖f z‖^2) := by
    rw [weight,ENNReal.ofReal_tsum_of_nonneg
      (fun g => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
      (weight_summable N hε hv z),←ENNReal.tsum_mul_right]
    apply tsum_congr
    intro g
    by_cases hg : g.val • z∈strip
    · rw [Set.indicator_of_mem hg,Set.indicator_of_mem hg]
      dsimp only [F]
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,hinv,
        ENNReal.ofReal_mul (sq_nonneg _)]
    · simp only [Set.indicator_of_notMem hg,ENNReal.ofReal_zero,zero_mul]
  rw [translation_quotient_measure,←lintegral_indicator strip_measurable F]
  have hu := lintegral_poincare_unfold volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (strip.indicator F) (hF.indicator strip_measurable)
  change (∫⁻ z,∑' g : gamma N,strip.indicator F (g.val • z) ∂quotientMeasure N)=
    ∫⁻ z,strip.indicator F z at hu
  simp_rw [he] at hu
  exact hu.symm

/-- A uniform bound on the explicit orbit weight gives the corresponding
energy bound for every measurable automorphic representative. -/
theorem weighted_quotient_energy_le (N : ℕ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) (C : ℝ) (hC : ∀ z,weight N ε v z≤C)
    (f : ℍ → ℂ) (hf : Measurable f)
    (hinv : ∀ g : gamma N,∀ z,f (g.val • z)=f z) :
    (∫⁻ z,ENNReal.ofReal (‖(cap ε v z:ℂ)*f z‖^2) ∂quotientMeasure 0)≤
      ENNReal.ofReal C * ∫⁻ z,ENNReal.ofReal (‖f z‖^2) ∂quotientMeasure N := by
  rw [weighted_quotient_energy N hε hv f hf hinv,
    ←lintegral_const_mul _ ((hf.norm.pow_const 2).ennreal_ofReal)]
  apply lintegral_mono
  intro z
  dsimp only
  gcongr
  exact hC z

#print axioms weighted_quotient_energy
#print axioms weighted_quotient_energy_le

end QuantitativeMaass
