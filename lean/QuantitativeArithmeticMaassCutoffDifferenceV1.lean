module

public import QuantitativeArithmeticMaassColumnTracePerturbationV1
public import QuantitativeMaassQuotientRestrictionOverlapV1
public import QuantitativeMaassCrossQuotientLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal

namespace QuantitativeMaass

/-- The difference of two bounded multipliers is paid only on the region
where their coefficients differ. -/
theorem multiplier_difference_collar {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (a b : α → ℂ) (ha : AEStronglyMeasurable a μ)
    (hb : AEStronglyMeasurable b μ) (A B C : ℝ)
    (haB : ∀ᵐ x ∂μ, ‖a x‖ ≤ A) (hbB : ∀ᵐ x ∂μ, ‖b x‖ ≤ B)
    (Ω : Set α) (hΩ : MeasurableSet Ω)
    (hchange : ∀ᵐ x ∂μ, ‖a x-b x‖ ≤ C ∧ (x ∉ Ω → a x=b x))
    (f : Lp ℂ 2 μ) :
    ‖AsymptoticL2Multiplier.operator a ha haB f-
      AsymptoticL2Multiplier.operator b hb hbB f‖^2 ≤
        C^2*(∫ x in Ω, ‖f x‖^2 ∂μ) := by
  classical
  let u := AsymptoticL2Multiplier.operator a ha haB f
  let v := AsymptoticL2Multiplier.operator b hb hbB f
  have hif := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hiuv := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (u-v))).mp (Lp.memLp (u-v))
  change ‖u-v‖^2 ≤ _
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
  calc
    _ ≤ ∫ x, C^2*Ω.indicator (fun x => ‖f x‖^2) x ∂μ := by
      apply integral_mono_ae hiuv ((hif.indicator hΩ).const_mul (C^2))
      filter_upwards [Lp.coeFn_sub u v, AsymptoticL2Multiplier.operator_coeFn a ha haB f,
        AsymptoticL2Multiplier.operator_coeFn b hb hbB f, hchange] with x huv hu hv hx
      change ‖(u-v) x‖^2 ≤ C^2*Ω.indicator (fun x => ‖f x‖^2) x
      rw [huv]
      simp only [Pi.sub_apply]
      rw [hu, hv, ← sub_mul, norm_mul, mul_pow]
      by_cases hmem : x ∈ Ω
      · rw [Set.indicator_of_mem hmem]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx.1 2) (sq_nonneg _)
      · rw [Set.indicator_of_notMem hmem, hx.2 hmem]
        simp
    _ = _ := by rw [integral_const_mul, integral_indicator hΩ]

/-- Measurable version of the compact quotient transfer, permitting a
sharp cutoff as well as the smooth cutoff used in the Green identity. -/
def boundedCrossQuotientLocalization (N M : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (a : ℍ → ℂ) (ha : AEStronglyMeasurable a (volume.restrict K))
    {A : ℝ} (hA : ∀ᵐ x ∂volume.restrict K, ‖a x‖ ≤ A) :
    AutomorphicSpace M →L[ℂ] AutomorphicSpace N :=
  (quotientRestriction N K hK hK.measurableSet).adjoint.comp
    ((AsymptoticL2Multiplier.operator a ha hA).comp
      (quotientRestriction M K hK hK.measurableSet))

theorem boundedCrossQuotientLocalization_smooth (N M : ℕ) (K : Set ℍ)
    (hK : IsCompact K) (b : SmoothUpperSeed) {B : ℝ}
    (hB : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B) :
    boundedCrossQuotientLocalization (A := B) N M K hK (upperFunction b.toFun)
      (upperFunction_continuous b.smooth).aestronglyMeasurable
      (by filter_upwards [ae_restrict_mem hK.measurableSet] with z hz; exact hB z hz) =
      crossQuotientLocalization N M K hK b hB := rfl

/-- Actual sharp/smooth transfer difference, with one target overlap
factor and the source's L2 mass in the collar. No global cutoff norm is
substituted for this local mass. -/
theorem boundedCrossQuotientLocalization_difference_collar (N M : ℕ)
    (K : Set ℍ) (hK : IsCompact K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N), (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ m)
    (a b : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume.restrict K))
    (hb : AEStronglyMeasurable b (volume.restrict K)) (A B C : ℝ)
    (haB : ∀ᵐ x ∂volume.restrict K, ‖a x‖ ≤ A)
    (hbB : ∀ᵐ x ∂volume.restrict K, ‖b x‖ ≤ B)
    (Ω : Set ℍ) (hΩ : MeasurableSet Ω)
    (hchange : ∀ᵐ x ∂volume.restrict K, ‖a x-b x‖ ≤ C ∧ (x ∉ Ω → a x=b x))
    (f : AutomorphicSpace M) :
    ‖boundedCrossQuotientLocalization N M K hK a ha haB f-
      boundedCrossQuotientLocalization N M K hK b hb hbB f‖^2 ≤
        (m : ℝ)*C^2*(∫ x in Ω,
          ‖quotientRestriction M K hK hK.measurableSet f x‖^2 ∂volume.restrict K) := by
  let R := quotientRestriction N K hK hK.measurableSet
  let u := quotientRestriction M K hK hK.measurableSet f
  let v := AsymptoticL2Multiplier.operator a ha haB u-
    AsymptoticL2Multiplier.operator b hb hbB u
  have hR : ‖R.adjoint‖ ≤ Real.sqrt (m : ℝ) := by
    rw [adjoint.norm_map]
    exact quotientRestriction_norm_le_of_overlap N K hK m hm
  have hv := multiplier_difference_collar (volume.restrict K) a b ha hb A B C haB hbB Ω hΩ hchange u
  change ‖R.adjoint (AsymptoticL2Multiplier.operator a ha haB u)-
    R.adjoint (AsymptoticL2Multiplier.operator b hb hbB u)‖^2 ≤ _
  rw [← map_sub]
  calc
    ‖R.adjoint v‖^2 ≤ (Real.sqrt (m : ℝ)*‖v‖)^2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (R.adjoint.le_opNorm v).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
    _ = (m : ℝ)*‖v‖^2 := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    _ ≤ (m : ℝ)*(C^2*(∫ x in Ω, ‖u x‖^2 ∂volume.restrict K)) :=
      mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg m)
    _ = _ := by ring

#print axioms multiplier_difference_collar
#print axioms boundedCrossQuotientLocalization_difference_collar

end QuantitativeMaass
