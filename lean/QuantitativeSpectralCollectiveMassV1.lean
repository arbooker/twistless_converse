module

public import QuantitativeSpectralDiagonalLogV1
public import QuantitativeSpectralBlockTriangularV1
public import QuantitativeTracialSpectralMeasureV1
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

set_option autoImplicit false
@[expose] public section

open MeasureTheory

namespace QuantitativeSpectralCollectiveMass

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A numeric lower bound for the actual CFC trace-log controls its spectral
distribution without division by the total trace. -/
theorem small_mass_of_trace_log_lower (τ : A →L[ℝ] ℝ) (hτ : Monotone τ)
    (S : A) (hS : IsSelfAdjoint S) (hpos : IsStrictlyPositive S)
    {L K lam : ℝ} (hK : 0 < K) (hlam : 0 < lam) (hlamK : lam < K)
    (hnorm : ‖S‖ ≤ K) (hlower : L ≤ τ (CFC.log S)) :
    (QuantitativeTracialSpectralMeasure.measure τ hτ S hS).real
      {x : spectrum ℝ S | (x : ℝ) ≤ lam} ≤
      (τ 1 * Real.log K-L) / Real.log (K/lam) := by
  have hf : ContinuousOn Real.log (spectrum ℝ S) :=
    Real.continuousOn_log.mono (fun x hx => (hpos.spectrum_pos hx).ne')
  have hi : Integrable (fun x : spectrum ℝ S => Real.log x)
      (QuantitativeTracialSpectralMeasure.measure τ hτ S hS) :=
    hf.domRestrict.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh := QuantitativeSpectralDistribution.small_mass_of_log_integral_lower
    (QuantitativeTracialSpectralMeasure.measure τ hτ S hS)
    (fun x : spectrum ℝ S => (x : ℝ)) measurable_subtype_coe hi (L:=L) hK hlam hlamK
    (Filter.Eventually.of_forall (fun x => hpos.spectrum_pos x.property))
    (Filter.Eventually.of_forall (fun x => (le_abs_self (x : ℝ)).trans
      ((quasispectrum.norm_le_norm_of_mem
        (spectrum_subset_quasispectrum ℝ S x.property)).trans hnorm)))
    (by simpa only [QuantitativeTracialSpectralMeasure.integral_log τ hτ S hS hpos] using hlower)
  rwa [QuantitativeTracialSpectralMeasure.measure_real_univ] at hh

/-- The exact collective determinant estimate. The retained projection
contributes its own trace, while the complement contributes only a logarithmic
deficit. Nilpotence and the trace-log identity follow from the finite blocks. -/
theorem collective_small_mass (τ : A →L[ℝ] ℝ) (hτ : Monotone τ)
    (hcyc : ∀ a b, τ (a*b) = τ (b*a)) (hstar : ∀ a, τ (star a) = τ a)
    {n : ℕ} (Q : Fin n → A) (hQ : ∑ i, Q i = 1) (hid : ∀ i, Q i*Q i = Q i)
    {V : A} (hV : QuantitativeSpectralBlockTriangular.Below Q V 1)
    (P : A) (hp : IsSelfAdjoint P) (hi : IsIdempotentElem P)
    (B : A) (hB : IsUnit B) (S : A) (hS : IsSelfAdjoint S) (hpos : IsStrictlyPositive S)
    {h K lam : ℝ} (hh : 0 < h) (hK : 0 < K) (hlam : 0 < lam) (hlamK : lam < K)
    (hnorm : ‖S‖ ≤ K) (hdiag : star B*B = h • (1 : A)+(lam-h) • P)
    (hdom : star (B*(1+V))*(B*(1+V)) ≤ S) :
    (QuantitativeTracialSpectralMeasure.measure τ hτ S hS).real
      {x : spectrum ℝ S | (x : ℝ) ≤ lam} ≤
      τ P + (τ 1-τ P) * Real.log (K/h) / Real.log (K/lam) := by
  have hu : IsUnit (B*(1+V)) := hB.mul
    ((show IsNilpotent V from
      ⟨n+1, QuantitativeSpectralBlockTriangular.pow_eq_zero Q hQ hV⟩).isUnit_one_add)
  have hg : IsStrictlyPositive (star (B*(1+V))*(B*(1+V))) :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mpr ⟨B*(1+V),hu,rfl⟩
  have htrace := hτ (CFC.log_le_log hdom hg)
  have he := QuantitativeSpectralBlockTriangular.trace_log_block_congruence
    Q hQ hid hV B hB τ hcyc hstar 1
  simp only [one_smul] at he
  rw [he, hdiag, QuantitativeSpectralDiagonalLog.trace_log_two_blocks τ P hp hi] at htrace
  have hm := small_mass_of_trace_log_lower τ hτ S hS hpos hK hlam hlamK hnorm htrace
  have hd : Real.log (K/lam) ≠ 0 :=
    (Real.log_pos ((one_lt_div hlam).mpr hlamK)).ne'
  convert hm using 1
  rw [Real.log_div hK.ne' hlam.ne'] at hd
  rw [Real.log_div hK.ne' hh.ne', Real.log_div hK.ne' hlam.ne']
  field_simp [hd]
  ring

#print axioms small_mass_of_trace_log_lower
#print axioms collective_small_mass

end QuantitativeSpectralCollectiveMass
