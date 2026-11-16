module

public import QuantitativeMaassLocalRegularWeightV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory ContinuousLinearMap UpperHalfPlane AsymptoticFiniteBranch AsymptoticRegularTrace
open AsymptoticRegularCompactBranch (Space)
open scoped ENNReal
namespace QuantitativeMaass.RawCommonReconstruction

/-- A bounded local regular pairing is integrable on every finite-volume
region; the full ambient volume need not be finite. -/
theorem local_regular_pairing_integrable (S : Set ℍ) (hS : volume S<∞)
    (u : ℍ→ℂ) (hu : Measurable u) (L : ℝ) (hL : 0≤L) (huL : ∀ x,‖u x‖≤L)
    (F : ℍ→Space→L[ℂ]Space) (hmF : Measurable (fun x => matrix (F x) 1 1))
    (A : ℝ) (hF : ∀ x,‖F x‖≤A) :
    IntegrableOn (fun x => (u x*matrix (F x) 1 1).re) S volume := by
  apply IntegrableOn.of_bound hS
    ((Complex.continuous_re.measurable.comp (hu.mul hmF)).aestronglyMeasurable) (L*A)
  apply Filter.Eventually.of_forall
  intro x
  have hm : ‖matrix (F x) 1 1‖≤A := by
    have hh := (lp.norm_apply_le_norm (by norm_num) (F x (delta 1)) 1).trans ((F x).le_opNorm _)
    exact hh.trans (by simpa only [AsymptoticOrbitDiagonal.root_delta_norm,mul_one] using hF x)
  change ‖(u x*matrix (F x) 1 1).re‖≤L*A
  calc
    _ ≤ ‖u x*matrix (F x) 1 1‖ := by
      simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (u x*matrix (F x) 1 1)
    _ = ‖u x‖*‖matrix (F x) 1 1‖ := norm_mul _ _
    _ ≤ L*A := mul_le_mul (huL x) hm (norm_nonneg _) hL

/-- The bounded local weighted estimate is an estimate of the difference
of the two actual integrals, with integrability explicitly discharged. -/
theorem local_regular_difference_bound
    (F Q : ℍ→Space→L[ℂ]Space) (E : ℝ)
    (hweighted : ∀ (B : ℍ→Space→L[ℂ]Space) (L : ℝ),0≤L →
      (∀ a b,Measurable (fun x => matrix (B x) a b)) → Covariant B →
      (∀ x,‖B x‖≤L) → |signedTrace volume (fun x => B x*(F x-Q x))|≤L*E)
    (hmF : Measurable (fun x => matrix (F x) 1 1))
    (hmQ : Measurable (fun x => matrix (Q x) 1 1))
    (A : ℝ) (hF : ∀ x,‖F x‖≤A) (hQ : ∀ x,‖Q x‖≤A)
    (S : Set ℍ) (hS : MeasurableSet S) (hSf : volume S<∞)
    (u : ℍ→ℂ) (hu : Measurable u) (L : ℝ) (hL : 0≤L) (huL : ∀ x,‖u x‖≤L) :
    |(∫ x in S,(u x*matrix (F x) 1 1).re)-
      (∫ x in S,(u x*matrix (Q x) 1 1).re)|≤L*E := by
  have hiF := local_regular_pairing_integrable S hSf u hu L hL huL F hmF A hF
  have hiQ := local_regular_pairing_integrable S hSf u hu L hL huL Q hmQ A hQ
  have hh := local_weighted_trace_bound (fun x => F x-Q x) E hweighted S hS u hu L hL huL
  rw [←integral_sub hiF hiQ]
  convert hh using 2
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change (u x*matrix (F x) 1 1).re-(u x*matrix (Q x) 1 1).re=
    (u x*(matrix (F x) 1 1-matrix (Q x) 1 1)).re
  rw [mul_sub,Complex.sub_re]

#print axioms local_regular_pairing_integrable
#print axioms local_regular_difference_bound
end QuantitativeMaass.RawCommonReconstruction
