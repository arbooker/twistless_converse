module

public import QuantitativeMaassWaveGeneratorScalarV1
public import QuantitativeMaassWaveSpectrumV1

set_option autoImplicit false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Generator difference quotient with two actual resolvent factors. -/
def rangeGeneratorError (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  (2/t^2 : ℝ) • ((rangeCosine A t-1)*A*A)+(A-A*A)

theorem rangeGeneratorError_cfc (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) (t : ℝ) :
    rangeGeneratorError A t=cfc (weightedCosineRemainder t) A := by
  have hg : rangeCosine A t*A=cfc (dampedCosine t) A := by
    ext v
    exact rangeCosine_range A hA hd t v
  unfold weightedCosineRemainder
  rw [cfc_add (a := A) (fun s => (2/t^2)*(dampedCosine t s*s-s^2)) (fun s => s-s^2)
      (continuous_const.mul (((dampedCosine_continuous t).mul continuous_id).sub
        (continuous_id.pow 2))).continuousOn (continuous_id.sub (continuous_id.pow 2)).continuousOn,
    cfc_const_mul (2/t^2) (fun s => dampedCosine t s*s-s^2) A
      (((dampedCosine_continuous t).mul continuous_id).sub (continuous_id.pow 2)).continuousOn,
    cfc_sub (fun s => dampedCosine t s*s) (fun s : ℝ => s^2) A
      ((dampedCosine_continuous t).mul continuous_id).continuousOn (continuous_id.pow 2).continuousOn,
    cfc_sub (fun s : ℝ => s) (fun s : ℝ => s^2) A
      continuous_id.continuousOn (continuous_id.pow 2).continuousOn,
    cfc_mul (dampedCosine t) (fun s : ℝ => s) A
      (dampedCosine_continuous t).continuousOn continuous_id.continuousOn,
    cfc_id' ℝ A hA,cfc_pow_id A 2 hA,pow_two]
  unfold rangeGeneratorError
  rw [sub_mul,one_mul,sub_mul,hg]
  simp only [pow_two]

theorem rangeGeneratorError_norm_le (A : H →L[ℂ] H) (hp : A.IsPositive)
    (hn : ‖A‖≤1) (hd : DenseRange A) {t : ℝ} (ht : t≠0) :
    ‖rangeGeneratorError A t‖≤6*t^2 := by
  rw [rangeGeneratorError_cfc A hp.isSelfAdjoint hd]
  apply norm_cfc_le (by positivity)
  intro s hs
  have hb := positiveContraction_spectrum_bound A hp hn hs
  exact weightedCosineRemainder_bound ht hb.1 hb.2

/-- The actual quotient family has the correct infinitesimal Laplacian
on the dense twice-resolvent range, with a uniform operator-norm error. -/
theorem quotientGeneratorError_norm_le (N : ℕ) {t : ℝ} (ht : t≠0) :
    ‖rangeGeneratorError (friedrichsResolvent N) t‖≤6*t^2 :=
  rangeGeneratorError_norm_le _ (friedrichsResolvent_isPositive N)
    (friedrichsResolvent_opNorm_le N) (friedrichsResolvent_denseRange N) ht

#print axioms rangeGeneratorError_cfc
#print axioms quotientGeneratorError_norm_le

end QuantitativeMaass.Wave
