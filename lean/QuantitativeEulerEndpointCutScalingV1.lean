module

public import QuantitativeEulerEndpointOriginalStepV1
public import QuantitativeSpectralPacketContractionV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open ContinuousLinearMap QuantitativeSpectralCut QuantitativeSpectralCutRow
open QuantitativeSpectralCornerCutRow AsymptoticPolarIsometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem lowAt_positive_scale (A : H →L[ℂ] H) (r : ℝ) (hr : 0<r) (a : ℝ) :
    lowAt (r • A) (r*a)=lowAt A a := by
  have he : r • A-(r*a) • (1 : H →L[ℂ] H)=r • (A-a • 1) := by
    rw [smul_sub,smul_smul]
  unfold lowAt low
  rw [he,CFC.posPart_smul_of_nonneg hr.le]
  ext v
  change (r • (A-a • (1 : H →L[ℂ] H))⁺) v=0 ↔ (A-a • (1 : H →L[ℂ] H))⁺ v=0
  simp only [_root_.smul_apply,smul_eq_zero,hr.ne',false_or]

theorem highAt_positive_scale (A : H →L[ℂ] H) (r : ℝ) (hr : 0<r) (a : ℝ) :
    highAt (r • A) (r*a)=highAt A a := by
  change (lowAt (r • A) (r*a))ᗮ=(lowAt A a)ᗮ
  rw [lowAt_positive_scale A r hr a]

theorem gram_real_scale (B : H →L[ℂ] H) (r : ℝ) :
    star (r • B)*(r • B)=r^2 • (star B*B) := by
  simp only [star_smul,star_trivial,smul_mul_assoc,mul_smul_comm,smul_smul,pow_two]

theorem removed_positive_scale (B : H →L[ℂ] H) (r : ℝ) (hr : 0<r) (c : ℝ) :
    removed (r • B) (r*c)=removed B c := by
  unfold removed
  apply starProjection_congr
  rw [gram_real_scale,mul_pow]
  exact highAt_positive_scale _ (r^2) (sq_pos_of_pos hr) (c^2)

theorem nextSpace_positive_scale (U : Submodule ℂ H) [CompleteSpace U]
    (B : H →L[ℂ] H) (r : ℝ) (hr : 0<r) (c : ℝ) :
    nextSpace U (r • B) (r*c)=nextSpace U B c := by
  simp only [nextSpace,restricted,smul_mul_assoc]
  rw [removed_positive_scale _ r hr]

#print axioms lowAt_positive_scale
#print axioms highAt_positive_scale
#print axioms removed_positive_scale
#print axioms nextSpace_positive_scale
end QuantitativeEulerEndpointPrepared
