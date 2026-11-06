module

public import QuantitativeSpectralCutRegularityV1
public import QuantitativeSpectralWhiteningMinmaxV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointHighInverse
open ContinuousLinearMap InnerProductSpace QuantitativeSpectralCut
open scoped InnerProduct lp

/-- A globally continuous inverse clipped below a positive threshold. -/
def clippedInverse (a x : ℝ) : ℝ := (max a x)⁻¹

theorem clippedInverse_continuous {a : ℝ} (ha : 0<a) : Continuous (clippedInverse a) := by
  apply Continuous.inv₀ (continuous_const.max continuous_id)
  intro x
  exact ne_of_gt (ha.trans_le (le_max_left a x))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def highInverse (A : H →L[ℂ] H) (a : ℝ) : H →L[ℂ] H :=
  cfc (clippedInverse a) A * (highAt A a).starProjection

theorem inverse_defect (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {a : ℝ} (ha : 0<a) :
    positivePart (A-a • 1) * (A*cfc (clippedInverse a) A-1)=0 := by
  have hf := (clippedInverse_continuous ha).continuousOn (s := spectrum ℝ A)
  have hs : cfc (fun r : ℝ => r-a) A=A-a • 1 := by
    rw [cfc_sub (fun r : ℝ => r) (fun _ => a) A, cfc_id' ℝ A hA,
      cfc_const a A hA,Algebra.algebraMap_eq_smul_one]
  have hp : positivePart (A-a • 1)=cfc (fun r : ℝ => (r-a)⁺) A := by
    rw [positivePart_eq_cfc,← hs,← cfc_comp (fun r : ℝ => r⁺) (fun r : ℝ => r-a) A hA]
    rfl
  have hd : A*cfc (clippedInverse a) A-1 =
      cfc (fun r : ℝ => r*clippedInverse a r-1) A := by
    rw [cfc_sub (fun r : ℝ => r*clippedInverse a r) (fun _ => 1) A
      ((continuous_id.mul (clippedInverse_continuous ha)).continuousOn) continuous_const.continuousOn,
      cfc_mul (fun r : ℝ => r) (clippedInverse a) A continuous_id.continuousOn hf,
      cfc_id' ℝ A hA,cfc_const_one ℝ A hA]
  rw [hp,hd,← cfc_mul (fun r : ℝ => (r-a)⁺) (fun r : ℝ => r*clippedInverse a r-1) A (by fun_prop)
    (((continuous_id.mul (clippedInverse_continuous ha)).sub continuous_const).continuousOn)]
  have hz : (fun r : ℝ => (r-a)⁺*(r*clippedInverse a r-1))=fun _ => 0 := by
    funext r
    by_cases hr : r≤a
    · simp [posPart_def,max_eq_right (sub_nonpos.mpr hr)]
    · have hrr : 0<r := ha.trans (lt_of_not_ge hr)
      simp [clippedInverse,max_eq_right (le_of_not_ge hr),mul_inv_cancel₀ hrr.ne']
  rw [hz,cfc_const_zero ℝ A]

theorem highInverse_factor (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    {a : ℝ} (ha : 0<a) : A*highInverse A a=(highAt A a).starProjection := by
  let D := A*cfc (clippedInverse a) A-1
  have hd : D=cfc (fun r : ℝ => r*clippedInverse a r-1) A := by
    rw [cfc_sub (fun r : ℝ => r*clippedInverse a r) (fun _ => 1) A
      ((continuous_id.mul (clippedInverse_continuous ha)).continuousOn) continuous_const.continuousOn,
      cfc_mul (fun r : ℝ => r) (clippedInverse a) A continuous_id.continuousOn
      (clippedInverse_continuous ha).continuousOn,cfc_id' ℝ A hA,cfc_const_one ℝ A hA]
  have hD : IsSelfAdjoint D := hd ▸ cfc_predicate _ _
  have hz (v : H) (hv : v∈highAt A a) : D v=0 := by
    apply ext_inner_right ℂ
    intro w
    rw [inner_zero_left]
    change ⟪(D : H →ₗ[ℂ] H) v,w⟫_ℂ=0
    rw [hD.isSymmetric v w]
    apply ((lowAt A a).mem_orthogonal' v).mp hv
    change positivePart (A-a • 1) (D w)=0
    exact congrArg (fun T : H →L[ℂ] H => T w) (inverse_defect A hA ha)
  ext v
  have hh := hz ((highAt A a).starProjection v) ((highAt A a).starProjection_apply_mem v)
  change A (cfc (clippedInverse a) A ((highAt A a).starProjection v))-
    (highAt A a).starProjection v=0 at hh
  exact sub_eq_zero.mp hh

theorem highInverse_norm (A : H →L[ℂ] H) {a : ℝ} (ha : 0<a) :
    ‖highInverse A a‖≤a⁻¹ := by
  have hn : ‖cfc (clippedInverse a) A‖≤a⁻¹ := by
    apply norm_cfc_le (inv_nonneg.mpr ha.le)
    intro r _
    rw [clippedInverse,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (ha.le.trans (le_max_left a r)))]
    exact inv_anti₀ ha (le_max_left a r)
  exact (norm_mul_le _ _).trans ((mul_le_mul hn
    (highAt A a).starProjection_norm_le (norm_nonneg _) (inv_nonneg.mpr ha.le)).trans_eq (mul_one _))

#print axioms clippedInverse_continuous
#print axioms inverse_defect
#print axioms highInverse_factor
#print axioms highInverse_norm
end QuantitativeEulerEndpointHighInverse
