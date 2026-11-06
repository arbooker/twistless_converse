module

public import QuantitativeEulerEndpointHighInverseV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointCutCalculus
open ContinuousLinearMap InnerProductSpace QuantitativeSpectralCut
open scoped InnerProduct

section CStar
variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

theorem projection_le_of_fixed (P F : 𝔄) (hP : IsStarProjection P)
    (hF : 0≤F) (hFP : F*P=P) : P≤F := by
  have hPF : P*F=P := by
    have hh := congrArg star hFP
    simpa only [star_mul,hP.isSelfAdjoint.star_eq,(IsSelfAdjoint.of_nonneg hF).star_eq] using hh
  have hh := conjugate_nonneg_of_nonneg hF (sub_nonneg.mpr hP.le_one)
  have he : (1-P)*F*(1-P)=F-P := by
    rw [sub_mul,one_mul,hPF,mul_sub,mul_one,sub_mul,hFP,hP.isIdempotentElem.eq]
    abel
  rw [he] at hh
  exact sub_nonneg.mp hh

theorem le_projection_of_supported (P F : 𝔄) (hP : IsStarProjection P)
    (hF0 : 0≤F) (hF1 : F≤1) (hFP : F*P=F) : F≤P := by
  have hPF : P*F=F := by
    have hh := congrArg star hFP
    simpa only [star_mul,hP.isSelfAdjoint.star_eq,(IsSelfAdjoint.of_nonneg hF0).star_eq] using hh
  have hh := conjugate_nonneg_of_nonneg (sub_nonneg.mpr hF1) hP.nonneg
  have he : P*(1-F)*P=P-F := by
    rw [mul_sub,mul_one,hPF,sub_mul,hP.isIdempotentElem.eq,hFP]
  rw [he] at hh
  exact sub_nonneg.mp hh
end CStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem shifted_positivePart (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (a : ℝ) :
    positivePart (A-a • 1)=cfc (fun r : ℝ => (r-a)⁺) A := by
  have hs : cfc (fun r : ℝ => r-a) A=A-a • 1 := by
    rw [cfc_sub (fun r : ℝ => r) (fun _ => a) A,cfc_id' ℝ A hA,
      cfc_const a A hA,Algebra.algebraMap_eq_smul_one]
  rw [positivePart_eq_cfc,← hs,← cfc_comp (fun r : ℝ => r⁺) (fun r : ℝ => r-a) A hA]
  rfl

/-- A continuous spectral function vanishing above the threshold kills
its actual high-cut subspace. No Borel functional calculus is assumed. -/
theorem cfc_zero_on_high (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (a : ℝ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hz : ∀ r ∈ spectrum ℝ A, (r-a)⁺*f r=0)
    {v : H} (hv : v∈highAt A a) : cfc f A v=0 := by
  have he : positivePart (A-a • 1)*cfc f A=0 := by
    rw [shifted_positivePart A hA a,← cfc_mul _ _ A (by fun_prop) hf.continuousOn]
    exact (cfc_congr hz).trans (cfc_const_zero ℝ A)
  have hD : IsSelfAdjoint (cfc f A) := cfc_predicate f A
  apply ext_inner_right ℂ
  intro w
  rw [inner_zero_left]
  change ⟪((cfc f A : H →L[ℂ] H) : H →ₗ[ℂ] H) v,w⟫_ℂ=0
  rw [hD.isSymmetric v w]
  apply ((lowAt A a).mem_orthogonal' v).mp hv
  exact congrArg (fun T : H →L[ℂ] H => T w) he

/-- A continuous function equal to one on the high spectrum fixes that
cut projection exactly. -/
theorem cfc_fixed_high (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (a : ℝ)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hone : ∀ r ∈ spectrum ℝ A, a<r → f r=1) :
    cfc f A*(highAt A a).starProjection=(highAt A a).starProjection := by
  ext v
  have hh := cfc_zero_on_high A hA a (fun r => f r-1) (hf.sub continuous_const)
    (fun r hr => by
      by_cases hx : r≤a
      · simp [posPart_def,max_eq_right (sub_nonpos.mpr hx)]
      · rw [hone r hr (lt_of_not_ge hx),sub_self,mul_zero])
    ((highAt A a).starProjection_apply_mem v)
  rw [cfc_sub f (fun _ => 1) A hf.continuousOn continuous_const.continuousOn,
    cfc_const_one ℝ A hA] at hh
  change cfc f A ((highAt A a).starProjection v)-(highAt A a).starProjection v=0 at hh
  exact sub_eq_zero.mp hh

/-- A continuous factor of the positive part is supported on the actual
high cut. This supplies quantitative spectral windows without a normality
or spectral-measure identification hypothesis. -/
theorem cfc_supported_high (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (a : ℝ)
    (f g : ℝ → ℝ) (_hf : Continuous f) (hg : Continuous g)
    (hfactor : ∀ r ∈ spectrum ℝ A, f r=(r-a)⁺*g r) :
    cfc f A*(highAt A a).starProjection=cfc f A := by
  have he : cfc f A=cfc g A*positivePart (A-a • 1) := by
    rw [shifted_positivePart A hA a,← cfc_mul _ _ A hg.continuousOn (by fun_prop)]
    apply cfc_congr
    intro r hr
    rw [hfactor r hr,mul_comm]
  ext v
  have hv := (highAt A a).sub_starProjection_mem_orthogonal v
  have hl : v-(highAt A a).starProjection v∈lowAt A a := by
    simpa only [highAt,high,lowAt,Submodule.orthogonal_orthogonal] using hv
  have hz : positivePart (A-a • 1) (v-(highAt A a).starProjection v)=0 := hl
  have hh : cfc f A (v-(highAt A a).starProjection v)=0 := by
    rw [he]
    change cfc g A (positivePart (A-a • 1) (v-(highAt A a).starProjection v))=0
    rw [hz,map_zero]
  rw [map_sub,sub_eq_zero] at hh
  exact hh.symm

#print axioms projection_le_of_fixed
#print axioms le_projection_of_supported
#print axioms shifted_positivePart
#print axioms cfc_zero_on_high
#print axioms cfc_fixed_high
#print axioms cfc_supported_high
end QuantitativeEulerEndpointCutCalculus
