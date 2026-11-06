module

public import AsymptoticPolarSupportV1
public import AsymptoticProjectionTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPolarIsometry

open ContinuousLinearMap

variable {H J K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem outputSpace_eq_adjoint_kernel (T : H →L[ℂ] J) : outputSpace T=T.adjoint.kerᗮ := by
  simpa only [outputSpace,adjoint_adjoint] using (orthogonal_ker T.adjoint).symm

theorem polar_adjoint_ker (T : H →L[ℂ] J) : (polar T).adjoint.ker=T.adjoint.ker := by
  rw [← (polar T).ker_self_comp_adjoint,polar_cogram,Submodule.ker_starProjection,
    outputSpace,Submodule.orthogonal_closure,orthogonal_range]

/-- Applying a bounded map after an operator or after its polar
isometry gives the same closed output range. This replaces the dense
range comparison needed in the rank-loss argument. -/
theorem outputSpace_comp_polar (D : J →L[ℂ] K) (T : H →L[ℂ] J) :
    outputSpace (D.comp T)=outputSpace (D.comp (polar T)) := by
  rw [outputSpace_eq_adjoint_kernel,outputSpace_eq_adjoint_kernel,adjoint_comp,adjoint_comp]
  congr 1
  ext x
  change D.adjoint x∈T.adjoint.ker ↔ D.adjoint x∈(polar T).adjoint.ker
  rw [polar_adjoint_ker]

omit [CompleteSpace J] in
/-- A contraction's column energy is bounded by the squared norm of its
source support projection. -/
theorem contraction_norm_le_support (T : H →L[ℂ] J) (hT : ‖T‖≤1) (x : H) :
    ‖T x‖≤‖T.kerᗮ.starProjection x‖ := by
  have hs := T.kerᗮ.sub_starProjection_mem_orthogonal x
  rw [Submodule.orthogonal_orthogonal] at hs
  change T (x-T.kerᗮ.starProjection x)=0 at hs
  rw [map_sub,sub_eq_zero] at hs
  rw [hs]
  simpa only [one_mul] using T.le_of_opNorm_le hT (T.kerᗮ.starProjection x)

#print axioms outputSpace_eq_adjoint_kernel
#print axioms polar_adjoint_ker
#print axioms outputSpace_comp_polar
#print axioms contraction_norm_le_support

end AsymptoticPolarIsometry

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap InnerProductSpace AsymptoticPolarIsometry
open scoped lp InnerProduct ENNReal

variable {G α J : Type*} [Group G] [MeasurableSpace α]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

omit [Group G] in
theorem rectangular_gram_root (T : ℓ²(G,ℂ) →L[ℂ] J) (h : G) :
    (matrix (T.adjoint.comp T) h h).re=‖T (delta h)‖^2 := by
  rw [matrix,← delta_inner,comp_apply,adjoint_inner_right]
  exact (norm_sq_eq_re_inner (𝕜:=ℂ) _).symm

/-- Positive contraction energy is no larger than the source support
trace, including finite labelled observation targets. -/
theorem trace_gram_le_support (μ : Measure α) (T : α → ℓ²(G,ℂ) →L[ℂ] J)
    (hT : ∀ x,‖T x‖≤1) :
    trace μ (fun x => (T x).adjoint.comp (T x))≤trace μ (fun x => (T x).kerᗮ.starProjection) := by
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  rw [rectangular_gram_root,projection_root_eq_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) (contraction_norm_le_support (T x) (hT x) (delta 1)) 2

#print axioms rectangular_gram_root
#print axioms trace_gram_le_support

end AsymptoticRegularTrace
