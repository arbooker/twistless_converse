module

public import QuantitativeSpectralCutV1
public import AsymptoticPolarApproximationV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralCutPolar

open ContinuousLinearMap InnerProductSpace QuantitativeSpectralCut AsymptoticPolarIsometry
open scoped InnerProduct

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- The actual positive cut for a possibly rectangular observation stack. -/
def cutSpace (X : H →L[ℂ] J) (c : ℝ) : Submodule ℂ H := highAt (X.adjoint.comp X) (c^2)
instance cutSpace_complete (X : H →L[ℂ] J) (c : ℝ) : CompleteSpace (cutSpace X c) :=
  highAt_complete _ _

def cutOperator (X : H →L[ℂ] J) (c : ℝ) : H →L[ℂ] J := X.comp (cutSpace X c).starProjection

theorem high_residual_injective (X : H →L[ℂ] J) {c : ℝ} (hc : 0 < c)
    {v : H} (hv : v ∈ cutSpace X c) (hz : X v = 0) : v = 0 := by
  have hs : IsSelfAdjoint (X.adjoint.comp X) := by
    rw [isSelfAdjoint_iff']
    simp only [adjoint_comp, adjoint_adjoint]
  have hh := quadratic_ge_on_highAt (X.adjoint.comp X) hs (c^2) hv
  simp only [comp_apply, hz, map_zero, inner_zero_left, Complex.zero_re] at hh
  have hn : ‖v‖ = 0 := by
    by_contra hn
    exact (not_lt_of_ge hh) (mul_pos (sq_pos_of_pos hc) (sq_pos_of_ne_zero hn))
  exact norm_eq_zero.mp hn

theorem cutOperator_kernel (X : H →L[ℂ] J) {c : ℝ} (hc : 0 < c) :
    (cutOperator X c).ker = (cutSpace X c)ᗮ := by
  ext v
  constructor
  · intro hv
    have hz : (cutSpace X c).starProjection v = 0 :=
      high_residual_injective X hc ((cutSpace X c).starProjection_apply_mem v) hv
    exact (cutSpace X c).starProjection_apply_eq_zero_iff.mp hz
  · intro hv
    change X ((cutSpace X c).starProjection v) = 0
    rw [(cutSpace X c).starProjection_apply_eq_zero_iff.mpr hv, map_zero]

theorem cutOperator_support (X : H →L[ℂ] J) {c : ℝ} (hc : 0 < c) :
    (cutOperator X c).kerᗮ = cutSpace X c := by
  rw [cutOperator_kernel X hc, Submodule.orthogonal_orthogonal]

/-- Truncation gives an exact partial isometry whose initial support is the
selected high cut; no closed-range assumption is introduced. -/
theorem polar_cut_gram (X : H →L[ℂ] J) {c : ℝ} (hc : 0 < c) :
    (polar (cutOperator X c)).adjoint.comp (polar (cutOperator X c)) =
      (cutSpace X c).starProjection := by
  rw [polar_gram]
  congr 1
  exact cutOperator_support X hc

theorem polar_cut_source (X : H →L[ℂ] J) {c : ℝ} (hc : 0 < c) :
    (polar (cutOperator X c)).comp (cutSpace X c).starProjection = polar (cutOperator X c) := by
  apply ContinuousLinearMap.ext
  intro v
  have hh : v - (cutSpace X c).starProjection v ∈ (cutOperator X c).ker := by
    rw [cutOperator_kernel X hc]
    exact (cutSpace X c).sub_starProjection_mem_orthogonal v
  have hz := polar_zero_on_kernel (cutOperator X c) hh
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

#print axioms high_residual_injective
#print axioms cutOperator_kernel
#print axioms cutOperator_support
#print axioms polar_cut_gram
#print axioms polar_cut_source

end QuantitativeSpectralCutPolar
