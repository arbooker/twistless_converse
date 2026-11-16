module

public import QuantitativeMaassLVCuspidalProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology MatrixGroups InnerProductSpace BigOperators

namespace QuantitativeMaass

variable (N p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
  (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
  (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1) (d : ℕ)

include hNp hpres

/-- A pointwise comparison against the genuine cuspidal projection.
No trace-class or discrete-spectrum premise is required. -/
theorem actualLVFilter_quadratic_bounds (f : AutomorphicSpace N) :
    0 ≤ (⟪actualLVFilter N p hN hpN a b hab d f,f⟫_ℂ).re ∧
    (⟪actualLVFilter N p hN hpN a b hab d f,f⟫_ℂ).re ≤
      ‖localCuspidalProjection N hN f‖^2 := by
  refine ⟨(ContinuousLinearMap.nonneg_iff_isPositive.mp
    (actualLVFilter_order N p hN hpN a b hab d).1).re_inner_nonneg_left f,?_⟩
  have h := (ContinuousLinearMap.le_def.mp
    (actualLVFilter_le_localCuspidalProjection N p hN hpN hNp hpres a b hab d)).re_inner_nonneg_left f
  have he : (⟪localCuspidalProjection N hN f,f⟫_ℂ).re =
      ‖localCuspidalProjection N hN f‖^2 :=
    (localCuspidalSpace N hN).re_inner_starProjection_eq_normSq f
  simp only [_root_.sub_apply,inner_sub_left,map_sub] at h
  change 0 ≤ (⟪localCuspidalProjection N hN f,f⟫_ℂ).re -
    (⟪actualLVFilter N p hN hpN a b hab d f,f⟫_ℂ).re at h
  linarith

/-- The actual LV filter vanishes on the orthogonal complement of the
geometrically defined all-cusp space. -/
theorem actualLVFilter_orthogonal_zero (f : AutomorphicSpace N)
    (hf : f∈(localCuspidalSpace N hN)ᗮ) :
    actualLVFilter N p hN hpN a b hab d f=0 := by
  have hp : localCuspidalProjection N hN f=0 :=
    (Submodule.starProjection_apply_eq_zero_iff (localCuspidalSpace N hN)).mpr hf
  have he := congrArg (fun T : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => T f)
    (actualLVFilter_localCuspidalProjection N p hN hpN hNp hpres a b hab d)
  change actualLVFilter N p hN hpN a b hab d (localCuspidalProjection N hN f)=_ at he
  rw [hp,map_zero] at he
  exact he.symm

/-- Finite smoothed diagonal sums of the actual LV operator are positive
and bounded by the actual cuspidal energy. The finite-family formulation
avoids assuming the spectral or trace estimates still needed for Weyl. -/
theorem actualLVFilter_finite_trace_bounds {ι : Type*} (s : Finset ι)
    (v : ι → AutomorphicSpace N)
    (K : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    0 ≤ ∑ i∈s, (⟪actualLVFilter N p hN hpN a b hab d (K (v i)),K (v i)⟫_ℂ).re ∧
    (∑ i∈s, (⟪actualLVFilter N p hN hpN a b hab d (K (v i)),K (v i)⟫_ℂ).re) ≤
      ∑ i∈s, ‖localCuspidalProjection N hN (K (v i))‖^2 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ =>
      (actualLVFilter_quadratic_bounds N p hN hpN hNp hpres a b hab d (K (v i))).1)
  · exact Finset.sum_le_sum (fun i _ =>
      (actualLVFilter_quadratic_bounds N p hN hpN hNp hpres a b hab d (K (v i))).2)

#print axioms actualLVFilter_quadratic_bounds
#print axioms actualLVFilter_orthogonal_zero
#print axioms actualLVFilter_finite_trace_bounds

end QuantitativeMaass
