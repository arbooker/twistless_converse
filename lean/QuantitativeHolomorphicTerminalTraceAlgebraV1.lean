module

public import QuantitativeHolomorphicClosedTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open ContinuousLinearMap AsymptoticFiniteBranch AsymptoticRegularTrace MeasureTheory
open scoped ENNReal

section Algebra
variable {G H K ι : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem contraction_gram_norm_le (V : G →L[ℂ] H) (hV : ‖V‖≤1) :
    ‖V.adjoint.comp V‖≤1 := by
  rw [norm_adjoint_comp_self]
  simpa using mul_le_mul hV hV (norm_nonneg V) zero_le_one

/-- The source trace product has the same linear perturbation loss as the
ambient sandwich, while remaining supported on its fixed terminal source. -/
theorem finiteRowFilter_sourceProduct_difference (qs : Finset ι) (L : ι → H →L[ℂ] K)
    (b : ι → ℝ) (hL : ∀ i, ‖L i‖≤b i) (U V : G →L[ℂ] H)
    (hU : ‖U‖≤1) (hV : ‖V‖≤1) (d : ℕ) :
    ‖(finiteRowFilter qs L b V d).comp (V.adjoint.comp V) -
      (finiteRowFilter qs L b U d).comp (U.adjoint.comp U)‖≤(2*d+2:ℝ)*‖V-U‖ := by
  let FV := finiteRowFilter qs L b V d
  let FU := finiteRowFilter qs L b U d
  let GV := V.adjoint.comp V
  let GU := U.adjoint.comp U
  have he : FV.comp GV-FU.comp GU=(FV-FU).comp GV+FU.comp (GV-GU) := by
    simp only [sub_comp,comp_sub]
    abel
  have hf := finiteRowFilter_difference qs L b hL U V hU hV d
  have hfu := (finiteRowFilter_order qs L b hL U hU d).2.2
  have hgv := contraction_gram_norm_le V hV
  have hg : ‖GV-GU‖≤2*‖V-U‖ :=
    (gram_difference_norm_le U V).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  change ‖FV.comp GV-FU.comp GU‖≤_
  rw [he]
  apply (norm_add_le _ _).trans
  have h1 : ‖(FV-FU).comp GV‖≤(2*d:ℝ)*‖V-U‖ := by
    apply (opNorm_comp_le _ _).trans
    exact (mul_le_mul hf hgv (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  have h2 : ‖FU.comp (GV-GU)‖≤2*‖V-U‖ := by
    apply (opNorm_comp_le _ _).trans
    exact (mul_le_mul hfu hg (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  exact (add_le_add h1 h2).trans_eq (by ring)
end Algebra

theorem regularRetained_trace_le_full (Y H : ℝ)
    (B : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace)
    (hm : ∀ g h, Measurable (fun z => matrix (B z) g h))
    (hp : ∀ z, (B z).IsPositive) (hf : AsymptoticRegularTrace.trace volume B<∞) :
    signedTrace volume (regularRetained Y H B)≤signedTrace volume B := by
  have hpr (z : UpperHalfPlane) : (regularRetained Y H B z).IsPositive := by
    simpa only [regularRetained,AsymptoticOrbitDiagonal.corner_adjoint,comp_assoc] using
      (hp z).adjoint_conj (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z)
  have htr : AsymptoticRegularTrace.trace volume (regularRetained Y H B)≤
      AsymptoticRegularTrace.trace volume B := by
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    change (matrix ((AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z).comp
      ((B z).comp (AsymptoticOrbitDiagonal.corner (retainedRegion Y H) z))) 1 1).re≤_
    rw [regular_corner_sandwich_root]
    classical
    by_cases hz : z∈retainedRegion Y H
    · simp only [Set.indicator_of_mem hz]
      exact le_rfl
    · simp only [Set.indicator_of_notMem hz,Complex.zero_re]
      exact root_nonneg _ (hp z)
  rw [signedTrace_eq_toReal volume _ (regularRetained_matrix_measurable Y H B hm 1 1) hpr,
    signedTrace_eq_toReal volume B (hm 1 1) hp]
  exact ENNReal.toReal_mono hf.ne htr

#print axioms finiteRowFilter_sourceProduct_difference
#print axioms regularRetained_trace_le_full

end QuantitativeHolomorphic
