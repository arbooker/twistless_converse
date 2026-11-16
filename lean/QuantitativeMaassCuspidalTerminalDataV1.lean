module

public import QuantitativeMaassWeightedCuspidalZeroModeV1
public import QuantitativeMaassNonzeroLeftInverseV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory AsymptoticClassicalPetersson

namespace QuantitativeMaass

/-- The inverse of the proved unitary change of cylinder coordinates. -/
def translationToProductCylinder : Lp ℂ 2 (quotientMeasure 0) ≃ₗᵢ[ℂ] AsymptoticCylinder.Space :=
  (LinearIsometryEquiv.ofSurjective productCylinderToTranslation productCylinderToTranslation_surjective).symm

theorem translationToProductCylinder_inverse (f : Lp ℂ 2 (quotientMeasure 0)) :
    productCylinderToTranslation (translationToProductCylinder f)=f :=
  (LinearIsometryEquiv.ofSurjective productCylinderToTranslation
    productCylinderToTranslation_surjective).apply_symm_apply f

/-- Raw terminal restriction of a canonical cusp vector has genuinely
zero horizontal mode, before any reconstruction or Gram normalization. -/
theorem cuspidal_terminal_nonzero (N : ℕ) (hN : 0<N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (x : AutomorphicSpace N) (hx : x∈localCuspidalSpace N hN) :
    AsymptoticCylinderTerminal.projection ε
      (translationToProductCylinder (weightedQuotientEmbedding N hε hv x))∈terminalNonzeroModes ε := by
  apply terminalRestriction_nonzero
  rw [translationToProductCylinder_inverse]
  exact weightedQuotientEmbedding_cuspidal_nonzero N hN hε hv x hx

def cuspidalTerminalData (N : ℕ) (hN : 0<N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) :
    localCuspidalSpace N hN →L[ℂ] terminalNonzeroModes ε :=
  ((AsymptoticCylinderTerminal.projection ε).comp
    (translationToProductCylinder.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((weightedQuotientEmbedding N hε hv).comp (localCuspidalSpace N hN).subtypeL))).codRestrict
        (terminalNonzeroModes ε) (fun x : localCuspidalSpace N hN =>
          cuspidal_terminal_nonzero N hN hε hv x.val x.property)

theorem cuspidalTerminalData_apply (N : ℕ) (hN : 0<N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) (x : localCuspidalSpace N hN) :
    (cuspidalTerminalData N hN hε hv x : AsymptoticCylinder.Space)=
      AsymptoticCylinderTerminal.projection ε
        (translationToProductCylinder (weightedQuotientEmbedding N hε hv x.val)) := rfl

theorem cuspidalTerminalData_norm_le (N : ℕ) (hN : 0<N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v) (x : localCuspidalSpace N hN) :
    ‖cuspidalTerminalData N hN hε hv x‖≤(quotientWeightBound ε+1)*‖x‖ := by
  have hp := (AsymptoticCylinderTerminal.projection ε).le_opNorm
    (translationToProductCylinder (weightedQuotientEmbedding N hε hv x.val))
  have hb := mul_le_mul_of_nonneg_right (AsymptoticCylinderTerminal.projection_norm_le ε)
    (norm_nonneg (translationToProductCylinder (weightedQuotientEmbedding N hε hv x.val)))
  have hJ := (weightedQuotientEmbedding N hε hv).le_opNorm x.val
  have hC := mul_le_mul_of_nonneg_right (weightedQuotientEmbedding_norm_le N hε hv) (norm_nonneg x.val)
  have ht : ‖weightedQuotientEmbedding N hε hv x.val‖≤(quotientWeightBound ε+1)*‖x‖ := hJ.trans hC
  exact (hp.trans hb).trans (by simpa only [one_mul,LinearIsometryEquiv.norm_map] using ht)

#print axioms translationToProductCylinder_inverse
#print axioms cuspidal_terminal_nonzero
#print axioms cuspidalTerminalData_apply
#print axioms cuspidalTerminalData_norm_le

end QuantitativeMaass
