module

public import QuantitativeEulerEndpointBlockRestrictionV1
public import QuantitativeEulerEndpointCutScalingV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBlockNormalization
open ContinuousLinearMap QuantitativeSpectralDeflationChain QuantitativeSpectralCornerCutRow
open QuantitativeEulerEndpointPrepared

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance closedSubmodule_complete (U : ClosedSubmodule ℂ H) :
    CompleteSpace U.toSubmodule := U.isClosed.completeSpace_coe

theorem step_positive_scale (U : ClosedSubmodule ℂ H) (B : H →L[ℂ] H)
    {r : ℝ} (hr : 0<r) (c : ℝ) : step U (r • B) (r*c)=step U B c := by
  apply SetLike.ext
  intro v
  change v∈nextSpace U.toSubmodule (r • B) (r*c) ↔ v∈nextSpace U.toSubmodule B c
  rw [nextSpace_positive_scale U.toSubmodule B r hr c]

/-- Global row normalization preserves the original hard chain exactly
when its threshold is scaled by the same positive factor. -/
theorem chain_positive_scale (U : ClosedSubmodule ℂ H) (B : ℕ → H →L[ℂ] H)
    {r : ℝ} (hr : 0<r) (c : ℝ) (n : ℕ) :
    chain U (fun i => r • B i) (r*c) n=chain U B c n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [chain,chain,ih,step_positive_scale _ _ hr]

/-- One explicit finite-packet normalization; its denominator is the
actual sum of squared row bounds plus one. -/
def factor (C : ℕ → ℝ) (n : ℕ) : ℝ := (1+∑ i : Fin n, (C i)^2)⁻¹

theorem factor_pos (C : ℕ → ℝ) (n : ℕ) : 0<factor C n := by
  apply inv_pos.mpr
  have hh : 0≤∑ i : Fin n, (C i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

theorem normalized_square_sum (C : ℕ → ℝ) (n : ℕ) :
    (∑ i : Fin n, (factor C n*C i)^2)≤1 := by
  let S := ∑ i : Fin n, (C i)^2
  have hS : 0≤S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hden : 0<1+S := by linarith
  have he : factor C n*(1+S)=1 := inv_mul_cancel₀ hden.ne'
  have hr0 := (factor_pos C n).le
  have hr1 : factor C n≤1 := by
    change (1+S)⁻¹≤1
    exact (inv_le_one₀ hden).mpr (by linarith)
  have hs : (∑ i : Fin n, (factor C n*C i)^2)=(factor C n)^2*S := by
    simp only [mul_pow,← Finset.mul_sum,S]
  rw [hs]
  nlinarith only [he,hr0,hr1,sq_nonneg (factor C n)]

#print axioms step_positive_scale
#print axioms chain_positive_scale
#print axioms factor_pos
#print axioms normalized_square_sum
end QuantitativeEulerEndpointBlockNormalization
