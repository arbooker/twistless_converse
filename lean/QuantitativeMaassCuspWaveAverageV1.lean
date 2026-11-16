module

public import QuantitativeMaassCuspConstantOperatorV1
public import QuantitativeMaassShiftedWavePacketV1
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology MatrixGroups InnerProductSpace

namespace QuantitativeMaass.Wave

/-- Actual constant terms of the quotient wave vary continuously in local
L2, for arbitrary quotient L2 initial states. -/
theorem cuspConstantLocal_wave_continuous (N : ℕ) (s : SL(2,ℤ)) (a b : ℝ) (ha : 0<a)
    (f : AutomorphicSpace N) :
    Continuous (fun t => cuspConstantLocal N s a b ha (shiftedQuotientWave N t f)) :=
  (cuspConstantLocal N s a b ha).continuous.comp (shiftedQuotientWave_stronglyContinuous N f)

/-- The constructed local constant-term operator passes through the
actual Bochner wave packet; all integrability follows from the spectral
cosh bound, including the exceptional spectrum. -/
theorem cuspConstantLocal_wavePacket (N : ℕ) (s : SL(2,ℤ)) (a b : ℝ) (ha : 0<a)
    (φ : ℝ → ℂ) (hφ : ShiftedWaveWeight φ) (f : AutomorphicSpace N) :
    cuspConstantLocal N s a b ha (shiftedQuotientWavePacket N φ hφ f)=
      ∫ t, φ t • cuspConstantLocal N s a b ha (shiftedQuotientWave N t f) := by
  rw [shiftedQuotientWavePacket_apply]
  have he := (cuspConstantLocal N s a b ha).integral_comp_comm
    (shiftedQuotientWave_packet_integrable N hφ f)
  simpa only [map_smul] using he.symm

/-- Explicit local norm control for the averaged wave. -/
theorem cuspConstantLocal_wave_bound (N : ℕ) (s : SL(2,ℤ)) (a b : ℝ) (ha : 0<a)
    (f : AutomorphicSpace N) (t : ℝ) :
    ‖cuspConstantLocal N s a b ha (shiftedQuotientWave N t f)‖≤
      ‖cuspRestriction N s _ (upperRectangle_compact 0 N a b ha)‖ *
        (Real.cosh (|t|/2)*‖f‖) := by
  apply ((cuspConstantLocal N s a b ha).le_opNorm _).trans
  apply mul_le_mul (cuspConstantLocal_norm_le N s a b ha)
    (shiftedQuotientWave_apply_norm_le N t f) (norm_nonneg _)
    (norm_nonneg (cuspRestriction N s _ (upperRectangle_compact 0 N a b ha)))

#print axioms cuspConstantLocal_wave_continuous
#print axioms cuspConstantLocal_wavePacket
#print axioms cuspConstantLocal_wave_bound

end QuantitativeMaass.Wave
