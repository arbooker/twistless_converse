module

public import QuantitativeMaassWaveSeedPropagationV1
public import QuantitativeMaassShiftedWavePacketV1
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology

namespace QuantitativeMaass.Weighted

open QuantitativeArithmeticMaassWave

theorem poincare_wave_observation_zero (N : ℕ) (b w : Cutoff N) (u : SmoothUpperSeed)
    (c d : ℝ)
    (hu : ∀ Z : ℍ, c<(upperFunction b.value Z).re → upperFunction u.toFun Z=0)
    (hw : ∀ᵐ Z ∂quotientMeasure N,
      (upperFunction b.value Z).re<d → upperFunction w.value Z=0)
    (t : ℝ) (hsep : c+|b.gradientBound| * |t|<d) :
    multiplier N w (Wave.shiftedQuotientWave N t (poincareSeedVector N u)).val=0 := by
  rw [← shiftedWave_abs_time N t]
  exact separated_wave_vanishes N b w (friedrichsGraph_poincareSeed N u)
    (friedrichsGraph_poincareSeed N u.laplacian) c d
    (seed_initial_value_support N b u c hu) (seed_initial_gradient_support N b u c hu)
    hw (abs_nonneg t) hsep

/-- A compact-time wave packet inherits the support radius of its constituent
waves. The packet and the observation are actual bounded quotient operators. -/
theorem poincare_packet_observation_zero (N : ℕ) (b w : Cutoff N) (u : SmoothUpperSeed)
    (c d : ℝ)
    (hu : ∀ Z : ℍ, c<(upperFunction b.value Z).re → upperFunction u.toFun Z=0)
    (hw : ∀ᵐ Z ∂quotientMeasure N,
      (upperFunction b.value Z).re<d → upperFunction w.value Z=0)
    {φ : ℝ → ℂ} (hφ : Wave.ShiftedWaveWeight φ)
    {R : ℝ} (hs : Function.support φ⊆Icc (-R) R)
    (hsep : c+|b.gradientBound| * R<d) :
    multiplier N w (Wave.shiftedQuotientWavePacket N φ hφ (poincareSeedVector N u)).val=0 := by
  let K := (multiplier N w).comp (AutomorphicSpace N).subtypeL
  rw [Wave.shiftedQuotientWavePacket_apply]
  change K (∫ t, φ t • Wave.shiftedQuotientWave N t (poincareSeedVector N u))=0
  rw [← K.integral_comp_comm (Wave.shiftedQuotientWave_packet_integrable N hφ _)]
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  by_cases hz : φ t=0
  · simp [hz]
  · have ht : |t|≤R := abs_le.mpr (hs hz)
    have hsep' : c+|b.gradientBound| * |t|<d := by
      have hm := mul_le_mul_of_nonneg_left ht (abs_nonneg b.gradientBound)
      linarith
    have h := poincare_wave_observation_zero N b w u c d hu hw t hsep'
    change K (φ t • Wave.shiftedQuotientWave N t (poincareSeedVector N u))=0
    rw [map_smul]
    change φ t • multiplier N w (Wave.shiftedQuotientWave N t (poincareSeedVector N u)).val=0
    rw [h,smul_zero]

#print axioms poincare_packet_observation_zero

end QuantitativeMaass.Weighted
