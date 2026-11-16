module

public import QuantitativeMaassCylinderMeanCancellationV1
public import QuantitativeMaassCylinderBandZeroModeV1
public import QuantitativeMaassCylinderCenteredCappedV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/-- Centering the actual weighted column changes none of its pairings
with the full closed nonzero-mode cylinder space. -/
theorem cylinderCenteredCappedColumn_nonzero (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ → ℂ)) (he : Function.Even f)
    (hr : ∀ s,star (f s)=f s) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (ε : ℝ) (t : ℕ)
    (z : ℍ) (v : Lp ℂ 2 (quotientMeasure 0)) (hv : v∈cylinderNonzeroModes) :
    inner ℂ (cylinderCenteredCappedColumn f hc he R hR hs ε t z) v=
      inner ℂ (cylinderCappedTimeColumn f (f.smooth ⊤) he hc R hR
        (evenCoshLift_support_of_time_support f R hR hs) ε t z) v := by
  let l : ℝ → ℝ := fun y => Real.log ((min (y/ε) 1)^t)
  have hl : Measurable l := Real.measurable_log.comp
    (((measurable_id.div_const ε).min measurable_const).pow_const t)
  have hv' := cylinderNonzeroModes_inverse_row l hl ⌈(t:ℝ)*R+1⌉₊ ⌊l z.im⌋ v hv
  unfold cylinderCenteredCappedColumn cylinderCappedTimeColumn
  rw [LogBands.conjugatedColumn_inner,LogBands.conjugatedColumn_inner]
  unfold cylinderCenteredTimeColumn
  rw [inner_sub_left]
  have hm := cylinderAbelColumn_mean_orthogonal (evenCoshLift f)
    (evenCoshLift_smoothOn f (f.smooth ⊤) he hc) (evenCoshLift_real f hr)
    R hR (evenCoshLift_support_of_time_support f R hR hs) z _ hv'
  change inner ℂ (∫ y in Icc (0:ℝ) 1,cylinderTimeColumn f hc he R hR hs (y+ᵥz))
    (LogBands.rowInverseSum (quotientMeasure 0)
      (fun w => Real.log (cappedHeightWeight ε t w)) (cappedHeightWeight_log_measurable ε t)
      ⌈(t:ℝ)*R+1⌉₊ ⌊Real.log (cappedHeightWeight ε t z)⌋ v)=0 at hm
  rw [hm,sub_zero]
  rfl

#print axioms cylinderCenteredCappedColumn_nonzero

end QuantitativeMaass
