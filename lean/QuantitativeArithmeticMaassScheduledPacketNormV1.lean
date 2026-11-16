module

public import QuantitativeMaassWindowOperatorBoundsV1
public import QuantitativeMaassWindowIdentityTermV1
public import QuantitativeMaassCylinderTimePacketV1
public import QuantitativeMaassStrongMomentScheduleV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Filter Set MeasureTheory ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- Conjugating the actual window packet onto cylinder L2 does not increase
its norm. This applies at level zero, with continuous spectrum. -/
theorem cylinderWindowPacket_norm_le (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) :
    ‖cylinderTimePacket (windowTimeSchwartz K hc R hR a b)
      ((windowTimeSchwartz K hc R hR a b).smooth ⊤)
      (symmetricWindowTimeTest_compact K hc R a b hR)‖≤
        ‖windowWavePacket 0 K hc R hR a b‖ := by
  apply opNorm_le_bound _ (norm_nonneg (windowWavePacket 0 K hc R hR a b))
  intro v
  change ‖windowWavePacket 0 K hc R hR a b (cylinderAutomorphic v)‖≤_
  simpa only [cylinderAutomorphic.norm_map] using
    (windowWavePacket 0 K hc R hR a b).le_opNorm (cylinderAutomorphic v)

/-- The propagation selected by epsilon*slowScale tending to infinity
makes the square norm of the actual packet smaller than exp(strongScale).
This is uniform in the level and includes the exceptional spectral weight. -/
theorem windowPacket_scheduled_norm (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∀ᶠ t in atTop,∀ N : ℕ,∀ hR : 0<propagation (slowScale t) (ε t),
      ‖windowWavePacket N K hc (propagation (slowScale t) (ε t)) hR t (t+ε t)‖^2≤
        Real.exp (Strong.strongScale t) := by
  obtain ⟨B,C,hB,hC,hbound⟩ := windowWavePacket_uniform_square_norm K hc
  have hL := slowScale_tendsto.eventually (eventually_gt_atTop (0:ℝ))
  have hprop := (propagation_limits slowScale ε hL (hε.mono (fun _ h => h.1)) hproduct).1
  filter_upwards [hε,slowScale_tendsto.eventually (eventually_ge_atTop (1:ℝ)),
    slowScale_tendsto.eventually (eventually_ge_atTop (C+B+2)),
    hprop.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with t he hl hlarge hp
  intro N hR
  let L := slowScale t
  let R := propagation L (ε t)
  have hLp : 0<L := by dsimp only [L]; linarith
  have hRL : R≤L := (div_le_one hLp).mp hp.le
  have hε2 : (ε t)^2≤1 := by nlinarith [he.1,he.2]
  have hR0 : 0≤R := Real.sqrt_nonneg _
  have hLe : L≤Real.exp L := by linarith [Real.add_one_le_exp L]
  have hCe : C≤Real.exp (C*L) := by
    have hh := Real.add_one_le_exp (C*L)
    have hx : C≤C*L := by nlinarith [hC,hl]
    linarith
  have hb := hbound N R hR t (t+ε t) (by linarith [he.1])
  have hmain : ‖windowWavePacket N K hc R hR t (t+ε t)‖^2≤
      C*(ε t)^2*R^2*Real.exp (B*R) := by simpa only [add_sub_cancel_left] using hb
  apply hmain.trans
  calc
    _ ≤ C*1*L^2*Real.exp (B*L) := by gcongr
    _ = C*L^2*Real.exp (B*L) := by ring
    _ ≤ Real.exp (C*L)*(Real.exp L)^2*Real.exp (B*L) := by gcongr
    _ = Real.exp ((C+B+2)*L) := by
      rw [pow_two,←Real.exp_add,←Real.exp_add,←Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Strong.strongScale t) := by
      apply Real.exp_le_exp.mpr
      change (C+B+2)*L≤L^2
      nlinarith [hLp,hlarge]

/-- The same scheduled bound for the literal cylinder operator used in
all column traces and finite-source error comparisons. -/
theorem cylinderWindowPacket_scheduled_norm (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    ∀ᶠ t in atTop,∀ hR : 0<propagation (slowScale t) (ε t),
      let R := propagation (slowScale t) (ε t)
      let f := windowTimeSchwartz K hc R hR t (t+ε t)
      ‖cylinderTimePacket f (f.smooth ⊤)
        (symmetricWindowTimeTest_compact K hc R t (t+ε t) hR)‖^2≤
          Real.exp (Strong.strongScale t) := by
  filter_upwards [windowPacket_scheduled_norm K hc ε hε hproduct] with t ht
  intro hR
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (cylinderWindowPacket_norm_le K hc _ hR t (t+ε t)) 2).trans (ht 0 hR)

#print axioms cylinderWindowPacket_norm_le
#print axioms windowPacket_scheduled_norm
#print axioms cylinderWindowPacket_scheduled_norm
end QuantitativeMaass
