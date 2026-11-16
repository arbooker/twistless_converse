module

public import QuantitativeMaassEnlargedUpperLimitV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand
open scoped Topology InnerProductSpace FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- First-moment majorant loss vanishes at every positive logarithmic-power radius. -/
theorem logPower_majorant_loss_tendsto (K : SchwartzMap ℝ ℝ) (c : ℝ) (hc : 0<c) :
    Tendsto (fun t => (∫ u,|u| * K u)/(logPowerRadius c t*logPowerMargin c t)) atTop (𝓝 0) := by
  have hh := (tendsto_inv_atTop_zero.comp (logPowerRadius_margin_tendsto c hc)).const_mul
    (∫ u,|u| * K u)
  simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using hh

/-- The sharp cusp counting upper coefficient at any positive level. The
kernel, propagation schedule, cusp truncation and all analytic estimates are
supplied internally. No Weyl estimate or trace formula is a hypothesis. -/
theorem principal_sharp_count_eventual_upper {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcus : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he0 : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (ξ : ℝ) (hξ : 0<ξ) :
    ∀ᶠ t in atTop,(Nat.card (principalWindowIndices e t (t+ε t)):ℝ)/(t*ε t)<
      (quotientMeasure N).real univ/(2*Real.pi)+ξ := by
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨K,hK,he,hm,hc⟩ := exists_positive_bandlimited_window_kernel
  obtain ⟨U,hU,htrace⟩ := windowWavePacket_enlarged_upper_limit N hN K he hc hK hm
    (1/2) (by norm_num) (by norm_num) v hv hcus ε hε hproduct
  let loss := fun t => (∫ u,|u| * K u)/(logPowerRadius (1/2) t*logPowerMargin (1/2) t)
  have hloss : Tendsto loss atTop (𝓝 0) := logPower_majorant_loss_tendsto K (1/2) (by norm_num)
  let η := fun t => (1-loss t)^2
  have hη : Tendsto η atTop (𝓝 1) := by
    simpa only [sub_zero,one_pow] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1)).sub hloss).pow 2
  have hquot : Tendsto (fun t => U t/η t) atTop
      (𝓝 ((quotientMeasure N).real univ/(2*Real.pi))) := by
    simpa only [div_one,Pi.div_def] using hU.div hη (by norm_num : (1:ℝ)≠0)
  filter_upwards [hε,htrace,eventually_gt_atTop (2:ℝ),
    hloss.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    hη.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1)),
    hquot.eventually (gt_mem_nhds (lt_add_of_pos_right _ hξ))] with t het htr ht hlt hηt hqt
  have ha : 0<t-logPowerMargin (1/2) t := by linarith [logPowerMargin_le_one (1/2) t]
  have hcount := principalWindow_count_le_packet N hN v hv hcus e he0 hgraph K hK hm he hc
    (logPowerRadius (1/2) t) (logPowerRadius_pos (1/2) t) t (t+ε t)
    (logPowerMargin (1/2) t) (logPowerMargin_pos (1/2) t) ha 1
    (by simpa only [pow_one] using hlt.le)
  have hnorm := div_le_div_of_nonneg_right hcount (mul_pos (show 0<t by linarith) het.1).le
  have htotal : η t*((Nat.card (principalWindowIndices e t (t+ε t)):ℝ)/(t*ε t))≤U t := by
    apply le_trans _ htr
    simpa only [pow_one,mul_div_assoc,η,loss] using hnorm
  apply lt_of_le_of_lt _ hqt
  apply (le_div_iff₀ hηt).mpr
  simpa only [mul_comm] using htotal

#print axioms logPower_majorant_loss_tendsto
#print axioms principal_sharp_count_eventual_upper

end QuantitativeMaass
