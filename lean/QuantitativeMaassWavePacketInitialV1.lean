module

public import QuantitativeMaassShiftedWavePacketV1

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass.Wave

/-- A normalized packet has its initial value by strong continuity of the
actual quotient wave. The normalization is the cosh-weighted mass appropriate
to the shifted Laplacian, and the support shrinks in the time variable. -/
theorem shiftedQuotientWavePacket_initial {ι : Type*} (l : Filter ι) (N : ℕ)
    (φ : ι → ℝ → ℂ) (hw : ∀ i,ShiftedWaveWeight (φ i))
    (hi : ∀ i,Integrable (fun t => (Real.cosh (t/2):ℂ)*φ i t))
    (hm : ∀ i,(∫ t,(Real.cosh (t/2):ℂ)*φ i t)=1)
    (hn : ∀ i,(∫ t,‖φ i t‖*Real.cosh (|t|/2))≤1)
    (R : ι → ℝ) (hs : ∀ i,Function.support (φ i)⊆Icc (-R i) (R i))
    (hR : Tendsto R l (𝓝 0)) (v : AutomorphicSpace N) :
    Tendsto (fun i => shiftedQuotientWavePacket N (φ i) (hw i) v) l (𝓝 v) := by
  let e : ℝ → AutomorphicSpace N := fun t =>
    shiftedQuotientWave N t v-(Real.cosh (t/2):ℂ) • v
  have hc : Continuous e := (shiftedQuotientWave_stronglyContinuous N v).sub
    ((Complex.continuous_ofReal.comp (Real.continuous_cosh.comp (continuous_id.div_const 2))).smul continuous_const)
  have he0 : e 0=0 := by simp [e,shiftedQuotientWave_zero]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδe⟩ := Metric.continuousAt_iff.mp hc.continuousAt (ε/2) (by positivity)
  have hr := (tendsto_order.mp hR).2 δ hδ
  filter_upwards [hr] with i hri
  have heq : shiftedQuotientWavePacket N (φ i) (hw i) v-v=∫ t,φ i t • e t := by
    rw [shiftedQuotientWavePacket_apply]
    have he (t : ℝ) : φ i t • e t=φ i t • shiftedQuotientWave N t v-
        ((Real.cosh (t/2):ℂ)*φ i t) • v := by
      simp only [e,smul_sub,smul_smul,mul_comm]
    simp_rw [he]
    rw [integral_sub (shiftedQuotientWave_packet_integrable N (hw i) v)
      ((hi i).smul_const v),integral_smul_const,hm i,one_smul]
  have hb : ‖∫ t,φ i t • e t‖≤(ε/2)*(∫ t,‖φ i t‖*Real.cosh (|t|/2)) := by
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le ((hw i).2.const_mul (ε/2))
    filter_upwards with t
    by_cases ht : φ i t=0
    · simp [ht]
    · have hab := abs_le.mpr (hs i ht)
      have hdist : dist t 0<δ := by simpa only [Real.dist_eq,sub_zero] using hab.trans_lt hri
      have he : ‖e t‖≤ε/2 := by simpa only [he0,dist_zero_right] using (hδe hdist).le
      rw [norm_smul]
      have hh := Real.one_le_cosh (|t|/2)
      calc
        _ ≤ ‖φ i t‖*(ε/2) := mul_le_mul_of_nonneg_left he (norm_nonneg _)
        _ ≤ (ε/2)*(‖φ i t‖*Real.cosh (|t|/2)) := by
          have hmul := mul_le_mul_of_nonneg_left hh (mul_nonneg (norm_nonneg (φ i t)) (by positivity : 0≤ε/2))
          nlinarith only [hmul]
  rw [dist_eq_norm,heq]
  exact lt_of_le_of_lt (hb.trans (by nlinarith [hn i])) (by linarith : ε/2<ε)

#print axioms shiftedQuotientWavePacket_initial

end QuantitativeMaass.Wave
