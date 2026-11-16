module

public import QuantitativeMaassShiftedWavePacketV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass.Wave

/-- Subtraction is respected by the actual strongly integrated packets. -/
theorem shiftedQuotientWavePacket_sub (N : ℕ) (φ ψ : ℝ → ℂ)
    (hφ : ShiftedWaveWeight φ) (hψ : ShiftedWaveWeight ψ)
    (hd : ShiftedWaveWeight (fun t => φ t-ψ t)) :
    shiftedQuotientWavePacket N (fun t => φ t-ψ t) hd=
      shiftedQuotientWavePacket N φ hφ-shiftedQuotientWavePacket N ψ hψ := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [sub_apply,shiftedQuotientWavePacket_apply]
  have he (t : ℝ) : (φ t-ψ t) • shiftedQuotientWave N t f=
      φ t • shiftedQuotientWave N t f-ψ t • shiftedQuotientWave N t f :=
    sub_smul (φ t) (ψ t) (shiftedQuotientWave N t f)
  simp_rw [he]
  exact integral_sub (shiftedQuotientWave_packet_integrable N hφ f)
    (shiftedQuotientWave_packet_integrable N hψ f)

theorem shiftedQuotientWavePacket_sub_norm (N : ℕ) (φ ψ : ℝ → ℂ)
    (hφ : ShiftedWaveWeight φ) (hψ : ShiftedWaveWeight ψ)
    (hd : ShiftedWaveWeight (fun t => φ t-ψ t)) :
    ‖shiftedQuotientWavePacket N φ hφ-shiftedQuotientWavePacket N ψ hψ‖≤
      ∫ t,‖φ t-ψ t‖*Real.cosh (|t|/2) := by
  rw [← shiftedQuotientWavePacket_sub N φ ψ hφ hψ hd]
  exact shiftedQuotientWavePacket_norm N _ hd

/-- A uniform amplitude and compact time support give a concrete packet
norm bound including the exceptional-spectrum weight. -/
theorem shiftedQuotientWavePacket_support_bound (N : ℕ) (φ : ℝ → ℂ)
    (hφ : ShiftedWaveWeight φ) (R B : ℝ) (hR : 0≤R) (hB : 0≤B)
    (hs : Function.support φ⊆Icc (-R) R) (hb : ∀ t,‖φ t‖≤B) :
    ‖shiftedQuotientWavePacket N φ hφ‖≤(B*Real.cosh (R/2))*(2*R) := by
  have he : (∫ t,‖φ t‖*Real.cosh (|t|/2))=
      ∫ t in Icc (-R) R,‖φ t‖*Real.cosh (|t|/2) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hz : φ t=0 := by by_contra hn; exact ht (hs hn)
    simp only [hz,norm_zero,zero_mul]
  have hh := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Icc (-R) R)
    (f:=fun t => ‖φ t‖*Real.cosh (|t|/2)) (by simp) (fun t ht => by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have ht' : |t|≤R := abs_le.mpr ht
      have hw : Real.cosh (|t|/2)≤Real.cosh (R/2) := by
        apply Real.cosh_le_cosh.mpr
        rw [abs_of_nonneg (by positivity : 0≤|t|/2),abs_of_nonneg (by positivity : 0≤R/2)]
        linarith
      exact mul_le_mul (hb t) hw (Real.cosh_pos _).le hB)
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun t => by positivity)),
    Real.volume_real_Icc_of_le (by linarith : -R≤R)] at hh
  have h := shiftedQuotientWavePacket_norm N φ hφ
  rw [he] at h
  exact h.trans (by simpa only [sub_neg_eq_add,← two_mul] using hh)

#print axioms shiftedQuotientWavePacket_sub
#print axioms shiftedQuotientWavePacket_support_bound

end QuantitativeMaass.Wave
