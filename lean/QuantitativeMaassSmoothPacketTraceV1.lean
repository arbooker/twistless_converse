module

public import QuantitativeMaassSmoothPacketDecayV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace QuantitativeMaass

/-- Compact smooth time tests satisfy the actual exceptional-spectrum
integrability condition in the definition of the wave packet. -/
theorem compactSmoothWaveWeight (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : Wave.ShiftedWaveWeight φ :=
  ⟨hφ.continuous.aestronglyMeasurable,
    (show Continuous (fun t => ‖φ t‖*Real.cosh (|t|/2)) by fun_prop).integrable_of_hasCompactSupport
      hc.norm.mul_right⟩

/-- Global, unlocalized absolute summability for the actual wave packet
on a genuine orthonormal cuspidal eigenfamily. -/
theorem cuspidal_smooth_packet_norm_summable {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Summable (fun i => ‖Wave.shiftedQuotientWavePacket N φ (compactSmoothWaveWeight φ hφ hc) (v i)‖) := by
  apply (cuspidal_smooth_packet_summable N hN v hv hcusp e he hgraph φ hφ hc).congr
  intro i
  rw [Wave.shiftedQuotientWavePacket_eigen N φ _ (he i) (hgraph i),norm_smul,hv.norm_eq_one i,mul_one]
  rfl

theorem cuspidal_smooth_packet_square_summable {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Summable (fun i => ‖Wave.shiftedQuotientWavePacket N φ (compactSmoothWaveWeight φ hφ hc) (v i)‖^2) := by
  let P := Wave.shiftedQuotientWavePacket N φ (compactSmoothWaveWeight φ hφ hc)
  have h := (cuspidal_smooth_packet_norm_summable N hN v hv hcusp e he hgraph φ hφ hc).mul_left ‖P‖
  apply Summable.of_nonneg_of_le (fun i => sq_nonneg _) _ h
  intro i
  have hb : ‖P (v i)‖≤‖P‖ := by simpa only [hv.norm_eq_one i,mul_one] using P.le_opNorm (v i)
  change ‖P (v i)‖^2≤‖P‖*‖P (v i)‖
  nlinarith only [mul_le_mul_of_nonneg_right hb (norm_nonneg (P (v i)))]

/-- Absolute convergence of the literal diagonal sum. A complete basis can
be supplied by the cuspidal spectral decomposition when forming the trace. -/
theorem cuspidal_smooth_packet_diagonal_summable {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Summable (fun i => ‖inner ℂ (v i)
      (Wave.shiftedQuotientWavePacket N φ (compactSmoothWaveWeight φ hφ hc) (v i))‖) := by
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _
    (cuspidal_smooth_packet_norm_summable N hN v hv hcusp e he hgraph φ hφ hc)
  intro i
  simpa only [hv.norm_eq_one i,one_mul] using
    norm_inner_le_norm (v i) (Wave.shiftedQuotientWavePacket N φ (compactSmoothWaveWeight φ hφ hc) (v i))

#print axioms compactSmoothWaveWeight
#print axioms cuspidal_smooth_packet_norm_summable
#print axioms cuspidal_smooth_packet_square_summable
#print axioms cuspidal_smooth_packet_diagonal_summable

end QuantitativeMaass
