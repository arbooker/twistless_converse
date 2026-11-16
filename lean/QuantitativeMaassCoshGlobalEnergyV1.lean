module

public import QuantitativeMaassSmoothPacketTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace QuantitativeMaass

/-- Global energy summability for the precise cosh packet occurring in the
Abel and LV kernel identities, on actual cuspidal eigenfamilies. -/
theorem cuspidal_cosh_packet_square_summable {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Summable (fun i => ‖coshWavePacket N F hF R hR hs (v i)‖^2) := by
  have ht : ContDiff ℝ ∞ (coshTimeTest F) := hF.comp Real.contDiff_cosh
  exact cuspidal_smooth_packet_square_summable N hN v hv hcusp e he hgraph
    (coshTimeTest F) ht (coshTimeTest_compact F R hR hs)

theorem cuspidal_cosh_filtered_square_summable {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R))
    (D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    Summable (fun i => ‖D (coshWavePacket N F hF R hR hs (v i))‖^2) := by
  have h := (cuspidal_cosh_packet_square_summable N hN v hv hcusp e he hgraph F hF R hR hs).mul_left (‖D‖^2)
  apply Summable.of_nonneg_of_le (fun i => sq_nonneg _) _ h
  intro i
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (D.le_opNorm (coshWavePacket N F hF R hR hs (v i))) 2

/-- Absolute convergence of the smoothed quadratic diagonal for every
bounded filter, including the actual LV filter. -/
theorem cuspidal_cosh_quadratic_norm_summable {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R))
    (D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    Summable (fun i => ‖inner ℂ (D (coshWavePacket N F hF R hR hs (v i)))
      (coshWavePacket N F hF R hR hs (v i))‖) := by
  have h := (cuspidal_cosh_packet_square_summable N hN v hv hcusp e he hgraph F hF R hR hs).mul_left ‖D‖
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ h
  intro i
  let w := coshWavePacket N F hF R hR hs (v i)
  calc
    _ ≤ ‖D w‖*‖w‖ := norm_inner_le_norm (D w) w
    _ ≤ (‖D‖*‖w‖)*‖w‖ := mul_le_mul_of_nonneg_right (D.le_opNorm w) (norm_nonneg w)
    _ = ‖D‖*‖w‖^2 := by ring

/-- The positive-part extended smoothed trace is genuinely finite on the
cuspidal eigenfamily; this is stronger than an identity at possibly infinite values. -/
theorem cuspidal_cosh_quadratic_trace_finite {ι : Type*} (N : ℕ) (hN : 0<N)
    (v : ι → AutomorphicSpace N) (hv : Orthonormal ℂ v)
    (hcusp : ∀ i,v i∈localCuspidalSpace N hN) (e : ι → ℝ) (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (v i) ((e i:ℂ) • v i))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R))
    (D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    (∑' i,ENNReal.ofReal ((inner ℂ (D (coshWavePacket N F hF R hR hs (v i)))
      (coshWavePacket N F hF R hR hs (v i))).re))<(∞:ℝ≥0∞) := by
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun i => ENNReal.ofReal_le_ofReal (Complex.re_le_norm _)))
  exact (cuspidal_cosh_quadratic_norm_summable N hN v hv hcusp e he hgraph F hF R hR hs D).tsum_ofReal_lt_top

#print axioms cuspidal_cosh_packet_square_summable
#print axioms cuspidal_cosh_filtered_square_summable
#print axioms cuspidal_cosh_quadratic_norm_summable
#print axioms cuspidal_cosh_quadratic_trace_finite

end QuantitativeMaass
