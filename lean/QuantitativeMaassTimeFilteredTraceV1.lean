module

public import QuantitativeMaassReflectionWaveV1
public import QuantitativeMaassLVKernelTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff InnerProductSpace ENNReal SchwartzMap

namespace QuantitativeMaass

variable (N : ℕ) [NeZero N]
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
    (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

include hr

/-- The original compact time packet has the literal continuous physical
Abel column as its evaluation vector. No smooth extension at cosh zero is used. -/
theorem timeAbelColumn_packet_coeFn (v : AutomorphicSpace N) :
    (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc) v).val
      =ᵐ[quotientMeasure N] (fun x => inner ℂ (timeAbelColumn N f hc he R hR hs x) v) := by
  simp_rw [timeAbelColumn,oneSidedAbelColumn_inner N _
    (evenCoshLift_smoothOn f (f.smooth ⊤) he hc) (evenCoshLift_real f hr)]
  exact evenWavePacket_kernel_coeFn N f (f.smooth ⊤) he hc hr R hR hs v

/-- Actual filtered pretrace for arbitrary bounded filters on the original
compact even time packet. Parseval is on the full quotient Hilbert space. -/
theorem timeWavePacket_filtered_pretrace {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    ∀ᵐ x ∂quotientMeasure N,
      HasSum (fun i => ‖(Wave.shiftedQuotientWavePacket N f
        (compactSmoothWaveWeight f (f.smooth ⊤) hc) (B (b i))).val x‖^2)
      (‖B.adjoint (timeAbelColumn N f hc he R hR hs x)‖^2) := by
  have hrep := ae_all_iff.mpr (fun i => timeAbelColumn_packet_coeFn N f hc he hr R hR hs (B (b i)))
  filter_upwards [hrep] with x hx
  have hp := hasSum_inner_norm_sq b (B.adjoint (timeAbelColumn N f hc he R hR hs x))
  simp only [B.adjoint_inner_left] at hp
  simpa only [hx] using hp

/-- Extended filtered energy identity, including a possibly infinite total
trace. This is proved directly for the one-sided radial lift of the time test. -/
theorem timeWavePacket_filtered_energy_trace {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) :
    (∑' i,ENNReal.ofReal (‖Wave.shiftedQuotientWavePacket N f
      (compactSmoothWaveWeight f (f.smooth ⊤) hc) (B (b i))‖^2))=
      ∫⁻ x,ENNReal.ofReal (‖B.adjoint (timeAbelColumn N f hc he R hR hs x)‖^2)
        ∂quotientMeasure N := by
  let A := Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc)
  have hm (i : ι) : AEMeasurable
      (fun x => ENNReal.ofReal (‖(A (B (b i))).val x‖^2)) (quotientMeasure N) :=
    ((Lp.stronglyMeasurable (A (B (b i))).val).norm.pow 2).measurable.ennreal_ofReal.aemeasurable
  simp_rw [automorphic_norm_square_lintegral]
  rw [← lintegral_tsum hm]
  apply lintegral_congr_ae
  filter_upwards [timeWavePacket_filtered_pretrace N f hc he hr R hR hs b B] with x hx
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hx.summable,hx.tsum_eq]
  exact automorphic_norm_square_lintegral N _

/-- Positive quadratic trace on the original compact even time operator.
The genuine columns supply every premise of the abstract square-root argument. -/
theorem timeWavePacket_positive_kernel_trace {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (hD : 0≤D) :
    (∑' i,ENNReal.ofReal ((inner ℂ (D (Wave.shiftedQuotientWavePacket N f
        (compactSmoothWaveWeight f (f.smooth ⊤) hc) (b i)))
      (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc) (b i))).re))=
      ∫⁻ x,ENNReal.ofReal ((inner ℂ (D (timeAbelColumn N f hc he R hR hs x))
        (timeAbelColumn N f hc he R hR hs x)).re) ∂quotientMeasure N := by
  apply positive_kernel_trace_of_filtered (quotientMeasure N) b _ D
    (Wave.shiftedQuotientWavePacket_isSelfAdjoint N f _ hr) hD
  intro B
  exact timeWavePacket_filtered_energy_trace N f hc he hr R hR hs b B

/-- The actual LV polynomial's original-time geometric trace is bounded by
the actual cuspidal smoothed energy. No quantitative lower estimate is asserted. -/
theorem timeWavePacket_actualLV_trace_le_cuspidal {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (p : ℕ) [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a c : ℤ) (hac : (p:ℤ)*a+(N:ℤ)*c=1) (d : ℕ) :
    (∫⁻ x,ENNReal.ofReal ((inner ℂ
      (actualLVFilter N p hN hpN a c hac d (timeAbelColumn N f hc he R hR hs x))
      (timeAbelColumn N f hc he R hR hs x)).re) ∂quotientMeasure N)≤
    ∑' i,ENNReal.ofReal (‖localCuspidalProjection N hN
      (Wave.shiftedQuotientWavePacket N f (compactSmoothWaveWeight f (f.smooth ⊤) hc) (b i))‖^2) := by
  rw [← timeWavePacket_positive_kernel_trace N f hc he hr R hR hs b
    (actualLVFilter N p hN hpN a c hac d) (actualLVFilter_order N p hN hpN a c hac d).1]
  apply ENNReal.tsum_le_tsum
  intro i
  exact ENNReal.ofReal_le_ofReal (actualLVFilter_quadratic_bounds N p hN hpN hNp hpres a c hac d _).2

#print axioms timeAbelColumn_packet_coeFn
#print axioms timeWavePacket_filtered_pretrace
#print axioms timeWavePacket_filtered_energy_trace
#print axioms timeWavePacket_positive_kernel_trace
#print axioms timeWavePacket_actualLV_trace_le_cuspidal

end QuantitativeMaass
