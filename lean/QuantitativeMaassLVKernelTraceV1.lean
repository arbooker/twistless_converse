module

public import QuantitativeMaassFilteredPretraceV1
public import QuantitativeMaassPositiveEnergyTraceV1
public import QuantitativeMaassShiftedPacketDomainV1
public import QuantitativeMaassLVCuspidalTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff ENNReal

namespace QuantitativeMaass

/-- Transfer the proved filtered-energy identity to a positive quadratic
trace. The application below supplies the identity for every bounded filter. -/
theorem positive_kernel_trace_of_filtered {H X ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [MeasurableSpace X]
    (μ : Measure X) (b : HilbertBasis ι ℂ H) (K D : H →L[ℂ] H)
    (hK : IsSelfAdjoint K) (hD : 0≤D) (row : X → H)
    (hkernel : ∀ B : H →L[ℂ] H,extendedHilbertEnergy b (K.comp B)=
      ∫⁻ x,ENNReal.ofReal (‖B.adjoint (row x)‖^2) ∂μ) :
    (∑' i,ENNReal.ofReal ((inner ℂ (D (K (b i))) (K (b i))).re))=
      ∫⁻ x,ENNReal.ofReal ((inner ℂ (D (row x)) (row x)).re) ∂μ := by
  rw [positive_smoothed_energy b K D hK hD,hkernel]
  have hS : IsSelfAdjoint (CFC.sqrt D) :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg D)).isSelfAdjoint
  simp only [hS.adjoint_eq,positive_sqrt_norm_square D hD]

/-- Positive smoothed trace equals the positive filter applied to literal
Abel kernel rows. This follows from the proved Abel identity and Parseval,
without assuming a trace formula or a discrete spectral decomposition. -/
theorem coshWavePacket_positive_kernel_trace {ι : Type*} [Countable ι] (N : ℕ) [NeZero N]
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (hD : 0≤D)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∑' i,ENNReal.ofReal ((inner ℂ (D (coshWavePacket N F hF R hR hs (b i)))
        (coshWavePacket N F hF R hR hs (b i))).re))=
      ∫⁻ x,ENNReal.ofReal ((inner ℂ
        (D (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
          x R hR (abelProfile_support F _ hs))))
        (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
          x R hR (abelProfile_support F _ hs)))).re) ∂quotientMeasure N := by
  have hK : IsSelfAdjoint (coshWavePacket N F hF R hR hs) :=
    Wave.shiftedQuotientWavePacket_isSelfAdjoint N (coshTimeTest F)
      (coshTimeTest_waveWeight F hF R hR hs) (fun t => hr (Real.cosh t))
  apply positive_kernel_trace_of_filtered (quotientMeasure N) b _ D hK hD
  intro B
  exact coshWavePacket_filtered_energy_trace N b B F hF hc hr R hR hs

/-- The geometric LV smoothed trace is a genuine lower bound for the
actual cuspidal smoothed energy. Its quantitative main term/error estimates
remain to be established; the extended-real inequality alone is not Weyl. -/
theorem actualLVFilter_kernel_trace_le_cuspidal {ι : Type*} [Countable ι]
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hN : 0<N) (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a c : ℤ) (hac : (p:ℤ)*a+(N:ℤ)*c=1) (d : ℕ)
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∫⁻ x,ENNReal.ofReal ((inner ℂ
        (actualLVFilter N p hN hpN a c hac d
          (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
            x R hR (abelProfile_support F _ hs))))
        (poincareSeedVector N (radialSeed (abelProfile F) (abelProfile_smooth F hF hc)
          x R hR (abelProfile_support F _ hs)))).re) ∂quotientMeasure N)≤
      ∑' i,ENNReal.ofReal (‖localCuspidalProjection N hN (coshWavePacket N F hF R hR hs (b i))‖^2) := by
  rw [← coshWavePacket_positive_kernel_trace N b (actualLVFilter N p hN hpN a c hac d)
    (actualLVFilter_order N p hN hpN a c hac d).1 F hF hc hr R hR hs]
  apply ENNReal.tsum_le_tsum
  intro i
  exact ENNReal.ofReal_le_ofReal (actualLVFilter_quadratic_bounds N p hN hpN hNp hpres a c hac d
    (coshWavePacket N F hF R hR hs (b i))).2

#print axioms positive_kernel_trace_of_filtered
#print axioms coshWavePacket_positive_kernel_trace
#print axioms actualLVFilter_kernel_trace_le_cuspidal

end QuantitativeMaass
