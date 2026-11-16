module

public import QuantitativeMaassAbelEnergyTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff ENNReal

namespace QuantitativeMaass

/-- Parseval after an arbitrary actual bounded filter: its adjoint acts on
the geometric kernel row. No eigenbasis or trace finiteness is assumed. -/
theorem radialKernel_filtered_parseval {ι : Type*} (N : ℕ)
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hr : ∀ q,star (g q)=g q)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) (x : ℍ) :
    HasSum (fun i => ‖(radialKernelData N g hg R hR hs).output (B (b i)).val x‖^2)
      (‖B.adjoint (poincareSeedVector N (radialSeed g hg x R hR hs))‖^2) := by
  have h := hasSum_inner_norm_sq b (B.adjoint (poincareSeedVector N (radialSeed g hg x R hR hs)))
  simp_rw [B.adjoint_inner_left,radialKernel_column_inner N g hg R hR hs hr x] at h
  exact h

/-- Local pretrace for the actual spectral smoothing composed with a
bounded filter, including the existing genuine LV filter as an instance. -/
theorem coshWavePacket_filtered_pretrace {ι : Type*} [Countable ι] (N : ℕ) [NeZero N]
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    ∀ᵐ x ∂quotientMeasure N,
      HasSum (fun i => ‖(coshWavePacket N F hF R hR hs (B (b i))).val x‖^2)
        (‖B.adjoint (poincareSeedVector N (radialSeed (abelProfile F)
          (abelProfile_smooth F hF hc) x R hR (abelProfile_support F _ hs)))‖^2) := by
  have he : ∀ᵐ x ∂quotientMeasure N,∀ i,
      (coshWavePacket N F hF R hR hs (B (b i))).val x=
        (radialKernelData N (abelProfile F) (abelProfile_smooth F hF hc)
          R hR (abelProfile_support F _ hs)).output (B (b i)).val x :=
    ae_all_iff.mpr (fun i => coshWavePacket_coeFn N F hF hc hr R hR hs (B (b i)))
  filter_upwards [he] with x hx
  simp_rw [hx]
  exact radialKernel_filtered_parseval N b B (abelProfile F) (abelProfile_smooth F hF hc)
    (abelProfile_real F hr) R hR (abelProfile_support F _ hs) x

/-- The exact extended square-energy trace of the actual filtered spectral
packet. Quantitative geometry must still bound the right-hand integral. -/
theorem coshWavePacket_filtered_energy_trace {ι : Type*} [Countable ι] (N : ℕ) [NeZero N]
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (B : AutomorphicSpace N →L[ℂ] AutomorphicSpace N)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∑' i,ENNReal.ofReal (‖coshWavePacket N F hF R hR hs (B (b i))‖^2))=
      ∫⁻ x,ENNReal.ofReal (‖B.adjoint (poincareSeedVector N (radialSeed (abelProfile F)
        (abelProfile_smooth F hF hc) x R hR (abelProfile_support F _ hs)))‖^2) ∂quotientMeasure N := by
  let K := coshWavePacket N F hF R hR hs
  have hm (i : ι) : AEMeasurable
      (fun x => ENNReal.ofReal (‖(K (B (b i))).val x‖^2)) (quotientMeasure N) :=
    ((Lp.stronglyMeasurable (K (B (b i))).val).norm.pow 2).measurable.ennreal_ofReal.aemeasurable
  simp_rw [automorphic_norm_square_lintegral]
  rw [← lintegral_tsum hm]
  apply lintegral_congr_ae
  filter_upwards [coshWavePacket_filtered_pretrace N b B F hF hc hr R hR hs] with x hx
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hx.summable,hx.tsum_eq]
  exact automorphic_norm_square_lintegral N _

#print axioms radialKernel_filtered_parseval
#print axioms coshWavePacket_filtered_pretrace
#print axioms coshWavePacket_filtered_energy_trace

end QuantitativeMaass
