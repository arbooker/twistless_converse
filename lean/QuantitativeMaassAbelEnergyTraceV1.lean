module

public import QuantitativeMaassRadialPretraceV1
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff ENNReal

namespace QuantitativeMaass

/-- Extended square-energy formula for an actual quotient L2 vector. -/
theorem automorphic_norm_square_lintegral (N : ℕ) (v : AutomorphicSpace N) :
    ENNReal.ofReal (‖v‖^2)=∫⁻ x,ENNReal.ofReal (‖v.val x‖^2) ∂quotientMeasure N := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp v.val).aestronglyMeasurable).mp (Lp.memLp v.val)
  change ENNReal.ofReal (‖v.val‖^2)=_
  rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
  exact ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))

/-- The squared geometric row is integrable and its extended integral is
exactly its genuine quotient-Hilbert norm. -/
theorem radialKernel_row_lintegral (N : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0≤R) (hs : Function.support g⊆Iic (Real.cosh R)) (x : ℍ) :
    ENNReal.ofReal (∫ y,‖radialPoincareKernel N g x y‖^2 ∂quotientMeasure N)=
      ∫⁻ y,ENNReal.ofReal (‖radialPoincareKernel N g x y‖^2) ∂quotientMeasure N := by
  rw [← radialKernel_row_energy N g hg R hR hs x,automorphic_norm_square_lintegral]
  apply lintegral_congr_ae
  filter_upwards [poincareSeedVector_coeFn N (radialSeed g hg x R hR hs)] with y hy
  rw [hy]
  rfl

/-- Exact nonnegative squared-kernel trace identity for the actual
spectral packet on the full quotient Hilbert space. Either side may be
infinite; this theorem does not assume or assert global trace finiteness. -/
theorem coshWavePacket_energy_trace {ι : Type*} [Countable ι] (N : ℕ) [NeZero N]
    (b : HilbertBasis ι ℂ (AutomorphicSpace N))
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∑' i,ENNReal.ofReal (‖coshWavePacket N F hF R hR hs (b i)‖^2))=
      ∫⁻ x,∫⁻ y,ENNReal.ofReal (‖radialPoincareKernel N (abelProfile F) x y‖^2)
        ∂quotientMeasure N ∂quotientMeasure N := by
  let K := coshWavePacket N F hF R hR hs
  have hm (i : ι) : AEMeasurable
      (fun x => ENNReal.ofReal (‖(K (b i)).val x‖^2)) (quotientMeasure N) :=
    ((Lp.stronglyMeasurable (K (b i)).val).norm.pow 2).measurable.ennreal_ofReal.aemeasurable
  simp_rw [automorphic_norm_square_lintegral]
  rw [← lintegral_tsum hm]
  apply lintegral_congr_ae
  filter_upwards [coshWavePacket_pretrace N b F hF hc hr R hR hs] with x hx
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hx.summable,hx.tsum_eq]
  exact radialKernel_row_lintegral N (abelProfile F) (abelProfile_smooth F hF hc)
    R hR (abelProfile_support F _ hs) x

#print axioms automorphic_norm_square_lintegral
#print axioms radialKernel_row_lintegral
#print axioms coshWavePacket_energy_trace

end QuantitativeMaass
