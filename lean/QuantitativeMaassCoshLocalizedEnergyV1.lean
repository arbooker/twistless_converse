module

public import QuantitativeMaassRadialCompactEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff ENNReal

namespace QuantitativeMaass

/-- Localized trace identity on any measurable region, before estimating
its geometric side. The representative equalities hold simultaneously on
a countable full Hilbert basis. -/
theorem coshWavePacket_restricted_energy_trace {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N)) (s : Set ℍ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∑' i,∫⁻ x in s,ENNReal.ofReal (‖(coshWavePacket N F hF R hR hs (b i)).val x‖^2)
      ∂quotientMeasure N)=
      ∫⁻ x in s,∫⁻ y,ENNReal.ofReal (‖radialPoincareKernel N (abelProfile F) x y‖^2)
        ∂quotientMeasure N ∂quotientMeasure N := by
  have hm (i : ι) : AEMeasurable
      (fun x => ENNReal.ofReal (‖(coshWavePacket N F hF R hR hs (b i)).val x‖^2))
      ((quotientMeasure N).restrict s) :=
    ((Lp.stronglyMeasurable (coshWavePacket N F hF R hR hs (b i)).val).norm.pow 2).measurable.ennreal_ofReal.aemeasurable
  rw [← lintegral_tsum hm]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (coshWavePacket_pretrace N b F hF hc hr R hR hs)] with x hx
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hx.summable,hx.tsum_eq]
  exact radialKernel_row_lintegral N (abelProfile F) (abelProfile_smooth F hF hc)
    R hR (abelProfile_support F _ hs) x

/-- Finite actual localized spectral energy on every compact ball. The
proof supplies geometric integrability instead of assuming it. -/
theorem coshWavePacket_local_energy_finite {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N)) (o : ℍ) (L : ℝ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    (∑' i,∫⁻ x in Metric.closedBall o L,
      ENNReal.ofReal (‖(coshWavePacket N F hF R hR hs (b i)).val x‖^2)
      ∂quotientMeasure N)<(∞:ℝ≥0∞) := by
  rw [coshWavePacket_restricted_energy_trace N b (Metric.closedBall o L) F hF hc hr R hR hs]
  exact radialKernel_local_energy_finite N o L R hR (abelProfile F)
    (abelProfile_smooth F hF hc) (abelProfile_support F _ hs)

/-- The localized square energies are also a genuinely summable REAL
series, not a totalized divergent real sum. -/
theorem coshWavePacket_local_energy_summable {ι : Type*} [Countable ι]
    (N : ℕ) [NeZero N] (b : HilbertBasis ι ℂ (AutomorphicSpace N)) (o : ℍ) (L : ℝ)
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hr : ∀ q,star (F q)=F q) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Summable (fun i => ∫ x in Metric.closedBall o L,
      ‖(coshWavePacket N F hF R hR hs (b i)).val x‖^2 ∂quotientMeasure N) := by
  have h := ENNReal.summable_toReal
    (coshWavePacket_local_energy_finite N b o L F hF hc hr R hR hs).ne
  apply h.congr
  intro i
  symm
  apply integral_eq_lintegral_of_nonneg_ae
  · exact Eventually.of_forall (fun _ => sq_nonneg _)
  · exact ((Lp.stronglyMeasurable (coshWavePacket N F hF R hR hs (b i)).val).norm.pow 2).aestronglyMeasurable

#print axioms coshWavePacket_restricted_energy_trace
#print axioms coshWavePacket_local_energy_finite
#print axioms coshWavePacket_local_energy_summable

end QuantitativeMaass
