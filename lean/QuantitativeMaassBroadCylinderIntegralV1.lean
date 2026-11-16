module

public import QuantitativeMaassBroadCylinderEnergyV1
public import QuantitativeArithmeticMaassTransferCenterSupportV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap ENNReal

namespace QuantitativeMaass

/-- Real-integral version of the actual cylinder-to-quotient deficit
bound. Compact height support proves all source integrability. -/
theorem broadCross_cylinder_integral_le
    (N : ℕ) [NeZero N] (L : ℝ) (hL : 0 < L) (t : ℝ)
    (K : Set ℍ) (hK : IsCompact K) (lo hi : ℝ) (hlo : 0 < lo)
    (hheight : ∀ z ∈ K, lo ≤ z.im ∧ z.im ≤ hi)
    (b : SmoothUpperSeed) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (m : ℕ) (hm : ∀ z : ℍ, ∀ S : Finset (gamma 0),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m)
    (D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (hD : IsSelfAdjoint D)
    (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ → ℂ))
    (he : Function.Even f) (hr : ∀ s, star (f s)=f s)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support f ⊆ Icc (-R) R) :
    (∫ z, ‖D (broadQuotientPacket N L hL t
      (crossQuotientLocalization N 0 K hK b hbound
        (cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z))))‖^2 ∂quotientMeasure 0) ≤
      ‖cylinderTimePacket f (f.smooth ⊤) hc‖^2*(B^2*(m:ℝ))*
        ∫ w in K, ‖D (broadAbelColumn N L hL t w)‖^2 := by
  have hb : ∀ᵐ z ∂volume.restrict K, ‖upperFunction b.toFun z‖ ≤ B := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact hbound z hz
  have hx : MemLp (fun z => crossQuotientLocalization N 0 K hK b hbound
      (cylinderAutomorphic (cylinderTimeColumn f hc he R hR hs z))) 2 (quotientMeasure 0) :=
    boundedCrossQuotientLocalization_column_memLp N (evenCoshLift f)
      (evenCoshLift_smoothOn f (f.smooth ⊤) he hc) R hR
      (evenCoshLift_support_of_time_support f R hR hs) K hK lo hi hlo hheight
      (upperFunction b.toFun) (upperFunction_continuous b.smooth).aestronglyMeasurable hb
  have hy := (hx.continuousLinearMap_comp (broadQuotientPacket N L hL t)).continuousLinearMap_comp D
  have hsrc := hy.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hdst : Integrable (fun w => ‖D (broadAbelColumn N L hL t w)‖^2) (volume.restrict K) :=
    (compact_column_memLp _
    (D.continuous.comp (broadAbelColumn_continuous N L hL t)) K hK).integrable_norm_pow
      (by norm_num : (2:ℕ) ≠ 0)
  have hh := broadCross_cylinder_column_energy_le N L hL t K hK b B hB hbound m hm D hD f hc he hr R hR hs
  rw [← ofReal_integral_eq_lintegral_ofReal hsrc (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hdst (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

#print axioms broadCross_cylinder_integral_le

end QuantitativeMaass
