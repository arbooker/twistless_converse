module

public import QuantitativeMaassBroadCompactEnergyV1
public import QuantitativeMaassCrossEnergyCompatibilityV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal

namespace QuantitativeMaass

/-- Compact cross-quotient localization supplies the actual factor in
the broad deficit energy estimate. Only the source orbit multiplicity
appears outside the compact target-column trace. -/
theorem broadCross_source_column_energy_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : α → Lp ℂ 2 μ)
    (hc : ∀ v : Lp ℂ 2 μ, A v =ᵐ[μ] (fun z => inner ℂ (c z) v))
    (N M : ℕ) [NeZero N] (I : Lp ℂ 2 μ →ₗᵢ[ℂ] AutomorphicSpace M)
    (L : ℝ) (hL : 0 < L) (t : ℝ) (K : Set ℍ) (hK : IsCompact K)
    (b : SmoothUpperSeed) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (m : ℕ) (hm : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m)
    (D : AutomorphicSpace N →L[ℂ] AutomorphicSpace N) (hD : IsSelfAdjoint D) :
    (∫⁻ z, ENNReal.ofReal (‖D (broadQuotientPacket N L hL t
      (crossQuotientLocalization N M K hK b hbound (I (c z))))‖^2) ∂μ) ≤
      ENNReal.ofReal (‖A‖^2)*ENNReal.ofReal (B^2*(m:ℝ))*
        ∫⁻ w in K, ENNReal.ofReal (‖D (broadAbelColumn N L hL t w)‖^2) := by
  have hb : ∀ᵐ z ∂volume.restrict K, ‖upperFunction b.toFun z‖ ≤ B := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact hbound z hz
  let U : Lp ℂ 2 (volume.restrict K) →L[ℂ] Lp ℂ 2 (volume.restrict K) :=
    AsymptoticL2Multiplier.operator (upperFunction b.toFun)
      (upperFunction_continuous b.smooth).aestronglyMeasurable hb
  let R := quotientRestriction M K hK hK.measurableSet
  let J := (U.comp R).comp I.toContinuousLinearMap
  have hU : ‖U‖ ≤ B := AsymptoticL2Multiplier.operator_norm_le _ _ hB hb
  have hR : ‖R‖ ≤ Real.sqrt (m:ℝ) := quotientRestriction_norm_le_of_overlap M K hK m hm
  have hJ : ‖J‖ ≤ B*Real.sqrt (m:ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change ‖U (R (I v))‖ ≤ _
    calc
      _ ≤ B*‖R (I v)‖ := (U.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hU (norm_nonneg _))
      _ ≤ B*(Real.sqrt (m:ℝ)*‖I v‖) := mul_le_mul_of_nonneg_left
        ((R.le_opNorm _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))) hB
      _ = _ := by rw [I.norm_map]; ring
  have hJ2 : ‖J.adjoint‖^2 ≤ B^2*(m:ℝ) := by
    rw [adjoint.norm_map]
    have hh := pow_le_pow_left₀ (norm_nonneg J) hJ 2
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)] using hh
  have hh := broadCompact_source_column_energy_le μ A c hc N L hL t K hK D hD J.adjoint
  rw [adjoint_adjoint] at hh
  have he (v : Lp ℂ 2 μ) :
      (quotientRestriction N K hK hK.measurableSet).adjoint (J v) =
        crossQuotientLocalization N M K hK b hbound (I v) := rfl
  simp_rw [he] at hh
  apply hh.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hJ2) (show 0 ≤ ENNReal.ofReal (‖A‖^2) from zero_le))
    (show 0 ≤ ∫⁻ w in K, ENNReal.ofReal (‖D (broadAbelColumn N L hL t w)‖^2) from zero_le)

#print axioms broadCross_source_column_energy_le

end QuantitativeMaass
