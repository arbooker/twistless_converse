module

public import QuantitativeMaassSmoothingGlobalEnergyV1
public import QuantitativeMaassSmoothingUpperSupportV1
public import QuantitativeMaassPoincareGraphV1
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set Metric Filter UpperHalfPlane
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- A concrete common-support smooth sequence converges to a compact Lipschitz
seed in both the mass and derivative square integrals. -/
theorem compact_lipschitz_sobolev_approx {L : NNReal} {f : Point → ℂ}
    (hf : LipschitzWith L f) (hc : HasCompactSupport f)
    (hp : tsupport f⊆{Z : Point | 0<Z.2}) :
    ∃ (K : Set ℍ) (u : ℕ → SmoothUpperSeed),IsCompact K ∧
      (∀ n,tsupport (upperFunction (u n).toFun)⊆K) ∧
      (∀ n,ContDiff ℝ ∞ (u n).toFun ∧ HasCompactSupport (u n).toFun ∧
        tsupport (u n).toFun⊆{Z : Point | 0<Z.2} ∧ LipschitzWith L (u n).toFun) ∧
      Tendsto (fun n => ∫ Z,‖(u n).toFun Z-f Z‖^2) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ Z,‖fderiv ℝ (u n).toFun Z-fderiv ℝ f Z‖^2) atTop (𝓝 0) ∧
      (∀ᵐ Z ∂(volume : Measure Point),
        Tendsto (fun n => fderiv ℝ (u n).toFun Z) atTop (𝓝 (fderiv ℝ f Z))) := by
  obtain ⟨r,hr,hrK⟩ := hc.isCompact.exists_forall_le' continuous_snd.continuousOn hp
  let R := r/2
  have hR : 0<R := half_pos hr
  let δ : ℕ → ℝ := fun n => R*(1/((n:ℝ)+1))
  have hδ (n : ℕ) : 0<δ n := by dsimp [δ]; positivity
  have hδR (n : ℕ) : δ n≤R := by
    dsimp [δ]
    apply mul_le_of_le_one_right hR.le
    apply (div_le_one (by positivity)).2
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul R
  let φ : ℕ → ContDiffBump (0 : Point) :=
    fun n => ⟨δ n/2,δ n,half_pos (hδ n),half_lt_self (hδ n)⟩
  have hφC : ∀ᶠ n in atTop,(φ n).rOut≤2*(φ n).rIn := by
    filter_upwards with n
    change δ n≤2*(δ n/2)
    linarith
  obtain ⟨K,hK,hKS⟩ := smoothBumpAverage_common_upper_support hc (half_lt_self hr) hrK
  let u : ℕ → SmoothUpperSeed := fun n =>
    ⟨smoothBumpAverage (φ n) f,(smoothBumpAverage_smooth (φ n) hf.continuous).contDiffOn,
      hK.of_isClosed_subset isClosed_closure (hKS (φ n) (hδR n))⟩
  refine ⟨K,u,hK,fun n => hKS (φ n) (hδR n),
    fun n => ⟨smoothBumpAverage_smooth (φ n) hf.continuous,
      smoothBumpAverage_compact (φ n) hc,
      smoothBumpAverage_support_positive (φ n) hc (hδR n) (half_lt_self hr) hrK,
      smoothBumpAverage_lipschitz (φ n) hf⟩,?_,?_,?_⟩
  · exact smoothBumpAverage_global_square_tendsto hf hc hδ0 hδR
  · exact smoothBumpAverage_fderiv_global_square_tendsto hf hc hδ0 hφC hδR
  · exact smoothBumpAverage_fderiv_tendsto_ae hf hδ0 hφC

#print axioms compact_lipschitz_sobolev_approx

end QuantitativeMaass
