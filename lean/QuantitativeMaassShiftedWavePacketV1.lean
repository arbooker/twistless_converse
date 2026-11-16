module

public import QuantitativeMaassShiftedWaveEigenV1
public import QuantitativeMaassShiftedWaveContinuityV1
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

/-- Weighted integrability accounts for the exceptional spectrum. -/
def ShiftedWaveWeight (φ : ℝ → ℂ) : Prop :=
  AEStronglyMeasurable φ ∧ Integrable (fun t => ‖φ t‖ * Real.cosh (|t|/2))

theorem shiftedWaveWeight_of_support {φ : ℝ → ℂ} (hφ : Integrable φ)
    {R : ℝ} (hR : 0 ≤ R) (hs : Function.support φ ⊆ Set.Icc (-R) R) :
    ShiftedWaveWeight φ := by
  refine ⟨hφ.aestronglyMeasurable, ?_⟩
  have hc : Continuous (fun t : ℝ => Real.cosh (|t|/2)) := by fun_prop
  apply (hφ.norm.mul_const (Real.cosh (R/2))).mono'
    (hφ.norm.aestronglyMeasurable.mul hc.aestronglyMeasurable)
  filter_upwards with t
  change ‖(‖φ t‖ * Real.cosh (|t|/2) : ℝ)‖ ≤ ‖φ t‖ * Real.cosh (R/2)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖φ t‖ * Real.cosh (|t|/2))]
  by_cases ht : φ t = 0
  · simp [ht]
  · have hts := hs ht
    have hab : |t| ≤ R := abs_le.mpr hts
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity : 0 ≤ |t|/2),
      abs_of_nonneg (div_nonneg hR (show (0 : ℝ) ≤ 2 by norm_num))]
    linarith

theorem shiftedQuotientWave_apply_norm_le (N : ℕ) (t : ℝ) (v : AutomorphicSpace N) :
    ‖shiftedQuotientWave N t v‖ ≤ Real.cosh (|t|/2) * ‖v‖ :=
  ((shiftedQuotientWave N t).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (shiftedQuotientWave_norm_le N t) (norm_nonneg v))

theorem shiftedQuotientWave_packet_integrable (N : ℕ) {φ : ℝ → ℂ}
    (hφ : ShiftedWaveWeight φ) (v : AutomorphicSpace N) :
    Integrable (fun t => φ t • shiftedQuotientWave N t v) := by
  refine (hφ.2.mul_const ‖v‖).mono'
    (hφ.1.smul (shiftedQuotientWave_stronglyContinuous N v).aestronglyMeasurable) ?_
  filter_upwards with t
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (shiftedQuotientWave_apply_norm_le N t v) (norm_nonneg _)

theorem shiftedQuotientWave_packet_bound (N : ℕ) {φ : ℝ → ℂ}
    (hφ : ShiftedWaveWeight φ) (v : AutomorphicSpace N) :
    ‖∫ t, φ t • shiftedQuotientWave N t v‖ ≤
      (∫ t, ‖φ t‖ * Real.cosh (|t|/2)) * ‖v‖ := by
  calc
    _ ≤ ∫ t, ‖φ t • shiftedQuotientWave N t v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, (‖φ t‖ * Real.cosh (|t|/2)) * ‖v‖ := by
      apply integral_mono (shiftedQuotientWave_packet_integrable N hφ v).norm
        (hφ.2.mul_const _)
      intro t
      dsimp only
      rw [norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (shiftedQuotientWave_apply_norm_le N t v) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

def shiftedQuotientWavePacketLinear (N : ℕ) (φ : ℝ → ℂ) (hφ : ShiftedWaveWeight φ) :
    AutomorphicSpace N →ₗ[ℂ] AutomorphicSpace N where
  toFun v := ∫ t, φ t • shiftedQuotientWave N t v
  map_add' v w := by
    simp only [map_add, smul_add]
    exact integral_add (shiftedQuotientWave_packet_integrable N hφ v)
      (shiftedQuotientWave_packet_integrable N hφ w)
  map_smul' c v := by
    simp only [map_smul, smul_comm (φ _) c]
    exact integral_smul c _

/-- A bounded packet constructed by strong integration on the actual
quotient space, with the correct weight for low eigenvalues. -/
def shiftedQuotientWavePacket (N : ℕ) (φ : ℝ → ℂ) (hφ : ShiftedWaveWeight φ) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  (shiftedQuotientWavePacketLinear N φ hφ).mkContinuous
    (∫ t, ‖φ t‖ * Real.cosh (|t|/2)) (shiftedQuotientWave_packet_bound N hφ)

theorem shiftedQuotientWavePacket_apply (N : ℕ) (φ : ℝ → ℂ) (hφ : ShiftedWaveWeight φ)
    (v : AutomorphicSpace N) :
    shiftedQuotientWavePacket N φ hφ v = ∫ t, φ t • shiftedQuotientWave N t v := rfl

theorem shiftedQuotientWavePacket_norm (N : ℕ) (φ : ℝ → ℂ) (hφ : ShiftedWaveWeight φ) :
    ‖shiftedQuotientWavePacket N φ hφ‖ ≤ ∫ t, ‖φ t‖ * Real.cosh (|t|/2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg (fun t => by positivity))
  exact shiftedQuotientWave_packet_bound N hφ

theorem shiftedQuotientWavePacket_eigen (N : ℕ) (φ : ℝ → ℂ) (hφ : ShiftedWaveWeight φ)
    {e : ℝ} (he : 0 ≤ e) {v : AutomorphicSpace N}
    (h : FriedrichsGraph N v ((e:ℂ) • v)) :
    shiftedQuotientWavePacket N φ hφ v =
      (∫ t, φ t * (signedCosine t (e-1/4) : ℂ)) • v := by
  rw [shiftedQuotientWavePacket_apply]
  simp_rw [shiftedQuotientWave_eigen N he h, smul_smul]
  exact integral_smul_const _ _

theorem shiftedQuotientWavePacket_principal (N : ℕ) (φ : ℝ → ℂ) (hφ : ShiftedWaveWeight φ)
    (r : ℝ) {v : AutomorphicSpace N}
    (h : FriedrichsGraph N v (((1/4+r^2 : ℝ):ℂ) • v)) :
    shiftedQuotientWavePacket N φ hφ v = (∫ t, φ t * (Real.cos (t*r) : ℂ)) • v := by
  rw [shiftedQuotientWavePacket_apply]
  simp_rw [shiftedQuotientWave_principal N r h, smul_smul]
  exact integral_smul_const _ _

#print axioms shiftedWaveWeight_of_support
#print axioms shiftedQuotientWavePacket_norm
#print axioms shiftedQuotientWavePacket_eigen
#print axioms shiftedQuotientWavePacket_principal

end QuantitativeMaass.Wave
