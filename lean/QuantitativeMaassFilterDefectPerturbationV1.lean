module

public import QuantitativeMaassTracialIntervalV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeMaass
variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
theorem contraction_defect_norm_sub (F G : 𝔄) (hF : ‖F‖≤1) (hG : ‖G‖≤1)
    {δ : ℝ} (he : ‖F-G‖≤δ) : ‖(F-F^2)-(G-G^2)‖≤3*δ := by
  have h1 : ‖F*(F-G)‖≤δ := (norm_mul_le _ _).trans
    ((mul_le_mul_of_nonneg_right hF (norm_nonneg _)).trans (by simpa using he))
  have h2 : ‖(F-G)*G‖≤δ := (norm_mul_le _ _).trans
    ((mul_le_mul_of_nonneg_left hG (norm_nonneg _)).trans (by simpa using he))
  have hid : F^2-G^2=F*(F-G)+(F-G)*G := by rw [pow_two,pow_two]; noncomm_ring
  have hsq : ‖F^2-G^2‖≤2*δ := by
    rw [hid]
    have hh := (norm_add_le _ _).trans (add_le_add h1 h2)
    linarith
  have hid' : (F-F^2)-(G-G^2)=(F-G)-(F^2-G^2) := by abel
  rw [hid']
  have hh := (norm_sub_le _ _).trans (add_le_add he hsq)
  linarith

omit [PartialOrder 𝔄] [StarOrderedRing 𝔄] in
theorem tracial_filter_defect_perturbation (τ : 𝔄→L[ℝ]ℝ)
    (F G : 𝔄) (hF : ‖F‖≤1) (hG : ‖G‖≤1) {δ : ℝ} (he : ‖F-G‖≤δ) :
    τ F≤τ G+‖τ‖*δ ∧ τ (F-F^2)≤τ (G-G^2)+3*‖τ‖*δ := by
  have h1 := (τ.le_opNorm (F-G)).trans
    (mul_le_mul_of_nonneg_left he (norm_nonneg τ))
  have h2 := (τ.le_opNorm ((F-F^2)-(G-G^2))).trans
    (mul_le_mul_of_nonneg_left (contraction_defect_norm_sub F G hF hG he) (norm_nonneg τ))
  rw [map_sub,Real.norm_eq_abs] at h1 h2
  exact ⟨by linarith [(abs_le.mp h1).2],by nlinarith [(abs_le.mp h2).2]⟩

#print axioms contraction_defect_norm_sub
#print axioms tracial_filter_defect_perturbation
end QuantitativeMaass
