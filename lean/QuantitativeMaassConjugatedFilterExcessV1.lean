module

public import QuantitativeMaassCyclicPowerFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeMaass

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- Metric transport keeps the canonical dimension with coefficient one;
only the positive regular excess pays the polynomial degree and metric norm. -/
theorem conjugated_power_filter_excess (τ : 𝔄→L[ℝ]ℝ) (hm : Monotone τ)
    (hc : ∀ a b,τ (a*b)=τ (b*a)) (hs : ∀ a,τ (star a)=τ a)
    (S F E : 𝔄) (hS : ‖S‖≤1) (hF0 : 0≤F) (hF1 : F≤1)
    (hE : IsStarProjection E) (hEF : E≤F) (m : ℕ) :
    τ (1-(1-S*F*star S)^m)-τ E ≤ (m:ℝ)*‖S‖^2*τ (F-E) := by
  have hn : ‖S*star S‖≤1 := by
    rw [CStarRing.norm_self_mul_star]
    nlinarith [norm_nonneg S]
  have hSS : S*star S≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (mul_star_self_nonneg S)).mp hn
  have hG0 : 0≤S*F*star S := by
    simpa only [star_star] using star_left_conjugate_nonneg hF0 (star S)
  have hG1 : S*F*star S≤1 := by
    have hh := star_left_conjugate_le_conjugate hF1 (star S)
    simp only [star_star,mul_one] at hh
    exact hh.trans hSS
  have h00 : 0≤S*E*star S := by
    simpa only [star_star] using star_left_conjugate_nonneg hE.nonneg (star S)
  have h0G : S*E*star S≤S*F*star S := by
    simpa only [star_star] using star_left_conjugate_le_conjugate hEF (star S)
  have hminor := conjugated_projection_filter_trace τ hm hc S E hS hE m
  have hh := positive_power_trace_lipschitz τ hm hc hs
    (1-S*E*star S) (1-S*F*star S)
    (sub_nonneg.mpr (h0G.trans hG1)) (sub_le_self 1 h00)
    (sub_nonneg.mpr hG1) (sub_le_self 1 hG0) (sub_le_sub_left h0G 1) m
  have he : (1-S*E*star S)-(1-S*F*star S)=S*(F-E)*star S := by
    noncomm_ring
  rw [he] at hh
  have ht : τ (S*(F-E)*star S)=τ ((star S*S)*(F-E)) := by
    rw [hc (S*(F-E)) (star S), ←mul_assoc]
  rw [ht] at hh
  have hw := positive_tracial_mul_bound τ hm hc hs (star S*S) (F-E)
    (sub_nonneg.mpr hEF)
  rw [CStarRing.norm_star_mul_self, ←pow_two] at hw
  have hw' := (le_abs_self (τ ((star S*S)*(F-E)))).trans hw
  have hu := (abs_le.mp hh).2
  have hc' := mul_le_mul_of_nonneg_left hw' (Nat.cast_nonneg m : (0:ℝ)≤m)
  rw [map_sub] at hminor ⊢
  nlinarith

#print axioms conjugated_power_filter_excess
end QuantitativeMaass
