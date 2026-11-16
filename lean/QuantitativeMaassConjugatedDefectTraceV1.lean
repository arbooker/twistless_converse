module

public import QuantitativeMaassTracialIntervalV1
public import QuantitativeMaassCyclicPowerFilterV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeMaass
variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- A projection approximation in an order interval suffices; no canonical
projection needs to be identified or preserved by the transported filter. -/
theorem conjugated_filter_trace_of_projection_approx
    (τ : 𝔄→L[ℝ]ℝ) (hm : Monotone τ)
    (hc : ∀ a b,τ (a*b)=τ (b*a)) (hs : ∀ a,τ (star a)=τ a)
    (S F E D : 𝔄) (hS : ‖S‖≤1) (hF0 : 0≤F) (hF1 : F≤1)
    (hE : IsStarProjection E) (hD : 0≤D) (hlo : F-D≤E) (hhi : E≤F+D) (m : ℕ) :
    τ (1-(1-S*F*star S)^m)≤τ F+((m:ℝ)+1)*τ D := by
  have hn : ‖S*star S‖≤1 := by
    rw [CStarRing.norm_self_mul_star]
    nlinarith [norm_nonneg S]
  have hSS : S*star S≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (mul_star_self_nonneg S)).mp hn
  have hcontract (X : 𝔄) (hX0 : 0≤X) (hX1 : X≤1) :
      0≤S*X*star S ∧ S*X*star S≤1 := by
    constructor
    · simpa only [star_star] using star_left_conjugate_nonneg hX0 (star S)
    · have hh := star_left_conjugate_le_conjugate hX1 (star S)
      simp only [star_star,mul_one] at hh
      exact hh.trans hSS
  have hF := hcontract F hF0 hF1
  have hE' := hcontract E hE.nonneg hE.le_one
  have hd : 0≤S*D*star S := by
    simpa only [star_star] using star_left_conjugate_nonneg hD (star S)
  have hmin : -D≤F-E := by
    convert sub_le_sub_left hhi F using 1
    abel
  have hmax : F-E≤D := by
    convert sub_le_sub_left hlo F using 1
    abel
  have hl : -(S*D*star S)≤S*F*star S-S*E*star S := by
    simpa only [star_star,mul_neg,neg_mul,mul_sub,sub_mul] using
      star_left_conjugate_le_conjugate hmin (star S)
  have hu : S*F*star S-S*E*star S≤S*D*star S := by
    simpa only [star_star,mul_sub,sub_mul] using
      star_left_conjugate_le_conjugate hmax (star S)
  have hh := power_filter_trace_order_interval τ hm hc hs _ _ _
    hF.1 hF.2 hE'.1 hE'.2 hd hl hu m
  have hp := conjugated_projection_filter_trace τ hm hc S E hS hE m
  have htE := hm hhi
  rw [map_add] at htE
  have htD : 0≤τ D := by simpa only [map_zero] using hm hD
  have hn' : ‖star S*S‖≤1 := by
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg S]
  have ht := (le_abs_self (τ ((star S*S)*D))).trans
    ((positive_tracial_mul_bound τ hm hc hs _ D hD).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn' htD))
  have he : τ (S*D*star S)=τ ((star S*S)*D) := by
    rw [hc (S*D) (star S),←mul_assoc]
  rw [he] at hh
  have hm' : 0≤(m:ℝ) := Nat.cast_nonneg m
  have hb := mul_le_mul_of_nonneg_left ht hm'
  have hh' := (abs_le.mp hh).2
  nlinarith

#print axioms conjugated_filter_trace_of_projection_approx
end QuantitativeMaass
