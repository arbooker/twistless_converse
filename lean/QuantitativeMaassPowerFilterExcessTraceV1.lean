module

public import QuantitativeMaassPositivePowerTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeMaass

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

theorem positive_contraction_filter_order (G : 𝔄) (hG0 : 0≤G) (hG1 : G≤1) (m : ℕ) :
    0≤1-(1-G)^m ∧ 1-(1-G)^m≤1 := by
  have h0 : 0≤1-G := sub_nonneg.mpr hG1
  have h1 : 1-G≤1 := sub_le_self 1 hG0
  have hp := CStarAlgebra.pow_nonneg (1-G) m h0
  have hn := positive_contraction_power_norm (1-G) h0 h1 m
  exact ⟨sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hp).mp hn),
    sub_le_self 1 hp⟩

/-- A positive contraction supported by a projection gives polynomial
minorants of that same projection, with no inverse or spectral gap. -/
theorem positive_power_filter_minorant (G Q : 𝔄) (hG0 : 0≤G) (hG1 : G≤1)
    (hQ : IsStarProjection Q) (hGQ : G≤Q) (m : ℕ) : 1-(1-G)^m≤Q := by
  have hGfix := hQ.mul_right_and_mul_left_of_nonneg_of_le hG0 hGQ
  have hright : (1-(1-G)^m)*Q=1-(1-G)^m := by
    induction m with
    | zero => simp
    | succ m ih =>
      have he : 1-(1-G)^(m+1)=(1-(1-G)^m)+(1-G)^m*G := by
        rw [pow_succ]
        noncomm_ring
      rw [he,add_mul,ih,mul_assoc,hGfix.1]
  obtain ⟨hp,hp1⟩ := positive_contraction_filter_order G hG0 hG1 m
  have hps := IsSelfAdjoint.of_nonneg hp
  have hleft : Q*(1-(1-G)^m)=1-(1-G)^m := by
    simpa only [star_mul,hQ.isSelfAdjoint.star_eq,hps.star_eq] using congrArg star hright
  have hh := star_left_conjugate_le_conjugate hp1 Q
  simpa only [hQ.isSelfAdjoint.star_eq,hleft,hright,mul_one,hQ.isIdempotentElem.eq] using hh

/-- The canonical projection keeps coefficient one. The polynomial's
regular excess is at most its degree times the original positive excess. -/
theorem positive_power_filter_excess_trace (τ : 𝔄→L[ℝ]ℝ) (hm : Monotone τ)
    (hc : ∀ a b,τ (a*b)=τ (b*a)) (hs : ∀ a,τ (star a)=τ a)
    (G G₀ Q : 𝔄) (hG0 : 0≤G) (hG1 : G≤1) (h00 : 0≤G₀) (h0G : G₀≤G)
    (hQ : IsStarProjection Q) (h0Q : G₀≤Q) (m : ℕ) :
    τ (1-(1-G)^m)-τ Q≤(m:ℝ)*τ (G-G₀) := by
  have h01 := h0G.trans hG1
  have hminor := hm (positive_power_filter_minorant G₀ Q h00 h01 hQ h0Q m)
  have hh := positive_power_trace_lipschitz τ hm hc hs (1-G₀) (1-G)
    (sub_nonneg.mpr h01) (sub_le_self 1 h00)
    (sub_nonneg.mpr hG1) (sub_le_self 1 hG0) (sub_le_sub_left h0G 1) m
  have he : (1-G₀)-(1-G)=G-G₀ := by abel
  rw [he] at hh
  have hu := (abs_le.mp hh).2
  rw [map_sub] at hminor ⊢
  linarith

#print axioms positive_contraction_filter_order
#print axioms positive_power_filter_minorant
#print axioms positive_power_filter_excess_trace
end QuantitativeMaass
