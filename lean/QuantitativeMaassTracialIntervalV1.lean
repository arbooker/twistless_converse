module

public import QuantitativeMaassPositivePowerTraceV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeMaass
variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

/-- An order interval controls a weighted trace even when the difference
itself is not positive. -/
theorem tracial_order_interval (τ : 𝔄→L[ℝ]ℝ) (hm : Monotone τ)
    (hc : ∀ a b,τ (a*b)=τ (b*a)) (hs : ∀ a,τ (star a)=τ a)
    (B X D : 𝔄) (_hD : 0≤D) (hlo : -D≤X) (hhi : X≤D) :
    |τ (B*X)|≤‖B‖*τ D := by
  have hp : 0≤D+X := by simpa only [add_comm] using (neg_le_iff_add_nonneg.mp hlo)
  have hq : 0≤D-X := sub_nonneg.mpr hhi
  have h1 := positive_tracial_mul_bound τ hm hc hs B (D+X) hp
  have h2 := positive_tracial_mul_bound τ hm hc hs B (D-X) hq
  have he : τ (B*(D+X))-τ (B*(D-X))=2*τ (B*X) := by
    rw [mul_add,mul_sub,map_add,map_sub]
    ring
  have hh := (abs_sub _ _).trans (add_le_add h1 h2)
  rw [he,abs_mul] at hh
  rw [map_add] at hh
  rw [map_sub] at hh
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  linarith

/-- Noncommutative telescoping with a fixed positive order envelope. -/
theorem power_trace_order_interval_weighted (τ : 𝔄→L[ℝ]ℝ) (hm : Monotone τ)
    (hc : ∀ a b,τ (a*b)=τ (b*a)) (hs : ∀ a,τ (star a)=τ a)
    (A C D : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) (hC0 : 0≤C) (hC1 : C≤1)
    (hD : 0≤D) (hlo : -D≤A-C) (hhi : A-C≤D) (m : ℕ)
    (B : 𝔄) (hB : ‖B‖≤1) :
    |τ (B*(A^m-C^m))|≤(m:ℝ)*τ D := by
  have htd : 0≤τ D := by simpa only [map_zero] using hm hD
  have hnC := (CStarAlgebra.norm_le_one_iff_of_nonneg C hC0).mpr hC1
  induction m generalizing B with
  | zero => simp
  | succ m ih =>
    have hCB : ‖C*B‖≤1 := (norm_mul_le C B).trans
      ((mul_le_mul hnC hB (norm_nonneg _) zero_le_one).trans (by norm_num))
    have hBA : ‖B*A^m‖≤1 := (norm_mul_le B (A^m)).trans
      ((mul_le_mul hB (positive_contraction_power_norm A hA0 hA1 m)
        (norm_nonneg _) zero_le_one).trans (by norm_num))
    have hi := ih (C*B) hCB
    have ht := (tracial_order_interval τ hm hc hs (B*A^m) (A-C) D hD hlo hhi).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hBA htd)
    have he : τ (B*(A^(m+1)-C^(m+1)))=
        τ ((C*B)*(A^m-C^m))+τ ((B*A^m)*(A-C)) := by
      have ha : B*(A^(m+1)-C^(m+1))=
          B*(A^m-C^m)*C+(B*A^m)*(A-C) := by
        rw [pow_succ,pow_succ]
        noncomm_ring
      rw [ha,map_add,hc (B*(A^m-C^m)) C,mul_assoc C B (A^m-C^m)]
    rw [he]
    have hh := (abs_add_le _ _).trans (add_le_add hi ht)
    simpa only [Nat.cast_succ,add_mul,one_mul] using hh

theorem power_filter_trace_order_interval (τ : 𝔄→L[ℝ]ℝ) (hm : Monotone τ)
    (hc : ∀ a b,τ (a*b)=τ (b*a)) (hs : ∀ a,τ (star a)=τ a)
    (F G D : 𝔄) (hF0 : 0≤F) (hF1 : F≤1) (hG0 : 0≤G) (hG1 : G≤1)
    (hD : 0≤D) (hlo : -D≤F-G) (hhi : F-G≤D) (m : ℕ) :
    |τ (1-(1-F)^m)-τ (1-(1-G)^m)|≤(m:ℝ)*τ D := by
  have h1 : ‖(1:𝔄)‖≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (1:𝔄) zero_le_one).mpr le_rfl
  have he : (1-G)-(1-F)=F-G := by abel
  have hh := power_trace_order_interval_weighted τ hm hc hs (1-G) (1-F) D
    (sub_nonneg.mpr hG1) (sub_le_self 1 hG0)
    (sub_nonneg.mpr hF1) (sub_le_self 1 hF0) hD (by rwa [he]) (by rwa [he]) m 1 h1
  rw [one_mul,map_sub] at hh
  simpa only [map_sub,sub_sub_sub_cancel_left] using hh

#print axioms tracial_order_interval
#print axioms power_trace_order_interval_weighted
#print axioms power_filter_trace_order_interval
end QuantitativeMaass
