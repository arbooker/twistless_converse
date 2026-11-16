module

public import QuantitativeMaassPositiveTracialBoundV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeMaass

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [PartialOrder 𝔄] [StarOrderedRing 𝔄]

theorem positive_contraction_power_norm (A : 𝔄) (h0 : 0≤A) (h1 : A≤1) (m : ℕ) :
    ‖A^m‖≤1 := by
  have hp := CStarAlgebra.pow_nonneg A m h0
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ hp).mpr
  simpa only [pow_zero] using CStarAlgebra.pow_antitone h1 h0 (Nat.zero_le m)

/-- Noncommutative telescoping under a genuine positive trace. The bound
uses the positive difference's trace, not the ambient identity trace. -/
theorem positive_power_trace_weighted (τ : 𝔄→L[ℝ]ℝ) (hm : Monotone τ)
    (hc : ∀ a b,τ (a*b)=τ (b*a)) (hs : ∀ a,τ (star a)=τ a)
    (A C : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) (hC0 : 0≤C) (hC1 : C≤1)
    (hCA : C≤A) (m : ℕ) (B : 𝔄) (hB : ‖B‖≤1) :
    |τ (B*(A^m-C^m))|≤(m:ℝ)*τ (A-C) := by
  have hD : 0≤A-C := sub_nonneg.mpr hCA
  have htd : 0≤τ (A-C) := by simpa only [map_zero] using hm hD
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
    have ht := (positive_tracial_mul_bound τ hm hc hs (B*A^m) (A-C) hD).trans
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

theorem positive_power_trace_lipschitz (τ : 𝔄→L[ℝ]ℝ) (hm : Monotone τ)
    (hc : ∀ a b,τ (a*b)=τ (b*a)) (hs : ∀ a,τ (star a)=τ a)
    (A C : 𝔄) (hA0 : 0≤A) (hA1 : A≤1) (hC0 : 0≤C) (hC1 : C≤1)
    (hCA : C≤A) (m : ℕ) :
    |τ (A^m)-τ (C^m)|≤(m:ℝ)*τ (A-C) := by
  have h1 : ‖(1:𝔄)‖≤1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (1:𝔄) zero_le_one).mpr le_rfl
  simpa only [one_mul,map_sub] using
    positive_power_trace_weighted τ hm hc hs A C hA0 hA1 hC0 hC1 hCA m 1 h1

#print axioms positive_contraction_power_norm
#print axioms positive_power_trace_weighted
#print axioms positive_power_trace_lipschitz
end QuantitativeMaass
