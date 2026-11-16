module

public import QuantitativeArithmeticExceptionalOldSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

open Module QuantitativeArithmeticExceptionalOldSpace

namespace QuantitativeMaass

/-- A positive contraction filter is exponentially accurate outside its
kernel and small positive spectrum; the latter costs only its dimension. -/
theorem finite_low_spectrum_filter {ι : Type*} [Fintype ι] (τ : ι→ℝ)
    (hτ : ∀ i,0≤τ i ∧ τ i≤1) (δ : ℝ) (_hδ : 0≤δ) (hδ1 : δ≤1) (m : ℕ) :
    (∑ i,(1-τ i)^m)≤(Nat.card {i : ι // τ i=0}:ℝ)+
      (Nat.card {i : ι // 0<τ i ∧ τ i≤δ}:ℝ)+(1-δ)^m*(Fintype.card ι:ℝ) := by
  classical
  have hbase : 0≤(1-δ)^m := pow_nonneg (sub_nonneg.mpr hδ1) _
  have hp (i : ι) : (1-τ i)^m≤
      (if τ i=0 then (1:ℝ) else 0)+(if 0<τ i ∧ τ i≤δ then (1:ℝ) else 0)+(1-δ)^m := by
    by_cases hz : τ i=0
    · simp only [hz,sub_zero,one_pow,ite_true,lt_self_iff_false,false_and,ite_false,add_zero]
      exact le_add_of_nonneg_right hbase
    · by_cases hi : τ i≤δ
      · have hs : 0<τ i ∧ τ i≤δ := ⟨lt_of_le_of_ne (hτ i).1 (Ne.symm hz),hi⟩
        simp only [ite_false,hz,hs,zero_add]
        exact (pow_le_one₀ (sub_nonneg.mpr (hτ i).2) (by linarith only [(hτ i).1])).trans
          (le_add_of_nonneg_right hbase)
      · have hs : ¬(0<τ i ∧ τ i≤δ) := fun h => hi h.2
        simp only [hz,hs,ite_false,zero_add]
        exact pow_le_pow_left₀ (sub_nonneg.mpr (hτ i).2) (by linarith only [hi]) m
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hp i)
  simpa [Finset.sum_add_distrib,Nat.card_eq_fintype_card,Fintype.card_subtype,mul_comm] using hh

/-- The low positive spectral rank is the actual multiplicity count. -/
theorem smallPositiveSpace_finrank_eq_card {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {S : E →ₗ[ℂ] E} (hS : S.IsSymmetric) (δ : ℝ) :
    finrank ℂ (smallPositiveSpace hS δ)=
      Nat.card {i : Fin (finrank ℂ E) // 0<hS.eigenvalues rfl i ∧ hS.eigenvalues rfl i≤δ} := by
  classical
  unfold smallPositiveSpace
  have hi := (hS.eigenvectorBasis rfl).orthonormal.linearIndependent.comp
    (fun i : {i : Fin (finrank ℂ E) // 0<hS.eigenvalues rfl i ∧ hS.eigenvalues rfl i≤δ} => i.val)
    Subtype.val_injective
  simpa only [Nat.card_eq_fintype_card,Function.comp_def] using finrank_span_eq_card hi

#print axioms finite_low_spectrum_filter
#print axioms smallPositiveSpace_finrank_eq_card

end QuantitativeMaass
