module

public import FinitenessCertificateV1
public import FinitenessHeightEnvelopeV1

@[expose] public section

namespace FinitenessIntegerWeight

open FinitenessCertificate SpanningIntegerRows

noncomputable def rowCost {N Q : ℕ} {hQ : 0 < Q}
    (A : Certificate N Q hQ) (j : Fin Q) : ℝ :=
  ∑ i ∈ (A.coeff j).support, |(A.coeff j i : ℝ)| *
    (((Finset.range i.val.1).filter (fun a => Nat.Coprime a i.val.1)).card : ℝ)

noncomputable def cost {N Q : ℕ} {hQ : 0 < Q}
    (A : Certificate N Q hQ) : ℝ := 1 + ∑ j : Fin Q, rowCost A j

theorem rowCost_nonneg {N Q : ℕ} {hQ : 0 < Q}
    (A : Certificate N Q hQ) (j : Fin Q) : 0 ≤ rowCost A j :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

theorem one_le_cost {N Q : ℕ} {hQ : 0 < Q}
    (A : Certificate N Q hQ) : 1 ≤ cost A := by
  have h := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin Q))) =>
    rowCost_nonneg A j)
  unfold cost
  linarith

theorem rowCost_le_cost {N Q : ℕ} {hQ : 0 < Q}
    (A : Certificate N Q hQ) (j : Fin Q) : rowCost A j ≤ cost A := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin Q))) =>
    rowCost_nonneg A i) (Finset.mem_univ j)
  unfold cost
  linarith

/-- An integer exponent suffices; it differs from the critical real
exponent by a certificate-dependent amount and does not change O_N(k). -/
theorem exists_exponent {C ρ : ℝ} (hC : 0 ≤ C) (hρ : ρ < 1) :
    ∃ s : ℕ, C * ρ^s ≤ 1 := by
  by_cases hc : C = 0
  · exact ⟨0, by simp [hc]⟩
  have hcp : 0 < C := lt_of_le_of_ne hC (Ne.symm hc)
  obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hcp) hρ
  refine ⟨s, le_of_lt ?_⟩
  have h := mul_lt_mul_of_pos_left hs hcp
  simpa [hc] using h

theorem weight_identity (m s : ℕ) {y d : ℝ} (hd : d ≠ 0) :
    y^(m+s) / d^m = d^s * (y/d)^(m+s) := by
  simp only [div_pow, pow_add]
  field_simp

theorem weighted_transfer (m s : ℕ) {y d v M : ℝ} (hd : 0 < d)
    (h : (y/d)^(m+s) * v ≤ M) :
    y^(m+s) / d^m * v ≤ d^s * M := by
  rw [weight_identity m s hd.ne']
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (pow_nonneg hd.le _)

theorem weighted_sum {ι : Type*} (t : Finset ι) (w d : ι → ℝ) (s : ℕ)
    {C ρ M : ℝ} (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hd : ∀ i ∈ t, 0 ≤ d i ∧ d i ≤ ρ)
    (hmass : ∑ i ∈ t, w i ≤ C) (hexp : C * ρ^s ≤ 1) :
    ∑ i ∈ t, w i * (d i)^s * M ≤ M := by
  calc
    (∑ i ∈ t, w i * (d i)^s * M) ≤ ∑ i ∈ t, w i * ρ^s * M := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ hM
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hd i hi).1 (hd i hi).2 s) (hw i hi)
    _ = (∑ i ∈ t, w i) * ρ^s * M := by rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ C * ρ^s * M := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmass (pow_nonneg hρ _)) hM
    _ ≤ M := by simpa using mul_le_mul_of_nonneg_right hexp hM

#print axioms exists_exponent
#print axioms weight_identity
#print axioms weighted_sum

end FinitenessIntegerWeight
