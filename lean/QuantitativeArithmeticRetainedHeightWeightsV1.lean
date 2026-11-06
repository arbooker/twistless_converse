module

public import QuantitativeArithmeticRetainedCertificateV1
public import FinitenessIntegerWeightV1
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace QuantitativeArithmeticRetainedHeightWeights

open QuantitativeArithmeticRetainedCertificate SpanningIntegerRows

/-- A primitive row has one branch per unit residue; a retained row becomes
a single dilation branch. Its normalized multiplier is bounded by one. -/
def branchCount {N Q : ℕ} {P : Finset ℕ} : AugIndex N (P : Set ℕ) Q → ℕ
  | Sum.inl i => ((Finset.range i.val.1).filter (fun a => Nat.Coprime a i.val.1)).card
  | Sum.inr _ => 1

noncomputable def rowCost {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) (j : Fin Q) : ℝ :=
  ∑ i ∈ (A.coeff j).support, |(A.coeff j i : ℝ)| * branchCount i

noncomputable def cost {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) : ℝ := 1 + ∑ j : Fin Q, rowCost A j

theorem rowCost_nonneg {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) (j : Fin Q) : 0 ≤ rowCost A j :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

theorem one_le_cost {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) : 1 ≤ cost A := by
  have h := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin Q))) =>
    rowCost_nonneg A j)
  unfold cost
  linarith

theorem rowCost_le_cost {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) (j : Fin Q) : rowCost A j ≤ cost A := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin Q))) =>
    rowCost_nonneg A i) (Finset.mem_univ j)
  unfold cost
  linarith

/-- Normalized dilation transfer: the factor `p^m` from a ramified
complete trace is canceled by the weight. The extra exponent contributes
`p^(-s)`, just as a reflected branch contributes its denominator to `s`. -/
theorem weighted_dilation {p y M : ℝ} {b F : ℂ} (m s : ℕ)
    (hp : 0 < p) (hy : 0 ≤ y) (hb : ‖b‖ ≤ p^m)
    (hbound : (p*y)^(m+s)*‖F‖ ≤ M) :
    y^(m+s)*‖b*F‖ ≤ (1/p)^s*M := by
  have he : y^(m+s)*p^m = (1/p)^s*(p*y)^(m+s) := by
    simp only [mul_pow, pow_add, div_pow, one_pow]
    field_simp
  calc
    y^(m+s)*‖b*F‖ = y^(m+s)*(‖b‖*‖F‖) := by rw [norm_mul]
    _ ≤ y^(m+s)*(p^m*‖F‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (pow_nonneg hy _)
    _ = (1/p)^s*((p*y)^(m+s)*‖F‖) := by rw [←mul_assoc, he, mul_assoc]
    _ ≤ (1/p)^s*M := mul_le_mul_of_nonneg_left hbound (pow_nonneg (by positivity) _)

/-- The finite mixed-row estimate. Its hypotheses are supplied separately
by the actual reflection and dilation laws. -/
theorem reconstruct_bound {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) (j : Fin Q)
    (V : AugIndex N (P : Set ℕ) Q → ℂ) (F : ℂ) (m s : ℕ)
    {y ρ M : ℝ} (hy : 0 ≤ y) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hrec : F = ∑ i ∈ (A.coeff j).support, (A.coeff j i : ℂ)*V i)
    (hs : cost A*ρ^s ≤ 1) (d : AugIndex N (P : Set ℕ) Q → ℝ)
    (hd : ∀ i ∈ (A.coeff j).support, 0 ≤ d i ∧ d i ≤ ρ)
    (hrow : ∀ i ∈ (A.coeff j).support,
      y^(m+s)*‖V i‖ ≤ (branchCount i : ℝ)*(d i)^s*M) :
    y^(m+s)*‖F‖ ≤ M := by
  have hnorm : ‖F‖ ≤ ∑ i ∈ (A.coeff j).support, |(A.coeff j i : ℝ)| *‖V i‖ := by
    rw [hrec]
    simpa only [norm_mul, Complex.norm_ratCast] using norm_sum_le (A.coeff j).support
      (fun i => (A.coeff j i : ℂ)*V i)
  calc
    y^(m+s)*‖F‖ ≤ y^(m+s)*∑ i ∈ (A.coeff j).support, |(A.coeff j i : ℝ)| *‖V i‖ :=
      mul_le_mul_of_nonneg_left hnorm (pow_nonneg hy _)
    _ = ∑ i ∈ (A.coeff j).support, |(A.coeff j i : ℝ)| *(y^(m+s)*‖V i‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ (A.coeff j).support,
        (|(A.coeff j i : ℝ)| *(branchCount i : ℝ))*(d i)^s*M := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hrow i hi) (abs_nonneg _)
    _ ≤ M := FinitenessIntegerWeight.weighted_sum _ _ d s hρ hM
      (fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) hd (rowCost_le_cost A j) hs

#print axioms weighted_dilation
#print axioms reconstruct_bound

end QuantitativeArithmeticRetainedHeightWeights
