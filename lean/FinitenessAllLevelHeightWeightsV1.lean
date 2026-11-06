module

public import FinitenessAllLevelReconstructionV1
public import QuantitativeArithmeticRetainedHeightWeightsV1

set_option autoImplicit false
@[expose] public section

namespace FinitenessAllLevelHeightWeights

open QuantitativeArithmeticRetainedCertificate SpanningIntegerRows
  FinitenessAllLevelGoodTrace

noncomputable def branchCost {N Q : ℕ} {P : Finset ℕ} (L : ℝ) :
    AugIndex N (P : Set ℕ) Q → ℝ
  | Sum.inl i => ((Finset.range i.val.1).filter (fun a => Nat.Coprime a i.val.1)).card
  | Sum.inr i => Real.sqrt i.1.val * L + 1

theorem branchCost_nonneg {N Q : ℕ} {P : Finset ℕ} {L : ℝ} (hL : 0 ≤ L)
    (i : AugIndex N (P : Set ℕ) Q) : 0 ≤ branchCost L i := by
  cases i <;> dsimp [branchCost] <;> positivity

noncomputable def rowCost {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) (L : ℝ) (j : Fin Q) : ℝ :=
  ∑ i ∈ (A.coeff j).support, |(A.coeff j i : ℝ)| * branchCost L i

noncomputable def cost {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) (L : ℝ) : ℝ := 1 + ∑ j : Fin Q, rowCost A L j

theorem rowCost_nonneg {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) {L : ℝ} (hL : 0 ≤ L) (j : Fin Q) :
    0 ≤ rowCost A L j :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (branchCost_nonneg hL i))

theorem one_le_cost {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) {L : ℝ} (hL : 0 ≤ L) : 1 ≤ cost A L := by
  have h := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin Q))) =>
    rowCost_nonneg A hL j)
  unfold cost
  linarith

theorem rowCost_le_cost {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) {L : ℝ} (hL : 0 ≤ L) (j : Fin Q) :
    rowCost A L j ≤ cost A L := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin Q))) =>
    rowCost_nonneg A hL i) (Finset.mem_univ j)
  unfold cost
  linarith

theorem weighted_dilation {p y M C : ℝ} {b F : ℂ} (m s : ℕ)
    (hp : 0 < p) (hy : 0 ≤ y) (hC : 0 ≤ C) (hb : ‖b‖ ≤ C * p ^ m)
    (hbound : (p * y) ^ (m + s) * ‖F‖ ≤ M) :
    y ^ (m + s) * ‖b * F‖ ≤ C * (1 / p) ^ s * M := by
  have he : y ^ (m + s) * p ^ m = (1 / p) ^ s * (p * y) ^ (m + s) := by
    simp only [mul_pow, pow_add, div_pow, one_pow]
    field_simp
  calc
    y ^ (m + s) * ‖b * F‖ = y ^ (m + s) * (‖b‖ * ‖F‖) := by rw [norm_mul]
    _ ≤ y ^ (m + s) * (C * p ^ m * ‖F‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (pow_nonneg hy _)
    _ = C * (1 / p) ^ s * ((p * y) ^ (m + s) * ‖F‖) := by
      calc
        _ = C * (y ^ (m + s) * p ^ m) * ‖F‖ := by ring
        _ = _ := by rw [he]; ring
    _ ≤ C * (1 / p) ^ s * M :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg hC (by positivity))

/-- Both actual good-prime dilation branches are controlled by the same
upward-height bound. Their combined cost is independent of m. -/
theorem weighted_two_dilations (lam : ℕ → ℂ) (m s : ℕ) {p : ℕ} (hp : p.Prime)
    {y M L : ℝ} (hy : 0 ≤ y) (hM : 0 ≤ M) (hL : 0 ≤ L) (hlam : ‖lam p‖ ≤ L)
    (F G : ℂ) (hF : ((p : ℝ) * y) ^ (m + s) * ‖F‖ ≤ M)
    (hG : ((p : ℝ) ^ 2 * y) ^ (m + s) * ‖G‖ ≤ M) :
    y ^ (m + s) * ‖firstMultiplier lam m p * F - (p : ℂ) ^ (2 * m) * G‖ ≤
      (Real.sqrt p * L + 1) * (1 / (p : ℝ)) ^ s * M := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb : ‖firstMultiplier lam m p‖ ≤ (Real.sqrt p * L) * (p : ℝ) ^ m := by
    simp only [firstMultiplier, norm_mul, norm_pow, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ (p : ℝ) ^ m * Real.sqrt p * L :=
        mul_le_mul_of_nonneg_left hlam (by positivity)
      _ = _ := by ring
  have hfirst := weighted_dilation m s hpR hy (mul_nonneg (Real.sqrt_nonneg _) hL) hb hF
  have hsecond := QuantitativeArithmeticRetainedHeightWeights.weighted_dilation
    (b := (p : ℂ) ^ (2 * m)) m s (sq_pos_of_pos hpR) hy
    (by simp only [norm_pow, Complex.norm_natCast, ← pow_mul]; exact le_rfl) hG
  have hrecip : 1 / (p : ℝ) ^ 2 ≤ 1 / (p : ℝ) := by
    apply one_div_le_one_div_of_le hpR
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    nlinarith
  have hsecond' : y ^ (m + s) * ‖(p : ℂ) ^ (2 * m) * G‖ ≤
      (1 / (p : ℝ)) ^ s * M := hsecond.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hrecip s) hM)
  calc
    _ ≤ y ^ (m + s) * (‖firstMultiplier lam m p * F‖ + ‖(p : ℂ) ^ (2 * m) * G‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg hy _)
    _ = y ^ (m + s) * ‖firstMultiplier lam m p * F‖ +
        y ^ (m + s) * ‖(p : ℂ) ^ (2 * m) * G‖ := by ring
    _ ≤ Real.sqrt p * L * (1 / (p : ℝ)) ^ s * M + (1 / (p : ℝ)) ^ s * M :=
      add_le_add hfirst hsecond'
    _ = _ := by ring

theorem reconstruct_bound {N Q : ℕ} {P : Finset ℕ} {hQ : 0 < Q}
    (A : Certificate N P Q hQ) {L : ℝ} (hL : 0 ≤ L) (j : Fin Q)
    (V : AugIndex N (P : Set ℕ) Q → ℂ) (F : ℂ) (m s : ℕ)
    {y ρ M : ℝ} (hy : 0 ≤ y) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hrec : F = ∑ i ∈ (A.coeff j).support, (A.coeff j i : ℂ) * V i)
    (hs : cost A L * ρ ^ s ≤ 1) (d : AugIndex N (P : Set ℕ) Q → ℝ)
    (hd : ∀ i ∈ (A.coeff j).support, 0 ≤ d i ∧ d i ≤ ρ)
    (hrow : ∀ i ∈ (A.coeff j).support,
      y ^ (m + s) * ‖V i‖ ≤ branchCost L i * (d i) ^ s * M) :
    y ^ (m + s) * ‖F‖ ≤ M := by
  have hnorm : ‖F‖ ≤ ∑ i ∈ (A.coeff j).support, |(A.coeff j i : ℝ)| * ‖V i‖ := by
    rw [hrec]
    simpa only [norm_mul, Complex.norm_ratCast] using norm_sum_le (A.coeff j).support
      (fun i => (A.coeff j i : ℂ) * V i)
  calc
    y ^ (m + s) * ‖F‖ ≤ y ^ (m + s) *
        ∑ i ∈ (A.coeff j).support, |(A.coeff j i : ℝ)| * ‖V i‖ :=
      mul_le_mul_of_nonneg_left hnorm (pow_nonneg hy _)
    _ = ∑ i ∈ (A.coeff j).support, |(A.coeff j i : ℝ)| * (y ^ (m + s) * ‖V i‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ (A.coeff j).support,
        (|(A.coeff j i : ℝ)| * branchCost L i) * (d i) ^ s * M := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hrow i hi) (abs_nonneg _)
    _ ≤ M := FinitenessIntegerWeight.weighted_sum _ _ d s hρ hM
      (fun i _ => mul_nonneg (abs_nonneg _) (branchCost_nonneg hL i)) hd
      (rowCost_le_cost A hL j) hs

#print axioms weighted_two_dilations
#print axioms reconstruct_bound

end FinitenessAllLevelHeightWeights
