module

public import FinitenessComplexGeometryV1
public import FinitenessIntegerWeightV1

@[expose] public section

namespace FinitenessLowHeight

open FinitenessAnalyticReconstruction FinitenessComplexGeometry
open FinitenessCertificate FinitenessIntegerWeight SpanningIntegerRows

theorem weighted_twist (F : ℂ → ℂ) (q m s : ℕ) (χ z : ℂ) {L M : ℝ}
    (hL : 0 < L) (hz : 0 < z.im) (hχ : ‖χ‖ = 1)
    (hFE : twist F q z = χ / (((Real.sqrt L : ℝ) : ℂ) * z)^(2*m) *
      twist F q (-1 / ((L : ℂ) * z)))
    (hbound : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ((-1 / ((L : ℂ) * z) + (a : ℂ)/q).im)^(m+s) *
        ‖F (-1 / ((L : ℂ) * z) + (a : ℂ)/q)‖ ≤ M) :
    z.im^(m+s) * ‖twist F q z‖ ≤
      (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) *
        (denominator L z)^s * M := by
  have hd := denominator_pos hL hz
  have him (a : ℕ) : (-1 / ((L : ℂ) * z) + (a : ℂ)/q).im =
      z.im / denominator L z := by
    simpa using translated_reflected_im hL hz ((a : ℝ)/q)
  calc
    z.im^(m+s) * ‖twist F q z‖ =
        (z.im^(m+s) / (denominator L z)^m) * ‖twist F q (-1 / ((L : ℂ)*z))‖ := by
      rw [hFE, norm_mul, automorphy_norm hL.le z χ hχ m]
      ring
    _ ≤ (z.im^(m+s) / (denominator L z)^m) *
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ‖F (-1 / ((L : ℂ)*z) + (a : ℂ)/q)‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
        (div_nonneg (pow_nonneg hz.le _) (pow_nonneg hd.le _))
    _ = ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        (z.im^(m+s) / (denominator L z)^m) *
          ‖F (-1 / ((L : ℂ)*z) + (a : ℂ)/q)‖ := Finset.mul_sum ..
    _ ≤ ∑ _a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        (denominator L z)^s * M := by
      apply Finset.sum_le_sum
      intro a ha
      apply weighted_transfer m s hd
      simpa only [him] using hbound a ha
    _ = _ := by simp; ring

/-- Sum the weighted row estimates using the actual rational certificate.
The next assembly supplies hrow from the transformation laws above. -/
theorem reconstruct_bound {N Q : ℕ} {hQ : 0 < Q}
    (A : Certificate N Q hQ) (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z)
    (j : Fin Q) (z : ℂ) (m s : ℕ) {ρ M : ℝ} (hz : 0 < z.im)
    (hρ : 0 ≤ ρ) (hM : 0 ≤ M) (hs : cost A * ρ^s ≤ 1)
    (d : RowIndex N Q → ℝ)
    (hd : ∀ i ∈ (A.coeff j).support, 0 ≤ d i ∧ d i ≤ ρ)
    (hrow : ∀ i ∈ (A.coeff j).support,
      z.im^(m+s) * ‖twist F i.val.1 (z + ((i.val.2 : ℂ)-(j : ℕ))/Q)‖ ≤
        (((Finset.range i.val.1).filter (fun a => Nat.Coprime a i.val.1)).card : ℝ) *
          (d i)^s * M) : z.im^(m+s) * ‖F z‖ ≤ M := by
  have hrec := reconstruct_twists A F hp j z
  have hnorm : ‖F z‖ ≤ ∑ i ∈ (A.coeff j).support,
      |(A.coeff j i : ℝ)| * ‖twist F i.val.1 (z + ((i.val.2 : ℂ)-(j : ℕ))/Q)‖ := by
    rw [hrec]
    simpa only [norm_mul, Complex.norm_ratCast] using norm_sum_le (A.coeff j).support
      (fun i => (A.coeff j i : ℂ) * twist F i.val.1 (z + ((i.val.2 : ℂ)-(j : ℕ))/Q))
  calc
    z.im^(m+s) * ‖F z‖ ≤ z.im^(m+s) * ∑ i ∈ (A.coeff j).support,
        |(A.coeff j i : ℝ)| * ‖twist F i.val.1 (z + ((i.val.2 : ℂ)-(j : ℕ))/Q)‖ :=
      mul_le_mul_of_nonneg_left hnorm (pow_nonneg hz.le _)
    _ = ∑ i ∈ (A.coeff j).support, |(A.coeff j i : ℝ)| *
        (z.im^(m+s) * ‖twist F i.val.1 (z + ((i.val.2 : ℂ)-(j : ℕ))/Q)‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ (A.coeff j).support,
        (|(A.coeff j i : ℝ)| *
          (((Finset.range i.val.1).filter (fun a => Nat.Coprime a i.val.1)).card : ℝ)) *
            (d i)^s * M := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hrow i hi) (abs_nonneg _)
    _ ≤ M := weighted_sum _ _ d s hρ hM
      (fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) hd
      (rowCost_le_cost A j) hs

/-- The low-height estimate with the actual FE substituted: the only
remaining bound is on values at heights at least Im(z)/rho. -/
theorem from_FE {N Q : ℕ} {hQ : 0 < Q} (hN : 0 < N)
    (A : Certificate N Q hQ) (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z)
    (χ : ℕ → ℂ) (m s : ℕ)
    (hχ : ∀ q, q ∣ Q → ‖χ q‖ = 1)
    (hFE : ∀ q : ℕ, q ∣ Q → ∀ z : ℂ, 0 < z.im →
      twist F q z = χ q / (((Real.sqrt (Nat.lcm N (q^2)) : ℝ) : ℂ) * z)^(2*m) *
        twist F q (-1 / ((Nat.lcm N (q^2) : ℕ) * z)))
    (j : Fin Q) (z : ℂ) {ρ M : ℝ} (hz : 0 < z.im)
    (hρ : 0 < ρ) (hM : 0 ≤ M) (hs : cost A * ρ^s ≤ 1)
    (hsmall : ∀ i ∈ (A.coeff j).support,
      denominator (Nat.lcm N (i.val.1^2)) (z + ((i.val.2 : ℂ)-(j : ℕ))/Q) ≤ ρ)
    (habove : ∀ w : ℂ, z.im / ρ ≤ w.im → w.im^(m+s) * ‖F w‖ ≤ M) :
    z.im^(m+s) * ‖F z‖ ≤ M := by
  let d : RowIndex N Q → ℝ := fun i =>
    denominator (Nat.lcm N (i.val.1^2)) (z + ((i.val.2 : ℂ)-(j : ℕ))/Q)
  have him (i : RowIndex N Q) : (z + ((i.val.2 : ℂ)-(j : ℕ))/Q).im = z.im := by simp
  have hL (i : RowIndex N Q) : (0 : ℝ) < Nat.lcm N (i.val.1^2) := by
    exact_mod_cast Nat.lcm_pos hN (pow_pos (Nat.pos_of_dvd_of_pos i.property.1 hQ) 2)
  have hd (i : RowIndex N Q) : 0 < d i := by
    apply denominator_pos (hL i)
    simpa only [him] using hz
  apply reconstruct_bound A F hp j z m s hz hρ.le hM hs d
    (fun i hi => ⟨(hd i).le, hsmall i hi⟩)
  intro i hi
  have hβ : 0 < (z + ((i.val.2 : ℂ)-(j : ℕ))/Q).im := by simpa only [him] using hz
  have hf := weighted_twist (M:=M) F i.val.1 m s (χ i.val.1)
    (z + ((i.val.2 : ℂ)-(j : ℕ))/Q) (hL i) hβ (hχ i.val.1 i.property.1)
    (by simpa using hFE i.val.1 i.property.1 _ hβ) (by
      intro a _
      apply habove
      have ht := translated_reflected_im (hL i) hβ ((a : ℝ)/i.val.1)
      have ht' : (-1 / (((Nat.lcm N (i.val.1^2) : ℝ) : ℂ) *
          (z + ((i.val.2 : ℂ)-(j : ℕ))/Q)) + (a : ℂ)/i.val.1).im = z.im / d i := by
        simpa [him, d] using ht
      rw [ht']
      exact div_le_div_of_nonneg_left hz.le (hd i) (hsmall i hi))
  simpa only [him, d] using hf

#print axioms weighted_twist
#print axioms reconstruct_bound
#print axioms from_FE

end FinitenessLowHeight
