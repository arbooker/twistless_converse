module

public import FinitenessEulerIdentificationV1
public import Mathlib.Data.Nat.Factorization.Induction

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalEulerProduct

open Complex Filter Asymptotics FinitenessOriginalInput FinitenessEulerCoefficients
  FinitenessEulerIdentification FinitenessEulerLocal

/-- Multiplicativity and the normalized local recurrences identify the
coefficients with the canonical reciprocal-quadratic construction. -/
theorem eq_canonical_of_arithmetic {N : ℕ} {f : ℕ → ℂ}
    (hzero : f 0 = 0) (hone : f 1 = 1)
    (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n)
    (hrec : ∀ p, p.Prime → ∀ j,
      f (p^(j+2)) = f p * f (p^(j+1)) - xi N p * f (p^j)) :
    f = value f (xi N) := by
  have hpowers (p : ℕ) (hp : p.Prime) (j : ℕ) :
      f (p^j) = coeff (f p) (xi N p) j := by
    induction j using Nat.twoStepInduction with
    | zero => simpa [coeff] using hone
    | one => simp [coeff]
    | more j ih0 ih1 => rw [hrec p hp, ih0, ih1]; rfl
  funext n
  induction n using Nat.recOnPrimePow with
  | zero => simp [hzero]
  | one => simp [hone]
  | prime_pow_mul a p j hp hpa _ ih =>
      have hc := (hp.coprime_iff_not_dvd.mpr hpa).pow_left j
      rw [hmul _ _ hc, FinitenessEulerCoefficients.multiplicative _ _ hc,
        ih, value_prime_pow _ _ hp, hpowers p hp j]

/-- The canonical Euler product converges on a complex right half-plane,
not merely on its real axis. -/
theorem canonical_hasProd_complex (a b : ℕ → ℂ) (d : ℕ)
    (hb : ∀ p, p.Prime → ‖b p‖ ≤ 1)
    (ha : ∀ p, p.Prime → ‖a p‖ + 1 ≤ (p : ℝ)^d)
    {s : ℂ} (hs : (d : ℝ) + 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
      (1-a p.val*(p.val:ℂ)^(-s)+b p.val*(p.val:ℂ)^(-2*s))⁻¹)
      (LSeries (value a b) s) := by
  have hsum : LSeriesSummable (value a b) s := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    exact (FinitenessEulerDirichlet.abscissa_bound a b d hb ha).trans_lt
      (by exact_mod_cast hs)
  have hprod := EulerProduct.eulerProduct_hasProd
    (f := LSeries.term (value a b) s) (by simp)
    (fun {_ _} hc => FinitenessEulerDirichlet.term_multiplicative a b s hc)
    hsum.norm (LSeries.term_zero _ _)
  apply hprod.congr
  intro t
  apply Finset.prod_congr rfl
  intro p _
  dsimp only
  rw [show (∑' j, LSeries.term (value a b) s (p.val^j)) =
      ∑' j, coeff (a p.val) (b p.val) j * ((p.val:ℂ)^(-s))^j from
        tsum_congr (fun j => FinitenessEulerDirichlet.term_prime_pow a b p.property s j)]
  have hdisk : (‖a p.val‖+1)*‖(p.val:ℂ)^(-s)‖ < 1 := by
    have H := FinitenessEulerDirichlet.local_disk a d ha p.property
      (show (d : ℝ) < s.re by linarith)
    simpa only [norm_natCast_cpow_of_pos p.property.pos, neg_re, ofReal_re] using H
  rw [inverse_factor _ _ _ (hb _ p.property) hdisk]
  congr 2
  rw [← cpow_nat_mul]
  congr 1
  ring

/-- Polynomial growth, multiplicativity, and prime-power recurrences
imply the literal Euler product required by the paper's definition. -/
theorem eulerProduct_of_arithmetic {N : ℕ} {f : ℕ → ℂ}
    (hzero : f 0 = 0) (hone : f 1 = 1) {τ : ℝ}
    (hgrowth : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n)
    (hrec : ∀ p, p.Prime → ∀ j,
      f (p^(j+2)) = f p * f (p^(j+1)) - xi N p * f (p^j)) :
    FinitenessOriginalInput.EulerProduct N f := by
  have heq := eq_canonical_of_arithmetic hzero hone hmul hrec
  obtain ⟨d, hd⟩ := prime_bound (input_polynomial hzero hgrowth)
  refine ⟨(d : ℝ)+1, fun s hs => ?_⟩
  have H := canonical_hasProd_complex f (xi N) d (fun p _ => xi_bound N p) hd hs
  have hsum : LSeriesSummable f s := by
    rw [heq]
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    exact (FinitenessEulerDirichlet.abscissa_bound f (xi N) d
      (fun p _ => xi_bound N p) hd).trans_lt (by exact_mod_cast hs)
  rw [L_eq_mathlib hzero hsum]
  rw [← heq] at H
  exact H

#print axioms eq_canonical_of_arithmetic
#print axioms canonical_hasProd_complex
#print axioms eulerProduct_of_arithmetic

end AsymptoticClassicalEulerProduct
