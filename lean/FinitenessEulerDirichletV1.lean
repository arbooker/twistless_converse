module

public import FinitenessEulerCoefficientsV1
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.LSeries.Injectivity

@[expose] public section

set_option autoImplicit false

namespace FinitenessEulerDirichlet

open Complex FinitenessEulerCoefficients FinitenessEulerLocal

theorem abscissa_bound (a b : ℕ → ℂ) (d : ℕ)
    (hb : ∀ p, p.Prime → ‖b p‖ ≤ 1)
    (ha : ∀ p, p.Prime → ‖a p‖+1 ≤ (p : ℝ)^d) :
    LSeries.abscissaOfAbsConv (value a b) ≤ (d : ℝ)+1 := by
  apply LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
  refine ⟨1,fun n _ => ?_⟩
  simpa only [one_mul,Real.rpow_natCast] using value_bound a b d hb ha n

theorem term_multiplicative (a b : ℕ → ℂ) (s : ℂ) {m n : ℕ} (hc : m.Coprime n) :
    LSeries.term (value a b) s (m*n)=
      LSeries.term (value a b) s m*LSeries.term (value a b) s n := by
  simp only [LSeries.term_def₀ (value_zero a b),multiplicative a b hc,Nat.cast_mul]
  have he : ((m : ℂ)*(n:ℂ))^(-s)=(m:ℂ)^(-s)*(n:ℂ)^(-s) := by
    simpa only [ofReal_natCast] using
      mul_cpow_ofReal_nonneg (Nat.cast_nonneg m : (0:ℝ)≤m)
        (Nat.cast_nonneg n : (0:ℝ)≤n) (-s)
  rw [he]
  ring

theorem term_prime_pow (a b : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (s : ℂ) (j : ℕ) :
    LSeries.term (value a b) s (p^j)=coeff (a p) (b p) j*((p:ℂ)^(-s))^j := by
  rw [LSeries.term_def₀ (value_zero a b),value_prime_pow a b hp,Nat.cast_pow,
    ← natCast_cpow_natCast_mul,cpow_nat_mul]

theorem local_disk (a : ℕ → ℂ) (d : ℕ)
    (ha : ∀ p, p.Prime → ‖a p‖+1 ≤ (p : ℝ)^d)
    {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : (d:ℝ)<x) :
    (‖a p‖+1)*‖(p:ℂ)^(-(x:ℂ))‖<1 := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hn : ‖(p:ℂ)^(-(x:ℂ))‖=(p:ℝ)^(-x) := by
    simpa only [ofReal_neg,norm_natCast] using norm_cpow_real (p:ℂ) (-x)
  rw [hn]
  calc
    (‖a p‖+1)*(p:ℝ)^(-x) ≤ (p:ℝ)^d*(p:ℝ)^(-x) :=
      mul_le_mul_of_nonneg_right (ha p hp) (Real.rpow_nonneg hp0.le _)
    _ = (p:ℝ)^((d:ℝ)-x) := by rw [sub_eq_add_neg,Real.rpow_add hp0,Real.rpow_natCast]
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

/-- Reconstruction of the ACTUAL convergent Euler product of the
canonical coefficients, before comparison with the original sequence. -/
theorem hasProd (a b : ℕ → ℂ) (d : ℕ)
    (hb : ∀ p, p.Prime → ‖b p‖ ≤ 1)
    (ha : ∀ p, p.Prime → ‖a p‖+1 ≤ (p : ℝ)^d)
    {x : ℝ} (hx : (d:ℝ)+1<x) :
    HasProd (fun p : Nat.Primes =>
      (1-a p.val*(p.val:ℂ)^(-(x:ℂ))+b p.val*(p.val:ℂ)^(-2*(x:ℂ)))⁻¹)
      (LSeries (value a b) (x:ℂ)) := by
  have hs : LSeriesSummable (value a b) (x:ℂ) := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    exact (abscissa_bound a b d hb ha).trans_lt (by exact_mod_cast hx)
  have H := EulerProduct.eulerProduct_hasProd
    (f := LSeries.term (value a b) (x:ℂ))
    (by simp)
    (fun {_ _} hc => term_multiplicative a b (x:ℂ) hc)
    hs.norm (LSeries.term_zero _ _)
  apply H.congr
  intro t
  apply Finset.prod_congr rfl
  intro p _
  dsimp only
  rw [show (∑' j, LSeries.term (value a b) (x:ℂ) (p.val^j))=
      ∑' j, coeff (a p.val) (b p.val) j*((p.val:ℂ)^(-(x:ℂ)))^j from
        tsum_congr (fun j => term_prime_pow a b p.property (x:ℂ) j)]
  rw [inverse_factor _ _ _ (hb _ p.property) (local_disk a d ha p.property (by linarith))]
  congr 2
  rw [← cpow_nat_mul]
  norm_num

#print axioms hasProd

end FinitenessEulerDirichlet
