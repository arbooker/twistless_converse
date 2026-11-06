module

public import FinitenessEulerDirichletV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessEulerIdentification

open Complex Filter Asymptotics FinitenessOriginalInput FinitenessEulerCoefficients

noncomputable def xi (N p : ℕ) : ℂ := if p ∣ N then 0 else 1

theorem xi_bound (N p : ℕ) : ‖xi N p‖ ≤ 1 := by
  unfold xi
  split_ifs <;> norm_num

theorem input_polynomial {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n:ℝ)^τ)) :
    FinitenessPolynomialSeries.PolynomialBound f := by
  have h := FinitenessGrowthNormalization.polynomial_bound
    (f := fun n => (f n:ℂ)) (by simp [hf0]) hf 0
  have he : FinitenessGrowthNormalization.normalized f 0=
      f := by
    funext n
    simp only [FinitenessGrowthNormalization.normalized,Real.rpow_zero,ofReal_one,mul_one]
  rwa [he] at h

theorem input_abscissa {f : ℕ → ℂ} {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n:ℝ)^τ)) :
    LSeries.abscissaOfAbsConv f < ⊤ :=
  (LSeries.abscissaOfAbsConv_le_of_isBigO_rpow hf).trans_lt
    (EReal.coe_lt_top _)

theorem L_eq_mathlib {f : ℕ → ℂ} (hf0 : f 0=0) {s : ℂ}
    (hs : LSeriesSummable f s) :
    L f s=LSeries f s := by
  unfold L LSeries
  rw [hs.tsum_eq_zero_add]
  simp only [LSeries.term_zero,zero_add]
  apply tsum_congr
  intro n
  rw [LSeries.term_def₀ (by simp [hf0])]

/-- The original infinite Euler product determines the canonical local
coefficients. Multiplicativity is a CONCLUSION, not an extra input. -/
theorem eq_canonical {N : ℕ} {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n:ℝ)^τ))
    (heuler : FinitenessOriginalInput.EulerProduct N f) :
    f=value f (xi N) := by
  let a : ℕ → ℂ := fun n => (f n:ℂ)
  obtain ⟨d,hd⟩ := prime_bound (input_polynomial hf0 hf)
  have hb : ∀ p, p.Prime → ‖xi N p‖ ≤ 1 := fun p _ => xi_bound N p
  have hga : LSeries.abscissaOfAbsConv (value a (xi N)) < ⊤ :=
    (FinitenessEulerDirichlet.abscissa_bound a (xi N) d hb hd).trans_lt
      (EReal.coe_lt_top _)
  obtain ⟨c,hc⟩ := heuler
  have he : (fun x : ℝ => LSeries a (x:ℂ)) =ᶠ[atTop]
      (fun x : ℝ => LSeries (value a (xi N)) (x:ℂ)) := by
    filter_upwards [eventually_gt_atTop (max c (max ((d:ℝ)+1) (τ+1)))] with x hx
    have hxc : c<x := lt_of_le_of_lt (le_max_left _ _) hx
    have hxd : (d:ℝ)+1<x := lt_of_le_of_lt
      ((le_max_left _ _).trans (le_max_right _ _)) hx
    have hxτ : τ+1<x := lt_of_le_of_lt
      ((le_max_right _ _).trans (le_max_right _ _)) hx
    have H := hc (x:ℂ) (by simpa only [ofReal_re] using hxc)
    have J := FinitenessEulerDirichlet.hasProd a (xi N) d hb hd hxd
    change HasProd (fun p : Nat.Primes =>
      (1-a p.val*(p.val:ℂ)^(-(x:ℂ))+xi N p.val*(p.val:ℂ)^(-2*(x:ℂ)))⁻¹) (L f (x:ℂ)) at H
    have hs : LSeriesSummable a (x:ℂ) := by
      apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
      exact (LSeries.abscissaOfAbsConv_le_of_isBigO_rpow hf).trans_lt
        (by exact_mod_cast hxτ)
    rw [← L_eq_mathlib hf0 hs]
    exact H.unique J
  funext n
  by_cases hn : n=0
  · simp [hn,hf0]
  exact LSeries.eq_of_LSeries_eventually_eq (input_abscissa hf) hga he hn

theorem normalized_one {N : ℕ} {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n:ℝ)^τ))
    (heuler : FinitenessOriginalInput.EulerProduct N f) : f 1=1 := by
  have h := congr_fun (eq_canonical hf0 hf heuler) 1
  simpa using h

theorem multiplicative {N : ℕ} {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n:ℝ)^τ))
    (heuler : FinitenessOriginalInput.EulerProduct N f) {m n : ℕ} (hc : m.Coprime n) :
    f (m*n)=f m*f n := by
  have he := congr_fun (eq_canonical hf0 hf heuler)
  rw [he (m*n),he m,he n]
  exact FinitenessEulerCoefficients.multiplicative _ _ hc

theorem prime_power_recurrence {N : ℕ} {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n:ℝ)^τ))
    (heuler : FinitenessOriginalInput.EulerProduct N f) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    f (p^(j+2))=f p*f (p^(j+1))-(if p ∣ N then (0:ℂ) else 1)*f (p^j) := by
  have he (t : ℕ) : (f (p^t):ℂ)=FinitenessEulerLocal.coeff (f p) (xi N p) t :=
    (congr_fun (eq_canonical hf0 hf heuler) (p^t)).trans (value_prime_pow _ _ hp t)
  change f (p^(j+2)) = f p*f (p^(j+1))-xi N p*f (p^j)
  rw [he (j+2), he (j+1), he j]
  rfl

theorem bad_prime_power {N : ℕ} {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n:ℝ)^τ))
    (heuler : FinitenessOriginalInput.EulerProduct N f) {p : ℕ}
    (hp : p.Prime) (hpN : p ∣ N) (j : ℕ) : f (p^j)=(f p)^j := by
  induction j using Nat.twoStepInduction with
  | zero => simpa using normalized_one hf0 hf heuler
  | one => simp
  | more j _ ih =>
      rw [prime_power_recurrence hf0 hf heuler hp,ite_eq_left hpN]
      simp only [zero_mul,sub_zero,ih]
      exact (pow_succ' (f p) (j+1)).symm

/-- Literal original solution inputs imply the standard normalized
multiplicative and local recurrence data needed for Ramanujan twists. -/
theorem euler_arithmetic {N : ℕ} {f : ℕ → ℂ} (hf : EulerData N f) :
    f 1=1 ∧ (∀ m n, m.Coprime n → f (m*n)=f m*f n) ∧
      ∀ p, p.Prime → ∀ j,
        f (p^(j+2))=f p*f (p^(j+1))-(if p ∣ N then (0:ℂ) else 1)*f (p^j) := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  exact ⟨normalized_one hf.zero hg hf.euler,
    fun _ _ hc => multiplicative hf.zero hg hf.euler hc,
    fun _ hp j => prime_power_recurrence hf.zero hg hf.euler hp j⟩

theorem solution_arithmetic {N k : ℕ} {f : ℕ → ℂ} (hf : IsSolution N k f) :
    f 1=1 ∧ (∀ m n, m.Coprime n → f (m*n)=f m*f n) ∧
      ∀ p, p.Prime → ∀ j,
        f (p^(j+2))=f p*f (p^(j+1))-(if p ∣ N then (0:ℂ) else 1)*f (p^j) :=
  euler_arithmetic hf.toEulerData

#print axioms eq_canonical
#print axioms multiplicative
#print axioms prime_power_recurrence
#print axioms bad_prime_power
#print axioms solution_arithmetic

end FinitenessEulerIdentification
