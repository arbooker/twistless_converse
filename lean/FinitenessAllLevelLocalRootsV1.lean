module

public import FinitenessEulerIdentificationV1
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

public section

namespace FinitenessAllLevelLocalRoots

open Filter Asymptotics

/-- A fixed multiplicative constant cannot dominate a faster exponential. -/
theorem le_of_geometric_bound {a b C : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ n : ℕ, a^(n+1) ≤ C*b^n) : a ≤ b := by
  by_contra! hab
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C/a) ((one_lt_div hb).mpr hab)
  have hlt : C < a*(a/b)^n := by
    simpa only [mul_div_cancel₀ _ ha.ne'] using mul_lt_mul_of_pos_left hn ha
  have he : (a*(a/b)^n)*b^n = a^(n+1) := by
    rw [mul_assoc, ← mul_pow, div_mul_cancel₀ _ hb.ne', pow_succ]
    ring
  have hh := mul_lt_mul_of_pos_right hlt (pow_pos hb n)
  rw [he] at hh
  exact (not_lt_of_ge (h n)) hh

/-- Factoring the reciprocal quadratic does not require distinct roots. -/
theorem exists_reciprocal_roots (a : ℂ) :
    ∃ α β : ℂ, α + β = a ∧ α*β = 1 := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (a^2-4) (by norm_num : 0 < (2 : ℕ))
  refine ⟨(a+d)/2, (a-d)/2, by ring, ?_⟩
  linear_combination -hd/4

/-- The recurrence detects each root separately, including repeated roots. -/
theorem root_power (c : ℕ → ℂ) (a α β : ℂ)
    (hzero : c 0 = 1) (hone : c 1 = a)
    (hrec : ∀ n, c (n+2) = a*c (n+1)-c n)
    (hsum : α+β = a) (hprod : α*β = 1) (n : ℕ) :
    α^(n+1) = c (n+1)-β*c n := by
  induction n with
  | zero => simp only [zero_add, pow_one, hzero, hone, mul_one]; linear_combination hsum
  | succ n ih =>
      calc
        α^(n+1+1) = α*(c (n+1)-β*c n) := by rw [pow_succ', ih]
        _ = c (n+2)-β*c (n+1) := by
          rw [hrec, ← hsum]
          linear_combination -hprod*c n

/-- Geometric bounds on the recurrence coefficients bound both roots. -/
theorem root_norm_le (c : ℕ → ℂ) (a α β : ℂ)
    (hzero : c 0 = 1) (hone : c 1 = a)
    (hrec : ∀ n, c (n+2) = a*c (n+1)-c n)
    (hsum : α+β = a) (hprod : α*β = 1)
    {C R : ℝ} (hR : 0 < R) (hbound : ∀ n, ‖c n‖ ≤ C*R^n) : ‖α‖ ≤ R := by
  have ha : α ≠ 0 := by intro h; simp [h] at hprod
  apply le_of_geometric_bound (norm_pos_iff.mpr ha) hR
    (C := C*(R+‖β‖))
  intro n
  calc
    ‖α‖^(n+1) = ‖c (n+1)-β*c n‖ := by
      rw [← norm_pow, root_power c a α β hzero hone hrec hsum hprod]
    _ ≤ ‖c (n+1)‖+‖β‖*‖c n‖ := by simpa only [norm_mul] using norm_sub_le (c (n+1)) (β*c n)
    _ ≤ C*R^(n+1)+‖β‖*(C*R^n) :=
      add_le_add (hbound _) (mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _))
    _ = (C*(R+‖β‖))*R^n := by rw [pow_succ]; ring

/-- A coefficient-growth hypothesis gives an exact geometric bound on
prime powers; its constant may depend on the individual sequence. -/
theorem prime_power_bound {f : ℕ → ℂ} {σ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^σ)) {p : ℕ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ‖f (p^j)‖ ≤ C*((p : ℝ)^σ)^j := by
  obtain ⟨C, hC, hb⟩ := bound_of_isBigO_nat_atTop hf
  refine ⟨C, hC, ?_⟩
  intro j
  have hpos : (0 : ℝ) < (p^j : ℕ) := by exact_mod_cast pow_pos hp j
  have h := hb (Real.rpow_pos_of_pos hpos σ).ne'
  have hh : ‖f (p^j)‖ ≤ C*((p^j : ℕ) : ℝ)^σ := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos σ)] using h
  simpa only [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg p)] using hh

/-- The literal Euler product and fixed coefficient exponent bound the
two local roots, with no common implicit coefficient constant assumed. -/
theorem good_prime_roots {N k p : ℕ} {f : ℕ → ℂ} {σ : ℝ}
    (hf : FinitenessOriginalInput.IsSolution N k f)
    (hg : f =O[atTop] (fun n : ℕ => (n : ℝ)^σ))
    (hp : p.Prime) (hgood : ¬ p ∣ N) :
    ∃ α β : ℂ, α+β = f p ∧ α*β = 1 ∧
      ‖α‖ ≤ (p : ℝ)^σ ∧ ‖β‖ ≤ (p : ℝ)^σ := by
  obtain ⟨α, β, hsum, hprod⟩ := exists_reciprocal_roots (f p)
  obtain ⟨C, _hC, hbound⟩ := prime_power_bound hg hp.pos
  have hzero : f (p^0) = 1 := by
    simpa only [pow_zero] using (FinitenessEulerIdentification.solution_arithmetic hf).1
  have hrec (n : ℕ) : f (p^(n+2)) = f p*f (p^(n+1))-f (p^n) := by
    simpa only [ite_eq_right hgood, one_mul] using
      (FinitenessEulerIdentification.solution_arithmetic hf).2.2 p hp n
  have hR := Real.rpow_pos_of_pos (show (0 : ℝ) < p by exact_mod_cast hp.pos) σ
  refine ⟨α, β, hsum, hprod, ?_, ?_⟩
  · exact root_norm_le (fun j => f (p^j)) (f p) α β hzero (by simp) hrec
      hsum hprod hR hbound
  · exact root_norm_le (fun j => f (p^j)) (f p) β α hzero (by simp) hrec
      (by simpa only [add_comm] using hsum) (by simpa only [mul_comm] using hprod) hR hbound

#print axioms le_of_geometric_bound
#print axioms root_norm_le
#print axioms good_prime_roots

end FinitenessAllLevelLocalRoots
