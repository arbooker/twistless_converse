module

public import QuantitativeHolomorphicPrimeProductV1
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open Finset
open scoped BigOperators

def reciprocalHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp [mul_comm]

theorem reciprocalHom_prime_norm {p : ℕ} (hp : p.Prime) :
    ‖reciprocalHom p‖ < 1 := by
  change ‖(p : ℝ)⁻¹‖ < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

/-- Finite Euler-product domination of the harmonic sum.  Global
summability of `1/n` is not assumed: only the sum over finitely generated
smooth numbers is used. -/
theorem harmonic_le_prime_euler_product (n : ℕ) :
    (harmonic n : ℝ) ≤ ∏ p ∈ (n + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  obtain ⟨_, hs⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := reciprocalHom) (fun {_} hp => reciprocalHom_prime_norm hp) (n + 1)
  have hs' : HasSum ((Nat.smoothNumbers (n + 1)).indicator (fun m : ℕ => (m : ℝ)⁻¹))
      (∏ p ∈ (n + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹) := by
    apply hasSum_subtype_iff_indicator.mp
    exact hs
  have hb := sum_le_hasSum (Icc 1 n)
    (fun m _ => Set.indicator_nonneg (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg j)) m) hs'
  have hid : (∑ m ∈ Icc 1 n,
      (Nat.smoothNumbers (n + 1)).indicator (fun j : ℕ => (j : ℝ)⁻¹) m) =
      (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    apply sum_congr rfl
    intro m hm
    rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt
      (by have := (mem_Icc.mp hm).1; omega)
      (by have := (mem_Icc.mp hm).2; omega))]
    simp
  rwa [hid] at hb

theorem log_prime_euler_product_le_loss (s : Finset ℕ)
    (hp : ∀ p ∈ s, p.Prime) :
    Real.log (∏ p ∈ s, (1 - (p : ℝ)⁻¹)⁻¹) ≤
      ∑ p ∈ s, 1 / ((p : ℝ) - 1) := by
  have hpos (p : ℕ) (h : p ∈ s) : 0 < (1 - (p : ℝ)⁻¹)⁻¹ := by
    apply inv_pos.mpr
    have hh : (1 : ℝ) < p := by exact_mod_cast (hp p h).one_lt
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hh)
  rw [Real.log_prod (fun p h => (hpos p h).ne')]
  apply sum_le_sum
  intro p h
  have hpR : (1 : ℝ) < p := by exact_mod_cast (hp p h).one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hid : (1 - (p : ℝ)⁻¹)⁻¹ - 1 = 1 / ((p : ℝ) - 1) := by
    field_simp
    ring
  exact (Real.log_le_sub_one_of_pos (hpos p h)).trans_eq hid

/-- An unconditional logarithmic lower bound with coefficient one for
the actual loss denominators.  This does not assert that every prime is
usable: shifted-divisor exclusions must still be controlled separately. -/
theorem loglog_le_prime_reciprocal_loss (n : ℕ) (hn : 0 < n) :
    Real.log (Real.log (n + 1 : ℕ)) ≤
      ∑ p ∈ (n + 1).primesBelow, 1 / ((p : ℝ) - 1) := by
  have hn' : (1 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast (show 1 < n + 1 by omega)
  have hprod : Real.log (n + 1 : ℕ) ≤
      ∏ p ∈ (n + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ :=
    (log_add_one_le_harmonic n).trans (harmonic_le_prime_euler_product n)
  exact (Real.log_le_log (Real.log_pos hn') hprod).trans
    (log_prime_euler_product_le_loss _ (fun p h => Nat.prime_of_mem_primesBelow h))

#print axioms harmonic_le_prime_euler_product
#print axioms log_prime_euler_product_le_loss
#print axioms loglog_le_prime_reciprocal_loss

end QuantitativeHolomorphic
