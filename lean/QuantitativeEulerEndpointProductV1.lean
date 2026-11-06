module

public import QuantitativeHolomorphicPrimeMassV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointProduct

open Finset QuantitativeHolomorphic

/-- Choosing the fresh-prime tolerance to be 1/p gives exactly the
classical Euler factor. This tolerance only has polynomial reciprocal cost. -/
theorem variable_tolerance_factor {p : ℕ} (hp : p.Prime) :
    1 - (1 - 1 / (p : ℝ)) / ((p : ℝ) - 1) = 1 - 1 / (p : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  field_simp

/-- Endpoint contraction product, with a finite and explicit exceptional
reciprocal mass. Relative density one alone does not supply this bound.
No asymptotic prime-number theorem is needed for this finite statement. -/
theorem endpoint_product (P : ℕ → Prop) [DecidablePred P]
    (n : ℕ) (hn : 0 < n) {B : ℝ}
    (hbad : (∑ p ∈ (n+1).primesBelow.filter (fun p => ¬ P p),
      1 / ((p : ℝ)-1)) ≤ B) :
    (∏ p ∈ (n+1).primesBelow.filter P,
      (1 - (1 - 1 / (p : ℝ)) / ((p : ℝ)-1))) ≤
        Real.exp B / Real.log (n+1 : ℝ) := by
  let S := (n+1).primesBelow
  let good := S.filter P
  let bad := S.filter (fun p => ¬ P p)
  let f : ℕ → ℝ := fun p => 1 - (p : ℝ)⁻¹
  have hf (p : ℕ) (hp : p ∈ S) : 0 < f p := by
    apply sub_pos.mpr
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast
      (Nat.prime_of_mem_primesBelow hp).one_lt)
  have hgood : 0 ≤ ∏ p ∈ good, f p :=
    prod_nonneg (fun p hp => (hf p (mem_filter.mp hp).1).le)
  have hbadpos : 0 < ∏ p ∈ bad, (f p)⁻¹ :=
    prod_pos (fun p hp => inv_pos.mpr (hf p (mem_filter.mp hp).1))
  have hbadexp : (∏ p ∈ bad, (f p)⁻¹) ≤ Real.exp B := by
    rw [← Real.exp_log hbadpos]
    apply Real.exp_le_exp.mpr
    exact (log_prime_euler_product_le_loss bad
      (fun p hp => Nat.prime_of_mem_primesBelow (mem_filter.mp hp).1)).trans hbad
  have hcancel : (∏ p ∈ good, (f p)⁻¹) * (∏ p ∈ good, f p) = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro p hp
    exact inv_mul_cancel₀ (hf p (mem_filter.mp hp).1).ne'
  have hsplit : (∏ p ∈ S, (f p)⁻¹) =
      (∏ p ∈ good, (f p)⁻¹) * (∏ p ∈ bad, (f p)⁻¹) :=
    (prod_filter_mul_prod_filter_not S P (fun p => (f p)⁻¹)).symm
  have hfull : Real.log (n+1 : ℝ) ≤ ∏ p ∈ S, (f p)⁻¹ := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (log_add_one_le_harmonic n).trans (harmonic_le_prime_euler_product n)
  have hmain : Real.log (n+1 : ℝ) * (∏ p ∈ good, f p) ≤ Real.exp B := by
    calc
      _ ≤ (∏ p ∈ S, (f p)⁻¹) * (∏ p ∈ good, f p) :=
        mul_le_mul_of_nonneg_right hfull hgood
      _ = ∏ p ∈ bad, (f p)⁻¹ := by rw [hsplit]; nlinarith [hcancel]
      _ ≤ Real.exp B := hbadexp
  have hlog : 0 < Real.log (n+1 : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n+1 by omega))
  have hresult : (∏ p ∈ good, f p) ≤ Real.exp B / Real.log (n+1 : ℝ) := by
    apply (le_div_iff₀ hlog).mpr
    simpa only [mul_comm] using hmain
  convert hresult using 1
  apply prod_congr rfl
  intro p hp
  simpa only [f, one_div] using
    variable_tolerance_factor (Nat.prime_of_mem_primesBelow (mem_filter.mp hp).1)

/-- A summable exceptional reciprocal mass supplies one constant for all
cutoffs. The summability premise remains an arithmetic obligation. -/
theorem endpoint_product_of_summable_exceptions
    (P : ℕ → Prop) [DecidablePred P]
    (hs : Summable (fun p : ℕ => if p.Prime ∧ ¬ P p then
      1 / ((p : ℝ)-1) else 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (∏ p ∈ (n+1).primesBelow.filter P,
        (1 - (1 - 1 / (p : ℝ)) / ((p : ℝ)-1))) ≤
          C / Real.log (n+1 : ℝ) := by
  let b : ℕ → ℝ := fun p => if p.Prime ∧ ¬ P p then
    1 / ((p : ℝ)-1) else 0
  refine ⟨Real.exp (∑' p, b p), Real.exp_pos _, ?_⟩
  intro n hn
  apply endpoint_product P n hn
  have hb (p : ℕ) : 0 ≤ b p := by
    dsimp [b]
    split_ifs with hp
    · have : (2 : ℝ) ≤ p := by exact_mod_cast hp.1.two_le
      exact div_nonneg (by norm_num) (by linarith)
    · exact le_rfl
  have hh := hs.sum_le_tsum ((n+1).primesBelow.filter (fun p => ¬ P p))
    (fun p _ => hb p)
  convert hh using 1
  apply sum_congr rfl
  intro p hp
  have h := mem_filter.mp hp
  simp [b, Nat.prime_of_mem_primesBelow h.1, h.2]

#print axioms variable_tolerance_factor
#print axioms endpoint_product
#print axioms endpoint_product_of_summable_exceptions

end QuantitativeEulerEndpointProduct
