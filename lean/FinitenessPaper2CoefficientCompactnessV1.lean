module

public import FinitenessPaper2CoefficientBoundsV1
public import Mathlib.Topology.Sequences

set_option autoImplicit false

@[expose] public section

namespace FinitenessPaper2

open Filter Asymptotics Set
open scoped Topology

/-- A uniform product of coefficient disks; compactness here is for the
coefficientwise topology, not yet the disk-algebra topology in the paper. -/
def coefficientBox (σ : ℝ) : Set (ℕ → ℂ) :=
  {f | ∀ n : ℕ, ‖f n‖ ≤ (n.divisors.card : ℝ)*(n : ℝ)^σ}

theorem coefficientBox_isCompact (σ : ℝ) : IsCompact (coefficientBox σ) := by
  simpa only [coefficientBox, Metric.mem_closedBall, dist_zero_right] using
    (isCompact_pi_infinite (fun n : ℕ =>
      isCompact_closedBall (0 : ℂ) ((n.divisors.card : ℝ)*(n : ℝ)^σ)))

theorem subset_coefficientBox {N k : ℕ} {σ : ℝ} (hN : 0 < N) :
    E N k σ ⊆ coefficientBox σ := by
  intro f hf n
  by_cases hn : n = 0
  · subst n
    have ho := ((mem_iff_original N k σ f).mp hf).1
    rw [ho.zero, norm_zero]
    positivity
  · exact coefficient_uniform_bound hN hf hn

theorem closure_subset_coefficientBox {N k : ℕ} {σ : ℝ} (hN : 0 < N) :
    closure (E N k σ) ⊆ coefficientBox σ :=
  closure_minimal (subset_coefficientBox hN) (coefficientBox_isCompact σ).isClosed

/-- Compactness of the coefficientwise closure, without assuming that the
original growth class or its analytic-continuation condition is closed. -/
theorem coefficient_closure_isCompact {N k : ℕ} {σ : ℝ} (hN : 0 < N) :
    IsCompact (closure (E N k σ)) :=
  (coefficientBox_isCompact σ).of_isClosed_subset isClosed_closure
    (closure_subset_coefficientBox hN)

/-- Every coefficient limit has a uniform polynomial envelope; this does
not assert that the limit has the original prescribed Big-O exponent. -/
theorem closure_growth {N k : ℕ} {σ : ℝ} {f : ℕ → ℂ}
    (hN : 0 < N) (hf : f ∈ closure (E N k σ)) :
    f =O[atTop] (fun n : ℕ => (n : ℝ)^(σ+1)) := by
  have hb := closure_subset_coefficientBox hN hf
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
  have hle : ‖f n‖ ≤ (n : ℝ)^(σ+1) := by
    calc
      ‖f n‖ ≤ (n.divisors.card : ℝ)*(n : ℝ)^σ := hb n
      _ ≤ (n : ℝ)*(n : ℝ)^σ :=
        mul_le_mul_of_nonneg_right hd (Real.rpow_pos_of_pos hn' σ).le
      _ = (n : ℝ)^(σ+1) := by rw [Real.rpow_add hn', Real.rpow_one]; ring
  simpa only [one_mul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hn' (σ+1))] using hle

theorem closure_zero {N k : ℕ} {σ : ℝ} {f : ℕ → ℂ}
    (hf : f ∈ closure (E N k σ)) : f 0 = 0 := by
  have hsub : E N k σ ⊆ {g : ℕ → ℂ | g 0 = 0} := fun g hg =>
    ((mem_iff_original N k σ g).mp hg).1.zero
  exact closure_minimal hsub (isClosed_eq (continuous_apply 0) continuous_const) hf

theorem closure_one {N k : ℕ} {σ : ℝ} {f : ℕ → ℂ}
    (hf : f ∈ closure (E N k σ)) : f 1 = 1 := by
  have hsub : E N k σ ⊆ {g : ℕ → ℂ | g 1 = 1} := fun g hg =>
    (FinitenessEulerIdentification.solution_arithmetic
      ((mem_iff_original N k σ g).mp hg).1).1
  exact closure_minimal hsub (isClosed_eq (continuous_apply 1) continuous_const) hf

theorem closure_multiplicative {N k : ℕ} {σ : ℝ} {f : ℕ → ℂ}
    (hf : f ∈ closure (E N k σ)) {m n : ℕ} (hc : m.Coprime n) :
    f (m*n) = f m*f n := by
  have hsub : E N k σ ⊆ {g : ℕ → ℂ | g (m*n) = g m*g n} := fun g hg =>
    (FinitenessEulerIdentification.solution_arithmetic
      ((mem_iff_original N k σ g).mp hg).1).2.1 m n hc
  exact closure_minimal hsub (isClosed_eq (continuous_apply (m*n))
    ((continuous_apply m).mul (continuous_apply n))) hf

theorem closure_recurrence {N k : ℕ} {σ : ℝ} {f : ℕ → ℂ}
    (hf : f ∈ closure (E N k σ)) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    f (p^(j+2)) = f p*f (p^(j+1))-(if p ∣ N then (0 : ℂ) else 1)*f (p^j) := by
  have hsub : E N k σ ⊆ {g : ℕ → ℂ |
      g (p^(j+2)) = g p*g (p^(j+1))-(if p ∣ N then (0 : ℂ) else 1)*g (p^j)} :=
    fun g hg => (FinitenessEulerIdentification.solution_arithmetic
      ((mem_iff_original N k σ g).mp hg).1).2.2 p hp j
  exact closure_minimal hsub (isClosed_eq (continuous_apply (p^(j+2)))
    (((continuous_apply p).mul (continuous_apply (p^(j+1)))).sub
      (continuous_const.mul (continuous_apply (p^j))))) hf

/-- The original ramified square equations are also closed under limits. -/
theorem closure_bad_primes {N k : ℕ} {σ : ℝ} {f : ℕ → ℂ}
    (hf : f ∈ closure (E N k σ)) : FinitenessOriginalInput.BadPrimeConditions N f := by
  intro p hp hpN
  have hsub : E N k σ ⊆ {g : ℕ → ℂ |
      g p^2 = if p^2 ∣ N then 0 else (p : ℂ)⁻¹} := fun g hg =>
    ((mem_iff_original N k σ g).mp hg).1.bad p hp hpN
  exact closure_minimal hsub (isClosed_eq ((continuous_apply p).pow 2) continuous_const) hf

#print axioms coefficient_closure_isCompact
#print axioms closure_growth
#print axioms closure_multiplicative
#print axioms closure_recurrence
#print axioms closure_bad_primes

end FinitenessPaper2
