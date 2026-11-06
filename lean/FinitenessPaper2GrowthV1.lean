module

public import FinitenessAllLevelLocalRootsV1
public import FinitenessPaperTheoremV1

set_option autoImplicit false

@[expose] public section

namespace FinitenessPaper2

open Filter Asymptotics FinitenessAllLevelLocalRoots

/-- The set `E_sigma(N,k)` in `paper2-Astra.tex`. The exponent is fixed,
but the implicit Big-O constant is allowed to depend on the sequence. -/
def E (N k : ℕ) (σ : ℝ) : Set (ℕ → ℂ) :=
  {f | FinitenessPaper.IsSolution N k f ∧
    f =O[atTop] (fun n : ℕ => (n : ℝ)^σ)}

theorem mem_iff_original (N k : ℕ) (σ : ℝ) (f : ℕ → ℂ) :
    f ∈ E N k σ ↔ FinitenessOriginalInput.IsSolution N k f ∧
      f =O[atTop] (fun n : ℕ => (n : ℝ)^σ) := by
  change (FinitenessPaper.IsSolution N k f ∧ _) ↔ _
  rw [FinitenessPaper.isSolution_iff_original]

/-- Uniform reciprocal-root geometry bounds the trace of the roots. -/
theorem norm_sum_le_of_reciprocal {α β : ℂ} {R : ℝ}
    (hR : 0 < R) (hprod : α*β = 1) (ha : ‖α‖ ≤ R) (hb : ‖β‖ ≤ R) :
    1 ≤ R ∧ ‖α+β‖ ≤ R+R⁻¹ := by
  have hp : ‖α‖*‖β‖ = 1 := by simpa only [norm_mul, norm_one] using congrArg norm hprod
  have hs : 1 ≤ R^2 := by
    simpa only [hp, pow_two] using mul_le_mul ha hb (norm_nonneg _) hR.le
  have hlarge : 1 ≤ R := by nlinarith
  refine ⟨hlarge, (norm_add_le α β).trans ?_⟩
  apply le_of_mul_le_mul_left (a := R) _ hR
  have hm := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  have hi := mul_inv_cancel₀ hR.ne'
  nlinarith

/-- The paper's exact eigenvalue bound at every good prime. Its constant
is independent of the solution and of that solution's Big-O constant. -/
theorem good_prime_bound {N k p : ℕ} {σ : ℝ} {f : ℕ → ℂ}
    (hf : f ∈ E N k σ) (hp : p.Prime) (hgood : ¬ p ∣ N) :
    1 ≤ (p : ℝ)^σ ∧ ‖f p‖ ≤ (p : ℝ)^σ+(p : ℝ)^(-σ) := by
  obtain ⟨ho, hg⟩ := (mem_iff_original N k σ f).mp hf
  obtain ⟨α, β, hsum, hprod, ha, hb⟩ := good_prime_roots ho hg hp hgood
  have hh := norm_sum_le_of_reciprocal
    (Real.rpow_pos_of_pos (show (0 : ℝ) < p by exact_mod_cast hp.pos) σ) hprod ha hb
  simpa only [hsum, Real.rpow_neg (Nat.cast_nonneg p)] using hh

/-- One can always choose a good prime larger than the square root of
the level. This choice does not impose any admissibility condition. -/
theorem exists_large_good_prime (N : ℕ) (hN : 0 < N) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ N ∧ N < p^2 := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N+1)
  have hNp : N < p := by omega
  refine ⟨p, hp, ?_, ?_⟩
  · intro hd
    exact (not_le_of_gt hNp) (Nat.le_of_dvd hN hd)
  · nlinarith [hp.two_le]

/-- A negative fixed exponent is impossible at every positive level. -/
theorem exponent_nonneg {N k : ℕ} {σ : ℝ} {f : ℕ → ℂ}
    (hN : 0 < N) (hf : f ∈ E N k σ) : 0 ≤ σ := by
  obtain ⟨p, hp, hgood, _⟩ := exists_large_good_prime N hN
  have hb := (good_prime_bound hf hp hgood).1
  by_contra! hneg
  exact (not_lt_of_ge hb) (Real.rpow_lt_one_of_one_lt_of_neg
    (show (1 : ℝ) < p by exact_mod_cast hp.one_lt) hneg)

theorem negative_exponent_empty {N k : ℕ} {σ : ℝ} (hN : 0 < N) (hσ : σ < 0) :
    E N k σ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro f hf
  exact (not_lt_of_ge (exponent_nonneg hN hf)) hσ

/-- The negative-exponent case of the requested Theorem 1.1. -/
theorem finite_of_exponent_neg {N k : ℕ} {σ : ℝ} (hN : 0 < N) (hσ : σ < 0) :
    (E N k σ).Finite := by
  rw [negative_exponent_empty hN hσ]
  exact Set.finite_empty

#print axioms good_prime_bound
#print axioms exists_large_good_prime
#print axioms exponent_nonneg
#print axioms finite_of_exponent_neg

end FinitenessPaper2
