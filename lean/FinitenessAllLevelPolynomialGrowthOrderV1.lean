module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelPolynomialPresentation

open Complex Set Filter Polynomial Asymptotics Bornology

variable {α : Type*} {l : Filter α} [l.NeBot] (z : α → ℂ)
    (hz : Tendsto z l (cobounded ℂ))

include hz

/-- Polynomial degree is detected along ANY filter escaping to infinity,
including a sequence avoiding every exceptional parameter. -/
theorem polynomial_degree_le_of_isBigO (P Q : Polynomial ℂ)
    (h : (fun t => P.eval (z t)) =O[l] (fun t => Q.eval (z t))) : P.degree ≤ Q.degree := by
  by_contra! hdeg
  have hp : P ≠ 0 := Polynomial.ne_zero_of_degree_gt hdeg
  have hne : ∀ᶠ t in l, P.eval (z t) ≠ 0 :=
    hz.eventually ((P.eventually_cofinite_not_isRoot hp).filter_mono (Bornology.le_cofinite ℂ))
  exact h.not_isLittleO hne.frequently
    ((Polynomial.isLittleO_cobounded_of_degree_lt hdeg).comp_tendsto hz)

/-- An upper polynomial-growth bound for powers of a polynomial gives the
corresponding integer degree inequality. -/
theorem polynomial_power_degree_bound (P : Polynomial ℂ) (m e : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᶠ t in l, ‖P.eval (z t)‖ ^ m ≤ C * (1 + ‖z t‖) ^ e) :
    m * P.natDegree ≤ e := by
  have hn : ∀ᶠ t in l, 1 ≤ ‖z t‖ :=
    (tendsto_norm_atTop_iff_cobounded.mpr hz).eventually (eventually_ge_atTop 1)
  have ho : (fun t => (P ^ m).eval (z t)) =O[l]
      (fun t => (Polynomial.X ^ e : Polynomial ℂ).eval (z t)) := by
    apply Asymptotics.IsBigO.of_bound (C * 2 ^ e)
    filter_upwards [hb, hn] with t ht hn
    simp only [Polynomial.eval_pow, Polynomial.eval_X, norm_pow]
    calc
      _ ≤ C * (1 + ‖z t‖) ^ e := ht
      _ ≤ C * (2 * ‖z t‖) ^ e := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith) e) hC
      _ = _ := by rw [mul_pow]; ring
  have hd := Polynomial.natDegree_le_natDegree (polynomial_degree_le_of_isBigO z hz _ _ ho)
  simpa only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one] using hd

/-- A reverse power bound gives the opposite integer degree inequality. -/
theorem base_power_degree_bound (P : Polynomial ℂ) (u v : ℕ) (C : ℝ)
    (hb : ∀ᶠ t in l, ‖z t‖ ^ u ≤ C * ‖P.eval (z t)‖ ^ v) :
    u ≤ v * P.natDegree := by
  have ho : (fun t => (Polynomial.X ^ u : Polynomial ℂ).eval (z t)) =O[l]
      (fun t => (P ^ v).eval (z t)) := by
    apply Asymptotics.IsBigO.of_bound C
    simpa only [Polynomial.eval_pow, Polynomial.eval_X, norm_pow] using hb
  have hd := Polynomial.natDegree_le_natDegree (polynomial_degree_le_of_isBigO z hz _ _ ho)
  simpa only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one] using hd

#print axioms polynomial_degree_le_of_isBigO
#print axioms polynomial_power_degree_bound
#print axioms base_power_degree_bound

end FinitenessAllLevelPolynomialPresentation
