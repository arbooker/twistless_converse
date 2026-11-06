module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticPolynomialVariation
open scoped BigOperators

/-- A deliberately coarse power bound, convenient for exact finite
polynomial certificates on a fixed disk. -/
theorem power_difference (z w : ℂ) (R : ℝ) (hR : 1≤R)
    (hz : ‖z‖≤R) (hw : ‖w‖≤R) (n : ℕ) :
    ‖z^n-w^n‖ ≤ (n:ℝ)*R^n*‖z-w‖ := by
  have hR0 : 0≤R := le_trans (by norm_num) hR
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z^(n+1)-w^(n+1) = (z^n-w^n)*z+w^n*(z-w) := by ring
    rw [he]
    calc
      ‖(z^n-w^n)*z+w^n*(z-w)‖ ≤ ‖z^n-w^n‖*‖z‖+‖w‖^n*‖z-w‖ := by
        simpa only [norm_mul,norm_pow] using norm_add_le ((z^n-w^n)*z) (w^n*(z-w))
      _ ≤ ((n:ℝ)*R^n*‖z-w‖)*R+R^n*‖z-w‖ :=
        add_le_add (mul_le_mul ih hz (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw n) (norm_nonneg _))
      _ ≤ ((n:ℝ)*R^n*‖z-w‖)*R+R^n*‖z-w‖*R := by
        exact add_le_add le_rfl (le_mul_of_one_le_right
          (show 0≤R^n*‖z-w‖ by positivity) hR)
      _ = ((n+1:ℕ):ℝ)*R^(n+1)*‖z-w‖ := by
        rw [Nat.cast_add,Nat.cast_one,pow_succ]
        ring

theorem finite_polynomial_difference {n : ℕ} (c : Fin n → ℂ)
    (z w : ℂ) (R B : ℝ) (hR : 1≤R) (hB : 0≤B)
    (hz : ‖z‖≤R) (hw : ‖w‖≤R) (hc : ∀ i, ‖c i‖≤B) :
    ‖(∑ i, c i*z^i.val)-(∑ i, c i*w^i.val)‖ ≤
      (B*∑ i : Fin n, (i.val:ℝ)*R^i.val)*‖z-w‖ := by
  have he : (∑ i, c i*z^i.val)-(∑ i, c i*w^i.val) =
      ∑ i, c i*(z^i.val-w^i.val) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  calc
    ‖∑ i, c i*(z^i.val-w^i.val)‖ ≤ ∑ i, ‖c i‖*‖z^i.val-w^i.val‖ := by
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun i : Fin n => c i*(z^i.val-w^i.val))
    _ ≤ ∑ i : Fin n, B*((i.val:ℝ)*R^i.val*‖z-w‖) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (hc i) (power_difference z w R hR hz hw i.val) (norm_nonneg _) hB
    _ = (B*∑ i : Fin n, (i.val:ℝ)*R^i.val)*‖z-w‖ := by
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

#print axioms power_difference
#print axioms finite_polynomial_difference
end QuantitativeArithmeticPolynomialVariation
