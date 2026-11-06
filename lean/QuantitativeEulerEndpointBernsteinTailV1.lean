module

public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBernstein
open Polynomial
open scoped unitInterval

/-- A binomial tail is a genuine polynomial; its threshold need not be a
rational number, because the sum has only n+1 coefficients. -/
def indices (n : ℕ) (b : ℝ) : Finset (Fin (n+1)) :=
  Finset.univ.filter (fun k => b ≤ (bernstein.z k : ℝ))

def tail (n : ℕ) (b : ℝ) : ℝ[X] :=
  ∑ k ∈ indices n b, bernsteinPolynomial ℝ n k

theorem tail_eval (n : ℕ) (b : ℝ) (x : I) :
    (tail n b).eval (x:ℝ) = ∑ k ∈ indices n b, bernstein n k x := by
  simp only [tail, Polynomial.eval_finsetSum]
  rfl

theorem tail_nonneg (n : ℕ) (b : ℝ) (x : I) : 0 ≤ (tail n b).eval (x:ℝ) := by
  rw [tail_eval]
  exact Finset.sum_nonneg (fun _ _ => bernstein_nonneg)

theorem tail_le_one (n : ℕ) (b : ℝ) (x : I) : (tail n b).eval (x:ℝ) ≤ 1 := by
  rw [tail_eval, ← bernstein.probability n x]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => bernstein_nonneg)

theorem tail_zero (n : ℕ) {b : ℝ} (hb : 0<b) : (tail n b).eval 0 = 0 := by
  simp only [tail, Polynomial.eval_finsetSum]
  apply Finset.sum_eq_zero
  intro k hk
  have hk0 : (k : ℕ) ≠ 0 := by
    intro he
    have hz : (bernstein.z k : ℝ)=0 := by simp [bernstein.z,he]
    have hmem := (Finset.mem_filter.mp hk).2
    rw [hz] at hmem
    linarith
  simp only [bernsteinPolynomial.eval_at_0, ite_eq_right hk0]

theorem tail_one {n : ℕ} (hn : n≠0) {b : ℝ} (hb : b≤1) : (tail n b).eval 1 = 1 := by
  simp only [tail, Polynomial.eval_finsetSum, bernsteinPolynomial.eval_at_1]
  have hm : Fin.last n ∈ indices n b := by simp [indices,bernstein.z_last hn,hb]
  rw [Finset.sum_eq_single_of_mem (Fin.last n) hm]
  · simp
  · intro k _ hk
    have hk' : (k : ℕ)≠n := by intro he; exact hk (Fin.ext he)
    simp only [ite_eq_right hk']

/-- The elementary binomial variance bound supplies a quantitative tail
estimate. This avoids an unquantified approximation theorem. -/
theorem separated_mass_le {n : ℕ} (hn : 0<n) (x : I) (S : Finset (Fin (n+1)))
    {w : ℝ} (hw : 0<w)
    (hsep : ∀ k∈S, w^2 ≤ ((x : ℝ)-(bernstein.z k : ℝ))^2) :
    (∑ k∈S, bernstein n k x) ≤ 1/((n:ℝ)*w^2) := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hsq : 0<w^2 := sq_pos_of_pos hw
  have hsum : w^2*(∑ k∈S, bernstein n k x) ≤ (x:ℝ)*(1-x)/(n:ℝ) := by
    rw [Finset.mul_sum]
    apply (Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right (hsep k hk) bernstein_nonneg)).trans
    rw [← bernstein.variance (Nat.ne_of_gt hn) x]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => mul_nonneg (sq_nonneg _) bernstein_nonneg)
  have hx0 : (0:ℝ)≤x := x.property.1
  have hx1 : (x:ℝ)≤1 := x.property.2
  have hx : (x:ℝ)*(1-x)≤1 := by nlinarith [sq_nonneg (x:ℝ)]
  have hmul := mul_le_mul_of_nonneg_left hsum hnR.le
  have hcancel : (n:ℝ)*((x:ℝ)*(1-x)/(n:ℝ))=(x:ℝ)*(1-x) := by field_simp
  rw [hcancel] at hmul
  apply (le_div_iff₀ (mul_pos hnR hsq)).mpr
  nlinarith only [hmul.trans hx]

theorem tail_low {n : ℕ} (hn : 0<n) {b w : ℝ} (hw : 0<w) (x : I)
    (hx : (x:ℝ)≤b-w) : (tail n b).eval (x:ℝ) ≤ 1/((n:ℝ)*w^2) := by
  rw [tail_eval]
  apply separated_mass_le hn x (indices n b) hw
  intro k hk
  have hk' := (Finset.mem_filter.mp hk).2
  nlinarith [sq_nonneg ((bernstein.z k : ℝ)-(x:ℝ)-w)]

theorem tail_high {n : ℕ} (hn : 0<n) {b w : ℝ} (hw : 0<w) (x : I)
    (hx : b+w≤(x:ℝ)) : 1-(tail n b).eval (x:ℝ) ≤ 1/((n:ℝ)*w^2) := by
  have he : 1-(tail n b).eval (x:ℝ) = ∑ k∈(indices n b)ᶜ, bernstein n k x := by
    have h := (indices n b).sum_add_sum_compl (fun k => bernstein n k x)
    rw [bernstein.probability, ← tail_eval] at h
    linarith
  rw [he]
  apply separated_mass_le hn x (indices n b)ᶜ hw
  intro k hk
  have hk' : (bernstein.z k : ℝ)<b := by
    simpa only [Finset.mem_compl,indices,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hk
  nlinarith [sq_nonneg ((x:ℝ)-(bernstein.z k : ℝ)-w)]

#print axioms tail_nonneg
#print axioms tail_le_one
#print axioms tail_zero
#print axioms tail_one
#print axioms separated_mass_le
#print axioms tail_low
#print axioms tail_high
end QuantitativeEulerEndpointBernstein
