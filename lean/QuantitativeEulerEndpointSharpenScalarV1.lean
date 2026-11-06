module

public import QuantitativeEulerEndpointBernsteinTailV1
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBernstein
open Polynomial MeasureTheory
open scoped unitInterval

/-- Multiplication by X makes sharpening order decreasing on [0,1]. -/
def sharpen (n : ℕ) (b : ℝ) : ℝ[X] := X * tail n b

theorem sharpen_bounds (n : ℕ) (b : ℝ) (x : I) :
    0 ≤ (sharpen n b).eval (x:ℝ) ∧ (sharpen n b).eval (x:ℝ) ≤ (x:ℝ) := by
  simp only [sharpen, eval_mul, eval_X]
  exact ⟨mul_nonneg x.property.1 (tail_nonneg n b x),
    (mul_le_mul_of_nonneg_left (tail_le_one n b x) x.property.1).trans_eq (mul_one _)⟩

theorem sharpen_zero (n : ℕ) (b : ℝ) : (sharpen n b).eval 0 = 0 := by simp [sharpen]
theorem sharpen_one {n : ℕ} (hn : n≠0) {b : ℝ} (hb : b≤1) :
    (sharpen n b).eval 1 = 1 := by simp [sharpen,tail_one hn hb]

theorem bernstein_natDegree_le (n : ℕ) (k : Fin (n+1)) :
    (bernsteinPolynomial ℝ n k).natDegree ≤ n := by
  have hsub : ((1:ℝ[X])-X).natDegree ≤ 1 := by compute_degree
  have hpow : (((1:ℝ[X])-X)^(n-k)).natDegree ≤ n-k := by
    simpa using natDegree_pow_le_of_le (n-k) hsub
  unfold bernsteinPolynomial
  apply natDegree_mul_le.trans
  have hfirst : (((n.choose k : ℝ[X])*X^(k:ℕ))).natDegree ≤ (k:ℕ) := by
    simpa only [natDegree_natCast,natDegree_X_pow,zero_add] using
      (natDegree_mul_le (p := (n.choose k : ℝ[X])) (q := X^(k:ℕ)))
  exact (add_le_add hfirst hpow).trans_eq (Nat.add_sub_of_le k.is_le)

theorem tail_natDegree_le (n : ℕ) (b : ℝ) : (tail n b).natDegree ≤ n := by
  exact natDegree_sum_le_of_forall_le _ _ (fun k _ => bernstein_natDegree_le n k)

theorem sharpen_natDegree_le (n : ℕ) (b : ℝ) : (sharpen n b).natDegree ≤ n+1 := by
  exact natDegree_mul_le.trans ((add_le_add (by simp : (X:ℝ[X]).natDegree≤1)
    (tail_natDegree_le n b)).trans_eq (Nat.add_comm 1 n))

/-- Outside a short transition interval close to 1, the idempotency defect
of the explicit polynomial is uniformly small. -/
theorem sharpen_defect_pointwise {n : ℕ} (hn : 0<n) {a b w : ℝ}
    (ha : 0≤a) (hw : 0<w) (hb : 1-2*a≤b) (x : I) :
    let y := (sharpen n b).eval (x:ℝ)
    y-y^2 ≤ 2*a+1/((n:ℝ)*w^2)+
      (Set.Icc (b-w) (b+w)).indicator (fun _ : ℝ => 1) (x:ℝ) := by
  intro y
  have hy := sharpen_bounds n b x
  have hy1 : y≤1 := hy.2.trans x.property.2
  have heps : 0≤1/((n:ℝ)*w^2) := by positivity
  by_cases hband : (x:ℝ)∈Set.Icc (b-w) (b+w)
  · rw [Set.indicator_of_mem hband]
    nlinarith [sq_nonneg y]
  · rw [Set.indicator_of_notMem hband]
    have hout : (x:ℝ)<b-w ∨ b+w<(x:ℝ) := by
      simpa only [Set.mem_Icc,not_and_or,not_le] using hband
    rcases hout with hlow | hhigh
    · have ht := tail_low hn hw x hlow.le
      have ht0 := tail_nonneg n b x
      have hyt : y≤(tail n b).eval (x:ℝ) := by
        dsimp only [y]
        rw [sharpen,eval_mul,eval_X]
        exact (mul_le_mul_of_nonneg_right x.property.2 ht0).trans_eq (one_mul _)
      nlinarith [sq_nonneg y]
    · have ht := tail_high hn hw x hhigh.le
      have ht1 := tail_le_one n b x
      have he : 1-y ≤ (1-(x:ℝ))+(1-(tail n b).eval (x:ℝ)) := by
        dsimp only [y]
        rw [sharpen,eval_mul,eval_X]
        nlinarith [mul_nonneg (sub_nonneg.mpr x.property.2) (sub_nonneg.mpr ht1)]
      have hyy : y-y^2≤1-y := by nlinarith [sq_nonneg (1-y)]
      linarith

/-- Quantitative scalar sharpening for any finite spectral measure.
Only the transition interval contributes a nonuniform term. -/
theorem sharpen_defect_integral {β : Type*} [MeasurableSpace β]
    (μ : Measure β) [IsFiniteMeasure μ] (f : β → I)
    (hf : Measurable (fun x => (f x : ℝ))) {n : ℕ} (hn : 0<n) {a b w : ℝ}
    (ha : 0≤a) (hw : 0<w) (hb : 1-2*a≤b) :
    (∫ x, ((sharpen n b).eval (f x : ℝ)-(sharpen n b).eval (f x : ℝ)^2) ∂μ) ≤
      (2*a+1/((n:ℝ)*w^2))*μ.real Set.univ+
        μ.real {x | (f x : ℝ)∈Set.Icc (b-w) (b+w)} := by
  let g := fun x => (sharpen n b).eval (f x : ℝ)
  have hg : Measurable g := (sharpen n b).continuous.measurable.comp hf
  have hgi : Integrable (fun x => g x-(g x)^2) μ := by
    apply (integrable_const (1:ℝ)).mono' (hg.sub (hg.pow_const 2)).aestronglyMeasurable
    filter_upwards [] with x
    have hy := sharpen_bounds n b (f x)
    have hy1 := hy.2.trans (f x).property.2
    change |g x-g x^2| ≤ 1
    rw [abs_le]
    change 0 ≤ g x ∧ g x ≤ (f x : ℝ) at hy
    change g x ≤ 1 at hy1
    constructor <;> nlinarith [sq_nonneg (g x),mul_nonneg hy.1 (sub_nonneg.mpr hy1)]
  let E := {x | (f x : ℝ)∈Set.Icc (b-w) (b+w)}
  have hE : MeasurableSet E := hf isClosed_Icc.measurableSet
  have hi : Integrable (E.indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator hE
  have h := integral_mono hgi ((integrable_const (2*a+1/((n:ℝ)*w^2))).add hi) (fun x => by
    exact sharpen_defect_pointwise hn ha hw hb (f x))
  simp only [Pi.add_apply] at h
  simpa only [integral_add (integrable_const _) hi,integral_const,
    integral_indicator_const (1:ℝ) hE,smul_eq_mul,mul_one,one_mul,mul_comm] using h

#print axioms sharpen_bounds
#print axioms sharpen_one
#print axioms sharpen_natDegree_le
#print axioms sharpen_defect_pointwise
#print axioms sharpen_defect_integral
end QuantitativeEulerEndpointBernstein
