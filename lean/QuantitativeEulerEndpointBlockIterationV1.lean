module

public import QuantitativeEulerEndpointBlockArithmeticV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBlocks
open Finset

/-- A scalar block iteration with explicit multiplicative and additive
losses. Its recurrence is a hypothesis, not an assertion about Euler counts.
The additive losses must be summable AFTER multiplication by the target scale. -/
theorem normalized_block_iteration (e loss err : ℕ → ℝ) {R : ℝ} (hR : 0<R)
    (_he : 0≤e 0) (hloss : ∀ j, 0≤loss j) (herr : ∀ j, 0≤err j)
    (hstep : ∀ j, e (j+1)≤Real.exp (loss j)/R*e j+err j) (n : ℕ) :
    R^n*e n≤Real.exp (∑ j ∈ range n, loss j)*
      (e 0+∑ j ∈ range n, R^(j+1)*err j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0≤R^(n+1) := (pow_pos hR _).le
    have hb := mul_le_mul_of_nonneg_left (hstep n) hn
    have hcoef : R^(n+1)*(Real.exp (loss n)/R*e n+err n)=
        Real.exp (loss n)*(R^n*e n)+R^(n+1)*err n := by
      rw [pow_succ]
      field_simp [hR.ne']
    rw [hcoef] at hb
    have hi := mul_le_mul_of_nonneg_left ih (Real.exp_pos (loss n)).le
    have hexp : 1≤Real.exp (∑ j ∈ range (n+1), loss j) :=
      Real.one_le_exp_iff.mpr (sum_nonneg (fun j _ => hloss j))
    have heterm : R^(n+1)*err n≤
        Real.exp (∑ j ∈ range (n+1), loss j)*(R^(n+1)*err n) := by
      exact le_mul_of_one_le_left (mul_nonneg hn (herr n)) hexp
    calc
      _ ≤ Real.exp (loss n)*(R^n*e n)+R^(n+1)*err n := hb
      _ ≤ Real.exp (loss n)*(Real.exp (∑ j ∈ range n, loss j)*
          (e 0+∑ j ∈ range n, R^(j+1)*err j))+
          Real.exp (∑ j ∈ range (n+1), loss j)*(R^(n+1)*err n) :=
        add_le_add hi heterm
      _ = _ := by rw [sum_range_succ,sum_range_succ,Real.exp_add]; ring

/-- Summable multiplicative loss and scale-weighted additive loss give the
exact endpoint R^(-n), with one constant. No loss in the exponent is needed. -/
theorem block_endpoint_of_summable_losses (e loss err : ℕ → ℝ) {R : ℝ} (hR : 0<R)
    (he : 0≤e 0) (hloss : ∀ j, 0≤loss j) (herr : ∀ j, 0≤err j)
    (hstep : ∀ j, e (j+1)≤Real.exp (loss j)/R*e j+err j)
    (hs : Summable loss) (ha : Summable (fun j => R^(j+1)*err j)) (n : ℕ) :
    e n≤(Real.exp (∑' j, loss j)*(e 0+∑' j, R^(j+1)*err j))/R^n := by
  have hn := normalized_block_iteration e loss err hR he hloss herr hstep n
  have hl := Real.exp_le_exp.mpr (hs.sum_le_tsum (range n) (fun j _ => hloss j))
  have hsum := ha.sum_le_tsum (range n) (fun j _ => mul_nonneg (pow_pos hR _).le (herr j))
  have hnonneg : 0≤e 0+∑ j ∈ range n, R^(j+1)*err j :=
    add_nonneg he (sum_nonneg (fun j _ => mul_nonneg (pow_pos hR _).le (herr j)))
  have hb := mul_le_mul hl (add_le_add le_rfl hsum) hnonneg (Real.exp_pos _).le
  apply (le_div_iff₀ (pow_pos hR n)).mpr
  simpa only [mul_comm] using hn.trans hb

#print axioms normalized_block_iteration
#print axioms block_endpoint_of_summable_losses
end QuantitativeEulerEndpointBlocks
