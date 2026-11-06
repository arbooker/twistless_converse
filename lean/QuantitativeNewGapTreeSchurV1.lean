module

public import QuantitativeMaassTreeOperatorV1
public import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
@[expose] public noncomputable section

open scoped BigOperators lp

namespace QuantitativeNewGap

/-- A positive weight for a finite sum of involutive neighbor permutations
bounds the actual counting-L² operator. The weight need not itself be L²
or bounded away from zero. -/
theorem involution_sum_norm_le {ι V : Type*} [Fintype ι]
    (e : ι → V ≃ V) (he : ∀ a, Function.Involutive (e a))
    (w : V → ℝ) (hw : ∀ v, 0<w v) (C : ℝ) (hC : 0≤C)
    (hs : ∀ v, ∑ a : ι, w (e a v)=C*w v) :
    ‖∑ a : ι, (QuantitativeMaass.l2Permutation (e a)).toContinuousLinearEquiv.toContinuousLinearMap‖≤C := by
  have heqstep (a : ι) (v : V) : e a (e a v)=v := he a v
  let A := ∑ a : ι, (QuantitativeMaass.l2Permutation (e a)).toContinuousLinearEquiv.toContinuousLinearMap
  have hrat (v : V) : (∑ a : ι, w (e a v)/w v)=C := by
    rw [← Finset.sum_div,hs, mul_div_cancel_right₀ _ (hw v).ne']
  have hrbound (a : ι) (v : V) : w (e a v)/w v≤C := by
    rw [← hrat v]
    exact Finset.single_le_sum (fun b _ => div_nonneg (hw (e b v)).le (hw v).le)
      (Finset.mem_univ a)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  have hf : Summable (fun v : V => ‖f v‖^2) := by
    simpa using (lp.hasSum_norm (p:=2) (by norm_num) f).summable
  have hn : (∑' v : V, ‖f v‖^2)=‖f‖^2 := by
    simpa using (lp.hasSum_norm (p:=2) (by norm_num) f).tsum_eq
  let q (a : ι) (v : V) := w v/w (e a v)*‖f (e a v)‖^2
  have hq (a : ι) : Summable (q a) := by
    apply Summable.of_nonneg_of_le (fun v => mul_nonneg (div_nonneg (hw v).le (hw _).le)
      (sq_nonneg _)) _ (((e a).summable_iff.mpr hf).mul_left C)
    intro v
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa only [he a v] using hrbound a (e a v)
  have hsum : (∑' v : V, ∑ a : ι, q a v)=C*‖f‖^2 := by
    rw [Summable.tsum_finsetSum (fun a _ => hq a)]
    have hperm (a : ι) : (∑' v : V,q a v)=∑' v : V,w (e a v)/w v*‖f v‖^2 := by
      rw [← (e a).tsum_eq (q a)]
      simp only [q,heqstep]
    simp_rw [hperm]
    have hqs (a : ι) : Summable (fun v : V => w (e a v)/w v*‖f v‖^2) := by
      have ht : Summable (fun v : V => q a (e a v)) := (e a).summable_iff.mpr (hq a)
      simpa only [q,heqstep] using ht
    rw [← Summable.tsum_finsetSum (fun a _ => hqs a)]
    simp_rw [← Finset.sum_mul,hrat]
    rw [tsum_mul_left,hn]
  have hpoint (v : V) : ‖A f v‖^2≤C*∑ a : ι,q a v := by
    have heq : A f v=∑ a : ι, f (e a v) := by
      simp only [A,sum_apply,lp.coeFn_sum,Finset.sum_apply,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe,QuantitativeMaass.l2Permutation_apply]
    rw [heq]
    calc
      ‖∑ a : ι,f (e a v)‖^2≤(∑ a : ι,‖f (e a v)‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (∑ a : ι,w (e a v)/w v)*(∑ a : ι,q a v) := by
        apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
        · intro a _; exact div_nonneg (hw _).le (hw _).le
        · intro a _; exact mul_nonneg (div_nonneg (hw _).le (hw _).le) (sq_nonneg _)
        · intro a _
          apply le_of_eq
          dsimp [q]
          field_simp [(hw v).ne',(hw (e a v)).ne']
      _ = _ := by rw [hrat]
  have hA : Summable (fun v : V => ‖A f v‖^2) := by
    simpa using (lp.hasSum_norm (p:=2) (by norm_num) (A f)).summable
  have hsumq := (hasSum_sum (fun a (_ : a∈Finset.univ) => (hq a).hasSum)).summable
  have hb := hA.tsum_le_tsum hpoint (hsumq.mul_left C)
  have hnA : (∑' v : V, ‖A f v‖^2)=‖A f‖^2 := by
    simpa using (lp.hasSum_norm (p:=2) (by norm_num) (A f)).tsum_eq
  rw [hnA,tsum_mul_left,hsum] at hb
  change ‖A f‖≤C*‖f‖
  nlinarith [norm_nonneg (A f),mul_nonneg hC (norm_nonneg f)]

#print axioms involution_sum_norm_le

end QuantitativeNewGap
