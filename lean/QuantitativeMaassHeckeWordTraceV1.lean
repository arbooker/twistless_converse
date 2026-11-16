module

public import QuantitativeMaassHeckeStandardV1
public import QuantitativeMaassCorrespondenceTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- Positive determinant is preserved by each literal standard Hecke branch. -/
theorem heckeUpper_left_det_pos (p : ℕ) [Fact p.Prime] (j : Option (ZMod p))
    (M : HeckeUpper) (hM : 0<M.matrix.det) : 0<(HeckeUpper.left p j M).matrix.det := by
  rw [HeckeUpper.det_matrix,HeckeUpper.left_det]
  rw [HeckeUpper.det_matrix] at hM
  exact mul_pos (by exact_mod_cast (Fact.out : p.Prime).pos) hM

/-- Literal finite standard word sum of actual window correspondence kernels.
Nonpositive determinants are extended by zero solely to make the recursion total. -/
def upperWindowKernel (N p : ℕ) [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) : ℕ → HeckeUpper → ℍ → ℂ
  | 0,M,x => if hM : 0<M.matrix.det then windowIntegralKernel N M.matrix hM K hc R hR a b x else 0
  | n+1,M,x => (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ) *
      ∑ j : Option (ZMod p),upperWindowKernel N p K hc R hR a b n (HeckeUpper.left p j M) x

/-- Every fixed finite standard word kernel is continuous on the actual
quotient model and is therefore locally integrable. -/
theorem upperWindowKernel_continuous (N p : ℕ) [NeZero N] [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (n : ℕ) (M : HeckeUpper) :
    Continuous (upperWindowKernel N p K hc R hR a b n M) := by
  induction n generalizing M with
  | zero =>
    by_cases hM : 0<M.matrix.det
    · simpa only [upperWindowKernel,dite_eq_left hM] using
        (windowIntegralKernel_continuous N M.matrix hM K he hc R hR a b).1
    · simp only [upperWindowKernel,dite_eq_right hM]
      exact continuous_const
  | succ n ih =>
    exact (continuous_finsetSum Finset.univ (fun j _ => ih (HeckeUpper.left p j M))).const_mul _

/-- Every fixed finite standard word trace has its exact returning-word
coefficient under the original shrinking-window hypotheses. -/
theorem upperWindowKernel_interval_trace_main (N p : ℕ) [NeZero N] [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (n : ℕ) (M : HeckeUpper) (hM : 0<M.matrix.det) :
    Tendsto (fun t =>
      (∫ x in Metric.closedBall o (positiveWindowRadius ε t),
        (upperWindowKernel N p K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
          t (t+ε t) n M x).re ∂quotientMeasure N)/(t*ε t))
      atTop (𝓝 ((Real.sqrt (p:ℝ))⁻¹^n*(HeckeUpper.rawWalks p n M:ℝ)*
        (quotientMeasure N).real univ/(2*Real.pi))) := by
  let α : ℝ := (Real.sqrt (p:ℝ))⁻¹
  let V := (quotientMeasure N).real univ
  induction n generalizing M with
  | zero =>
    have hh := windowIntegralKernel_interval_trace_main N M.matrix hM K he hc hK hm o ε hε hproduct
    by_cases ht : M.translation
    · simpa only [upperWindowKernel,dite_eq_left hM,HeckeUpper.rawWalks,
        ite_eq_left ht,Nat.cast_one,pow_zero,one_mul,integralIdentityCoset_upper_iff N M hM] using hh
    · simpa only [upperWindowKernel,dite_eq_left hM,HeckeUpper.rawWalks,
        ite_eq_right ht,Nat.cast_zero,pow_zero,one_mul,mul_zero,zero_mul,zero_div,
        integralIdentityCoset_upper_iff N M hM] using hh
  | succ n ih =>
    have hi (j : Option (ZMod p)) := ih (HeckeUpper.left p j M) (heckeUpper_left_det_pos p j M hM)
    have hlim := (tendsto_finsetSum Finset.univ (fun j _ => hi j)).const_mul α
    have hfun (t : ℝ) :
        (∫ x in Metric.closedBall o (positiveWindowRadius ε t),
          (upperWindowKernel N p K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
            t (t+ε t) (n+1) M x).re ∂quotientMeasure N)/(t*ε t)=
        α*∑ j : Option (ZMod p),
          (∫ x in Metric.closedBall o (positiveWindowRadius ε t),
            (upperWindowKernel N p K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
              t (t+ε t) n (HeckeUpper.left p j M) x).re ∂quotientMeasure N)/(t*ε t) := by
      have hj (j : Option (ZMod p)) : IntegrableOn (fun x =>
          (upperWindowKernel N p K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
            t (t+ε t) n (HeckeUpper.left p j M) x).re)
          (Metric.closedBall o (positiveWindowRadius ε t)) (quotientMeasure N) :=
        (Complex.continuous_re.comp (upperWindowKernel_continuous N p K he hc _
          (positiveWindowRadius_pos ε t) t (t+ε t) n (HeckeUpper.left p j M))).continuousOn.integrableOn_compact
            (isCompact_closedBall o (positiveWindowRadius ε t))
      simp only [upperWindowKernel,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero,Complex.re_sum]
      rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ => hj j)]
      rw [mul_div_assoc,Finset.sum_div]
    have hconst : α*(∑ j : Option (ZMod p),α^n*(HeckeUpper.rawWalks p n (HeckeUpper.left p j M):ℝ)*V/(2*Real.pi))=
        α^(n+1)*(HeckeUpper.rawWalks p (n+1) M:ℝ)*V/(2*Real.pi) := by
      simp only [HeckeUpper.rawWalks,Nat.cast_sum,Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    change Tendsto (fun t => α*∑ j : Option (ZMod p),
      (∫ x in Metric.closedBall o (positiveWindowRadius ε t),
        (upperWindowKernel N p K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
          t (t+ε t) n (HeckeUpper.left p j M) x).re ∂quotientMeasure N)/(t*ε t))
      atTop (𝓝 (α*(∑ j : Option (ZMod p),α^n*(HeckeUpper.rawWalks p n (HeckeUpper.left p j M):ℝ)*V/(2*Real.pi)))) at hlim
    rw [hconst] at hlim
    exact hlim.congr (fun t => (hfun t).symm)

/-- Rooted standard word traces have the checked regular-tree moments,
with the actual normalized-Hecke factor p^(-n/2). -/
theorem upperWindowKernel_root_trace_main (N p : ℕ) [NeZero N] [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (o : ℍ)
    (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) (n : ℕ) :
    Tendsto (fun t =>
      (∫ x in Metric.closedBall o (positiveWindowRadius ε t),
        (upperWindowKernel N p K hc (positiveWindowRadius ε t) (positiveWindowRadius_pos ε t)
          t (t+ε t) n HeckeUpper.root x).re ∂quotientMeasure N)/(t*ε t))
      atTop (𝓝 ((Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*
        (quotientMeasure N).real univ/(2*Real.pi))) := by
  have hh := upperWindowKernel_interval_trace_main N p K he hc hK hm o ε hε hproduct n
    HeckeUpper.root (by norm_num [HeckeUpper.det_matrix,HeckeUpper.root_det])
  simpa only [HeckeUpper.rawWalks_root_eq_tree] using hh

#print axioms heckeUpper_left_det_pos
#print axioms upperWindowKernel_continuous
#print axioms upperWindowKernel_interval_trace_main
#print axioms upperWindowKernel_root_trace_main

end QuantitativeMaass
