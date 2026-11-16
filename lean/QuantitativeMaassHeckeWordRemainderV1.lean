module

public import QuantitativeMaassHeckeWordHeightV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip
open scoped Topology FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- The literal nonscalar part of the finite Hecke correspondence sum. -/
def upperWindowRemainder (N p : ℕ) [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) : ℕ → HeckeUpper → ℍ → ℂ
  | 0,M,x => if hM : 0<M.matrix.det then windowIntegralRemainder N M.matrix hM K hc R hR a b x else 0
  | n+1,M,x => (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ) *
      ∑ j : Option (ZMod p),upperWindowRemainder N p K hc R hR a b n (HeckeUpper.left p j M) x

/-- Exact returning-word main term, before taking any limit in the word degree. -/
theorem upperWindowKernel_split (N p : ℕ) [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (n : ℕ) (M : HeckeUpper)
    (hM : 0<M.matrix.det) (x : ℍ) :
    upperWindowKernel N p K hc R hR a b n M x=
      (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ)^n*(HeckeUpper.rawWalks p n M:ℂ)*
        windowIdentityContribution K hc R hR a b+
      upperWindowRemainder N p K hc R hR a b n M x := by
  classical
  induction n generalizing M with
  | zero =>
    rw [upperWindowKernel,dite_eq_left hM,windowIntegralKernel_split,upperWindowRemainder,dite_eq_left hM]
    simp only [pow_zero,one_mul,HeckeUpper.rawWalks,integralIdentityCoset_upper_iff N M hM]
    split_ifs <;> simp
  | succ n ih =>
    simp only [upperWindowKernel,upperWindowRemainder]
    simp_rw [ih _ (heckeUpper_left_det_pos p _ M hM)]
    rw [Finset.sum_add_distrib,mul_add]
    congr 1
    simp only [HeckeUpper.rawWalks,Nat.cast_sum,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring

/-- The finite nonscalar sum is continuous, hence integrable on compact sets. -/
theorem upperWindowRemainder_continuous (N p : ℕ) [NeZero N] [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (n : ℕ) (M : HeckeUpper)
    (hM : 0<M.matrix.det) :
    Continuous (upperWindowRemainder N p K hc R hR a b n M) := by
  have hh : upperWindowRemainder N p K hc R hR a b n M=(fun x =>
      upperWindowKernel N p K hc R hR a b n M x-
      (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ)^n*(HeckeUpper.rawWalks p n M:ℂ)*windowIdentityContribution K hc R hR a b) := by
    funext x
    rw [upperWindowKernel_split N p K hc R hR a b n M hM x]
    ring
  rw [hh]
  exact (upperWindowKernel_continuous N p K he hc R hR a b n M).sub continuous_const

#print axioms upperWindowKernel_split
#print axioms upperWindowRemainder_continuous

end QuantitativeMaass
