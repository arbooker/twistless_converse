module

public import QuantitativeMaassHeckeWordHeightV1
public import QuantitativeMaassTranslatedCorrespondenceUniformV1
public import QuantitativeMaassMixedHeckeTraceV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip
open scoped Topology FourierTransform SchwartzMap ENNReal

namespace QuantitativeMaass

/-- The literal nonscalar part of the finite Hecke correspondence sum. -/
def upperTranslatedWindowRemainder (τ : ℝ) (N p : ℕ) [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) : ℕ → HeckeUpper → ℍ → ℂ
  | 0,M,x => if hM : 0<M.matrix.det then translatedWindowIntegralRemainder τ N M.matrix hM K hc R hR a b x else 0
  | n+1,M,x => (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ) *
      ∑ j : Option (ZMod p),upperTranslatedWindowRemainder τ N p K hc R hR a b n (HeckeUpper.left p j M) x

/-- Exact returning-word main term, before taking any limit in the word degree. -/
theorem upperTranslatedWindowKernel_split (τ : ℝ) (N p : ℕ) [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (n : ℕ) (M : HeckeUpper)
    (hM : 0<M.matrix.det) (x : ℍ) :
    upperTranslatedWindowKernel τ N p K hc R hR a b n M x=
      (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ)^n*(HeckeUpper.rawWalks p n M:ℂ)*
        translatedWindowIdentity τ K hc R hR a b+
      upperTranslatedWindowRemainder τ N p K hc R hR a b n M x := by
  classical
  induction n generalizing M with
  | zero =>
    rw [upperTranslatedWindowKernel,dite_eq_left hM,translatedWindowIntegralKernel_split,upperTranslatedWindowRemainder,dite_eq_left hM]
    simp only [pow_zero,one_mul,HeckeUpper.rawWalks,integralIdentityCoset_upper_iff N M hM]
    split_ifs <;> simp
  | succ n ih =>
    simp only [upperTranslatedWindowKernel,upperTranslatedWindowRemainder]
    simp_rw [ih _ (heckeUpper_left_det_pos p _ M hM)]
    rw [Finset.sum_add_distrib,mul_add]
    congr 1
    simp only [HeckeUpper.rawWalks,Nat.cast_sum,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring

/-- The finite nonscalar sum is continuous, hence integrable on compact sets. -/
theorem upperTranslatedWindowRemainder_continuous (τ : ℝ) (N p : ℕ) [NeZero N] [Fact p.Prime]
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (n : ℕ) (M : HeckeUpper)
    (hM : 0<M.matrix.det) :
    Continuous (upperTranslatedWindowRemainder τ N p K hc R hR a b n M) := by
  have hh : upperTranslatedWindowRemainder τ N p K hc R hR a b n M=(fun x =>
      upperTranslatedWindowKernel τ N p K hc R hR a b n M x-
      (((Real.sqrt (p:ℝ))⁻¹:ℝ):ℂ)^n*(HeckeUpper.rawWalks p n M:ℂ)*translatedWindowIdentity τ K hc R hR a b) := by
    funext x
    rw [upperTranslatedWindowKernel_split τ N p K hc R hR a b n M hM x]
    ring
  rw [hh]
  exact (upperTranslatedWindowKernel_continuous τ N p K he hc R hR a b n M).sub continuous_const

#print axioms upperTranslatedWindowKernel_split
#print axioms upperTranslatedWindowRemainder_continuous

end QuantitativeMaass
