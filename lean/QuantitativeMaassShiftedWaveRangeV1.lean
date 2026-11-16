module

public import QuantitativeMaassShiftedWaveScalarV1
public import QuantitativeMaassWaveCFCV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def shiftedDampedOperator (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  cfc (p := IsSelfAdjoint) (shiftedDampedCosine t) A

theorem shiftedDampedCosine_apply_norm_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (t : ℝ) (v : H) :
    ‖cfc (shiftedDampedCosine t) A v‖ ≤ Real.cosh (|t|/2) * ‖A v‖ := by
  let C := Real.cosh (|t|/2)
  have hC : 0 ≤ C := le_of_lt (Real.cosh_pos _)
  have h := cfc_apply_norm_le_of_sq_le A hA (shiftedDampedCosine t) (fun s => C*s)
    (shiftedDampedCosine_continuous t) (continuous_const.mul continuous_id)
    (fun s _ => by
      have hs := shiftedDampedCosine_norm_le t s
      have hg : ‖C*s‖ = C*‖s‖ := by rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC]
      rw [← hg] at hs
      simpa only [Real.norm_eq_abs, sq_abs] using
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hs) v
  have hc : cfc (fun s : ℝ => C*s) A = C • A := by
    exact cfc_const_mul_id C A hA
  rw [hc, smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC] at h
  exact h

/-- Shifted wave extended from the dense range of the actual resolvent. -/
def shiftedRangeCosine (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  (cfc (p := IsSelfAdjoint) (shiftedDampedCosine t) A).toLinearMap.extendOfNorm A.toLinearMap

theorem shiftedRangeCosine_range (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) (t : ℝ) (v : H) :
    shiftedRangeCosine A t (A v) = cfc (shiftedDampedCosine t) A v := by
  exact LinearMap.extendOfNorm_eq
    (f := (cfc (p := IsSelfAdjoint) (shiftedDampedCosine t) A).toLinearMap)
    (e := A.toLinearMap) hd ⟨Real.cosh (|t|/2), shiftedDampedCosine_apply_norm_le A hA t⟩ v

theorem shiftedRangeCosine_norm_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) (t : ℝ) :
    ‖shiftedRangeCosine A t‖ ≤ Real.cosh (|t|/2) := by
  exact LinearMap.opNorm_extendOfNorm_le
    (f := (cfc (p := IsSelfAdjoint) (shiftedDampedCosine t) A).toLinearMap)
    (e := A.toLinearMap) hd (le_of_lt (Real.cosh_pos _))
    (shiftedDampedCosine_apply_norm_le A hA t)

theorem shiftedRangeCosine_zero (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) : shiftedRangeCosine A 0 = ContinuousLinearMap.id ℂ _ := by
  apply DFunLike.coe_injective
  apply hd.equalizer (shiftedRangeCosine A 0).continuous (ContinuousLinearMap.id ℂ _).continuous
  funext v
  change shiftedRangeCosine A 0 (A v) = A v
  rw [shiftedRangeCosine_range A hA hd, shiftedDampedCosine_zero, cfc_id ℝ A hA]

theorem shiftedRangeCosine_neg (A : H →L[ℂ] H) (t : ℝ) :
    shiftedRangeCosine A (-t) = shiftedRangeCosine A t := by
  unfold shiftedRangeCosine
  rw [shiftedDampedCosine_neg]

theorem shiftedRangeCosine_commute (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hd : DenseRange A) (t : ℝ) : Commute (shiftedRangeCosine A t) A := by
  apply DFunLike.coe_injective
  apply hd.equalizer ((shiftedRangeCosine A t)*A).continuous (A*(shiftedRangeCosine A t)).continuous
  funext v
  change shiftedRangeCosine A t (A (A v)) = A (shiftedRangeCosine A t (A v))
  rw [shiftedRangeCosine_range A hA hd, shiftedRangeCosine_range A hA hd]
  have h := cfc_commute_cfc (p := IsSelfAdjoint) (shiftedDampedCosine t) (id : ℝ → ℝ) A
  rw [cfc_id ℝ A hA] at h
  exact congrArg (fun B : H →L[ℂ] H => B v) h.eq

/-- Actual quotient shifted wave. Finite propagation and kernel estimates are
separate analytic obligations, not assertions hidden in this definition. -/
def shiftedQuotientWave (N : ℕ) (t : ℝ) : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  shiftedRangeCosine (friedrichsResolvent N) t

theorem shiftedQuotientWave_resolvent (N : ℕ) (t : ℝ) (v : AutomorphicSpace N) :
    shiftedQuotientWave N t (friedrichsResolvent N v) =
      shiftedDampedOperator (friedrichsResolvent N) t v :=
  shiftedRangeCosine_range _ (friedrichsResolvent_isSelfAdjoint N)
    (friedrichsResolvent_denseRange N) t v

theorem shiftedQuotientWave_commute_resolvent (N : ℕ) (t : ℝ) :
    Commute (shiftedQuotientWave N t) (friedrichsResolvent N) :=
  shiftedRangeCosine_commute _ (friedrichsResolvent_isSelfAdjoint N)
    (friedrichsResolvent_denseRange N) t

theorem shiftedQuotientWave_norm_le (N : ℕ) (t : ℝ) :
    ‖shiftedQuotientWave N t‖ ≤ Real.cosh (|t|/2) :=
  shiftedRangeCosine_norm_le _ (friedrichsResolvent_isSelfAdjoint N)
    (friedrichsResolvent_denseRange N) t

theorem shiftedQuotientWave_zero (N : ℕ) :
    shiftedQuotientWave N 0 = ContinuousLinearMap.id ℂ _ :=
  shiftedRangeCosine_zero _ (friedrichsResolvent_isSelfAdjoint N)
    (friedrichsResolvent_denseRange N)

#print axioms shiftedRangeCosine_range
#print axioms shiftedRangeCosine_commute
#print axioms shiftedQuotientWave_norm_le
#print axioms shiftedQuotientWave_zero

end QuantitativeMaass.Wave
