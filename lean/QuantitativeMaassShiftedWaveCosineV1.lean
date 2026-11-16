module

public import QuantitativeMaassShiftedWaveRangeV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

open Set
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

theorem signedCosine_add_sub (t u x : ℝ) :
    signedCosine (t+u) x + signedCosine (t-u) x =
      signedCosine t x * signedCosine u x + signedCosine t x * signedCosine u x := by
  rcases le_total 0 x with hx | hx
  · simp only [signedCosine_nonneg_energy _ _ hx, add_mul, sub_mul,
      Real.cos_add, Real.cos_sub]
    ring
  · simp only [signedCosine_nonpos_energy _ _ hx, add_mul, sub_mul,
      Real.cosh_add, Real.cosh_sub]
    ring

theorem shiftedDampedCosine_add_sub (t u s : ℝ) :
    (shiftedDampedCosine (t+u) s+shiftedDampedCosine (t-u) s)*s =
      shiftedDampedCosine t s*shiftedDampedCosine u s+
        shiftedDampedCosine t s*shiftedDampedCosine u s := by
  unfold shiftedDampedCosine
  have h := signedCosine_add_sub t u (max (s⁻¹-1) 0-1/4)
  calc
    _ = s^2 * (signedCosine (t+u) (max (s⁻¹-1) 0-1/4) +
      signedCosine (t-u) (max (s⁻¹-1) 0-1/4)) := by ring
    _ = _ := by rw [h]; ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cfc_shiftedDampedCosine_add_sub (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t u : ℝ) :
    (shiftedDampedOperator A (t+u)+
      shiftedDampedOperator A (t-u))*A=
    shiftedDampedOperator A t*shiftedDampedOperator A u+
      shiftedDampedOperator A t*shiftedDampedOperator A u := by
  unfold shiftedDampedOperator
  have h := congrArg (fun f : ℝ → ℝ => cfc (p := IsSelfAdjoint) f A)
    (funext (shiftedDampedCosine_add_sub t u))
  rw [cfc_mul (fun s => shiftedDampedCosine (t+u) s+shiftedDampedCosine (t-u) s)
      (fun s : ℝ => s) A ((shiftedDampedCosine_continuous _).add
        (shiftedDampedCosine_continuous _)).continuousOn continuous_id.continuousOn,
    cfc_id' ℝ A hA,
    cfc_add (a := A) (shiftedDampedCosine (t+u)) (shiftedDampedCosine (t-u))
      (shiftedDampedCosine_continuous _).continuousOn (shiftedDampedCosine_continuous _).continuousOn,
    cfc_add (a := A) (fun s => shiftedDampedCosine t s*shiftedDampedCosine u s)
      (fun s => shiftedDampedCosine t s*shiftedDampedCosine u s)
      ((shiftedDampedCosine_continuous _).mul (shiftedDampedCosine_continuous _)).continuousOn
      ((shiftedDampedCosine_continuous _).mul (shiftedDampedCosine_continuous _)).continuousOn,
    cfc_mul (shiftedDampedCosine t) (shiftedDampedCosine u) A
      (shiftedDampedCosine_continuous _).continuousOn (shiftedDampedCosine_continuous _).continuousOn] at h
  exact h

/-- The actual shifted quotient operators satisfy the cosine functional equation
on the entire quotient Hilbert space. -/
theorem shiftedQuotientWave_cosine (N : ℕ) (t u : ℝ) :
    shiftedQuotientWave N (t+u)+shiftedQuotientWave N (t-u)=
      shiftedQuotientWave N t*shiftedQuotientWave N u+shiftedQuotientWave N t*shiftedQuotientWave N u := by
  apply DFunLike.coe_injective
  have hd := (friedrichsResolvent_denseRange N).comp (friedrichsResolvent_denseRange N)
    (friedrichsResolvent N).continuous
  apply hd.equalizer ((shiftedQuotientWave N (t+u)+shiftedQuotientWave N (t-u))).continuous
    ((shiftedQuotientWave N t*shiftedQuotientWave N u+shiftedQuotientWave N t*shiftedQuotientWave N u)).continuous
  funext v
  change shiftedQuotientWave N (t+u) (friedrichsResolvent N (friedrichsResolvent N v))+
    shiftedQuotientWave N (t-u) (friedrichsResolvent N (friedrichsResolvent N v))=
    shiftedQuotientWave N t (shiftedQuotientWave N u (friedrichsResolvent N (friedrichsResolvent N v)))+
    shiftedQuotientWave N t (shiftedQuotientWave N u (friedrichsResolvent N (friedrichsResolvent N v)))
  have hc := congrArg (fun A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N =>
    A (friedrichsResolvent N v)) (shiftedQuotientWave_commute_resolvent N u).eq
  change shiftedQuotientWave N u (friedrichsResolvent N (friedrichsResolvent N v))=
    friedrichsResolvent N (shiftedQuotientWave N u (friedrichsResolvent N v)) at hc
  rw [hc]
  simp only [shiftedQuotientWave_resolvent]
  exact congrArg (fun A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => A v)
    (cfc_shiftedDampedCosine_add_sub (friedrichsResolvent N) (friedrichsResolvent_isSelfAdjoint N) t u)

#print axioms shiftedQuotientWave_cosine

end QuantitativeMaass.Wave
