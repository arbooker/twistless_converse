module

public import QuantitativeMaassWaveOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 300000
@[expose] public noncomputable section

open Set
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

theorem dampedCosine_add_sub (t u s : ℝ) :
    (dampedCosine (t+u) s+dampedCosine (t-u) s)*s=
      dampedCosine t s*dampedCosine u s+dampedCosine t s*dampedCosine u s := by
  simp only [dampedCosine,add_mul,sub_mul,Real.cos_add,Real.cos_sub]
  ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cfc_dampedCosine_add_sub (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t u : ℝ) :
    (dampedOperator A (t+u)+
      dampedOperator A (t-u))*A=
    dampedOperator A t*dampedOperator A u+
      dampedOperator A t*dampedOperator A u := by
  unfold dampedOperator
  have h := congrArg (fun f : ℝ → ℝ => cfc (p := IsSelfAdjoint) f A)
    (funext (dampedCosine_add_sub t u))
  rw [cfc_mul (fun s => dampedCosine (t+u) s+dampedCosine (t-u) s)
      (fun s : ℝ => s) A ((dampedCosine_continuous _).add
        (dampedCosine_continuous _)).continuousOn continuous_id.continuousOn,
    cfc_id' ℝ A hA,
    cfc_add (a := A) (dampedCosine (t+u)) (dampedCosine (t-u))
      (dampedCosine_continuous _).continuousOn (dampedCosine_continuous _).continuousOn,
    cfc_add (a := A) (fun s => dampedCosine t s*dampedCosine u s)
      (fun s => dampedCosine t s*dampedCosine u s)
      ((dampedCosine_continuous _).mul (dampedCosine_continuous _)).continuousOn
      ((dampedCosine_continuous _).mul (dampedCosine_continuous _)).continuousOn,
    cfc_mul (dampedCosine t) (dampedCosine u) A
      (dampedCosine_continuous _).continuousOn (dampedCosine_continuous _).continuousOn] at h
  exact h

/-- The actual quotient contractions satisfy the cosine functional equation
on the entire quotient Hilbert space. -/
theorem quotientWave_cosine (N : ℕ) (t u : ℝ) :
    quotientWave N (t+u)+quotientWave N (t-u)=
      quotientWave N t*quotientWave N u+quotientWave N t*quotientWave N u := by
  apply DFunLike.coe_injective
  have hd := (friedrichsResolvent_denseRange N).comp (friedrichsResolvent_denseRange N)
    (friedrichsResolvent N).continuous
  apply hd.equalizer ((quotientWave N (t+u)+quotientWave N (t-u))).continuous
    ((quotientWave N t*quotientWave N u+quotientWave N t*quotientWave N u)).continuous
  funext v
  change quotientWave N (t+u) (friedrichsResolvent N (friedrichsResolvent N v))+
    quotientWave N (t-u) (friedrichsResolvent N (friedrichsResolvent N v))=
    quotientWave N t (quotientWave N u (friedrichsResolvent N (friedrichsResolvent N v)))+
    quotientWave N t (quotientWave N u (friedrichsResolvent N (friedrichsResolvent N v)))
  have hc := congrArg (fun A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N =>
    A (friedrichsResolvent N v)) (quotientWave_commute_resolvent N u).eq
  change quotientWave N u (friedrichsResolvent N (friedrichsResolvent N v))=
    friedrichsResolvent N (quotientWave N u (friedrichsResolvent N v)) at hc
  rw [hc]
  simp only [quotientWave_resolvent]
  exact congrArg (fun A : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => A v)
    (cfc_dampedCosine_add_sub (friedrichsResolvent N) (friedrichsResolvent_isSelfAdjoint N) t u)

#print axioms quotientWave_cosine

end QuantitativeMaass.Wave
