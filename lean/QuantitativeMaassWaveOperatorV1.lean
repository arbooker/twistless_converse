module

public import QuantitativeMaassWaveRangeV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

/-- The actual unshifted quotient family `cos(t√Δ_F)`, constructed by
continuous extension from the actual Friedrichs resolvent range. -/
def quotientWave (N : ℕ) (t : ℝ) : AutomorphicSpace N →L[ℂ] AutomorphicSpace N :=
  rangeCosine (friedrichsResolvent N) t

theorem quotientWave_resolvent (N : ℕ) (t : ℝ) (v : AutomorphicSpace N) :
    quotientWave N t (friedrichsResolvent N v)=dampedOperator (friedrichsResolvent N) t v :=
  rangeCosine_range _ (friedrichsResolvent_isSelfAdjoint N) (friedrichsResolvent_denseRange N) t v

theorem quotientWave_norm_le (N : ℕ) (t : ℝ) : ‖quotientWave N t‖≤1 :=
  rangeCosine_norm_le _ (friedrichsResolvent_isSelfAdjoint N) (friedrichsResolvent_denseRange N) t

theorem quotientWave_apply_norm_le (N : ℕ) (t : ℝ) (v : AutomorphicSpace N) :
    ‖quotientWave N t v‖≤‖v‖ :=
  rangeCosine_apply_norm_le _ (friedrichsResolvent_isSelfAdjoint N) (friedrichsResolvent_denseRange N) t v

theorem quotientWave_zero (N : ℕ) : quotientWave N 0=ContinuousLinearMap.id ℂ _ :=
  rangeCosine_zero _ (friedrichsResolvent_isSelfAdjoint N) (friedrichsResolvent_denseRange N)

theorem quotientWave_neg (N : ℕ) (t : ℝ) : quotientWave N (-t)=quotientWave N t :=
  rangeCosine_neg _ t

theorem quotientWave_commute_resolvent (N : ℕ) (t : ℝ) :
    Commute (quotientWave N t) (friedrichsResolvent N) :=
  rangeCosine_commute _ (friedrichsResolvent_isSelfAdjoint N) (friedrichsResolvent_denseRange N) t

#print axioms quotientWave_resolvent
#print axioms quotientWave_norm_le
#print axioms quotientWave_zero
#print axioms quotientWave_commute_resolvent

end QuantitativeMaass.Wave
