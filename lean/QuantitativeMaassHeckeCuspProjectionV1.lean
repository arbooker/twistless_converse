module

public import QuantitativeNinaMaassHeckeOperatorsV1
public import QuantitativeMaassLVCuspidalProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson
open scoped InnerProductSpace

namespace QuantitativeMaass

/-- Every actual unramified Hecke operator commutes with the closed cusp
projection, using the proved preservation theorem at all good primes. -/
theorem hecke_localCuspidalProjection_commute (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1) :
    Commute (HeckeL2.operator N p hN hpN A B hAB) (localCuspidalProjection N hN) := by
  let T := HeckeL2.operator N p hN hpN A B hAB
  have hT : T.toLinearMap.IsSymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (HeckeL2.operator_selfAdjoint N p hN hpN A B hAB)
  have hpres (v : AutomorphicSpace N) (hv : v∈localCuspidalSpace N hN) :
      T v∈localCuspidalSpace N hN :=
    QuantitativeNinaMaass.hecke_mem_cuspidal_all_good_primes N p hN hpN A B hAB v hv
  apply ContinuousLinearMap.ext
  intro v
  change T ((localCuspidalSpace N hN).starProjection v)=
    (localCuspidalSpace N hN).starProjection (T v)
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hpres _ ((localCuspidalSpace N hN).starProjection_apply_mem v))
  intro w hw
  rw [←map_sub]
  have hh := hT (v-(localCuspidalSpace N hN).starProjection v) w
  change inner ℂ (T (v-(localCuspidalSpace N hN).starProjection v)) w=
    inner ℂ (v-(localCuspidalSpace N hN).starProjection v) (T w) at hh
  rw [hh]
  exact (localCuspidalSpace N hN).starProjection_inner_eq_zero v (T w) (hpres w hw)

/-- The actual cusp projection can be dropped in an upper bound for a
Hecke-power column energy. No band or spectral decomposition is assumed. -/
theorem hecke_power_cusp_projection_norm_le (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1)
    (d : ℕ) (v : AutomorphicSpace N) :
    ‖((HeckeL2.operator N p hN hpN A B hAB)^d) (localCuspidalProjection N hN v)‖≤
      ‖((HeckeL2.operator N p hN hpN A B hAB)^d) v‖ := by
  have hcomm := (hecke_localCuspidalProjection_commute N p hN hpN A B hAB).pow_left d
  have hh := congrArg (fun U : AutomorphicSpace N →L[ℂ] AutomorphicSpace N => U v) hcomm.eq
  change ((HeckeL2.operator N p hN hpN A B hAB)^d) (localCuspidalProjection N hN v)=
    localCuspidalProjection N hN (((HeckeL2.operator N p hN hpN A B hAB)^d) v) at hh
  rw [hh]
  exact (localCuspidalSpace N hN).norm_starProjection_apply_le _

#print axioms hecke_localCuspidalProjection_commute
#print axioms hecke_power_cusp_projection_norm_le

end QuantitativeMaass
