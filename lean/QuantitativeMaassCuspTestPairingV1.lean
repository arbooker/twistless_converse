module

public import QuantitativeMaassCuspTestSeedV1
public import QuantitativeMaassLocalTestPairingV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups InnerProductSpace

namespace QuantitativeMaass

theorem cuspPullback_localSeed (s : SL(2,ℤ)) (K : Set ℍ) (hK : IsCompact K) (u : SmoothUpperSeed) :
    Lp.compMeasurePreserving (cuspAction s) (cuspAction_restricted_preserving s K hK)
      (localSeedVector (cuspAction s '' K) (u.cuspPush s))=localSeedVector K u := by
  apply Lp.ext
  have hp := (cuspAction_restricted_preserving s K hK).quasiMeasurePreserving.ae
    (localSeedMemLp (cuspAction s '' K) (u.cuspPush s)).coeFn_toLp
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (localSeedVector (cuspAction s '' K) (u.cuspPush s))
    (cuspAction_restricted_preserving s K hK),hp,(localSeedMemLp K u).coeFn_toLp] with Z hc hp hu
  rw [hc]
  change (localSeedMemLp (cuspAction s '' K) (u.cuspPush s)).toLp
    (upperFunction (u.cuspPush s).toFun) (cuspAction s Z)=
      (localSeedMemLp K u).toLp (upperFunction u.toFun) Z
  rw [hp,hu,cuspPush_upper]

/-- Compact tests in any integral cusp chart pair with the actual transported
Poincare seed. Both sides are defined for every quotient L2 vector. -/
theorem cuspRestriction_pairing (N : ℕ) (s : SL(2,ℤ)) (K : Set ℍ) (hK : IsCompact K)
    (u : SmoothUpperSeed) (hs : tsupport (upperFunction u.toFun)⊆K) (f : AutomorphicSpace N) :
    inner ℂ (localSeedVector K u) (cuspRestriction N s K hK f)=
      inner ℂ (poincareSeedVector N (u.cuspPush s)) f := by
  let e : Lp ℂ 2 (volume.restrict (cuspAction s '' K)) →ₗᵢ[ℂ] Lp ℂ 2 (volume.restrict K) :=
    Lp.compMeasurePreservingₗᵢ ℂ (cuspAction s) (cuspAction_restricted_preserving s K hK)
  have hu : e (localSeedVector (cuspAction s '' K) (u.cuspPush s))=localSeedVector K u :=
    cuspPullback_localSeed s K hK u
  change inner ℂ (localSeedVector K u)
    (e (quotientRestriction N (cuspAction s '' K) (hK.image (cuspAction_continuous s))
      (hK.image (cuspAction_continuous s)).measurableSet f))=_
  rw [← hu,e.inner_map_map]
  exact quotientRestriction_pairing N _ (hK.image (cuspAction_continuous s))
    (hK.image (cuspAction_continuous s)).measurableSet (u.cuspPush s)
    (cuspPush_support s u K hK hs) f

theorem localSeedVector_inner_integral (K : Set ℍ) (u : SmoothUpperSeed)
    (f : Lp ℂ 2 (volume.restrict K)) :
    inner ℂ (localSeedVector K u) f=∫ Z in K, star (upperFunction u.toFun Z)*f Z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(localSeedMemLp K u).coeFn_toLp] with Z hu
  change inner ℂ ((localSeedMemLp K u).toLp (upperFunction u.toFun) Z) (f Z)=_
  rw [hu]
  simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]

#print axioms cuspRestriction_pairing

end QuantitativeMaass
