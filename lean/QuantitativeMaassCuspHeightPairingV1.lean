module

public import QuantitativeMaassCuspConstantOperatorV1
public import QuantitativeMaassCuspTestPairingV1

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups InnerProductSpace

namespace QuantitativeMaass

/-- Exact height-test pairing on continuous or measurable invariant
representatives; continuity is not needed for this integral identity. -/
theorem cuspHeightAverage_test_representative (N : ℕ) (s : SL(2,ℤ))
    (K : Set ℍ) (hK : IsCompact K) (g : ℝ → ℂ) (hg : Continuous g)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    inner ℂ (heightTestVector K hK g hg)
      (cuspHeightAverage N s K hK (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f))=
      ∫ Z in K, star (g Z.im)*f.val (cuspAction s Z) := by
  change inner ℂ (heightTestVector K hK g hg) (localHeightAverage K
    (cuspRestriction N s K hK (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)))=_
  rw [localHeightAverage_test]
  apply integral_congr_ae
  filter_upwards [cuspRestriction_representative_ae N s K hK f] with Z hZ
  rw [hZ]

/-- Compact test pairing with the actual representative in a cusp chart. -/
theorem cuspSeed_test_representative (N : ℕ) (s : SL(2,ℤ))
    (K : Set ℍ) (hK : IsCompact K) (u : SmoothUpperSeed)
    (hs : tsupport (upperFunction u.toFun)⊆K)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    inner ℂ (poincareSeedVector N (u.cuspPush s))
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)=
      ∫ Z in K, star (upperFunction u.toFun Z)*f.val (cuspAction s Z) := by
  rw [← cuspRestriction_pairing N s K hK u hs,localSeedVector_inner_integral]
  apply integral_congr_ae
  filter_upwards [cuspRestriction_representative_ae N s K hK f] with Z hZ
  rw [hZ]

/-- Density transfers a literal continuous-representative test identity to
all quotient L2 states. Both sides are already constructed bounded pairings. -/
theorem cuspSeed_height_pairing_of_integrals (N : ℕ) (s : SL(2,ℤ))
    (K L : Set ℍ) (hK : IsCompact K) (hL : IsCompact L)
    (u : SmoothUpperSeed) (hs : tsupport (upperFunction u.toFun)⊆K)
    (g : ℝ → ℂ) (hg : Continuous g)
    (hi : ∀ f : AutomorphicL2.representatives (gamma N) (quotientMeasure N), Continuous f.val →
      (∫ Z in K, star (upperFunction u.toFun Z)*f.val (cuspAction s Z))=
        ∫ Z in L, star (g Z.im)*f.val (cuspAction s Z))
    (f : AutomorphicSpace N) :
    inner ℂ (poincareSeedVector N (u.cuspPush s)) f=
      inner ℂ (heightTestVector L hL g hg) (cuspHeightAverage N s L hL f) := by
  have he : (fun f : AutomorphicSpace N => inner ℂ (poincareSeedVector N (u.cuspPush s)) f)=
      fun f => inner ℂ (heightTestVector L hL g hg) (cuspHeightAverage N s L hL f) := by
    apply (poincareSeedVector_dense N).equalizer (by fun_prop) (by fun_prop)
    funext v
    dsimp only [Function.comp_apply]
    let vf : AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
      ⟨_,poincareSeed_representative N v⟩
    change inner ℂ (poincareSeedVector N (u.cuspPush s))
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) vf)=
        inner ℂ (heightTestVector L hL g hg) (cuspHeightAverage N s L hL
          (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) vf))
    rw [cuspSeed_test_representative N s K hK u hs vf,
      cuspHeightAverage_test_representative N s L hL g hg vf]
    apply hi vf
    let : ContinuousConstSMul (gamma N) ℍ :=
      ⟨fun γ => AsymptoticRationalBranches.action_continuous γ.val⟩
    exact poincareSum_continuous (G := gamma N) _ v.compact (upperFunction_continuous v.smooth)
  exact congrFun he f

#print axioms cuspHeightAverage_test_representative
#print axioms cuspSeed_height_pairing_of_integrals

end QuantitativeMaass
