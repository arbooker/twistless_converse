module

public import QuantitativeMaassLocalRestrictionV1
public import QuantitativeMaassCuspPeriodV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups

namespace QuantitativeMaass

def cuspAction (s : SL(2,ℤ)) (Z : ℍ) : ℍ := (SpecialLinearGroup.mapGL ℝ s) • Z

theorem cuspAction_continuous (s : SL(2,ℤ)) : Continuous (cuspAction s) :=
  continuous_const_smul _

theorem cuspAction_injective (s : SL(2,ℤ)) : Function.Injective (cuspAction s) := by
  intro Z W h
  have he := congrArg (fun V : ℍ => (SpecialLinearGroup.mapGL ℝ s)⁻¹ • V) h
  simpa only [cuspAction,inv_smul_smul] using he

theorem cuspAction_restricted_preserving (s : SL(2,ℤ)) (K : Set ℍ) (hK : IsCompact K) :
    MeasurePreserving (cuspAction s) (volume.restrict K)
      (volume.restrict (cuspAction s '' K)) := by
  have hm : MeasurePreserving (cuspAction s) volume volume :=
    measurePreserving_smul (SpecialLinearGroup.mapGL ℝ s) (volume : Measure ℍ)
  have h := hm.restrict_preimage (hK.image (cuspAction_continuous s)).measurableSet
  simpa only [Set.preimage_image_eq K (cuspAction_injective s)] using h

/-- Actual bounded pullback of a quotient L2 vector to a compact region in
any integral cusp chart. The change of chart preserves hyperbolic volume. -/
def cuspRestriction (N : ℕ) (s : SL(2,ℤ)) (K : Set ℍ) (hK : IsCompact K) :
    AutomorphicSpace N →L[ℂ] Lp ℂ 2 (volume.restrict K) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (cuspAction s) (cuspAction_restricted_preserving s K hK)).toContinuousLinearMap.comp
    (quotientRestriction N (cuspAction s '' K) (hK.image (cuspAction_continuous s))
      (hK.image (cuspAction_continuous s)).measurableSet)

theorem cuspRestriction_representative_ae (N : ℕ) (s : SL(2,ℤ)) (K : Set ℍ)
    (hK : IsCompact K) (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    (cuspRestriction N s K hK
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f) : ℍ → ℂ)=ᵐ[volume.restrict K]
        fun Z => f.val (cuspAction s Z) := by
  have hR := quotientRestriction_representative_ae N (cuspAction s '' K)
    (hK.image (cuspAction_continuous s)) (hK.image (cuspAction_continuous s)).measurableSet f
  have hp := (cuspAction_restricted_preserving s K hK).quasiMeasurePreserving.ae hR
  have hc := Lp.coeFn_compMeasurePreserving
    (quotientRestriction N (cuspAction s '' K) (hK.image (cuspAction_continuous s))
      (hK.image (cuspAction_continuous s)).measurableSet
      (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f))
    (cuspAction_restricted_preserving s K hK)
  filter_upwards [hc,hp] with Z hZ hf
  exact hZ.trans hf

#print axioms cuspRestriction
#print axioms cuspRestriction_representative_ae

end QuantitativeMaass
