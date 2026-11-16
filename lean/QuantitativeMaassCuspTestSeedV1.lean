module

public import QuantitativeMaassCuspRestrictionV1
public import QuantitativeMaassCuspChartCovarianceV1
public import QuantitativeMaassPoincareGraphLinearV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups

namespace QuantitativeMaass

theorem cuspAction_inv_apply (s : SL(2,ℤ)) (Z : ℍ) :
    cuspAction s⁻¹ (cuspAction s Z)=Z := by
  simp [cuspAction,map_inv]

theorem cuspAction_apply_inv (s : SL(2,ℤ)) (Z : ℍ) :
    cuspAction s (cuspAction s⁻¹ Z)=Z := by
  simpa only [inv_inv] using cuspAction_inv_apply s⁻¹ Z

theorem upperFunction_cuspChart (s : SL(2,ℤ)) (u : MaassDifferential.Point → ℂ) (Z : ℍ) :
    upperFunction (u ∘ integralCuspChart s) Z=upperFunction u (cuspAction s Z) := by
  change u (integralCuspChart s (Z.re,Z.im))=u ((cuspAction s Z).re,(cuspAction s Z).im)
  rw [integralCuspChart_action s Z.re Z.im Z.im_pos]
  rfl

theorem cuspPush_support (s : SL(2,ℤ)) (u : SmoothUpperSeed)
    (K : Set ℍ) (hK : IsCompact K) (hs : tsupport (upperFunction u.toFun)⊆K) :
    tsupport (upperFunction (u.toFun ∘ integralCuspChart s⁻¹))⊆cuspAction s '' K := by
  apply closure_minimal
  · intro Z hZ
    refine ⟨cuspAction s⁻¹ Z,hs (subset_closure ?_),cuspAction_apply_inv s Z⟩
    change upperFunction u.toFun (cuspAction s⁻¹ Z)≠0
    rwa [← upperFunction_cuspChart]
  · exact (hK.image (cuspAction_continuous s)).isClosed

/-- Transport a genuine compact smooth test seed from an integral cusp chart
to the upper half-plane. -/
def SmoothUpperSeed.cuspPush (u : SmoothUpperSeed) (s : SL(2,ℤ)) : SmoothUpperSeed where
  toFun := u.toFun ∘ integralCuspChart s⁻¹
  smooth := integralCuspChart_pullback_smooth s⁻¹ u.smooth
  compact := (u.compact.image (cuspAction_continuous s)).of_isClosed_subset isClosed_closure
    (cuspPush_support s u _ u.compact subset_rfl)

theorem cuspPush_upper (u : SmoothUpperSeed) (s : SL(2,ℤ)) (Z : ℍ) :
    upperFunction (u.cuspPush s).toFun (cuspAction s Z)=upperFunction u.toFun Z := by
  change upperFunction (u.toFun ∘ integralCuspChart s⁻¹) (cuspAction s Z)=_
  rw [upperFunction_cuspChart,cuspAction_inv_apply]

/-- Transport of compact cusp tests commutes with the actual differential
Laplacian after passing to the Poincare vector. -/
theorem poincare_cuspPush_laplacian (N : ℕ) (u : SmoothUpperSeed) (s : SL(2,ℤ)) :
    poincareSeedVector N (u.cuspPush s).laplacian=
      poincareSeedVector N (u.laplacian.cuspPush s) := by
  apply poincareSeedVector_congr
  funext Z
  exact hyperbolic_integralCuspChart s⁻¹ u.smooth Z.re Z.im Z.im_pos

#print axioms SmoothUpperSeed.cuspPush
#print axioms poincare_cuspPush_laplacian

end QuantitativeMaass
