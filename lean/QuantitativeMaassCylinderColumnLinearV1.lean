module

public import QuantitativeMaassPhysicalAbelLinearV1
public import QuantitativeMaassPhysicalProfileExtensionV1
public import QuantitativeMaassCylinderColumnDomainV1
public import QuantitativeMaassPoincareGraphLinearV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/- Min-owned draft: not compiler-verified when written. -/

/-- Actual cylinder Abel columns are linear in the physical profile.
The three profiles need agree only on the physical half-line. -/
theorem cylinderAbelColumn_linear_physical (F G H : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (hG : ContDiffOn ℝ ∞ G (Ici 1))
    (hH : ContDiffOn ℝ ∞ H (Ici 1))
    (R : ℝ) (hR : 0 ≤ R)
    (hsF : Function.support F ⊆ Iic (Real.cosh R))
    (hsG : Function.support G ⊆ Iic (Real.cosh R))
    (hsH : Function.support H ⊆ Iic (Real.cosh R))
    (a b : ℂ) (hlin : ∀ q ∈ Ici (1 : ℝ), H q = a*F q+b*G q) (z : ℍ) :
    cylinderAutomorphic (cylinderAbelColumn H hH R hR hsH z) =
      a • cylinderAutomorphic (cylinderAbelColumn F hF R hR hsF z) +
        b • cylinderAutomorphic (cylinderAbelColumn G hG R hR hsG z) := by
  simp only [cylinderAbelColumn_eq_physicalRadialSeed]
  rw [← poincareSeedVector_smul, ← poincareSeedVector_smul, ← poincareSeedVector_add]
  apply poincareSeedVector_congr
  funext w
  change upperFunction (radialFunction (abelProfile H) z) w =
    a * upperFunction (radialFunction (abelProfile F) z) w +
      b * upperFunction (radialFunction (abelProfile G) z) w
  rw [radialFunction_upper, radialFunction_upper, radialFunction_upper]
  rw [abelProfile_congr_above_threshold H (fun q => a*F q+b*G q) 1
    (fun q hq => hlin q hq.le) _ (Real.one_le_cosh _)]
  exact abelProfile_linear_physical F G hF hG (Real.cosh R)
    (Real.one_le_cosh R) hsF hsG a b _ (Real.one_le_cosh _)

/-- Linearity for the literal compact even Schwartz time columns, all
represented with the same propagation radius. -/
theorem cylinderTimeColumn_linear (f g h : SchwartzMap ℝ ℂ)
    (hfc : HasCompactSupport (f : ℝ → ℂ))
    (hgc : HasCompactSupport (g : ℝ → ℂ))
    (hhc : HasCompactSupport (h : ℝ → ℂ))
    (hfe : Function.Even f) (hge : Function.Even g) (hhe : Function.Even h)
    (R : ℝ) (hR : 0 ≤ R)
    (hsf : Function.support f ⊆ Icc (-R) R)
    (hsg : Function.support g ⊆ Icc (-R) R)
    (hsh : Function.support h ⊆ Icc (-R) R)
    (a b : ℂ) (hlin : h = a • f + b • g) (z : ℍ) :
    cylinderAutomorphic (cylinderTimeColumn h hhc hhe R hR hsh z) =
      a • cylinderAutomorphic (cylinderTimeColumn f hfc hfe R hR hsf z) +
        b • cylinderAutomorphic (cylinderTimeColumn g hgc hge R hR hsg z) := by
  refine cylinderAbelColumn_linear_physical (evenCoshLift f) (evenCoshLift g) (evenCoshLift h)
    (evenCoshLift_smoothOn f (f.smooth ⊤) hfe hfc)
    (evenCoshLift_smoothOn g (g.smooth ⊤) hge hgc)
    (evenCoshLift_smoothOn h (h.smooth ⊤) hhe hhc) R hR
    (evenCoshLift_support_of_time_support f R hR hsf)
    (evenCoshLift_support_of_time_support g R hR hsg)
    (evenCoshLift_support_of_time_support h R hR hsh) a b ?_ z
  intro q _
  unfold evenCoshLift
  rw [hlin]
  rfl

#print axioms cylinderAbelColumn_linear_physical
#print axioms cylinderTimeColumn_linear

end QuantitativeMaass
