module

public import QuantitativeMaassCuspTestPairingV1
public import QuantitativeMaassWaveWeakEquationV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups InnerProductSpace

namespace QuantitativeMaass.Wave

/-- The actual quotient wave obeys the weak differential equation in every
integral cusp chart, for arbitrary quotient L2 initial data. -/
theorem cusp_weakWave_equation (N : ℕ) (s : SL(2,ℤ)) (K : Set ℍ) (hK : IsCompact K)
    (u : SmoothUpperSeed) (hs : tsupport (upperFunction u.toFun)⊆K)
    (f : AutomorphicSpace N) (t : ℝ) :
    deriv (deriv (fun r => inner ℂ (localSeedVector K u)
      (cuspRestriction N s K hK (shiftedQuotientWave N r f)))) t=
      (1/4 : ℂ)*inner ℂ (localSeedVector K u)
        (cuspRestriction N s K hK (shiftedQuotientWave N t f))-
      inner ℂ (localSeedVector K u.laplacian)
        (cuspRestriction N s K hK (shiftedQuotientWave N t f)) := by
  have hsL : tsupport (upperFunction u.laplacian.toFun)⊆K :=
    closure_minimal ((upperLaplacian_support u.toFun).trans hs) hK.isClosed
  have he : (fun r => inner ℂ (localSeedVector K u)
      (cuspRestriction N s K hK (shiftedQuotientWave N r f)))=
      fun r => inner ℂ (poincareSeedVector N (u.cuspPush s)) (shiftedQuotientWave N r f) :=
    funext (fun r => cuspRestriction_pairing N s K hK u hs _)
  rw [he,cuspRestriction_pairing N s K hK u hs,
    cuspRestriction_pairing N s K hK u.laplacian hsL]
  rw [poincare_weakWave_equation,poincare_cuspPush_laplacian]

/-- The same all-cusp weak PDE in literal compact-region integral form. -/
theorem cusp_local_wave_equation (N : ℕ) (s : SL(2,ℤ)) (K : Set ℍ) (hK : IsCompact K)
    (u : SmoothUpperSeed) (hs : tsupport (upperFunction u.toFun)⊆K)
    (f : AutomorphicSpace N) (t : ℝ) :
    deriv (deriv (fun r => ∫ Z in K, star (upperFunction u.toFun Z)*
      (cuspRestriction N s K hK (shiftedQuotientWave N r f)) Z)) t=
      (1/4 : ℂ)*(∫ Z in K, star (upperFunction u.toFun Z)*
        (cuspRestriction N s K hK (shiftedQuotientWave N t f)) Z)-
      ∫ Z in K, star (upperLaplacian u.toFun Z)*
        (cuspRestriction N s K hK (shiftedQuotientWave N t f)) Z := by
  have h := cusp_weakWave_equation N s K hK u hs f t
  simpa only [localSeedVector_inner_integral,SmoothUpperSeed.laplacian,upperFunction,upperLaplacian] using h

theorem cusp_weakWave_initial_velocity (N : ℕ) (s : SL(2,ℤ)) (K : Set ℍ) (hK : IsCompact K)
    (u : SmoothUpperSeed) (hs : tsupport (upperFunction u.toFun)⊆K)
    (f : AutomorphicSpace N) :
    deriv (fun r => inner ℂ (localSeedVector K u)
      (cuspRestriction N s K hK (shiftedQuotientWave N r f))) 0=0 := by
  have he : (fun r => inner ℂ (localSeedVector K u)
      (cuspRestriction N s K hK (shiftedQuotientWave N r f)))=
      fun r => inner ℂ (poincareSeedVector N (u.cuspPush s)) (shiftedQuotientWave N r f) :=
    funext (fun r => cuspRestriction_pairing N s K hK u hs _)
  rw [he]
  exact (poincare_weakWave_initial N f (u.cuspPush s)).2

#print axioms cusp_local_wave_equation
#print axioms cusp_weakWave_initial_velocity

end QuantitativeMaass.Wave
