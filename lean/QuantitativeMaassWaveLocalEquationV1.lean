module

public import QuantitativeMaassLocalTestPairingV1
public import QuantitativeMaassWaveWeakEquationV1

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology InnerProductSpace

namespace QuantitativeMaass.Wave

/-- The weak wave equation written as literal local integrals for every L2
initial vector. The restriction map and both differential test functions
are constructed; no regularity of an evolving pointwise representative is used. -/
theorem local_wave_equation (N : ℕ) (K : Set ℍ) (hK : IsCompact K) (hKm : MeasurableSet K)
    (u : SmoothUpperSeed) (hs : tsupport (upperFunction u.toFun)⊆K)
    (f : AutomorphicSpace N) (t : ℝ) :
    deriv (deriv (fun s => ∫ Z in K, star (upperFunction u.toFun Z)*
      (quotientRestriction N K hK hKm (shiftedQuotientWave N s f)) Z)) t=
      (1/4 : ℂ)*(∫ Z in K, star (upperFunction u.toFun Z)*
        (quotientRestriction N K hK hKm (shiftedQuotientWave N t f)) Z)-
      ∫ Z in K, star (upperLaplacian u.toFun Z)*
        (quotientRestriction N K hK hKm (shiftedQuotientWave N t f)) Z := by
  have hsL : tsupport (upperFunction u.laplacian.toFun)⊆K :=
    closure_minimal ((upperLaplacian_support u.toFun).trans hs) hK.isClosed
  have he : (fun s => ∫ Z in K, star (upperFunction u.toFun Z)*
      (quotientRestriction N K hK hKm (shiftedQuotientWave N s f)) Z)=
      fun s => inner ℂ (poincareSeedVector N u) (shiftedQuotientWave N s f) :=
    funext (fun s => quotientRestriction_test_integral N K hK hKm u hs _)
  rw [he,quotientRestriction_test_integral N K hK hKm u hs]
  change deriv (deriv (fun s => inner ℂ (poincareSeedVector N u)
    (shiftedQuotientWave N s f))) t=_-
      ∫ Z in K, star (upperFunction u.laplacian.toFun Z)*
        (quotientRestriction N K hK hKm (shiftedQuotientWave N t f)) Z
  rw [quotientRestriction_test_integral N K hK hKm u.laplacian hsL]
  exact poincare_weakWave_equation N f u t

theorem local_wave_initial (N : ℕ) (K : Set ℍ) (hK : IsCompact K) (hKm : MeasurableSet K)
    (u : SmoothUpperSeed) (hs : tsupport (upperFunction u.toFun)⊆K)
    (f : AutomorphicSpace N) :
    deriv (fun s => ∫ Z in K, star (upperFunction u.toFun Z)*
      (quotientRestriction N K hK hKm (shiftedQuotientWave N s f)) Z) 0=0 := by
  have he : (fun s => ∫ Z in K, star (upperFunction u.toFun Z)*
      (quotientRestriction N K hK hKm (shiftedQuotientWave N s f)) Z)=
      fun s => inner ℂ (poincareSeedVector N u) (shiftedQuotientWave N s f) :=
    funext (fun s => quotientRestriction_test_integral N K hK hKm u hs _)
  rw [he]
  exact (poincare_weakWave_initial N f u).2

#print axioms local_wave_equation
#print axioms local_wave_initial

end QuantitativeMaass.Wave
