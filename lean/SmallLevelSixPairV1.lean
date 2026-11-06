module

public import SmallLevelThirtyPairsV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelNormalized

open Matrix UpperHalfPlane
open FinitenessFourierConstruction FinitenessOriginalFourier FinitenessAnalyticReconstruction
open scoped MatrixGroups ModularForm

/-- The modulus-six pair at its actual conductor, retaining the exact root. -/
theorem original_six_pair {N L k : ℕ} (hN : 0<N) (hL : 0<L)
    (hc : Nat.lcm N (6^2)=L) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke N hN)⁻¹*translation (1/6)*fricke L hL))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke N hN)⁻¹*translation (-(1/6))*fricke L hL))=
    FinitenessNormalizedTwistProduct.root N f 6 •
      ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/6))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/6)))) := by
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  apply pair_of_fricke N L k hN hL (1/6)
    (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f k))
    (ε*Complex.I^k) _ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 6)
  · intro z hz
    simpa [FinitenessNormalizedTwistProduct.root, FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  · intro z hz
    have h := hlaw 6 (by decide) z hz
    rw [hc, SmallLevelThirty.twist_six _ (FinitenessFourierConstruction.periodic _),
      SmallLevelThirty.twist_six _ (FinitenessFourierConstruction.periodic _)] at h
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_assoc] using h

#print axioms original_six_pair

end SmallLevelNormalized
