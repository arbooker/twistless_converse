module

public import SmallLevelHalfConjugateV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelGenerators

open UpperHalfPlane FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

/-- The half-translation conjugate is controlled by the actual conductor
of the modulus-two twist, also when two divides the level only once. -/
theorem original_halfConjugate_of_lcm {N b k : ℕ} (hN : 0<N) (hb : 0<b)
    (hL : Nat.lcm N (2^2)=4*b) {f : ℕ → ℂ} (hf : IsSolution N k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] halfConjugate b=
      SmallLevelOriginal.fourierFunction k f := by
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  apply halfConjugate_of_lower
  apply lower_of_fricke (k:=k) (by omega : 0<4*b)
    (fun z : ℂ => fourier (fullCoefficients f k) (z+1/2))
    (FinitenessNormalizedTwistProduct.root N f 2*ε*Complex.I^k)
  · intro z
    rw [show z+1+1/2=(z+1/2)+1 by ring]
    exact periodic _ _
  · intro z hz
    have h := hlaw 2 (by decide) z hz
    have ht (G : ℂ → ℂ) (w : ℂ) :
        FinitenessAnalyticReconstruction.twist G 2 w=G (w+1/2) := by
      unfold FinitenessAnalyticReconstruction.twist
      rw [show (Finset.range 2).filter (fun a => Nat.Coprime a 2)={1} by decide]
      simp
    simpa only [hL, ht] using h

#print axioms original_halfConjugate_of_lcm

end SmallLevelGenerators
