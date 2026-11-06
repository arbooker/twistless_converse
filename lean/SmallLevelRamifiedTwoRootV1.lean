module
public import SmallLevelRamifiedTwoFrickeV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelRamifiedTwo
open Matrix UpperHalfPlane
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

/-- The ramified-two eigenvalue is exactly the original local root. -/
theorem original_eigen_root {N a k : ℕ} (hN : 0<N) (ha : 2*a=N+2)
    (hL : Nat.lcm N (2^2)=2*N) {f : ℕ → ℂ} (hf : IsSolution N k f) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] Q N a ha=
      FinitenessNormalizedTwistProduct.root N f 2 • SmallLevelOriginal.fourierFunction k f := by
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws hN hf
  apply eigen_of_fricke hN ha _ (ε*Complex.I^k)
  · intro z hz
    have h := hlaw 1 (by decide) z hz
    simpa [FinitenessNormalizedTwistProduct.root, FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using h
  · intro z hz
    have h := hlaw 2 (by decide) z hz
    have ht (G : ℂ → ℂ) (w : ℂ) :
        FinitenessAnalyticReconstruction.twist G 2 w=G (w+1/2) := by
      unfold FinitenessAnalyticReconstruction.twist
      rw [show (Finset.range 2).filter (fun a => Nat.Coprime a 2)={1} by decide]
      simp
    have hsqrt : Real.sqrt (2*N:ℕ)=Real.sqrt 2*Real.sqrt (N:ℝ) := by
      rw [Nat.cast_mul, Real.sqrt_mul (by norm_num)]
      norm_num
    rw [hL, hsqrt, Complex.ofReal_mul, ht, ht] at h
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using h

#print axioms original_eigen_root
end SmallLevelRamifiedTwo
