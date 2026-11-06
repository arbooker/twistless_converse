module

public import SmallLevelSixPairV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentySix
open Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessNormalizedTwistProduct
open scoped MatrixGroups ModularForm

/-- The roots in the two paired equations are the same local bad-prime sign. -/
theorem root4 (f : ℕ → ℂ) : root 26 f 4=root 26 f 2 := by
  have hp : Nat.primeFactors 4={2} := by
    rw [show (4:ℕ)=2*2 by norm_num,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  have h4 : (4:ℕ).factorization 2=2 := by
    simpa using Nat.factorization_pow_self (n:=2) Nat.prime_two
  simp [root,hp,Nat.prime_two.primeFactors,Nat.prime_two.factorization_self,h4,FinitenessNormalizedTwistLocal.sign]

theorem root6 (f : ℕ → ℂ) : root 26 f 6=root 26 f 2 := by
  have hp : Nat.primeFactors 6={2,3} := by
    rw [show (6:ℕ)=2*3 by norm_num,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  have h6 : (6:ℕ).factorization 2=1 := by
    rw [show (6:ℕ)=2*3 by norm_num,Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization]
  simp [root,hp,Nat.prime_two.primeFactors,Nat.prime_two.factorization_self,h6,FinitenessNormalizedTwistLocal.sign]

theorem original_pair4 {k : ℕ} {f : ℕ → ℂ} (hf : FinitenessOriginalInput.IsSolution 26 k f) :
    (fourierFunction k f ∣[(k:ℤ)] ((fricke 26 (by decide))⁻¹*translation (1/4)*fricke 208 (by decide)))+
    (fourierFunction k f ∣[(k:ℤ)] ((fricke 26 (by decide))⁻¹*translation (-(1/4))*fricke 208 (by decide)))=
    FinitenessNormalizedTwistProduct.root 26 f 4 •
      ((fourierFunction k f ∣[(k:ℤ)] translation (1/4))+
      (fourierFunction k f ∣[(k:ℤ)] translation (-(1/4)))) := by
  obtain ⟨ε,_,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<26) hf
  apply pair_of_fricke 26 208 k (by decide) (by decide) (1/4)
    (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f k))
    (ε*Complex.I^k) _ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 4)
  · intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  · intro z hz
    have h := hlaw 4 (by decide) z hz
    rw [show Nat.lcm 26 (4^2)=208 by decide,
      SmallLevelThirty.twist_four _ (FinitenessFourierConstruction.periodic _),
      SmallLevelThirty.twist_four _ (FinitenessFourierConstruction.periodic _)] at h
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,mul_assoc] using h

theorem original_pair6 {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 26 k f) :
    (fourierFunction k f ∣[(k:ℤ)]
      ((fricke 26 (by decide))⁻¹*translation (1/6)*fricke 468 (by decide)))+
    (fourierFunction k f ∣[(k:ℤ)]
      ((fricke 26 (by decide))⁻¹*translation (-(1/6))*fricke 468 (by decide)))=
    root 26 f 2 • ((fourierFunction k f ∣[(k:ℤ)] translation (1/6))+
      (fourierFunction k f ∣[(k:ℤ)] translation (-(1/6)))) := by
  simpa only [root6] using original_six_pair (by decide : 0<26)
    (by decide : 0<468) (by decide : Nat.lcm 26 (6^2)=468) hf

#print axioms original_pair4
#print axioms original_pair6
end SmallLevelTwentySix
