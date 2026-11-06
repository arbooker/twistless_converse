module

public import SmallLevelNormalizedFrickeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelThirty

open Matrix UpperHalfPlane SmallLevelNormalized
open FinitenessFourierConstruction FinitenessOriginalFourier FinitenessAnalyticReconstruction
open scoped MatrixGroups ModularForm

theorem twist_six (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z) (z : ℂ) :
    twist F 6 z=F (z+1/6)+F (z-1/6) := by
  unfold twist
  rw [show (Finset.range 6).filter (fun a => Nat.Coprime a 6)={1,5} by decide]
  norm_num
  rw [show z+5/6=(z-1/6)+1 by ring, hp]

theorem twist_four (F : ℂ → ℂ) (hp : ∀ z, F (z+1)=F z) (z : ℂ) :
    twist F 4 z=F (z+1/4)+F (z-1/4) := by
  unfold twist
  rw [show (Finset.range 4).filter (fun a => Nat.Coprime a 4)={1,3} by decide]
  norm_num
  rw [show z+3/4=(z-1/4)+1 by ring, hp]

theorem original_pair_six {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 30 k f) :
    ∃ δ : ℂ, (δ=1 ∨ δ= -1) ∧
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 30 (by decide))⁻¹*translation (1/6)*fricke 180 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 30 (by decide))⁻¹*translation (-(1/6))*fricke 180 (by decide)))=
    δ • ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/6))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/6)))) := by
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<30) hf
  refine ⟨FinitenessNormalizedTwistProduct.root 30 f 6,
    FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 6, ?_⟩
  apply pair_of_fricke 30 180 k (by decide) (by decide) (1/6)
    (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f k))
    (ε*Complex.I^k) _ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 6)
  · intro z hz
    simpa [FinitenessNormalizedTwistProduct.root, FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  · intro z hz
    have h := hlaw 6 (by decide) z hz
    rw [show Nat.lcm 30 (6^2)=180 by decide,
      twist_six _ (FinitenessFourierConstruction.periodic _),
      twist_six _ (FinitenessFourierConstruction.periodic _)] at h
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_assoc] using h

theorem original_pair_four {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 30 k f) :
    ∃ δ : ℂ, (δ=1 ∨ δ= -1) ∧
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 30 (by decide))⁻¹*translation (1/4)*fricke 240 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 30 (by decide))⁻¹*translation (-(1/4))*fricke 240 (by decide)))=
    δ • ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/4))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/4)))) := by
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<30) hf
  refine ⟨FinitenessNormalizedTwistProduct.root 30 f 4,
    FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 4, ?_⟩
  apply pair_of_fricke 30 240 k (by decide) (by decide) (1/4)
    (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f k))
    (ε*Complex.I^k) _ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 4)
  · intro z hz
    simpa [FinitenessNormalizedTwistProduct.root, FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  · intro z hz
    have h := hlaw 4 (by decide) z hz
    rw [show Nat.lcm 30 (4^2)=240 by decide,
      twist_four _ (FinitenessFourierConstruction.periodic _),
      twist_four _ (FinitenessFourierConstruction.periodic _)] at h
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_assoc] using h

theorem original_pair_four_exact {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 30 k f) :
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 30 (by decide))⁻¹*translation (1/4)*fricke 240 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 30 (by decide))⁻¹*translation (-(1/4))*fricke 240 (by decide)))=
    FinitenessNormalizedTwistProduct.root 30 f 4 • ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/4))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/4)))) := by
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<30) hf
  apply pair_of_fricke 30 240 k (by decide) (by decide) (1/4)
    (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f k))
    (ε*Complex.I^k) _ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 4)
  · intro z hz
    simpa [FinitenessNormalizedTwistProduct.root, FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  · intro z hz
    have h := hlaw 4 (by decide) z hz
    rw [show Nat.lcm 30 (4^2)=240 by decide,
      twist_four _ (FinitenessFourierConstruction.periodic _),
      twist_four _ (FinitenessFourierConstruction.periodic _)] at h
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_assoc] using h

#print axioms original_pair_four_exact

#print axioms original_pair_six
#print axioms original_pair_four

end SmallLevelThirty
