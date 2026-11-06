module

public import SmallLevelNormalizedFrickeV1
public import SmallLevelEvenScaleV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelTwentyFour

open Complex UpperHalfPlane SmallLevelNormalized SmallLevelEvenScale
open FinitenessFourierConstruction FinitenessOriginalFourier FinitenessAnalyticReconstruction
open scoped MatrixGroups ModularForm

theorem halve_fricke (N k : ℕ) (F : ℂ → ℂ) (χ : ℂ)
    (h : ∀ z : ℂ, 0<z.im → F z=χ/(((Real.sqrt (4*N):ℂ)*z)^k)*F (-1/((4*N:ℂ)*z))) :
    ∀ z : ℂ, 0<z.im → F (z/2)=χ/(((Real.sqrt N:ℂ)*z)^k)*F ((-1/((N:ℂ)*z))/2) := by
  intro z hz
  have he := h (z/2) (by simpa using div_pos hz (by norm_num : (0:ℝ)<2))
  have hsqrt : Real.sqrt (4*(N:ℝ))=2*Real.sqrt (N:ℝ) := by
    rw [Real.sqrt_mul (by norm_num)]
    norm_num
  rw [hsqrt, ofReal_mul, ofReal_ofNat] at he
  rw [show (2*(Real.sqrt N:ℂ))*(z/2)=(Real.sqrt N:ℂ)*z by ring,
    show -1/((4*(N:ℂ))*(z/2))=(-1/((N:ℂ)*z))/2 by ring] at he
  exact he

theorem scaled_twist_three {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 24 k f) (z : ℂ) (hz : 0<z.im) :
    twist (fourier (fullCoefficients f k)) 3 (z/2)=
      -(scaledFourier k f (z+1/3)+scaledFourier k f (z-1/3)) := by
  rw [SmallLevelThree.twist_three _ (periodic _)]
  have hp := scaled_antiperiod (L:=6) hf.toEulerData k
    (z:=z-1/3) (by simpa using hz)
  have hm := scaled_antiperiod (L:=6) hf.toEulerData k
    (z:=z-2/3) (by simpa using hz)
  rw [show (z-1/3)+1=z+2/3 by ring] at hp
  rw [show (z-2/3)+1=z+1/3 by ring] at hm
  rw [show z/2+1/3=(z+2/3)/2 by ring, show z/2-1/3=(z-2/3)/2 by ring]
  change scaledFourier k f (z+2/3)+scaledFourier k f (z-2/3)= _
  rw [hp]
  linear_combination hm

theorem original_pair_fricke {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 24 k f) :
    ∃ δ : ℂ, (δ=1 ∨ δ= -1) ∧
    (scaledFunction k f ∣[(k:ℤ)] ((fricke 6 (by decide))⁻¹*translation (1/3)*fricke 18 (by decide)))+
    (scaledFunction k f ∣[(k:ℤ)] ((fricke 6 (by decide))⁻¹*translation (-(1/3))*fricke 18 (by decide)))=
    δ • ((scaledFunction k f ∣[(k:ℤ)] translation (1/3))+
      (scaledFunction k f ∣[(k:ℤ)] translation (-(1/3)))) := by
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<24) hf
  let χ : ℂ := ε*Complex.I^k
  let δ : ℂ := FinitenessNormalizedTwistProduct.root 24 f 3
  have hδ : δ=1 ∨ δ= -1 := FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3
  have hF := halve_fricke 6 k (fourier (fullCoefficients f k)) χ (by
    intro z hz
    norm_num only [Nat.cast_ofNat]
    simpa [χ, FinitenessNormalizedTwistProduct.root, twist, Finset.sum_range_succ]
      using hlaw 1 (by decide) z hz)
  have hG := halve_fricke 18 k (twist (fourier (fullCoefficients f k)) 3) (δ*χ) (by
    intro z hz
    norm_num only [Nat.cast_ofNat]
    have h := hlaw 3 (by decide) z hz
    rw [show Nat.lcm 24 (3^2)=72 by decide] at h
    simpa only [χ, δ, mul_assoc, Nat.cast_ofNat] using h)
  refine ⟨δ,hδ,?_⟩
  apply pair_of_fricke 6 18 k (by decide) (by decide) (1/3) (scaledFourier k f) χ δ hδ
  · exact hF
  · intro z hz
    have hi : 0<(-1/((18:ℂ)*z)).im := by
      have hh := (fricke 18 (by decide) • (⟨z,hz⟩ : ℍ)).im_pos
      change 0<(((fricke 18 (by decide) • (⟨z,hz⟩ : ℍ) : ℍ):ℂ)).im at hh
      rw [fricke_point] at hh
      simpa only [Nat.cast_ofNat, coe_mk] using hh
    have hh := hG z hz
    norm_num only [Nat.cast_ofNat] at hh
    rw [scaled_twist_three hf z hz, scaled_twist_three hf _ hi] at hh
    have hh' := congrArg Neg.neg hh
    simpa only [neg_neg, mul_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat, Nat.cast_ofNat] using hh'

#print axioms halve_fricke
#print axioms scaled_twist_three
#print axioms original_pair_fricke

end SmallLevelTwentyFour
