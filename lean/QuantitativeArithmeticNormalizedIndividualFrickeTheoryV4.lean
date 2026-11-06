module

public import SmallLevelNormalizedFrickeV1

/-! Consolidated chapter: QuantitativeArithmeticNormalizedIndividualFricke. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticNormalizedIndividualFrickeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticNormalizedIndividualFricke
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

/-- Two individual Fricke equations with a common multiplier give a
single invariant matrix. No cancellation or nonvanishing premise on F is used. -/
theorem single_of_fricke (N L k : ℕ) (hN : 0<N) (hL : 0<L) (r : ℝ)
    (F : ℂ → ℂ) (χ : ℂ)
    (hF : ∀ z : ℂ, 0<z.im → F z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z)))
    (hG : ∀ z : ℂ, 0<z.im → F (z+r)=
      χ/(((Real.sqrt L:ℂ)*z)^k)*F (-1/((L:ℂ)*z)+r)) :
    (fun z : ℍ => F z) ∣[(k:ℤ)]
      ((fricke N hN)⁻¹*translation r*fricke L hL*(translation r)⁻¹)=
        (fun z : ℍ => F z) := by
  let f : ℍ → ℂ := fun z => F z
  have htw := fricke_law L k hL (fun z => F (z+r)) χ hG
  have hf := fricke_inverse_law N k hN F χ hF
  have ht : (fun z : ℍ => F ((z:ℂ)+r))=f ∣[(k:ℤ)] translation r := by
    funext z
    simp only [translation_slash,translation_point,f]
  rw [ht] at htw
  have hbranch : f ∣[(k:ℤ)] ((fricke N hN)⁻¹*translation r*fricke L hL)=
      f ∣[(k:ℤ)] translation r := by
    simp only [SlashAction.slash_mul,f,hf,
      det_one_smul _ (translation_det _),det_one_smul _ (fricke_det _ _)]
    exact htw.symm
  have h := congrArg (fun g : ℍ → ℂ => g ∣[(k:ℤ)] (translation r)⁻¹) hbranch
  simpa only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] using h

#print axioms single_of_fricke
end QuantitativeArithmeticNormalizedIndividualFricke
end
end

/-! ## QuantitativeArithmeticNormalizedIndividualEigenV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticNormalizedIndividualFricke
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem single_eigen_of_fricke (N L k : ℕ) (hN : 0<N) (hL : 0<L) (r : ℝ)
    (F : ℂ→ℂ) (χ δ : ℂ) (hδ : δ=1 ∨ δ= -1)
    (hF : ∀ z : ℂ,0<z.im → F z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z)))
    (hG : ∀ z : ℂ,0<z.im → F (z+r)=
      (δ*χ)/(((Real.sqrt L:ℂ)*z)^k)*F (-1/((L:ℂ)*z)+r)) :
    (fun z : ℍ => F z) ∣[(k:ℤ)]
      ((fricke N hN)⁻¹*translation r*fricke L hL*(translation r)⁻¹)=
        δ • (fun z : ℍ => F z) := by
  let f : ℍ→ℂ := fun z => F z
  have htw := fricke_law L k hL (fun z => F (z+r)) (δ*χ) hG
  have hf := fricke_inverse_law N k hN F χ hF
  have ht : (fun z : ℍ => F ((z:ℂ)+r))=f ∣[(k:ℤ)] translation r := by
    funext z
    simp only [translation_slash,translation_point,f]
  let H := f ∣[(k:ℤ)] ((fricke N hN)⁻¹*translation r*fricke L hL)
  have hh : H=χ • ((f ∣[(k:ℤ)] translation r) ∣[(k:ℤ)] fricke L hL) := by
    simp only [H,SlashAction.slash_mul,f,hf,
      det_one_smul _ (translation_det _),det_one_smul _ (fricke_det _ _)]
  rw [ht,mul_smul,← hh] at htw
  have hbranch : H=δ • (f ∣[(k:ℤ)] translation r) := by
    rcases hδ with rfl|rfl
    · simpa using htw.symm
    · simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg htw.symm
  have h := congrArg (fun g : ℍ→ℂ => g ∣[(k:ℤ)] (translation r)⁻¹) hbranch
  rw [det_one_smul _ (det_one_inv _ (translation_det r))] at h
  simpa only [H,← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] using h

#print axioms single_eigen_of_fricke
end QuantitativeArithmeticNormalizedIndividualFricke
end
end
