module

public import SmallLevelNormalizedMatricesV1
public import SmallLevelThreePairV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace SmallLevelNormalized

open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem fricke_law (N k : ℕ) (hN : 0<N) (F : ℂ → ℂ) (χ : ℂ)
    (h : ∀ z : ℂ, 0<z.im → F z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z))) :
    (fun z : ℍ => F z)=χ • ((fun z : ℍ => F z) ∣[(k:ℤ)] fricke N hN) := by
  funext z
  rw [Pi.smul_apply, smul_eq_mul, det_one_slash _ (fricke_det _ _), fricke_denom, fricke_point]
  simpa only [zpow_neg, zpow_natCast, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    using h z z.im_pos

theorem fricke_inverse_law (N k : ℕ) (hN : 0<N) (F : ℂ → ℂ) (χ : ℂ)
    (h : ∀ z : ℂ, 0<z.im → F z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z))) :
    (fun z : ℍ => F z) ∣[(k:ℤ)] (fricke N hN)⁻¹=χ • (fun z : ℍ => F z) := by
  have hh := congrArg (fun g : ℍ → ℂ => g ∣[(k:ℤ)] (fricke N hN)⁻¹)
    (fricke_law N k hN F χ h)
  rw [det_one_smul _ (det_one_inv _ (fricke_det _ _)),
    ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at hh
  exact hh

/-- Two coherent Fricke laws give the exact normalized two-branch relation.
No division by either functional-equation multiplier is used. -/
theorem pair_of_fricke (N L k : ℕ) (hN : 0<N) (hL : 0<L) (r : ℝ)
    (F : ℂ → ℂ) (χ δ : ℂ) (hδ : δ=1 ∨ δ= -1)
    (hF : ∀ z : ℂ, 0<z.im → F z=χ/(((Real.sqrt N:ℂ)*z)^k)*F (-1/((N:ℂ)*z)))
    (hG : ∀ z : ℂ, 0<z.im → F (z+r)+F (z-r)=
      (δ*χ)/(((Real.sqrt L:ℂ)*z)^k)*(F (-1/((L:ℂ)*z)+r)+F (-1/((L:ℂ)*z)-r))) :
    ((fun z : ℍ => F z) ∣[(k:ℤ)] ((fricke N hN)⁻¹*translation r*fricke L hL))+
      ((fun z : ℍ => F z) ∣[(k:ℤ)] ((fricke N hN)⁻¹*translation (-r)*fricke L hL))=
    δ • (((fun z : ℍ => F z) ∣[(k:ℤ)] translation r)+
      ((fun z : ℍ => F z) ∣[(k:ℤ)] translation (-r))) := by
  let f : ℍ → ℂ := fun z => F z
  let G : ℂ → ℂ := fun z => F (z+r)+F (z-r)
  have htw := fricke_law L k hL G (δ*χ) hG
  have hf := fricke_inverse_law N k hN F χ hF
  have ht : (fun z : ℍ => G z)=(f ∣[(k:ℤ)] translation r)+(f ∣[(k:ℤ)] translation (-r)) := by
    funext z
    simp only [Pi.add_apply, translation_slash, f, G, translation_point,
      Complex.ofReal_neg, sub_eq_add_neg]
  let H := (f ∣[(k:ℤ)] ((fricke N hN)⁻¹*translation r*fricke L hL))+
    (f ∣[(k:ℤ)] ((fricke N hN)⁻¹*translation (-r)*fricke L hL))
  have hh : H=χ • (((f ∣[(k:ℤ)] translation r)+(f ∣[(k:ℤ)] translation (-r))) ∣[(k:ℤ)] fricke L hL) := by
    dsimp only [H]
    simp only [SlashAction.slash_mul, f, hf,
      det_one_smul _ (translation_det _), det_one_smul _ (fricke_det _ _)]
    rw [← smul_add, ← SlashAction.add_slash]
  rw [ht, mul_smul, ← hh] at htw
  change H=δ • _
  rcases hδ with rfl | rfl
  · simpa using htw.symm
  · simpa only [neg_one_smul, neg_neg] using congrArg Neg.neg htw.symm

/-- The actual level-fifteen modulus-three pair before identifying its
explicit matrix branches. -/
theorem original_fifteen_pair {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 15 k f) :
    ∃ δ : ℂ, (δ=1 ∨ δ= -1) ∧
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 15 (by decide))⁻¹*translation (1/3)*fricke 45 (by decide)))+
    (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)]
      ((fricke 15 (by decide))⁻¹*translation (-(1/3))*fricke 45 (by decide)))=
    δ • ((SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (1/3))+
      (SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] translation (-(1/3)))) := by
  obtain ⟨ε, _, hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<15) hf
  refine ⟨FinitenessNormalizedTwistProduct.root 15 f 3,
    FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3, ?_⟩
  apply pair_of_fricke 15 45 k (by decide) (by decide) (1/3)
    (FinitenessFourierConstruction.fourier (FinitenessOriginalFourier.fullCoefficients f k))
    (ε*Complex.I^k) _ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3)
  · intro z hz
    simpa [FinitenessNormalizedTwistProduct.root, FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  · intro z hz
    have h := hlaw 3 (by decide) z hz
    rw [show Nat.lcm 15 (3^2)=45 by decide,
      SmallLevelThree.twist_three _ (FinitenessFourierConstruction.periodic _),
      SmallLevelThree.twist_three _ (FinitenessFourierConstruction.periodic _)] at h
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_assoc] using h

#print axioms fricke_inverse_law
#print axioms pair_of_fricke
#print axioms original_fifteen_pair

end SmallLevelNormalized
