module

public import SmallLevelThirtySixFrickeV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open Complex UpperHalfPlane ModularGroup FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction
open scoped ModularForm MatrixGroups Manifold

theorem scaledFunction_holomorphic {k : ℕ} {f : ℕ → ℂ} (hf : EulerData 36 f) :
    MDiff (scaledFunction k f) := by
  obtain ⟨τ, _, hg⟩ := hf.growth
  intro z
  have hd : DifferentiableAt ℂ (scaledFourier k f) (z:ℂ) :=
    (FinitenessFourierConstruction.holomorphic (polynomial_bound hf.zero hg k)
      (z := (z:ℂ)/6) (by simpa using div_pos z.im_pos (by norm_num : (0:ℝ)<6))).comp
      (z:ℂ) (differentiableAt_id.div_const 6)
  exact hd.mdifferentiableAt.comp z (mdifferentiable_coe z)

theorem obstruction_holomorphic {m : ℕ} {g : ℍ → ℂ} (hg : MDiff g) :
    MDiff (obstruction m g) := by
  have ht := hg.slash ((2*m : ℕ):ℤ) (Matrix.SpecialLinearGroup.mapGL ℝ T)
  have hts := ht.slash ((2*m : ℕ):ℤ) (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S)
  exact ht.add hts

/-- Unconditional orbit data from the literal original level-36 solution.
The negative-sign obstruction is holomorphic and invariant under the full
modular group. Its vanishing still requires the separate Hecke identity. -/
theorem original_orbit_data {f : ℕ → ℂ} (m : ℕ) (hf : IsSolution 36 (2*m) f) :
    MDiff (scaledFunction (2*m) f) ∧
    ((scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] T) ∣[((2*m:ℕ):ℤ)] T=
      (scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] T)-scaledFunction (2*m) f) ∧
    ∃ χ : ℂ, (χ=1 ∨ χ = -1) ∧
      scaledFunction (2*m) f ∣[((2*m:ℕ):ℤ)] ModularGroup.S=χ • scaledFunction (2*m) f ∧
      (χ = -1 → ∀ γ : SL(2,ℤ),
        obstruction m (scaledFunction (2*m) f) ∣[((2*m:ℕ):ℤ)] γ=
          obstruction m (scaledFunction (2*m) f)) := by
  obtain ⟨χ, hχ, hS⟩ := scaledFunction_sign m hf
  have hT := scaledFunction_quadratic hf.toEulerData (2*m)
  refine ⟨scaledFunction_holomorphic hf.toEulerData, hT, χ, hχ, hS, ?_⟩
  intro hn
  apply obstruction_modular m _ hT
  simpa only [hn, neg_one_smul] using hS

#print axioms scaledFunction_holomorphic
#print axioms obstruction_holomorphic
#print axioms original_orbit_data

end SmallLevelThirtySix
