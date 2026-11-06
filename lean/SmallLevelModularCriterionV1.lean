module

public import SmallLevelCuspGrowthTheoryV4
public import SmallLevelOriginalHeightV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelOriginal

open UpperHalfPlane Matrix SmallLevelCuspGrowth
open scoped ModularForm MatrixGroups Manifold

/-- The original hypotheses supply a global height bound at every positive
level, by choosing one auxiliary good prime. -/
theorem inverse_height_exists {N m : ℕ} (hN : 0<N) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N (2*m) f) :
    ∃ b : ℕ, ∃ M : ℝ, 0≤M ∧ ∀ z : ℍ, z.im^b*‖fourierFunction (2*m) f z‖≤M := by
  obtain ⟨p,hp,hgood,hlarge⟩ := FinitenessPaper2.exists_large_good_prime N hN
  exact inverse_height_bound hN hp hgood hlarge hf

/-- Cusp boundedness follows from the original height bound and actual
Gamma0 transformation laws. It is not an extra modularity hypothesis. -/
theorem bounded_at_cusp_of_transformations {N m : ℕ} (hN : 0<N) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N (2*m) f)
    (hs : ∀ γ : SL(2,ℤ), γ∈CongruenceSubgroup.Gamma0 N →
      fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f)
    (γ : SL(2,ℤ)) : IsBoundedAtImInfty (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ) := by
  obtain ⟨b,M,hM,hb⟩ := inverse_height_exists hN hf
  have hp := gamma_zero_period N ((2*m:ℕ):ℤ) _ hs γ
  have hol := (fourierFunction_holomorphic hf).slash ((2*m:ℕ):ℤ) (SpecialLinearGroup.mapGL ℝ γ)
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  apply bounded_of_strip hNR hp hol (2*b)
    (M*(|(γ 1 0:ℝ)| * ((N:ℝ)+1)+|(γ 1 1:ℝ)|)^(2*b)) 1
  intro z hx hy
  exact slash_polynomial_strip (2*m) b _ hM hNR.le hb γ z hx hy

/-- General assembly criterion for the remaining small levels. Only the
transformation equations remain to be established level by level; all
analytic and cusp conditions are deduced from the original input. -/
theorem modular_of_transformations {N m : ℕ} (hN : 0<N) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N (2*m) f)
    (hs : ∀ γ : SL(2,ℤ), γ∈CongruenceSubgroup.Gamma0 N →
      fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f) :
    IsModular N (2*m) f := by
  let F : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ((2*m:ℕ):ℤ) := {
    toFun := fourierFunction (2*m) f
    slash_action_eq' := by
      intro g hg
      obtain ⟨γ,hγ,rfl⟩ := hg
      exact hs γ hγ
    holo' := fourierFunction_holomorphic hf
    bdd_at_cusps' := by
      intro c hc
      have hle : (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))≤𝒮ℒ := by
        rintro g ⟨γ,_,rfl⟩
        exact ⟨γ,rfl⟩
      apply (OnePoint.isBoundedAt_iff_forall_SL2Z (hc.mono hle)).mpr
      intro γ _
      exact bounded_at_cusp_of_transformations hN hf hs γ }
  exact ⟨F,rfl⟩

#print axioms inverse_height_exists
#print axioms bounded_at_cusp_of_transformations
#print axioms modular_of_transformations

end SmallLevelOriginal
