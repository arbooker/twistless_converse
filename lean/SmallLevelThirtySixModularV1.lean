module

public import SmallLevelThirtySixPeriodV1
public import SmallLevelOriginalHeightV1
public import SmallLevelCuspGrowthTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThirtySix

open UpperHalfPlane Matrix
open scoped ModularForm MatrixGroups Manifold

theorem original_bounded_at_cusp {f : ℕ → ℂ} (m : ℕ) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 36 (2*m) f) (γ : SL(2,ℤ)) :
    IsBoundedAtImInfty (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ) := by
  obtain ⟨b,M,hM,hb⟩ := SmallLevelOriginal.inverse_height_bound
    (p:=7) (by decide) (by decide) (by decide) (by decide) hf
  have hp := gamma_zero_cusp_period ((2*m:ℕ):ℤ) _ (original_gamma_zero m hm hf) γ
  have hol := (SmallLevelOriginal.fourierFunction_holomorphic hf).slash
    ((2*m:ℕ):ℤ) (SpecialLinearGroup.mapGL ℝ γ)
  apply SmallLevelCuspGrowth.bounded_of_strip (by norm_num : (0:ℝ)<36) hp hol (2*b)
    (M*(|(γ 1 0:ℝ)| * (36+1)+|(γ 1 1:ℝ)|)^(2*b)) 1
  intro z hx hy
  exact SmallLevelCuspGrowth.slash_polynomial_strip (2*m) b _ hM (by norm_num) hb γ z hx hy

/-- A genuine Mathlib modular form, with the original Fourier function and
all cusp conditions derived from the literal original hypotheses. -/
def originalModular (m : ℕ) (hm : 0<m) (f : FinitenessOriginalInput.S 36 (2*m)) :
    ModularForm (CongruenceSubgroup.Gamma0 36 : Subgroup (GL (Fin 2) ℝ)) ((2*m:ℕ):ℤ) where
  toFun := SmallLevelOriginal.fourierFunction (2*m) f.val
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ,hγ,rfl⟩ := hg
    exact original_gamma_zero m hm f.property γ hγ
  holo' := SmallLevelOriginal.fourierFunction_holomorphic f.property
  bdd_at_cusps' hc := by
    have hle : (CongruenceSubgroup.Gamma0 36 : Subgroup (GL (Fin 2) ℝ))≤𝒮ℒ := by
      rintro g ⟨γ,_,rfl⟩
      exact ⟨γ,rfl⟩
    apply (OnePoint.isBoundedAt_iff_forall_SL2Z (hc.mono hle)).mpr
    intro γ _
    exact original_bounded_at_cusp m hm f.property γ

/-- The complete level-36 case of paper2's small-level modularity theorem. -/
theorem level_thirty_six {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 36 k f) : SmallLevelOriginal.IsModular 36 k f := by
  obtain ⟨m,hm⟩ := heven
  have heq : k=2*m := by omega
  rw [heq] at hf ⊢
  exact ⟨originalModular m (by omega) ⟨f,hf⟩,rfl⟩

#print axioms original_bounded_at_cusp
#print axioms originalModular
#print axioms level_thirty_six

end SmallLevelThirtySix
