module

public import QuantitativeEulerEndpointLevelOneIndependentV1
public import AsymptoticClassicalNewEigenCountV1
public import QuantitativeConcreteGoalsV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointLevelOne
open UpperHalfPlane Filter Asymptotics
open AsymptoticClassicalCusp AsymptoticSectorComparison QuantitativeConcreteGoals
open scoped ModularForm MatrixGroups

theorem level_one_eq_SL : level 1=𝒮ℒ := by
  apply le_antisymm (level_le_SL 1)
  rintro g ⟨γ,rfl⟩
  exact ⟨γ,by change (γ 1 0 : ZMod 1)=0; exact Subsingleton.elim _ _,rfl⟩

theorem one_admissible : GridAdmissibleGap.Admissible 1 := by
  refine ⟨by decide,by decide,?_⟩
  intro p hp _hp2 hd
  exact hp.not_dvd_one (dvd_trans (dvd_pow_self p (by decide : 2≠0)) hd)

theorem cusp_finrank_congr (G H : Subgroup (GL (Fin 2) ℝ)) [G.HasDetOne] [H.HasDetOne]
    (he : G=H) (k : ℤ) : Module.finrank ℂ (CuspForm G k)=Module.finrank ℂ (CuspForm H k) := by
  subst H
  rfl

/-- At level one the original Euler count equals the actual classical
newspace dimension at EVERY positive even weight. -/
theorem original_count_eq_new_dimension (m : ℕ) (hm : 0<m) :
    (FinitenessOriginalInput.S 1 (2*m)).ncard=
      Module.finrank ℂ (newSpace 1 (by decide) ((2*m : ℕ) : ℤ)) := by
  have hu := original_count_le_cusp_dimension m hm
  have he : Module.finrank ℂ (newSpace 1 (by decide) ((2*m : ℕ) : ℤ))=
      Module.finrank ℂ (CuspForm 𝒮ℒ ((2*m : ℕ) : ℤ)) := by
    rw [newSpace_one,_root_.finrank_top]
    exact cusp_finrank_congr _ _ level_one_eq_SL _
  rw [he]
  apply le_antisymm hu
  obtain ⟨C,_hC,hfin⟩ := FinitenessOriginalTheorem.admissible_level 1 one_admissible.1
    one_admissible.2.1 one_admissible.2.2
  have hl := newspace_dimension_le_euler_count 1 (2*m) (by decide) (by omega)
    (even_two_mul m) (hfin m hm).1
  rwa [he] at hl

theorem holomorphicError_one_eventually_zero :
    ∀ᶠ k : ℕ in evenWeights,holomorphicError 1 (by decide) k=0 := by
  have hk : ∀ᶠ k : ℕ in evenWeights,0<k := (eventually_gt_atTop 0).filter_mono inf_le_left
  have he : ∀ᶠ k : ℕ in evenWeights,Even k :=
    Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun _ h => h))
  filter_upwards [hk,he] with k hk he
  obtain ⟨m,hm⟩ := he
  have hkm : k=2*m := by omega
  rw [hkm]
  have h := original_count_eq_new_dimension m (by omega)
  simp only [holomorphicError,h,sub_self]

/-- The user's endpoint claim is proved at level one, with zero eventual
remainder. This theorem makes no assertion for levels N>=2. -/
theorem level_one_endpoint : HolomorphicCountClaim 1 (by decide) 1 := by
  apply Asymptotics.IsBigO.of_bound 0
  filter_upwards [holomorphicError_one_eventually_zero] with k hk
  simp only [hk,norm_zero,zero_mul,le_refl]

#print axioms original_count_eq_new_dimension
#print axioms holomorphicError_one_eventually_zero
#print axioms level_one_endpoint
end QuantitativeEulerEndpointLevelOne
