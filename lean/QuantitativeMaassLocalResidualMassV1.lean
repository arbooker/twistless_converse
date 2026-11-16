module

public import QuantitativeMaassQuotientRestrictionOverlapV1
public import QuantitativeMaassPoincareEnergyV1
public import QuantitativeMaassPoincareGraphLinearV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson

namespace QuantitativeMaass

/-- Local mass of an invariant representative is controlled by its
quotient L2 norm and the geometric overlap multiplicity. -/
theorem representative_local_mass_le (N : ℕ) (K : Set ℍ)
    (hK : IsCompact K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    (∫ z in K, ‖f.val z‖^2) ≤
      (m : ℝ)*‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f‖^2 := by
  have hb := representativeRestriction_bound_of_overlap N K hK m hm f
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr hb
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg m)] at hs
  change ‖(representativeLocalMemLp N K hK hK.measurableSet f).toLp f.val‖^2 ≤ _ at hs
  rw [complex_toLp_norm_sq] at hs
  exact hs

/-- The local differential residual is bounded by the original quotient
L2 residual, without differentiating that residual a second time. -/
theorem poincare_local_residual_mass_le (N : ℕ) (v : SmoothUpperSeed)
    (K : Set ℍ) (hK : IsCompact K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m) (μ : ℂ) :
    (∫ z in K, ‖upperLaplacian (congruencePoincareCartesian N v.toFun) z-
      μ*upperFunction (congruencePoincareCartesian N v.toFun) z‖^2) ≤
      (m : ℝ)*‖poincareSeedVector N v.laplacian-μ • poincareSeedVector N v‖^2 := by
  let f : AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
    ⟨_,poincareSeed_representative N v⟩
  let g : AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
    ⟨_,poincareSeed_representative N v.laplacian⟩
  have hb := representative_local_mass_le N K hK m hm (g-μ • f)
  rw [map_sub,map_smul] at hb
  change (∫ z in K, ‖poincareSum (G := gamma N) (upperFunction v.laplacian.toFun) z-
      μ*poincareSum (G := gamma N) (upperFunction v.toFun) z‖^2) ≤ _ at hb
  rw [upperLaplacian_congruencePoincareCartesian N v.smooth v.compact]
  simp_rw [congruencePoincareCartesian_represents]
  exact hb

#print axioms representative_local_mass_le
#print axioms poincare_local_residual_mass_le

end QuantitativeMaass
