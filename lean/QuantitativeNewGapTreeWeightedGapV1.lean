module

public import QuantitativeNewGapTreeProjectionGapV1
public import QuantitativeEulerOldProjectionWeightedV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open InnerProductSpace AsymptoticNestedQuotients AsymptoticQuotientOperators
open AsymptoticCongruenceStrip UpperHalfPlane
open scoped InnerProductSpace lp

/-- The cross Gram controls the literal common-kernel projection. -/
theorem coset_old_gap_of_cross_norm {G : Type*} [Group G] {H J K : Subgroup G}
    (hJ : H≤J) (hK : H≤K)
    [Finite (J ⧸ H.subgroupOf J)] [Finite (K ⧸ H.subgroupOf K)]
    {a : ℝ} (ha : 0≤a) (ha1 : a<1)
    (hcross : ‖(isometry hJ).toContinuousLinearMap.adjoint.comp
      (isometry hK).toContinuousLinearMap‖≤a) (w : ℓ²(Classes H,ℂ)) :
    (1-a)*‖w-(newSpace hJ hK).starProjection w‖^2≤
      ‖(space hJ).starProjection w‖^2+‖(space hK).starProjection w‖^2 := by
  have hn : newSpace hJ hK=(space hJ⊔space hK)ᗮ := by
    ext v
    rw [newSpace_mem,← Submodule.inf_orthogonal,Submodule.mem_inf,
      ← Submodule.starProjection_apply_eq_zero_iff,← Submodule.starProjection_apply_eq_zero_iff]
  rw [AsymptoticPolarIsometry.starProjection_congr _ _ hn]
  apply projection_complement_gap _ _ ha ha1
  rintro u ⟨f,rfl⟩ v ⟨g,rfl⟩
  let T := (isometry hJ).toContinuousLinearMap.adjoint.comp
    (isometry hK).toContinuousLinearMap
  have he := ContinuousLinearMap.adjoint_inner_right (isometry hJ).toContinuousLinearMap f
    (isometry hK g)
  change ⟪f,T g⟫_ℂ=⟪isometry hJ f,isometry hK g⟫_ℂ at he
  change ‖⟪isometry hJ f,isometry hK g⟫_ℂ‖≤a*‖isometry hJ f‖*‖isometry hK g‖
  rw [← he,LinearIsometry.norm_map,LinearIsometry.norm_map]
  have hb : ‖T g‖≤a*‖g‖ := (T.le_opNorm g).trans
    (mul_le_mul_of_nonneg_right hcross (norm_nonneg g))
  calc
    ‖⟪f,T g⟫_ℂ‖≤‖f‖*‖T g‖ := norm_inner_le_norm _ _
    _ ≤ ‖f‖*(a*‖g‖) := mul_le_mul_of_nonneg_left hb (norm_nonneg f)
    _ = a*‖f‖*‖g‖ := by ring

/-- Explicit simple-prime gap on the actual infinite arithmetic quotient. -/
theorem simple_coset_old_gap (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hpM : ¬p∣M) (w : ℓ²(Classes (gamma (p*M)),ℂ)) :
    (1-2*Real.sqrt p/((p:ℝ)+1))*
      ‖w-(newSpace (gamma_le_of_dvd (Nat.dvd_mul_left M p))
        (gamma_le_degeneracyGroup M p (Nat.pos_of_ne_zero (NeZero.ne M))
          (Fact.out : p.Prime).pos)).starProjection w‖^2≤
      ‖(space (gamma_le_of_dvd (Nat.dvd_mul_left M p))).starProjection w‖^2+
      ‖(space (gamma_le_degeneracyGroup M p (Nat.pos_of_ne_zero (NeZero.ne M))
        (Fact.out : p.Prime).pos)).starProjection w‖^2 := by
  exact coset_old_gap_of_cross_norm _ _ (by positivity)
    (arithmetic_old_cross_gram_sharp M p hpM).2 (arithmetic_old_cross_gram_sharp M p hpM).1 w

/-- Uniform sharp old-projection coercivity in the actual weighted
quotient space, independent of base point, weight and truncation height. -/
theorem simple_weighted_old_gap (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬p∣M)
    {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ)
    (w : ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hw : w∈AsymptoticCongruenceQuotient.quotientSpace (p*M) hε ht z) :
    (1-2*Real.sqrt p/((p:ℝ)+1))*
      ‖w-(AsymptoticCongruenceOldSpace.newSpace (p*M) (gamma M)
        (degeneracyGroup M p (Fact.out : p.Prime).pos)
        (gamma_le_of_dvd (Nat.dvd_mul_left M p))
        (gamma_le_degeneracyGroup M p (Nat.pos_of_ne_zero (NeZero.ne M))
          (Fact.out : p.Prime).pos) hε ht z).starProjection w‖^2≤
      ‖(AsymptoticCongruenceOldSpace.space (p*M) (gamma M)
        (gamma_le_of_dvd (Nat.dvd_mul_left M p)) hε ht z).starProjection w‖^2+
      ‖(AsymptoticCongruenceOldSpace.space (p*M)
        (degeneracyGroup M p (Fact.out : p.Prime).pos)
        (gamma_le_degeneracyGroup M p (Nat.pos_of_ne_zero (NeZero.ne M))
          (Fact.out : p.Prime).pos) hε ht z).starProjection w‖^2 := by
  obtain ⟨f,rfl⟩ := hw
  simp only [LinearIsometry.coe_toLinearMap]
  rw [QuantitativeEulerOldProjectionBlock.weighted_new_induction,
    AsymptoticCongruenceOldSpace.projection_induction,
    AsymptoticCongruenceOldSpace.projection_induction,← map_sub]
  simpa only [LinearIsometry.norm_map] using simple_coset_old_gap M p hpM f

#print axioms coset_old_gap_of_cross_norm
#print axioms simple_coset_old_gap
#print axioms simple_weighted_old_gap

end QuantitativeNewGap
