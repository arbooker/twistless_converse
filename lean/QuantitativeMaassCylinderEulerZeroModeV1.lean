module

public import QuantitativeMaassCylinderZeroModeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology ContDiff MatrixGroups

namespace QuantitativeMaass

variable {N Q : ℕ} {hQ : 0<Q} (hN : 0<N)
  (A : FinitenessCertificate.Certificate N Q hQ) (P : FinitenessGlobalHeight.Parameters A)
  (r : ℝ) (σ : ℕ) {b : ℕ → ℂ} (hb : MaassOriginal.IsEulerSolution N (.principal r) σ b)

/-- The actual weighted original wave as a periodic cylinder representative. -/
def principalEulerCylinderRepresentative :
    AutomorphicL2.representatives (gamma 0) (quotientMeasure 0) := by
  refine ⟨AsymptoticWeightedBranches.weighted P.ε (P.s+3) 0 (principalEulerPhysical b r σ),?_,?_,
    principalEulerCylinder_memLp hN A P r σ hb⟩
  · change Measurable (fun z : ℍ => AsymptoticWeightedBranches.weighted P.ε (P.s+3) 0
      (principalEulerPhysical b r σ) z)
    simp only [weighted_zero_eq_capped]
    exact (cappedEuler_continuous hb.polynomialGrowth r σ P.ε (P.s+3)).measurable
  · intro γ z
    simp only [weighted_zero_eq_capped,cappedHeightWeight_cylinder_invariant,
      principalEulerPhysical_cylinder_invariant]

theorem principalEulerCylinderRepresentative_class :
    AutomorphicL2.denseEmbedding (gamma 0) (quotientMeasure 0)
      (principalEulerCylinderRepresentative hN A P r σ hb)=
      cylinderAutomorphic (principalEulerCylinderLp hN A P r σ hb) := by
  apply Subtype.ext
  apply Lp.ext
  exact (principalEulerCylinder_memLp hN A P r σ hb).coeFn_toLp.trans
    (principalEulerCylinderLp_coeFn hN A P r σ hb).symm

/-- Every bounded local mean of the literal original cylinder class is zero. -/
theorem principalEulerCylinder_local_mean (a c : ℝ) (ha : 0<a) :
    cylinderLocalMean a c ha (principalEulerCylinderLp hN A P r σ hb)=0 := by
  let F : ℍ → ℂ := AsymptoticWeightedBranches.weighted P.ε (P.s+3) 0 (principalEulerPhysical b r σ)
  have hF : Continuous F := by
    change Continuous (fun z : ℍ => AsymptoticWeightedBranches.weighted P.ε (P.s+3) 0
      (principalEulerPhysical b r σ) z)
    simp only [weighted_zero_eq_capped]
    exact cappedEuler_continuous hb.polynomialGrowth r σ P.ε (P.s+3)
  let K := upperRectangle 0 1 a c
  have hK : IsCompact K := upperRectangle_compact 0 1 a c ha
  let rep := principalEulerCylinderRepresentative hN A P r σ hb
  let f := cuspRestriction 0 1 K hK (AutomorphicL2.denseEmbedding (gamma 0) (quotientMeasure 0) rep)
  have hf : f=ᵐ[volume.restrict K] F := by
    have hh := cuspRestriction_representative_ae 0 1 K hK rep
    filter_upwards [hh] with z hz
    change f z=rep.val (cuspAction 1 z) at hz
    simpa only [cuspAction,map_one,one_smul] using! hz
  have hm := localHeightAverage_horocycle_ae 0 1 a c (by norm_num) ha F hF f hf
  have hz (y : ℝ) : horocycleAverageExtension 0 1 a F y=0 := by
    unfold horocycleAverageExtension
    have he : (∫ x in Icc (0:ℝ) 1,F (cartesianLift (x,max a y)))=0 := by
      simpa only [F,weighted_zero_eq_capped] using
        cappedEuler_mean_zero hb.polynomialGrowth r σ P.ε (P.s+3) (max a y)
          (ha.trans_le (le_max_left _ _))
    rw [he,mul_zero]
  change cuspHeightAverage 0 1 K hK
    (cylinderAutomorphic (principalEulerCylinderLp hN A P r σ hb))=0
  rw [←principalEulerCylinderRepresentative_class hN A P r σ hb]
  change localHeightAverage K f=0
  apply Lp.ext
  filter_upwards [hm,Lp.coeFn_zero ℂ 2 (heightMeasure K)] with y hy hy0
  rw [hy,hz]
  exact hy0.symm

/-- Original Euler data lie in the genuine closed nonzero-mode cylinder
space, rather than a hypothesized or spectrally substituted solution space. -/
theorem principalEulerCylinder_nonzero_modes :
    principalEulerCylinderLp hN A P r σ hb∈cylinderNonzeroModes := by
  simp only [cylinderNonzeroModes,Submodule.mem_iInf,LinearMap.mem_ker]
  intro a c ha
  exact principalEulerCylinder_local_mean hN A P r σ hb a c ha

#print axioms principalEulerCylinderRepresentative_class
#print axioms principalEulerCylinder_local_mean
#print axioms principalEulerCylinder_nonzero_modes

end QuantitativeMaass
