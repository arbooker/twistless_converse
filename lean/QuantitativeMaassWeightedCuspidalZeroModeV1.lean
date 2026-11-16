module

public import QuantitativeMaassWeightedCuspMeanV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCompactBranch
open QuantitativeNinaMaass QuantitativeArithmeticMaassCuspBand

namespace QuantitativeMaass

theorem weighted_cuspidal_local_mean (N : ℕ) (hN : 0<N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) (hc : AutomorphicL2.denseEmbedding _ _ f∈localCuspidalSpace N hN)
    (a b : ℝ) (ha : 0<a) :
    cylinderLocalMean a b ha (weightedQuotientRepresentative N hε hv f)=0 := by
  let F : ℍ → ℂ := fun z => (cappedHeightWeight ε v z:ℂ)*f.val z
  have hF : Continuous F := (Complex.continuous_ofReal.comp (cap_continuous ε v)).mul hf
  let K := upperRectangle 0 1 a b
  have hK : IsCompact K := upperRectangle_compact 0 1 a b ha
  let rep := weightedCylinderRepresentative N hε hv f
  let u := cuspRestriction 0 1 K hK (AutomorphicL2.denseEmbedding _ _ rep)
  have hu : u=ᵐ[volume.restrict K] F := by
    filter_upwards [cuspRestriction_representative_ae 0 1 K hK rep] with z hz
    change u z=rep.val (cuspAction 1 z) at hz
    simpa only [cuspAction,map_one,one_smul] using! hz
  have hm := localHeightAverage_horocycle_ae 0 1 a b (by norm_num) ha F hF u hu
  have hz (y : ℝ) : horocycleAverageExtension 0 1 a F y=0 := by
    unfold horocycleAverageExtension
    have he : (∫ x in Icc (0:ℝ) 1,F (cartesianLift (x,max a y)))=0 :=
      weighted_cuspidal_unit_mean N hN f hf hc ε v (max a y) (ha.trans_le (le_max_left _ _))
    rw [he,mul_zero]
  change cuspHeightAverage 0 1 K hK
    (cylinderAutomorphic (weightedQuotientRepresentative N hε hv f))=0
  rw [←weightedCylinderRepresentative_class N hε hv f]
  change localHeightAverage K u=0
  apply Lp.ext
  filter_upwards [hm,Lp.coeFn_zero ℂ 2 (heightMeasure K)] with y hy hy0
  rw [hy,hz]
  exact hy0.symm

/-- Every canonical cuspidal Hilbert vector embeds into the genuine
nonzero-mode cylinder space. Continuous eigenvectors are used only through
the already constructed complete geometric basis. -/
theorem weightedQuotientEmbedding_cuspidal_nonzero (N : ℕ) (hN : 0<N)
    {ε : ℝ} (hε : 0<ε) {v : ℕ} (hv : 1≤v)
    (x : AutomorphicSpace N) (hx : x∈localCuspidalSpace N hN) :
    weightedQuotientEmbedding N hε hv x∈cylinderNonzeroModes := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨κ,basis,e,henergy,hgraph,_⟩ := exists_cuspidal_energy_basis N hN
  have hgen (j : κ) : weightedQuotientEmbedding N hε hv (basis j : AutomorphicSpace N)∈
      cylinderNonzeroModes := by
    obtain ⟨f,hf,heq⟩ := exists_continuous_eigen_representative N
      (basis j : AutomorphicSpace N) (e j) (henergy j) (hgraph j)
    rw [←heq,weightedQuotientEmbedding_representative]
    have hc : AutomorphicL2.denseEmbedding _ _ f∈localCuspidalSpace N hN := by
      rw [heq]
      exact (basis j).property
    simp only [cylinderNonzeroModes,Submodule.mem_iInf,LinearMap.mem_ker]
    intro a b ha
    exact weighted_cuspidal_local_mean N hN hε hv f hf hc a b ha
  let L := (weightedQuotientEmbedding N hε hv).comp (localCuspidalSpace N hN).subtypeL
  have hs := L.hasSum (basis.hasSum_repr ⟨x,hx⟩)
  apply cylinderNonzeroModes_closed.mem_of_tendsto hs
  apply Eventually.of_forall
  intro S
  apply Submodule.sum_mem
  intro j _
  change weightedQuotientEmbedding N hε hv
    ((basis.repr ⟨x,hx⟩ j) • (basis j : AutomorphicSpace N))∈_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (hgen j)

#print axioms weighted_cuspidal_local_mean
#print axioms weightedQuotientEmbedding_cuspidal_nonzero

end QuantitativeMaass
