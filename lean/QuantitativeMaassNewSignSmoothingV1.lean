module

public import QuantitativeMaassCompletedNewSignPacketV1
public import QuantitativeMaassAllLevelAbelInitialV1
public import QuantitativeMaassAbelColumnContinuityV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeNinaMaass
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem abelNormalizedOperator_continuous_representative (N : ℕ) [NeZero N]
    (R : ℝ) (hR : 0<R) (x : AutomorphicSpace N) :
    ∃ f : AutomorphicL2.representatives (gamma N) (quotientMeasure N),
      Continuous f.val ∧ AutomorphicL2.denseEmbedding _ _ f=AllLevel.abelNormalizedOperator N R hR x := by
  let F := abelNormalizedTest R
  let u : ℍ → ℂ := fun z => ∫ y,radialPoincareKernel N (abelProfile F) z y*x.val y ∂quotientMeasure N
  have hu : Continuous u := oneSidedAbelKernel_output_continuous N F
    (abelNormalizedTest_smooth R).contDiffOn (abelNormalizedTest_real R)
    R hR.le (abelNormalizedTest_support R hR) x
  have hi (γ : gamma N) (z : ℍ) : u (γ • z)=u z :=
    radialKernel_output_invariant N (abelNormalizedProfile R)
      (abelNormalizedProfile_smooth R hR) R hR.le (abelNormalizedProfile_support R hR) x.val γ z
  have he : ((AllLevel.abelNormalizedOperator N R hR x).val : ℍ → ℂ)=ᵐ[quotientMeasure N] u :=
    AllLevel.radialKernelOperator_coeFn N (abelNormalizedProfile R)
      (abelNormalizedProfile_smooth R hR) R hR.le (abelNormalizedProfile_support R hR) x
  have hm : u∈AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
    ⟨hu.measurable,hi,(memLp_congr_ae he).mp (Lp.memLp (AllLevel.abelNormalizedOperator N R hR x).val)⟩
  refine ⟨⟨u,hm⟩,hu,?_⟩
  apply Subtype.ext
  apply Lp.ext
  exact hm.2.2.coeFn_toLp.trans he.symm

theorem completedNewSignSpace_abelNormalized (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ) (R : ℝ) (hR : 0<R)
    (x : AutomorphicSpace N) (hx : x∈completedNewSignSpace N hN χ) :
    AllLevel.abelNormalizedOperator N R hR x∈completedNewSignSpace N hN χ := by
  have he : AllLevel.abelNormalizedOperator N R hR=
      coshWavePacket N (abelNormalizedTest R) (abelNormalizedTest_smooth R)
        R hR.le (abelNormalizedTest_support R hR) :=
    AllLevel.abelKernelOperator_eq_coshWavePacket N (abelNormalizedTest R)
      (abelNormalizedTest_smooth R) (abelNormalizedTest_compact R hR)
      (abelNormalizedTest_real R) R hR.le (abelNormalizedTest_support R hR)
  refine ⟨?_,?_,?_⟩
  · rw [he]
    exact shiftedQuotientWavePacket_mem_localCuspidalSpace N hN _ _ x hx.1
  · rw [he]
    exact actualNewSpace_timePacket N hN _ _ x hx.2.1
  · intro i
    change quotientNormalizerPullback N (admissibleGeneratorLift N hN i)
      (AllLevel.radialKernelOperator N (abelNormalizedProfile R) (abelNormalizedProfile_smooth R hR)
        R hR.le (abelNormalizedProfile_support R hR) x)=χ i • _
    rw [quotientNormalizerPullback_radial,hx.2.2 i,map_smul]
    rfl

/-- Continuous representatives are dense inside the actual completed
new/sign space, because the normalized geometric smoothing preserves it. -/
theorem completedNewSignSpace_continuous_approximation (N : ℕ) [NeZero N] (hN : 0<N)
    (χ : admissibleGeneratorIndex N hN → ℂ)
    (x : AutomorphicSpace N) (hx : x∈completedNewSignSpace N hN χ) :
    ∃ f : ℕ → AutomorphicL2.representatives (gamma N) (quotientMeasure N),
      (∀ n,Continuous (f n).val) ∧
      (∀ n,AutomorphicL2.denseEmbedding _ _ (f n)∈completedNewSignSpace N hN χ) ∧
      Tendsto (fun n => AutomorphicL2.denseEmbedding _ _ (f n)) atTop (𝓝 x) := by
  let R : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hR (n : ℕ) : 0<R n := by dsimp only [R]; positivity
  choose f hf he using fun n => abelNormalizedOperator_continuous_representative N (R n) (hR n) x
  refine ⟨f,hf,?_,?_⟩
  · intro n
    rw [he]
    exact completedNewSignSpace_abelNormalized N hN χ (R n) (hR n) x hx
  · simp_rw [he]
    exact AllLevel.abelNormalizedOperator_tendsto atTop N R hR
      tendsto_one_div_add_atTop_nhds_zero_nat x

#print axioms abelNormalizedOperator_continuous_representative
#print axioms completedNewSignSpace_abelNormalized
#print axioms completedNewSignSpace_continuous_approximation

end QuantitativeMaass
