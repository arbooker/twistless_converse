module

public import QuantitativeMaassAmbientSectorExpressionV1
public import QuantitativeMaassParityWindowV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open ContinuousLinearMap QuantitativeNinaMaass AsymptoticSectorSigns QuantitativeNewGap
namespace QuantitativeMaass

theorem clm_commute_smul_right {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (R A : H→L[ℂ]H) (h : Commute R A) (c : ℂ) : Commute R (c • A) := by
  change R.comp (c • A)=(c • A).comp R
  rw [comp_smul,smul_comp,show R.comp A=A.comp R from h.eq]

theorem clm_commute_sub_right {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (R A B : H→L[ℂ]H) (hA : Commute R A) (hB : Commute R B) : Commute R (A-B) := by
  change R.comp (A-B)=(A-B).comp R
  rw [comp_sub,sub_comp,show R.comp A=A.comp R from hA.eq,show R.comp B=B.comp R from hB.eq]

theorem ambient_cover_trace_reflection {M N : ℕ} [NeZero N] (hMN : M∣N) :
    Commute (reflectionIsometry N).toContinuousLinearMap
      ((levelCover hMN).comp (levelTrace hMN)) := by
  apply ContinuousLinearMap.ext
  intro x
  change reflectionIsometry N (levelCover hMN (levelTrace hMN x)) =
    levelCover hMN (levelTrace hMN (reflectionIsometry N x))
  rw [levelCover_reflection,levelTrace_reflection]

theorem ambient_fricke_reflection (N : ℕ) (hN : 0<N) :
    Commute (reflectionIsometry N).toContinuousLinearMap
      (frickeIsometry N hN).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  exact (frickeIsometry_reflection N hN x).symm

theorem ambientDivisorOldPair_reflection {M N : ℕ} [NeZero N]
    (hN : 0<N) (hMN : M∣N) :
    Commute (reflectionIsometry N).toContinuousLinearMap (ambientDivisorOldPair hN hMN) := by
  have hB := ambient_cover_trace_reflection hMN
  have hW := ambient_fricke_reflection N hN
  exact hB.add_right (hW.mul_right (hB.mul_right hW))

theorem ambientSimpleNewFilter_reflection {M N : ℕ} [NeZero N]
    (hN : 0<N) (hMN : M∣N) (p m : ℕ) :
    Commute (reflectionIsometry N).toContinuousLinearMap (ambientSimpleNewFilter hN hMN p m) := by
  let R := (reflectionIsometry N).toContinuousLinearMap
  have hb := clm_commute_smul_right R _
    (clm_commute_smul_right R _ (ambientDivisorOldPair_reflection hN hMN)
      (((((p:ℝ)+1)⁻¹:ℝ):ℂ))) (1/2:ℂ)
  exact (clm_commute_sub_right R 1 _ (Commute.one_right R) hb).pow_right m


theorem ambientRepeatedTwoNewFilter_reflection {M N : ℕ} [NeZero N]
    (hN : 0<N) (hMN : M∣N) :
    Commute (reflectionIsometry N).toContinuousLinearMap (ambientRepeatedTwoNewFilter hN hMN) := by
  let R := (reflectionIsometry N).toContinuousLinearMap
  let B := (levelCover hMN).comp (levelTrace hMN)-1
  let W := (frickeIsometry N hN).toContinuousLinearMap
  let U := B+W.comp (B.comp W)
  have hB : Commute R B := clm_commute_sub_right R _ 1
    (ambient_cover_trace_reflection hMN) (Commute.one_right R)
  have hW : Commute R W := ambient_fricke_reflection N hN
  have hU : Commute R U := hB.add_right (hW.mul_right (hB.mul_right hW))
  exact clm_commute_smul_right R _
    ((clm_commute_sub_right R _ _
      (clm_commute_sub_right R _ _ (hU.pow_right 4)
        (clm_commute_smul_right R _ (hU.pow_right 3) (2:ℂ)))
      (hU.pow_right 2)).add_right (clm_commute_smul_right R _ hU (2:ℂ))) (1/24:ℂ)

theorem ambientLocalNewFilter_reflection (N : ℕ) [NeZero N] (hN : 0<N)
    (m : ℕ) (p : ↥N.primeFactors) :
    Commute (reflectionIsometry N).toContinuousLinearMap (ambientAdmissibleLocalNewFilter N hN m p) := by
  classical
  unfold ambientAdmissibleLocalNewFilter
  split
  · exact ambientRepeatedTwoNewFilter_reflection hN _
  · exact ambientSimpleNewFilter_reflection hN _ _ _

theorem ambientSignFactor_reflection (N : ℕ) (hN : 0<N)
    (e : Sector N) (i : SectorSignIndex N) :
    Commute (reflectionIsometry N).toContinuousLinearMap (ambientSectorSignFactor N hN e i) := by
  have hr : Commute (reflectionIsometry N).toContinuousLinearMap (completedSectorNormalizer N hN i) := by
    apply ContinuousLinearMap.ext
    intro x
    have hh := sectorNormalizerGroup_reflection N hN i x
    change (quotientNormalizerPullback N (sectorNormalizerGroup N hN i)).toContinuousLinearMap
        (reflectionIsometry N x) = reflectionIsometry N
        ((quotientNormalizerPullback N (sectorNormalizerGroup N hN i)).toContinuousLinearMap x) at hh
    rw [sectorNormalizerGroup_action] at hh
    exact hh.symm
  exact clm_commute_smul_right _ _ ((Commute.one_right _).add_right
    (clm_commute_smul_right _ _ hr (sectorNormalizerSign e i:ℂ))) (1/2:ℂ)

/-- The literal full-quotient polynomial preserves geometric parity,
without restricting its input to cusp forms or to a spectral band. -/
theorem ambientSectorNewFilter_reflection (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (m : ℕ) :
    Commute (reflectionIsometry N).toContinuousLinearMap (ambientSectorNewFilter N hN e m) := by
  have hn : Commute (reflectionIsometry N).toContinuousLinearMap (ambientAdmissibleTotalNewFilter N hN m) := by
    apply Commute.list_prod_right
    intro A hA
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
    exact ambientLocalNewFilter_reflection N hN m p
  have hs : Commute (reflectionIsometry N).toContinuousLinearMap (ambientSectorSignProduct N hN e) := by
    apply Commute.list_prod_right
    intro A hA
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hA
    exact ambientSignFactor_reflection N hN e i
  exact hn.mul_right hs

theorem ambientSectorNewFilter_parity (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (m : ℕ) (σ : ℝ) :
    Commute (parityProjection N σ) (ambientSectorNewFilter N hN e m) :=
  parityProjection_commute N σ _ (ambientSectorNewFilter_reflection N hN e m)

#print axioms ambientDivisorOldPair_reflection
#print axioms ambientRepeatedTwoNewFilter_reflection
#print axioms ambientSectorNewFilter_reflection
#print axioms ambientSectorNewFilter_parity

end QuantitativeMaass
