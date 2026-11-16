module

public import QuantitativeMaassCompletedSectorNormalizersV1
public import QuantitativeMaassInvolutionSignProjectionV1
public import QuantitativeNewGapSectorSpaceV1
public import QuantitativeMaassSectorCharacterChoiceV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson AsymptoticSectorSigns AsymptoticSubspaceIntersection
open QuantitativeNinaMaass QuantitativeNewGap
namespace QuantitativeMaass

def completedSectorSignConstraint (N : ℕ) (hN : 0<N) (e : Sector N) (i : SectorSignIndex N) :
    Submodule ℂ (AutomorphicSpace N) :=
  involutionSignSpace (completedSectorNormalizer N hN i) (sectorNormalizerSign e i)
instance (N : ℕ) (hN : 0<N) (e : Sector N) (i : SectorSignIndex N) :
    CompleteSpace (completedSectorSignConstraint N hN e i) := inferInstanceAs
      (CompleteSpace (involutionSignSpace (completedSectorNormalizer N hN i) (sectorNormalizerSign e i)))

theorem completedSectorSignProjections_commute (N : ℕ) (hN : 0<N) (e : Sector N)
    (i j : SectorSignIndex N) :
    Commute (completedSectorSignConstraint N hN e i).starProjection
      (completedSectorSignConstraint N hN e j).starProjection :=
  involutionSignProjections_commute _ _ (completedSectorNormalizer_selfAdjoint N hN i)
    (completedSectorNormalizer_selfAdjoint N hN j) (completedSectorNormalizers_commute N hN i j) _ _

theorem completedNew_sectorSign_commute (N : ℕ) [NeZero N] (hN : 0<N)
    (e : Sector N) (i : SectorSignIndex N) :
    Commute (completedCuspidalNewSpace N hN).starProjection
      (completedSectorSignConstraint N hN e i).starProjection :=
  subspace_involutionSign_commute _ _ (completedSectorNormalizer_selfAdjoint N hN i)
    (completedSectorNormalizer_new_commute N hN i) _

/-- The actual cuspidal-new sector defined by the finite original Fricke
and simple-prime sign equations. -/
def completedCountingSectorSpace (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N) :
    Submodule ℂ (AutomorphicSpace N) :=
  inter (completedCuspidalNewSpace N hN)
    (jointListSpace (completedSectorSignConstraint N hN e) (Finset.univ : Finset (SectorSignIndex N)).toList)
instance (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N) :
    CompleteSpace (completedCountingSectorSpace N hN e) := inferInstanceAs
      (CompleteSpace (inter (completedCuspidalNewSpace N hN)
        (jointListSpace (completedSectorSignConstraint N hN e) (Finset.univ : Finset (SectorSignIndex N)).toList)))

theorem completedCountingSectorSpace_mem (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N)
    (x : AutomorphicSpace N) :
    x∈completedCountingSectorSpace N hN e ↔ x∈completedCuspidalNewSpace N hN ∧
      ∀ i : SectorSignIndex N,completedSectorNormalizer N hN i x=(sectorNormalizerSign e i:ℂ) • x := by
  rw [completedCountingSectorSpace,inter_mem,jointListSpace_mem]
  simp only [Finset.mem_toList,Finset.mem_univ,forall_true_left,completedSectorSignConstraint,
    involutionSignSpace,LinearMap.mem_ker,ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_smul,ContinuousLinearMap.toLinearMap_one,
    LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,sub_eq_zero]
  rfl

theorem completedNew_jointSigns_commute (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N) :
    Commute (completedCuspidalNewSpace N hN).starProjection
      (jointListSpace (completedSectorSignConstraint N hN e)
        (Finset.univ : Finset (SectorSignIndex N)).toList).starProjection := by
  rw [jointListSpace_projection _ (completedSectorSignProjections_commute N hN e)]
  apply Commute.list_prod_right
  intro T hT
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hT
  exact completedNew_sectorSign_commute N hN e i

/-- Exact finite product for the physical sector projector, retaining the
actual cuspidal-new projection as its first factor. -/
theorem completedCountingSectorSpace_projection (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N) :
    (completedCountingSectorSpace N hN e).starProjection=
      (completedCuspidalNewSpace N hN).starProjection.comp
        (((Finset.univ : Finset (SectorSignIndex N)).toList.map fun i =>
          (completedSectorSignConstraint N hN e i).starProjection).prod) := by
  change (inter (completedCuspidalNewSpace N hN)
    (jointListSpace (completedSectorSignConstraint N hN e)
      (Finset.univ : Finset (SectorSignIndex N)).toList)).starProjection=_
  rw [inter_projection_of_commute _ _ (completedNew_jointSigns_commute N hN e),
    jointListSpace_projection _ (completedSectorSignProjections_commute N hN e)]

/-- Every canonical generator sector belongs to its original finite sign sector. -/
theorem completedNewSign_le_countingSector (N : ℕ) [NeZero N] (hN : 0<N) (e : Sector N) :
    completedNewSignSpace N hN (sectorCharacter N hN e)≤completedCountingSectorSpace N hN e := by
  intro x hx
  apply (completedCountingSectorSpace_mem N hN e x).mpr
  refine ⟨⟨hx.1,hx.2.1⟩,?_⟩
  intro i
  cases i with
  | none =>
    have hh := hx.2.2 (frickeGeneratorIndex N hN)
    rw [(sectorCharacter_coherent N hN e).1] at hh
    change frickeIsometry N hN x=sign e.1 • x at hh
    change frickeIsometry N hN x=(signReal e.1:ℂ) • x
    rw [signReal_coe]
    exact hh
  | some p =>
    have hh := hx.2.2 (simpleAtkinGeneratorIndex N hN p)
    have hi : admissibleGeneratorLift N hN (simpleAtkinGeneratorIndex N hN p)=
        completedLocalAtkinNormalizer N hN p := Subtype.ext (simpleAtkinGeneratorIndex_value N hN p)
    rw [hi,(sectorCharacter_coherent N hN e).2 p] at hh
    change quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p) x=
      ((-signReal (e.2 p):ℝ):ℂ) • x
    rw [Complex.ofReal_neg,signReal_coe]
    simpa only [delta,dite_eq_left p.property] using hh

#print axioms completedSectorSignProjections_commute
#print axioms completedNew_sectorSign_commute
#print axioms completedCountingSectorSpace_mem
#print axioms completedNew_jointSigns_commute
#print axioms completedCountingSectorSpace_projection
#print axioms completedNewSign_le_countingSector
end QuantitativeMaass
