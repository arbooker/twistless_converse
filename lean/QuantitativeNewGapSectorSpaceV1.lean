module

public import QuantitativeNewGapLocalInvarianceV1
public import QuantitativeNewGapSignCommutationV1
public import QuantitativeNewGapFrickeSignGapV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticNestedQuotients AsymptoticCongruenceStrip AsymptoticSectorSigns
open AsymptoticSubspaceIntersection
open scoped lp

abbrev SectorSignIndex (N : ℕ) := Option (SimplePrime N)

def sectorNormalizer (N : ℕ) (hN : 0<N) : SectorSignIndex N → Classes (gamma N) ≃ Classes (gamma N)
  | none => globalFrickeEquiv N hN
  | some p => localAtkinEquiv N hN p

def signReal (b : Bool) : ℝ := if b then 1 else -1

theorem signReal_sq (b : Bool) : signReal b^2=1 := by cases b <;> norm_num [signReal]

theorem signReal_coe (b : Bool) : (signReal b:ℂ)=sign b := by cases b <;> simp [signReal,sign]

def sectorNormalizerSign {N : ℕ} (e : Sector N) : SectorSignIndex N → ℝ
  | none => signReal e.1
  | some p => -signReal (e.2 p)

theorem sectorNormalizerSign_sq {N : ℕ} (e : Sector N) (i : SectorSignIndex N) :
    sectorNormalizerSign e i^2=1 := by
  cases i with
  | none => exact signReal_sq _
  | some p => simpa only [sectorNormalizerSign,neg_sq] using signReal_sq (e.2 p)

theorem sectorNormalizer_involutive (N : ℕ) (hN : 0<N) (i : SectorSignIndex N) :
    Function.Involutive (sectorNormalizer N hN i) := by
  cases i with
  | none => exact globalFrickeEquiv_involutive N hN
  | some p => exact localAtkinEquiv_involutive N hN p

theorem sectorNormalizers_commute (N : ℕ) (hN : 0<N) (i j : SectorSignIndex N) :
    Function.Commute (sectorNormalizer N hN i) (sectorNormalizer N hN j) := by
  cases i with
  | none =>
    cases j with
    | none => intro q; rfl
    | some p => exact (localAtkin_globalFricke_commute N hN p).symm
  | some p =>
    cases j with
    | none => exact localAtkin_globalFricke_commute N hN p
    | some q => exact localAtkinEquivs_commute N hN p q

def sectorSignConstraint (N : ℕ) (hN : 0<N) (e : Sector N) (i : SectorSignIndex N) :
    Submodule ℂ ℓ²(Classes (gamma N),ℂ) :=
  permutationSignSpace (sectorNormalizer N hN i) (sectorNormalizerSign e i)

instance sectorSignConstraint_complete (N : ℕ) (hN : 0<N) (e : Sector N) (i : SectorSignIndex N) :
    CompleteSpace (sectorSignConstraint N hN e i) := inferInstanceAs
      (CompleteSpace (permutationSignSpace (sectorNormalizer N hN i) (sectorNormalizerSign e i)))

theorem sectorSignProjections_commute (N : ℕ) (hN : 0<N) (e : Sector N) (i j : SectorSignIndex N) :
    Commute (sectorSignConstraint N hN e i).starProjection (sectorSignConstraint N hN e j).starProjection :=
  permutationSignProjections_commute _ _ (sectorNormalizer_involutive N hN i)
    (sectorNormalizer_involutive N hN j) (sectorNormalizers_commute N hN i j) _ _

theorem totalNew_sectorSign_commute (N : ℕ) (hN : 0<N) (e : Sector N) (i : SectorSignIndex N) :
    Commute (AsymptoticTotalNewCorner.space N hN).starProjection (sectorSignConstraint N hN e i).starProjection := by
  cases i with
  | none => exact globalFricke_totalNew_sign_commute N hN _
  | some p => exact localAtkin_totalNew_sign_commute N hN p _

def countingSectorSpace (N : ℕ) (hN : 0<N) (e : Sector N) :
    Submodule ℂ ℓ²(Classes (gamma N),ℂ) :=
  inter (AsymptoticTotalNewCorner.space N hN)
    (jointListSpace (sectorSignConstraint N hN e) (Finset.univ : Finset (SectorSignIndex N)).toList)

instance countingSectorSpace_complete (N : ℕ) (hN : 0<N) (e : Sector N) :
    CompleteSpace (countingSectorSpace N hN e) := inferInstanceAs (CompleteSpace
      (inter (AsymptoticTotalNewCorner.space N hN)
        (jointListSpace (sectorSignConstraint N hN e) (Finset.univ : Finset (SectorSignIndex N)).toList)))

theorem countingSectorSpace_mem (N : ℕ) (hN : 0<N) (e : Sector N)
    (f : ℓ²(Classes (gamma N),ℂ)) :
    f∈countingSectorSpace N hN e ↔ f∈AsymptoticTotalNewCorner.space N hN ∧
      ∀ i : SectorSignIndex N,permutationOperator (sectorNormalizer N hN i) f=
        (sectorNormalizerSign e i:ℂ) • f := by
  rw [countingSectorSpace,inter_mem,jointListSpace_mem]
  simp only [Finset.mem_toList,Finset.mem_univ,forall_true_left,sectorSignConstraint,
    permutationSignSpace,LinearMap.mem_ker,ContinuousLinearMap.toLinearMap_sub,ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.toLinearMap_one,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,sub_eq_zero]
  rfl

theorem totalNew_jointSectorSigns_commute (N : ℕ) (hN : 0<N) (e : Sector N) :
    Commute (AsymptoticTotalNewCorner.space N hN).starProjection
      (jointListSpace (sectorSignConstraint N hN e)
        (Finset.univ : Finset (SectorSignIndex N)).toList).starProjection := by
  rw [jointListSpace_projection _ (sectorSignProjections_commute N hN e)]
  apply Commute.list_prod_right
  intro T hT
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hT
  exact totalNew_sectorSign_commute N hN e i

#print axioms sectorSignProjections_commute
#print axioms totalNew_sectorSign_commute
#print axioms countingSectorSpace_mem

end QuantitativeNewGap
