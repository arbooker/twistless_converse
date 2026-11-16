module

public import QuantitativeMaassCountingGramExpressionV1
public import QuantitativeNewGapNewCommutationV1
public import QuantitativeArithmeticCrossPrimeV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open QuantitativeNewGap AsymptoticSectorSigns AsymptoticSubspaceIntersection
open AsymptoticPolarIsometry AsymptoticCongruenceStrip
namespace QuantitativeMaass.Counting

/-- The arithmetic permutability identities apply directly to the prime
factors in the ordered product. -/
theorem primeLocalProjections_commute (N : ℕ) (hN : 0<N) (p q : ↥N.primeFactors) :
    Commute (AsymptoticTotalNewCorner.localSpace N hN p.val).starProjection
      (AsymptoticTotalNewCorner.localSpace N hN q.val).starProjection := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  by_cases hpq : p.val=q.val
  · rw [hpq]
  have hp : p.val.Prime ∧ p.val∣N :=
    ⟨Nat.prime_of_mem_primeFactors p.property,Nat.dvd_of_mem_primeFactors p.property⟩
  have hq : q.val.Prime ∧ q.val∣N :=
    ⟨Nat.prime_of_mem_primeFactors q.property,Nat.dvd_of_mem_primeFactors q.property⟩
  have hep : AsymptoticTotalNewCorner.localSpace N hN p.val=
      AsymptoticQuotientOperators.newSpace (gamma_le_of_dvd (Nat.div_dvd_of_dvd hp.2))
        (gamma_le_frickeOldGroup hN (Nat.div_dvd_of_dvd hp.2)) := by
    simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_left hp]
  have heq : AsymptoticTotalNewCorner.localSpace N hN q.val=
      AsymptoticQuotientOperators.newSpace (gamma_le_of_dvd (Nat.div_dvd_of_dvd hq.2))
        (gamma_le_frickeOldGroup hN (Nat.div_dvd_of_dvd hq.2)) := by
    simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_left hq]
  rw [starProjection_congr _ _ hep,starProjection_congr _ _ heq]
  exact new_projections_commute_of_permutable _ _ _ _
    (QuantitativeArithmeticCrossPrime.first_first_permute N p.val q.val hN hp.1 hq.1 hp.2 hq.2 hpq)
    (QuantitativeArithmeticCrossPrime.first_second_permute N p.val q.val hN hp.1 hq.1 hp.2 hq.2 hpq)
    (QuantitativeArithmeticCrossPrime.second_first_permute N p.val q.val hN hp.1 hq.1 hp.2 hq.2 hpq)
    (QuantitativeArithmeticCrossPrime.second_second_permute N p.val q.val hN hp.1 hq.1 hp.2 hq.2 hpq)

/-- The limiting prime-local product is the actual common new-space
projection, including the empty product at level one. -/
theorem localProjection_product (N : ℕ) (hN : 0<N) :
    (((Finset.univ : Finset ↥N.primeFactors).toList).map
      (fun p => (AsymptoticTotalNewCorner.localSpace N hN p.val).starProjection)).prod=
      (AsymptoticTotalNewCorner.space N hN).starProjection := by
  classical
  let V := fun p : ↥N.primeFactors => AsymptoticTotalNewCorner.localSpace N hN p.val
  let L := (Finset.univ : Finset ↥N.primeFactors).toList
  have he : jointListSpace V L=AsymptoticTotalNewCorner.space N hN := by
    ext x
    rw [jointListSpace_mem,AsymptoticTotalNewCorner.space,Submodule.mem_iInf]
    simp only [L,Finset.mem_toList,Finset.mem_univ,forall_true_left]
    constructor
    · intro hx q
      by_cases hq : q.Prime ∧ q∣N
      · exact hx ⟨q,Nat.mem_primeFactors.mpr ⟨hq.1,hq.2,hN.ne'⟩⟩
      · simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_right hq,Submodule.mem_top]
    · intro hx p
      exact hx p.val
  rw [←starProjection_congr _ _ he,jointListSpace_projection V
    (primeLocalProjections_commute N hN) L]

theorem signProduct_projection (N : ℕ) (hN : 0<N) (e : Sector N) :
    signProduct N hN e=
      (jointListSpace (sectorSignConstraint N hN e)
        (Finset.univ : Finset (SectorSignIndex N)).toList).starProjection := by
  rw [jointListSpace_projection _ (sectorSignProjections_commute N hN e)]
  rw [signProduct,show signFactor N hN e=
    (fun i => (sectorSignConstraint N hN e i).starProjection) from
      funext (signFactor_projection N hN e)]

theorem signProduct_norm (N : ℕ) (hN : 0<N) (e : Sector N) :
    ‖signProduct N hN e‖≤1 := by
  rw [signProduct_projection]
  exact Submodule.starProjection_norm_le _

/-- The limiting local-new and sign product is the original counting
sector projection, with its actual signs and normalizers. -/
theorem countingSector_projection (N : ℕ) (hN : 0<N) (e : Sector N) :
    (countingSectorSpace N hN e).starProjection=
      (AsymptoticTotalNewCorner.space N hN).starProjection.comp (signProduct N hN e) := by
  change (inter (AsymptoticTotalNewCorner.space N hN)
    (jointListSpace (sectorSignConstraint N hN e)
      (Finset.univ : Finset (SectorSignIndex N)).toList)).starProjection=_
  rw [inter_projection_of_commute _ _
    (totalNew_jointSectorSigns_commute N hN e),signProduct_projection]

#print axioms primeLocalProjections_commute
#print axioms localProjection_product
#print axioms signProduct_projection
#print axioms countingSector_projection
end QuantitativeMaass.Counting
