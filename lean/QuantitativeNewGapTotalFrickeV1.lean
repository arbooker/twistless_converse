module

public import QuantitativeNewGapFrickeSymmetryV1
public import QuantitativeNewGapJointProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticSubspaceIntersection AsymptoticPermutationInvariant AsymptoticPolarIsometry
open AsymptoticCongruenceStrip AsymptoticNestedQuotients
open scoped lp

theorem invariant_inter {ι : Type*} (e : ι ≃ ι) (U V : Submodule ℂ ℓ²(ι,ℂ))
    [CompleteSpace U] [CompleteSpace V] (hU : Invariant e U.starProjection)
    (hV : Invariant e V.starProjection) : Invariant e (inter U V).starProjection := by
  let A := (1 : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))-U.starProjection
  let B := (1 : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))-V.starProjection
  have hA : Invariant e A := invariant_sub e _ _ (invariant_one e) hU
  have hB : Invariant e B := invariant_sub e _ _ (invariant_one e) hV
  have he : inter U V=(A.adjoint.comp A+B.adjoint.comp B).ker := by
    ext w
    rw [inter_mem,AsymptoticJointKernel.mem_ker_gram_add]
    change (w∈U ∧ w∈V) ↔ w-U.starProjection w=0 ∧ w-V.starProjection w=0
    rw [sub_eq_zero,sub_eq_zero]
    exact and_congr (U.starProjection_eq_self_iff.symm.trans eq_comm)
      (V.starProjection_eq_self_iff.symm.trans eq_comm)
  rw [starProjection_congr _ _ he]
  exact invariant_kernel e _ (invariant_add e _ _
    (invariant_comp e _ _ (invariant_adjoint e _ hA) hA)
    (invariant_comp e _ _ (invariant_adjoint e _ hB) hB))

theorem invariant_jointListSpace {ι κ : Type*} (e : ι ≃ ι)
    (V : κ → Submodule ℂ ℓ²(ι,ℂ)) [∀ i,CompleteSpace (V i)]
    (hV : ∀ i,Invariant e (V i).starProjection) (l : List κ) :
    Invariant e (jointListSpace V l).starProjection := by
  induction l with
  | nil =>
    let : CompleteSpace (⊤ : Submodule ℂ ℓ²(ι,ℂ)) := by
      change CompleteSpace (Set.univ : Set ℓ²(ι,ℂ))
      exact completeSpace_coe_iff_isComplete.mpr isComplete_univ
    rw [starProjection_congr _ _ (jointListSpace_nil V),Submodule.starProjection_top]
    exact invariant_one e
  | cons i l ih =>
    rw [starProjection_congr _ _ (jointListSpace_cons V i l)]
    exact invariant_inter e _ _ (hV i) ih

theorem totalNewSpace_eq_jointList (N : ℕ) (hN : 0<N) :
    AsymptoticTotalNewCorner.space N hN=
      jointListSpace (AsymptoticTotalNewCorner.localSpace N hN) N.primeFactors.toList := by
  classical
  ext w
  rw [AsymptoticTotalNewCorner.space,Submodule.mem_iInf,jointListSpace_mem]
  constructor
  · exact fun hw p _ => hw p
  · intro hw p
    by_cases hp : p.Prime ∧ p∣N
    · exact hw p (by simpa only [Finset.mem_toList,Nat.mem_primeFactors] using ⟨hp.1,hp.2,hN.ne'⟩)
    · simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_right hp,Submodule.mem_top]

/-- Every actual prime-local new projector, including repeated primes,
is preserved by the actual global Fricke permutation. -/
theorem globalFricke_localNew_invariant (N : ℕ) (hN : 0<N) (p : ℕ) :
    Invariant (globalFrickeEquiv N hN) (AsymptoticTotalNewCorner.localSpace N hN p).starProjection := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  by_cases hp : p.Prime ∧ p∣N
  · have he : AsymptoticTotalNewCorner.localSpace N hN p=
        AsymptoticQuotientOperators.newSpace (gamma_le_of_dvd (Nat.div_dvd_of_dvd hp.2))
          (gamma_le_frickeOldGroup hN (Nat.div_dvd_of_dvd hp.2)) := by
      simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_left hp]
    rw [starProjection_congr _ _ he]
    exact globalFricke_new_invariant N (N/p) hN (Nat.div_dvd_of_dvd hp.2)
  · have he : AsymptoticTotalNewCorner.localSpace N hN p=⊤ := by
      simp only [AsymptoticTotalNewCorner.localSpace,dite_eq_right hp]
    rw [starProjection_congr _ _ he,Submodule.starProjection_top]
    exact invariant_one _

/-- Global Fricke preserves the literal joint new projector over all
prime divisors, without assuming pairwise commutation of local corners. -/
theorem globalFricke_totalNew_invariant (N : ℕ) (hN : 0<N) :
    Invariant (globalFrickeEquiv N hN) (AsymptoticTotalNewCorner.space N hN).starProjection := by
  rw [starProjection_congr _ _ (totalNewSpace_eq_jointList N hN)]
  exact invariant_jointListSpace _ _ (globalFricke_localNew_invariant N hN) _

#print axioms totalNewSpace_eq_jointList
#print axioms globalFricke_localNew_invariant
#print axioms globalFricke_totalNew_invariant

end QuantitativeNewGap
