module

public import QuantitativeNewGapRepeatedAllV1
public import AsymptoticQuotientLeftActionV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticQuotientOperators
open AsymptoticFreshMatrices AsymptoticRegularTrace AsymptoticPermutationInvariant
open AsymptoticCongruenceLabels
open scoped lp

def globalFrickeEquiv (N : ℕ) (hN : 0<N) : Classes (gamma N) ≃ Classes (gamma N) :=
  leftMulEquiv (gamma N) (frickeLabel N hN)
    (fun _ hg => fricke_conj_mem N hN hg)
    (by intro g hg; simpa only [frickeLabel_inv] using fricke_conj_mem N hN hg)

theorem globalFrickeEquiv_involutive (N : ℕ) (hN : 0<N) :
    Function.Involutive (globalFrickeEquiv N hN) := by
  intro q
  induction q using Quotient.inductionOn with
  | h g =>
    change classOf (gamma N) (frickeLabel N hN*(frickeLabel N hN*g))=classOf (gamma N) g
    rw [← mul_assoc,frickeLabel_mul_self,one_mul]

theorem frickeOld_mem_iff (N d : ℕ) (hN : 0<N) (g : AsymptoticRationalGroup.Group) :
    frickeLabel N hN*g*(frickeLabel N hN)⁻¹∈gamma d ↔ g∈frickeOldGroup N d hN := by
  constructor
  · intro hg
    refine ⟨frickeLabel N hN*g*(frickeLabel N hN)⁻¹,hg,?_⟩
    change frickeLabel N hN*(frickeLabel N hN*g*(frickeLabel N hN)⁻¹)*
      (frickeLabel N hN)⁻¹=g
    rw [frickeLabel_inv]
    simp only [← mul_assoc,frickeLabel_mul_self,one_mul]
    simp only [mul_assoc,frickeLabel_mul_self,mul_one]
  · rintro ⟨a,ha,rfl⟩
    change a∈gamma d at ha
    change frickeLabel N hN*(frickeLabel N hN*a*(frickeLabel N hN)⁻¹)*
      (frickeLabel N hN)⁻¹∈gamma d
    rw [frickeLabel_inv]
    simp only [← mul_assoc,frickeLabel_mul_self,one_mul]
    simpa only [mul_assoc,frickeLabel_mul_self,mul_one] using ha

/-- The actual global Fricke permutation exchanges the two old
projections at every divisor level, including repeated primes. -/
theorem globalFricke_old_swap (N d : ℕ) [NeZero N] (hN : 0<N) (hd : d∣N)
    (q r : Classes (gamma N)) :
    matrix (space (gamma_le_of_dvd hd)).starProjection
      (globalFrickeEquiv N hN q) (globalFrickeEquiv N hN r)=
    matrix (space (gamma_le_frickeOldGroup hN hd)).starProjection q r := by
  classical
  induction q using Quotient.inductionOn with
  | h g =>
    induction r using Quotient.inductionOn with
    | h k =>
      change (space (gamma_le_of_dvd hd)).starProjection
        (delta (classOf (gamma N) (frickeLabel N hN*k)))
        (classOf (gamma N) (frickeLabel N hN*g))=_
      rw [projection_matrix]
      change _=(space (gamma_le_frickeOldGroup hN hd)).starProjection
        (delta (classOf (gamma N) k)) (classOf (gamma N) g)
      rw [projection_matrix]
      have hi : ((gamma N).subgroupOf (frickeOldGroup N d hN)).index=
          ((gamma N).subgroupOf (gamma d)).index := frickeOldGroup_index N d hN
      rw [hi]
      have he : forget (gamma_le_of_dvd hd) (classOf (gamma N) (frickeLabel N hN*g))=
          forget (gamma_le_of_dvd hd) (classOf (gamma N) (frickeLabel N hN*k)) ↔
          forget (gamma_le_frickeOldGroup hN hd) (classOf (gamma N) g)=
          forget (gamma_le_frickeOldGroup hN hd) (classOf (gamma N) k) := by
        simp only [forget_classOf,classOf_eq_iff,mul_inv_rev,mul_assoc]
        simpa only [mul_assoc] using frickeOld_mem_iff N d hN (g*k⁻¹)
      exact if_congr he rfl rfl

/-- The actual local-new projection is invariant under global Fricke;
this is derived by exchanging its two old summands. -/
theorem globalFricke_new_invariant (N d : ℕ) [NeZero N] (hN : 0<N) (hd : d∣N) :
    Invariant (globalFrickeEquiv N hN)
      (newSpace (gamma_le_of_dvd hd) (gamma_le_frickeOldGroup hN hd)).starProjection := by
  let P := (space (gamma_le_of_dvd hd)).starProjection
  let Q := (space (gamma_le_frickeOldGroup hN hd)).starProjection
  have hs : Invariant (globalFrickeEquiv N hN) (P+Q) := by
    intro q r
    have h₁ := globalFricke_old_swap N d hN hd q r
    have h₂ := globalFricke_old_swap N d hN hd (globalFrickeEquiv N hN q) (globalFrickeEquiv N hN r)
    rw [globalFrickeEquiv_involutive N hN,globalFrickeEquiv_involutive N hN] at h₂
    change matrixCLM _ _ (P+Q)=matrixCLM _ _ (P+Q)
    simp only [map_add,matrixCLM_apply]
    rw [h₁,← h₂,add_comm]
  have he : P.adjoint.comp P+Q.adjoint.comp Q=P+Q := by
    have hP : P.adjoint=P := isSelfAdjoint_starProjection _
    have hQ : Q.adjoint=Q := isSelfAdjoint_starProjection _
    rw [hP,hQ]
    have hp : P.comp P=P := Submodule.isIdempotentElem_starProjection _
    have hq : Q.comp Q=Q := Submodule.isIdempotentElem_starProjection _
    rw [hp,hq]
  change Invariant _ (P.adjoint.comp P+Q.adjoint.comp Q).ker.starProjection
  simpa only [he] using invariant_kernel (globalFrickeEquiv N hN) (P+Q) hs

#print axioms globalFricke_old_swap
#print axioms globalFricke_new_invariant

end QuantitativeNewGap
