module

public import QuantitativeNewGapTotalFrickeV1
public import QuantitativeNewGapNewCommutationV1
public import QuantitativeMaassTreeOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeNewGap

open AsymptoticRegularTrace AsymptoticPermutationInvariant QuantitativeMaass
open scoped lp InnerProduct

def permutationOperator {ι : Type*} (e : ι ≃ ι) : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ) :=
  (l2Permutation e).toContinuousLinearEquiv.toContinuousLinearMap

theorem permutationOperator_delta {ι : Type*} (e : ι ≃ ι) (r : ι) :
    permutationOperator e (delta r)=delta (e.symm r) := by
  classical
  ext q
  change (delta r) (e q)=(delta (e.symm r)) q
  simp only [delta,lp.single_apply,Pi.single_apply]
  exact if_congr e.eq_symm_apply.symm rfl rfl

theorem invariant_commute_permutation {ι : Type*} (e : ι ≃ ι)
    (B : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ)) (hB : Invariant e B) :
    Commute (permutationOperator e) B := by
  apply sub_eq_zero.mp
  apply eq_zero_of_columns
  intro r
  ext q
  change (B (delta r)) (e q)-(B (permutationOperator e (delta r))) q=0
  rw [permutationOperator_delta,sub_eq_zero]
  simpa only [matrix,Equiv.apply_symm_apply] using hB q (e.symm r)

theorem permutationOperator_involutive {ι : Type*} (e : ι ≃ ι)
    (he : Function.Involutive e) :
    (permutationOperator e).comp (permutationOperator e)=1 := by
  ext f q
  exact congrArg f (he q)

theorem permutationOperator_selfAdjoint {ι : Type*} (e : ι ≃ ι)
    (he : Function.Involutive e) : IsSelfAdjoint (permutationOperator e) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  have hi := (l2Permutation e).inner_map_map f (l2Permutation e g)
  have hg : l2Permutation e (l2Permutation e g)=g := by
    ext q
    exact congrArg g (he q)
  rw [hg] at hi
  exact hi

/-- The literal sign eigenspace of a quotient permutation. -/
def permutationSignSpace {ι : Type*} (e : ι ≃ ι) (s : ℝ) :
    Submodule ℂ ℓ²(ι,ℂ) := (permutationOperator e-(s:ℂ) • 1).ker

instance permutationSignSpace_complete {ι : Type*} (e : ι ≃ ι) (s : ℝ) :
    CompleteSpace (permutationSignSpace e s) := inferInstanceAs
      (CompleteSpace ((permutationOperator e-(s:ℂ) • 1).ker))

theorem invariant_commute_signProjection {ι : Type*} (e : ι ≃ ι)
    (he : Function.Involutive e) (U : Submodule ℂ ℓ²(ι,ℂ)) [CompleteSpace U]
    (hU : Invariant e U.starProjection) (s : ℝ) :
    Commute U.starProjection (permutationSignSpace e s).starProjection := by
  have hc : U.starProjection.comp (permutationOperator e-(s:ℂ) • 1)=
      (permutationOperator e-(s:ℂ) • 1).comp U.starProjection := by
    have h := (invariant_commute_permutation e _ hU).symm
    exact (h.sub_right ((Commute.one_right _).smul_right (s:ℂ))).eq
  have hs0 : IsSelfAdjoint ((s:ℂ) • (1 : ℓ²(ι,ℂ) →L[ℂ] ℓ²(ι,ℂ))) := by
    apply IsSelfAdjoint.smul
    · simp [IsSelfAdjoint]
    · exact IsSelfAdjoint.one _
  have hs : IsSelfAdjoint (permutationOperator e-(s:ℂ) • 1) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    rw [map_sub,(permutationOperator_selfAdjoint e he).adjoint_eq,hs0.adjoint_eq]
  change U.starProjection.comp (permutationSignSpace e s).starProjection=
    (permutationSignSpace e s).starProjection.comp U.starProjection
  apply ContinuousLinearMap.ext
  intro f
  exact QuantitativeEulerOldProjectionBlock.kernel_intertwine U.starProjection _ _ hs hs hc f

/-- The actual global Fricke sign projector commutes with the literal
joint new projector at every positive level. -/
theorem globalFricke_totalNew_sign_commute (N : ℕ) (hN : 0<N) (s : ℝ) :
    Commute (AsymptoticTotalNewCorner.space N hN).starProjection
      (permutationSignSpace (globalFrickeEquiv N hN) s).starProjection :=
  invariant_commute_signProjection _ (globalFrickeEquiv_involutive N hN) _
    (globalFricke_totalNew_invariant N hN) s

#print axioms invariant_commute_permutation
#print axioms globalFricke_totalNew_sign_commute

end QuantitativeNewGap
