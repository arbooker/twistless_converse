module

public import QuantitativeHolomorphicGramV1
public import QuantitativeMaassSimilarityCountV1

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeMaass

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

section Extension

variable (W : Submodule ℂ H) [W.HasOrthogonalProjection]

/-- Extend a change of coordinates on the target by the identity on its
orthogonal complement. -/
def targetBlockMap (T : W →L[ℂ] W) : H →L[ℂ] H :=
  W.subtypeL.comp (T.comp W.orthogonalProjectionOnto)+Wᗮ.starProjection

theorem targetBlockMap_projection (T : W →L[ℂ] W) (x : H) :
    W.orthogonalProjectionOnto (targetBlockMap W T x)=T (W.orthogonalProjectionOnto x) := by
  change W.orthogonalProjectionOnto ((T (W.orthogonalProjectionOnto x):H)+Wᗮ.starProjection x)=_
  rw [map_add,W.orthogonalProjectionOnto_mem_subspace_eq_self,
    W.orthogonalProjectionOnto_apply_of_mem_orthogonal (Wᗮ.starProjection_apply_mem x),add_zero]

theorem targetBlockMap_perp (T : W →L[ℂ] W) (x : H) :
    Wᗮ.starProjection (targetBlockMap W T x)=Wᗮ.starProjection x := by
  rw [W.starProjection_orthogonal_val]
  have hp := congrArg (fun y : W => (y:H)) (targetBlockMap_projection W T x)
  change W.starProjection (targetBlockMap W T x)=(T (W.orthogonalProjectionOnto x):H) at hp
  rw [hp]
  change (T (W.orthogonalProjectionOnto x):H)+Wᗮ.starProjection x-
    (T (W.orthogonalProjectionOnto x):H)=_
  abel

theorem targetBlockMap_inverse (T : W ≃L[ℂ] W) (x : H) :
    targetBlockMap W T.symm.toContinuousLinearMap (targetBlockMap W T.toContinuousLinearMap x)=x := by
  change (T.symm (W.orthogonalProjectionOnto (targetBlockMap W T.toContinuousLinearMap x)):H)+
    Wᗮ.starProjection (targetBlockMap W T.toContinuousLinearMap x)=x
  rw [targetBlockMap_projection,targetBlockMap_perp]
  change (T.symm (T (W.orthogonalProjectionOnto x)):H)+Wᗮ.starProjection x=x
  rw [T.symm_apply_apply]
  exact W.starProjection_add_starProjection_orthogonal x

def targetBlockEquiv (T : W ≃L[ℂ] W) : H ≃L[ℂ] H where
  toLinearMap := (targetBlockMap W T.toContinuousLinearMap).toLinearMap
  invFun := targetBlockMap W T.symm.toContinuousLinearMap
  left_inv := targetBlockMap_inverse W T
  right_inv := targetBlockMap_inverse W T.symm
  continuous_toFun := (targetBlockMap W T.toContinuousLinearMap).continuous
  continuous_invFun := (targetBlockMap W T.symm.toContinuousLinearMap).continuous

theorem targetBlockEquiv_apply_target (T : W ≃L[ℂ] W) (x : W) :
    targetBlockEquiv W T (x:H)=(T x:H) := by
  change (T (W.orthogonalProjectionOnto (x:H)):H)+Wᗮ.starProjection (x:H)=_
  rw [W.orthogonalProjectionOnto_mem_subspace_eq_self,W.starProjection_orthogonal_val,
    W.starProjection_mem_subspace_eq_self,sub_self,add_zero]

theorem targetBlockEquiv_symm_perp (T : W ≃L[ℂ] W) (x : H) :
    (targetBlockEquiv W T).symm (Wᗮ.starProjection x)=Wᗮ.starProjection x := by
  change (T.symm (W.orthogonalProjectionOnto (Wᗮ.starProjection x)):H)+
    Wᗮ.starProjection (Wᗮ.starProjection x)=_
  rw [W.orthogonalProjectionOnto_apply_of_mem_orthogonal (Wᗮ.starProjection_apply_mem x),
    map_zero,Submodule.coe_zero,zero_add]
  exact Submodule.starProjection_eq_self_iff.mpr (Wᗮ.starProjection_apply_mem x)

end Extension

section Normalized

variable [CompleteSpace H]

/-- Gram normalization converts a bounded equivalence into a surjective
isometry. Surjectivity follows from the explicit reconstruction identity. -/
def normalizedTargetEquiv (J : V ≃L[ℂ] H) {a : ℝ} (ha : 0<a)
    (hJ : ∀ x,a*‖x‖^2≤‖J x‖^2) : V ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (QuantitativeHolomorphic.normalizedReconstruction J.toContinuousLinearMap).toLinearMap
      norm_map' := QuantitativeHolomorphic.normalizedReconstruction_norm J.toContinuousLinearMap ha hJ }
    (by
      intro y
      let R := J.toContinuousLinearMap
      refine ⟨((R.adjoint.comp R).comp (QuantitativeHolomorphic.inverseSqrtCFC (R.adjoint.comp R)))
        (J.symm y),?_⟩
      change QuantitativeHolomorphic.normalizedReconstruction R _=y
      rw [QuantitativeHolomorphic.normalizedReconstruction_reconstruct R ha hJ]
      exact J.apply_symm_apply y)

end Normalized

/-- Constructed metric change for a closed target embedding. Its norm on
the embedded target is exactly the original canonical norm. -/
def targetMetric (W : Submodule ℂ H) [CompleteSpace W]
    (J : V ≃L[ℂ] W) {a : ℝ} (ha : 0<a) (hJ : ∀ x,a*‖x‖^2≤‖J x‖^2) : H ≃L[ℂ] H :=
  targetBlockEquiv W (J.symm.trans (normalizedTargetEquiv J ha hJ).toContinuousLinearEquiv)

theorem targetMetric_embedded (W : Submodule ℂ H) [CompleteSpace W]
    (J : V ≃L[ℂ] W) {a : ℝ} (ha : 0<a) (hJ : ∀ x,a*‖x‖^2≤‖J x‖^2) (v : V) :
    targetMetric W J ha hJ (J v:H)=(normalizedTargetEquiv J ha hJ v:H) := by
  rw [targetMetric,targetBlockEquiv_apply_target]
  simp only [ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.symm_apply_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]

theorem targetMetric_norm (W : Submodule ℂ H) [CompleteSpace W]
    (J : V ≃L[ℂ] W) {a : ℝ} (ha : 0<a) (hJ : ∀ x,a*‖x‖^2≤‖J x‖^2) (v : V) :
    ‖targetMetric W J ha hJ (J v:H)‖=‖v‖ := by
  rw [targetMetric_embedded]
  exact (normalizedTargetEquiv J ha hJ).norm_map v

theorem targetMetric_symm_perp (W : Submodule ℂ H) [CompleteSpace W]
    (J : V ≃L[ℂ] W) {a : ℝ} (ha : 0<a) (hJ : ∀ x,a*‖x‖^2≤‖J x‖^2) (x : H) :
    (targetMetric W J ha hJ).symm (Wᗮ.starProjection x)=Wᗮ.starProjection x :=
  targetBlockEquiv_symm_perp W _ x

#print axioms targetBlockMap_projection
#print axioms targetBlockMap_perp
#print axioms targetBlockMap_inverse
#print axioms targetBlockEquiv_apply_target
#print axioms targetBlockEquiv_symm_perp
#print axioms normalizedTargetEquiv
#print axioms targetMetric_embedded
#print axioms targetMetric_norm
#print axioms targetMetric_symm_perp

end QuantitativeMaass
