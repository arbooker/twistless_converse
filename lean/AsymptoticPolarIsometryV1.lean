module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPolarIsometry

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

noncomputable def closedRange (S : H →L[ℂ] H) : Submodule ℂ H := S.range.topologicalClosure

noncomputable instance closedRange_complete (S : H →L[ℂ] H) : CompleteSpace (closedRange S) :=
  S.range.isClosed_topologicalClosure.completeSpace_coe

noncomputable def rangeMap (S : H →L[ℂ] H) : H →L[ℂ] closedRange S :=
  S.codRestrict (closedRange S) (fun x => S.range.le_topologicalClosure ⟨x,rfl⟩)

omit [CompleteSpace H] in
theorem rangeMap_dense (S : H →L[ℂ] H) : DenseRange (rangeMap S) := by
  have hd : DenseRange (Set.inclusion (show (S.range : Set H)⊆closure (S.range : Set H) from subset_closure)) :=
    (denseRange_inclusion_iff subset_closure).mpr subset_rfl
  have hr : Function.Surjective (fun x : H => (⟨S x,⟨x,rfl⟩⟩ : S.range)) := by
    rintro ⟨x,y,hy⟩
    exact ⟨y,Subtype.ext hy⟩
  exact hd.comp hr.denseRange (by fun_prop)

/-- Equal norms identify the closures of the source and target ranges;
this extension is the isometric part of polar decomposition. -/
noncomputable def rangeIsometry (T : H →L[ℂ] J) (S : H →L[ℂ] H)
    (h : ∀ x,‖T x‖=‖S x‖) : closedRange S →ₗᵢ[ℂ] J :=
  T.toLinearMap.extendOfIsometry (rangeMap_dense S) h

omit [CompleteSpace H] in
theorem rangeIsometry_map (T : H →L[ℂ] J) (S : H →L[ℂ] H)
    (h : ∀ x,‖T x‖=‖S x‖) (x : H) :
    rangeIsometry T S h (rangeMap S x)=T x :=
  T.toLinearMap.extendOfIsometry_eq (rangeMap_dense S) h x

noncomputable def partialIsometry (T : H →L[ℂ] J) (S : H →L[ℂ] H)
    (h : ∀ x,‖T x‖=‖S x‖) : H →L[ℂ] J :=
  (rangeIsometry T S h).toContinuousLinearMap.comp (closedRange S).orthogonalProjectionOnto

theorem partialIsometry_norm (T : H →L[ℂ] J) (S : H →L[ℂ] H)
    (h : ∀ x,‖T x‖=‖S x‖) (x : H) :
    ‖partialIsometry T S h x‖=‖(closedRange S).starProjection x‖ :=
  (rangeIsometry T S h).norm_map _

theorem partialIsometry_norm_le (T : H →L[ℂ] J) (S : H →L[ℂ] H)
    (h : ∀ x,‖T x‖=‖S x‖) : ‖partialIsometry T S h‖≤1 := by
  apply opNorm_le_bound _ (by norm_num)
  intro x
  rw [one_mul,partialIsometry_norm]
  exact (closedRange S).norm_starProjection_apply_le x

theorem partialIsometry_factor (T : H →L[ℂ] J) (S : H →L[ℂ] H)
    (h : ∀ x,‖T x‖=‖S x‖) : (partialIsometry T S h).comp S=T := by
  ext x
  change rangeIsometry T S h ((closedRange S).orthogonalProjectionOnto (S x))=T x
  have hp : (closedRange S).orthogonalProjectionOnto (S x)=rangeMap S x :=
    (closedRange S).orthogonalProjectionOnto_mem_subspace_eq_self (rangeMap S x)
  rw [hp,rangeIsometry_map]

theorem partialIsometry_gram (T : H →L[ℂ] J) (S : H →L[ℂ] H)
    (h : ∀ x,‖T x‖=‖S x‖) :
    (partialIsometry T S h).adjoint.comp (partialIsometry T S h)=(closedRange S).starProjection := by
  let V := (rangeIsometry T S h).toContinuousLinearMap
  let P := (closedRange S).orthogonalProjectionOnto
  change (V.comp P).adjoint.comp (V.comp P)=_
  rw [adjoint_comp,comp_assoc,← comp_assoc V.adjoint V P,
    (rangeIsometry T S h).adjoint_comp_self,one_def,id_comp]
  rw [(closedRange S).adjoint_orthogonalProjectionOnto]
  rfl

/-- The positive square root of T*T supplies the norm identity used by
the isometric extension. This uses continuous functional calculus. -/
noncomputable def absolute (T : H →L[ℂ] J) : H →L[ℂ] H := CFC.sqrt (T.adjoint.comp T)

theorem absolute_gram (T : H →L[ℂ] J) :
    (absolute T).adjoint.comp (absolute T)=T.adjoint.comp T := by
  have hp : 0≤T.adjoint.comp T := nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self T)
  have ha : (absolute T).adjoint=absolute T := (CFC.sqrt_nonneg (T.adjoint.comp T)).star_eq
  rw [ha]
  exact CFC.sqrt_mul_sqrt_self (T.adjoint.comp T) hp

theorem absolute_norm (T : H →L[ℂ] J) (x : H) : ‖T x‖=‖absolute T x‖ := by
  have hg := congrArg (fun B : H →L[ℂ] H => (⟪x,B x⟫_ℂ).re) (absolute_gram T)
  simp only [comp_apply,adjoint_inner_right] at hg
  change RCLike.re (⟪absolute T x,absolute T x⟫_ℂ)=RCLike.re (⟪T x,T x⟫_ℂ) at hg
  rw [← norm_sq_eq_re_inner,← norm_sq_eq_re_inner] at hg
  nlinarith [norm_nonneg (T x),norm_nonneg (absolute T x)]

theorem absolute_adjoint (T : H →L[ℂ] J) : (absolute T).adjoint=absolute T :=
  (CFC.sqrt_nonneg (T.adjoint.comp T)).star_eq

theorem absolute_ker (T : H →L[ℂ] J) : (absolute T).ker=T.ker := by
  ext x
  change absolute T x=0 ↔ T x=0
  constructor
  · intro hx
    apply norm_eq_zero.mp
    rw [absolute_norm T x,hx,norm_zero]
  · intro hx
    apply norm_eq_zero.mp
    rw [← absolute_norm T x,hx,norm_zero]

theorem absolute_closedRange (T : H →L[ℂ] J) : closedRange (absolute T)=T.kerᗮ := by
  rw [closedRange,← Submodule.orthogonal_orthogonal_eq_closure,orthogonal_range,
    absolute_adjoint,absolute_ker]

noncomputable def polar (T : H →L[ℂ] J) : H →L[ℂ] J :=
  partialIsometry T (absolute T) (absolute_norm T)

theorem polar_factor (T : H →L[ℂ] J) : (polar T).comp (absolute T)=T :=
  partialIsometry_factor T (absolute T) (absolute_norm T)

theorem polar_norm_le (T : H →L[ℂ] J) : ‖polar T‖≤1 :=
  partialIsometry_norm_le T (absolute T) (absolute_norm T)

theorem polar_gram (T : H →L[ℂ] J) :
    (polar T).adjoint.comp (polar T)=T.kerᗮ.starProjection := by
  simpa only [polar,absolute_closedRange] using partialIsometry_gram T (absolute T) (absolute_norm T)

#print axioms absolute_ker
#print axioms absolute_closedRange
#print axioms polar_factor
#print axioms polar_norm_le
#print axioms polar_gram

#print axioms rangeMap_dense
#print axioms rangeIsometry_map
#print axioms partialIsometry_norm_le
#print axioms partialIsometry_factor
#print axioms partialIsometry_gram
#print axioms absolute_gram
#print axioms absolute_norm

end AsymptoticPolarIsometry
