module

public import QuantitativeMaassReflectionOperatorV1
public import QuantitativeMaassTraceAdjointV1
public import AsymptoticFrickeNormalizerV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open AsymptoticCongruenceLabels AsymptoticFreshMatrices QuantitativeMaass
open scoped ENNReal InnerProductSpace

/-!
Physical old directions and new trace kernels in the actual automorphic L2
space. These definitions use finite-cover pullback, its genuine finite-coset
adjoint, and the global Fricke isometry. No regular-representation substitute
or oldform multiplicity formula is used.

This chapter does not prove the spectral oldform decomposition, the dimensions
of its summands, or existence of normalized Maass newforms. Those are separate
steps needed for the original Euler-product lower bound.
-/

namespace QuantitativeNinaMaass

/-- Literal pullback from level M to level N, on quotient Hilbert spaces. -/
def levelCover {M N : ℕ} [NeZero N] (hMN : M ∣ N) :
    AutomorphicSpace M →L[ℂ] AutomorphicSpace N :=
  AutomorphicL2.coverOperator volume AsymptoticRationalGroup.measurePreserving
    (gamma N) (gamma M) (gamma_le_of_dvd hMN)
    (density M) (density N) (density_measurable M) (density_measurable N)
    (density_orbit_sum M) (density_orbit_sum N)

def levelCoverRepresentative {M N : ℕ} [NeZero N] (hMN : M ∣ N) :
    AutomorphicL2.representatives (gamma M) (quotientMeasure M) →ₗ[ℂ]
      AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
  AutomorphicL2.coverRepresentative volume AsymptoticRationalGroup.measurePreserving
    (gamma N) (gamma M) (gamma_le_of_dvd hMN)
    (density M) (density N) (density_measurable M) (density_measurable N)
    (density_orbit_sum M) (density_orbit_sum N)

theorem levelCover_apply {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma M) (quotientMeasure M)) :
    levelCover hMN (AutomorphicL2.denseEmbedding _ _ f) =
      AutomorphicL2.denseEmbedding _ _ (levelCoverRepresentative hMN f) :=
  AutomorphicL2.coverOperator_apply volume AsymptoticRationalGroup.measurePreserving
    (gamma N) (gamma M) (gamma_le_of_dvd hMN)
    (density M) (density N) (density_measurable M) (density_measurable N)
    (density_orbit_sum M) (density_orbit_sum N) f

/-- Covering preserves the actual reflection, before and after completion. -/
theorem levelCover_reflection {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (v : AutomorphicSpace M) :
    reflectionIsometry N (levelCover hMN v) =
      levelCover hMN (reflectionIsometry M v) := by
  have he : (fun x : AutomorphicSpace M => reflectionIsometry N (levelCover hMN x)) =
      fun x => levelCover hMN (reflectionIsometry M x) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma M) (quotientMeasure M)).equalizer
      ((reflectionIsometry N).continuous.comp (levelCover hMN).continuous)
      ((levelCover hMN).continuous.comp (reflectionIsometry M).continuous)
    funext f
    simp only [Function.comp_apply, levelCover_apply, reflectionIsometry_apply]
    rfl
  exact congrFun he v

/-- The sharp cover norm identity holds on all completed vectors. -/
theorem levelCover_norm {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (v : AutomorphicSpace M) :
    ‖levelCover hMN v‖ = Real.sqrt ((gamma N).relIndex (gamma M) : ℝ) * ‖v‖ := by
  have he : (fun x : AutomorphicSpace M => ‖levelCover hMN x‖) =
      fun x => Real.sqrt ((gamma N).relIndex (gamma M) : ℝ) * ‖x‖ := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma M) (quotientMeasure M)).equalizer
      (levelCover hMN).continuous.norm (continuous_const.mul continuous_norm)
    funext f
    simp only [Function.comp_apply, levelCover_apply]
    exact AutomorphicL2.coverRepresentative_norm volume AsymptoticRationalGroup.measurePreserving
      (gamma N) (gamma M) (gamma_le_of_dvd hMN)
      (density M) (density N) (density_measurable M) (density_measurable N)
      (density_orbit_sum M) (density_orbit_sum N) f
  exact congrFun he v

/-- Actual lower-level functions are not collapsed by the Hilbert completion. -/
theorem levelCover_injective {M N : ℕ} [NeZero N] (hMN : M ∣ N) :
    Function.Injective (levelCover hMN) := by
  let := gamma_finite_relIndex N M
  have hi : 0 < ((gamma N).relIndex (gamma M) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Subgroup.relIndex_ne_zero (H := gamma N) (K := gamma M))
  intro x y hxy
  have hz : levelCover hMN (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  have hn := levelCover_norm hMN (x-y)
  rw [hz, norm_zero] at hn
  have hd : ‖x-y‖ = 0 := (mul_eq_zero.mp hn.symm).resolve_left (Real.sqrt_pos.mpr hi).ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp hd)

/-- The genuine finite-coset trace, defined as the adjoint of pullback. -/
def levelTrace {M N : ℕ} [NeZero N] (hMN : M ∣ N) :
    AutomorphicSpace N →L[ℂ] AutomorphicSpace M := (levelCover hMN).adjoint

theorem levelTrace_apply {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    levelTrace hMN (AutomorphicL2.denseEmbedding _ _ f) =
      AutomorphicL2.denseEmbedding _ _
        (let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
         AutomorphicL2.traceRepresentative volume AsymptoticRationalGroup.measurePreserving
           (gamma N) (gamma M) (gamma_le_of_dvd hMN)
           (density M) (density N) (density_measurable M) (density_measurable N)
           (density_orbit_sum M) (density_orbit_sum N) f) := by
  let := Fintype.ofFinite (gamma M ⧸ (gamma N).subgroupOf (gamma M))
  exact AutomorphicL2.coverOperator_adjoint_apply volume AsymptoticRationalGroup.measurePreserving
    (gamma N) (gamma M) (gamma_le_of_dvd hMN)
    (density M) (density N) (density_measurable M) (density_measurable N)
    (density_orbit_sum M) (density_orbit_sum N) f

theorem levelTrace_reflection {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (v : AutomorphicSpace N) :
    levelTrace hMN (reflectionIsometry N v) =
      reflectionIsometry M (levelTrace hMN v) := by
  have he : (reflectionIsometry N).toContinuousLinearMap.comp (levelCover hMN) =
      (levelCover hMN).comp (reflectionIsometry M).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact levelCover_reflection hMN x
  have ha := congrArg ContinuousLinearMap.adjoint he
  simp only [ContinuousLinearMap.adjoint_comp,
    (reflectionIsometry_selfAdjoint N).adjoint_eq,
    (reflectionIsometry_selfAdjoint M).adjoint_eq] at ha
  exact DFunLike.congr_fun ha v

/-- The actual global Fricke action on level-N quotient L2. -/
def frickeIsometry (N : ℕ) (hN : 0 < N) :
    AutomorphicSpace N →ₗᵢ[ℂ] AutomorphicSpace N :=
  AutomorphicL2.normalizerIsometry volume AsymptoticRationalGroup.measurePreserving
    (gamma N) (frickeLabel N hN)
    (fun _ ha => fricke_conj_mem N hN ha)
    (fun _ ha => by simpa only [frickeLabel_inv] using fricke_conj_mem N hN ha)
    (density N) (density_measurable N) (density_orbit_sum N)

def frickeRepresentative (N : ℕ) (hN : 0 < N) :
    AutomorphicL2.representatives (gamma N) (quotientMeasure N) →ₗ[ℂ]
      AutomorphicL2.representatives (gamma N) (quotientMeasure N) :=
  AutomorphicL2.normalizerRepresentative volume AsymptoticRationalGroup.measurePreserving
    (gamma N) (frickeLabel N hN)
    (fun _ ha => fricke_conj_mem N hN ha)
    (fun _ ha => by simpa only [frickeLabel_inv] using fricke_conj_mem N hN ha)
    (density N) (density_measurable N) (density_orbit_sum N)

theorem frickeIsometry_apply (N : ℕ) (hN : 0 < N)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    frickeIsometry N hN (AutomorphicL2.denseEmbedding _ _ f) =
      AutomorphicL2.denseEmbedding _ _ (frickeRepresentative N hN f) :=
  AutomorphicL2.normalizerIsometry_apply volume AsymptoticRationalGroup.measurePreserving
    (gamma N) (frickeLabel N hN) _ _ (density N) (density_measurable N)
    (density_orbit_sum N) f

/-- The concrete Fricke map commutes with z ↦ -conj(z). -/
theorem frickeLabel_reflection (N : ℕ) (hN : 0 < N) (z : ℍ) :
    frickeLabel N hN • (J • z) = J • (frickeLabel N hN • z) := by
  have ha (w : ℍ) : ((frickeLabel N hN • w : ℍ) : ℂ) = -1 / ((N : ℂ) * w) := by
    rw [frickeLabel, AsymptoticRationalBranches.ofMatrix_action,
      AsymptoticRationalBranches.realMatrix_branch]
    simpa using AsymptoticReconstructionBranch.branch_action
      (show (0 : ℝ) < N by exact_mod_cast hN) 0 0 w
  apply UpperHalfPlane.ext
  rw [ha, coe_J_smul, coe_J_smul, ha]
  simp [mul_neg, div_eq_mul_inv, mul_comm]

theorem frickeIsometry_reflection (N : ℕ) (hN : 0 < N) (v : AutomorphicSpace N) :
    frickeIsometry N hN (reflectionIsometry N v) =
      reflectionIsometry N (frickeIsometry N hN v) := by
  have he : (fun x : AutomorphicSpace N => frickeIsometry N hN (reflectionIsometry N x)) =
      fun x => reflectionIsometry N (frickeIsometry N hN x) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      ((frickeIsometry N hN).continuous.comp (reflectionIsometry N).continuous)
      ((reflectionIsometry N).continuous.comp (frickeIsometry N hN).continuous)
    funext f
    simp only [Function.comp_apply, frickeIsometry_apply, reflectionIsometry_apply]
    apply congrArg (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))
    apply Subtype.ext
    funext z
    exact congrArg f.val (frickeLabel_reflection N hN z).symm
  exact congrFun he v

theorem frickeIsometry_involutive (N : ℕ) (hN : 0 < N) :
    Function.Involutive (frickeIsometry N hN) :=
  AutomorphicL2.normalizerIsometry_involutive volume AsymptoticRationalGroup.measurePreserving
    (gamma N) (frickeLabel N hN) _ _ (density N) (density_measurable N)
    (density_orbit_sum N) (by rw [frickeLabel_mul_self]; exact (gamma N).one_mem)

theorem frickeIsometry_selfAdjoint (N : ℕ) (hN : 0 < N) :
    IsSelfAdjoint (frickeIsometry N hN).toContinuousLinearMap :=
  AutomorphicL2.normalizerIsometry_selfAdjoint volume AsymptoticRationalGroup.measurePreserving
    (gamma N) (frickeLabel N hN) _ _ (density N) (density_measurable N)
    (density_orbit_sum N) (by rw [frickeLabel_mul_self]; exact (gamma N).one_mem)

/-- Both physical old directions at an arbitrary divisor, including repeated primes. -/
def oldDirections {M N : ℕ} [NeZero N] (hN : 0 < N) (hMN : M ∣ N) :
    Submodule ℂ (AutomorphicSpace N) :=
  (levelCover hMN).range ⊔
    ((frickeIsometry N hN).toContinuousLinearMap.comp (levelCover hMN)).range

def newTraceKernel {M N : ℕ} [NeZero N] (hN : 0 < N) (hMN : M ∣ N) :
    Submodule ℂ (AutomorphicSpace N) :=
  (levelTrace hMN).ker ⊓
    ((levelTrace hMN).comp (frickeIsometry N hN).toContinuousLinearMap).ker

/-- The two literal trace equations are exactly physical old orthogonality. -/
theorem newTraceKernel_eq_orthogonal {M N : ℕ} [NeZero N]
    (hN : 0 < N) (hMN : M ∣ N) :
    newTraceKernel hN hMN = (oldDirections hN hMN)ᗮ := by
  rw [oldDirections, ← Submodule.inf_orthogonal]
  simp only [ContinuousLinearMap.orthogonal_range, ContinuousLinearMap.adjoint_comp,
    (frickeIsometry_selfAdjoint N hN).adjoint_eq]
  rfl

theorem newTraceKernel_reflection {M N : ℕ} [NeZero N]
    (hN : 0 < N) (hMN : M ∣ N) (v : AutomorphicSpace N)
    (hv : v ∈ newTraceKernel hN hMN) :
    reflectionIsometry N v ∈ newTraceKernel hN hMN := by
  change levelTrace hMN v = 0 ∧ levelTrace hMN (frickeIsometry N hN v) = 0 at hv
  change levelTrace hMN (reflectionIsometry N v) = 0 ∧
    levelTrace hMN (frickeIsometry N hN (reflectionIsometry N v)) = 0
  constructor
  · rw [levelTrace_reflection, hv.1, map_zero]
  · rw [frickeIsometry_reflection, levelTrace_reflection, hv.2, map_zero]

/-- The closed span of all physical prime-old directions. -/
def oldSpace (N : ℕ) [NeZero N] (hN : 0 < N) : Submodule ℂ (AutomorphicSpace N) :=
  (⨆ p : {p : ℕ // p.Prime ∧ p ∣ N},
    oldDirections hN (Nat.div_dvd_of_dvd p.property.2)).topologicalClosure

/-- Physical newspace, defined by all genuine lower trace equations. -/
def newSpace (N : ℕ) [NeZero N] (hN : 0 < N) : Submodule ℂ (AutomorphicSpace N) :=
  ⨅ p : {p : ℕ // p.Prime ∧ p ∣ N},
    newTraceKernel hN (Nat.div_dvd_of_dvd p.property.2)

theorem newSpace_eq_oldSpace_orthogonal (N : ℕ) [NeZero N] (hN : 0 < N) :
    newSpace N hN = (oldSpace N hN)ᗮ := by
  simp only [newSpace, oldSpace, Submodule.orthogonal_closure,
    newTraceKernel_eq_orthogonal, Submodule.iInf_orthogonal]

/-- Genuine physical newness is preserved separately by reflection parity. -/
theorem newSpace_reflection (N : ℕ) [NeZero N] (hN : 0 < N)
    (v : AutomorphicSpace N) (hv : v ∈ newSpace N hN) :
    reflectionIsometry N v ∈ newSpace N hN := by
  simp only [newSpace, Submodule.mem_iInf] at hv ⊢
  intro p
  exact newTraceKernel_reflection hN (Nat.div_dvd_of_dvd p.property.2) v (hv p)

theorem newSpace_one : newSpace 1 (by norm_num) = ⊤ := by
  apply top_unique
  intro v _
  simp only [newSpace, Submodule.mem_iInf]
  intro p
  exact False.elim (p.property.1.not_dvd_one p.property.2)

#print axioms levelCover_apply
#print axioms levelCover_reflection
#print axioms levelCover_norm
#print axioms levelCover_injective
#print axioms levelTrace_apply
#print axioms levelTrace_reflection
#print axioms frickeIsometry_apply
#print axioms frickeLabel_reflection
#print axioms frickeIsometry_reflection
#print axioms frickeIsometry_involutive
#print axioms frickeIsometry_selfAdjoint
#print axioms newTraceKernel_eq_orthogonal
#print axioms newTraceKernel_reflection
#print axioms newSpace_eq_oldSpace_orthogonal
#print axioms newSpace_reflection
#print axioms newSpace_one

end QuantitativeNinaMaass
