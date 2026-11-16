module

public import QuantitativeMaassReflectionNormalizationV1
public import QuantitativeMaassNormalizerSymmetryV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ENNReal InnerProductSpace

namespace QuantitativeMaass

/-- The genuine reflected function has exactly the same quotient L2 norm. -/
theorem reflection_eLpNorm (N : ℕ) (f : ℍ → ℂ) (hf : Measurable f)
    (hinv : ∀ γ : gamma N,∀ z,f (γ•z)=f z) :
    eLpNorm (fun z => f (J•z)) 2 (quotientMeasure N)=eLpNorm f 2 (quotientMeasure N) := by
  have hj : Measurable (fun z : ℍ => J•z) := (continuous_const_smul J).measurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p:=2) (μ:=quotientMeasure N)
      (f:=fun z => f (J•z)) (by norm_num) (by norm_num) (hf.comp hj).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (p:=2) (μ:=quotientMeasure N)
      (f:=f) (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  congr 1
  exact reflection_lintegral N (fun z => ‖f z‖ₑ ^ (2:ℝ≥0∞).toReal) (by fun_prop)
    (fun γ z => by rw [hinv])

/-- Reflection on actual measurable automorphic representatives. -/
def reflectionRepresentative (N : ℕ) :
    AutomorphicL2.representatives (gamma N) (quotientMeasure N) →ₗ[ℂ]
      AutomorphicL2.representatives (gamma N) (quotientMeasure N) where
  toFun f := ⟨fun z => f.val (J•z),
    f.property.1.comp (continuous_const_smul J).measurable, (by
      intro γ z
      change f.val (J•(γ•z))=f.val (J•z)
      have hi := f.property.2.1 (reflectedCongruence N γ) (J•z)
      change f.val ((reflectedCongruence N γ)•(J•z))=f.val (J•z) at hi
      simpa only [reflectedCongruence_action,reflection_involutive] using hi), (by
      change eLpNorm (fun z => f.val (J•z)) 2 (quotientMeasure N)<∞
      rw [reflection_eLpNorm N f.val f.property.1 f.property.2.1]
      exact f.property.2.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem reflectionRepresentative_norm (N : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    ‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) (reflectionRepresentative N f)‖=
      ‖AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f‖ := by
  rw [AutomorphicL2.embedding_norm,AutomorphicL2.embedding_norm]
  congr 1
  exact reflection_eLpNorm N f.val f.property.1 f.property.2.1

/-- The actual quotient reflection, extended isometrically from invariant
representatives to the automorphic Hilbert completion. -/
def reflectionIsometry (N : ℕ) : AutomorphicSpace N →ₗᵢ[ℂ] AutomorphicSpace N :=
  ((AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N)).comp
    (reflectionRepresentative N)).extendOfIsometry
    (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N))
    (reflectionRepresentative_norm N)

theorem reflectionIsometry_apply (N : ℕ)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N)) :
    reflectionIsometry N (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f)=
      AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) (reflectionRepresentative N f) := by
  exact LinearMap.extendOfIsometry_eq _ _ _ f

theorem reflectionIsometry_involutive (N : ℕ) : Function.Involutive (reflectionIsometry N) := by
  let U := reflectionIsometry N
  have he : (fun x : AutomorphicSpace N => U (U x))=(fun x => x) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma N) (quotientMeasure N)).equalizer
      (U.continuous.comp U.continuous) continuous_id
    funext f
    change U (U (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f))=
      AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N) f
    simp only [U,reflectionIsometry_apply]
    apply congrArg (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))
    apply Subtype.ext
    funext z
    change f.val (J•(J•z))=f.val z
    rw [reflection_involutive]
  intro x
  exact congrFun he x

/-- The genuine reflection is self-adjoint as well as isometric. -/
theorem reflectionIsometry_selfAdjoint (N : ℕ) :
    IsSelfAdjoint (reflectionIsometry N).toContinuousLinearMap := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hi := (reflectionIsometry N).inner_map_map x (reflectionIsometry N y)
  rw [reflectionIsometry_involutive N y] at hi
  exact hi

#print axioms reflection_eLpNorm
#print axioms reflectionRepresentative_norm
#print axioms reflectionIsometry_apply
#print axioms reflectionIsometry_involutive
#print axioms reflectionIsometry_selfAdjoint

end QuantitativeMaass
