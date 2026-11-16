module

public import QuantitativeMaassNormalizerActionV1
public import QuantitativeNinaMaassOldSpectrumV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory AsymptoticCongruenceStrip AsymptoticClassicalPetersson QuantitativeNinaMaass
namespace QuantitativeMaass

/-- Equal rational normalizers at two nested levels intertwine the actual
finite-cover map on the completed quotient Hilbert spaces. -/
theorem normalizer_levelCover {M N : ℕ} [NeZero N] (hMN : M∣N)
    (g : quotientNormalizerGroup N) (h : quotientNormalizerGroup M) (he : g.val=h.val)
    (x : AutomorphicSpace M) :
    quotientNormalizerPullback N g (levelCover hMN x)=
      levelCover hMN (quotientNormalizerPullback M h x) := by
  have hh : (fun x : AutomorphicSpace M => quotientNormalizerPullback N g (levelCover hMN x))=
      fun x => levelCover hMN (quotientNormalizerPullback M h x) := by
    apply (AutomorphicL2.denseEmbedding_dense (gamma M) (quotientMeasure M)).equalizer
      ((quotientNormalizerPullback N g).continuous.comp (levelCover hMN).continuous)
      ((levelCover hMN).continuous.comp (quotientNormalizerPullback M h).continuous)
    funext f
    change quotientNormalizerPullback N g (levelCover hMN (AutomorphicL2.denseEmbedding _ _ f))=
      levelCover hMN (quotientNormalizerPullback M h (AutomorphicL2.denseEmbedding _ _ f))
    rw [levelCover_apply,quotientNormalizerPullback_representative,
      quotientNormalizerPullback_representative,levelCover_apply]
    apply congrArg (AutomorphicL2.denseEmbedding (gamma N) (quotientMeasure N))
    apply Subtype.ext
    funext z
    change f.val (g.val • z)=f.val (h.val • z)
    rw [he]
  exact congrFun hh x

/-- Preservation of the genuine lower-level old image, before any choice
of spectral basis or projection. -/
theorem normalizer_levelCover_range {M N : ℕ} [NeZero N] (hMN : M∣N)
    (g : quotientNormalizerGroup N) (h : quotientNormalizerGroup M) (he : g.val=h.val)
    (x : AutomorphicSpace N) (hx : x∈(levelCover hMN).range) :
    quotientNormalizerPullback N g x∈(levelCover hMN).range := by
  obtain ⟨y,rfl⟩ := hx
  exact ⟨quotientNormalizerPullback M h y,(normalizer_levelCover hMN g h he y).symm⟩

/-- A self-adjoint normalizer preserving the actual old image preserves
the adjoint trace kernel. -/
theorem normalizer_levelTrace_kernel {M N : ℕ} [NeZero N] (hMN : M∣N)
    (g : quotientNormalizerGroup N) (h : quotientNormalizerGroup M) (he : g.val=h.val)
    (hg : IsSelfAdjoint (quotientNormalizerPullback N g).toContinuousLinearMap)
    (x : AutomorphicSpace N) (hx : levelTrace hMN x=0) :
    levelTrace hMN (quotientNormalizerPullback N g x)=0 := by
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((levelCover hMN).adjoint (quotientNormalizerPullback N g x))=inner ℂ y 0
  rw [ContinuousLinearMap.adjoint_inner_right,inner_zero_right]
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hg) (levelCover hMN y) x
  change inner ℂ (quotientNormalizerPullback N g (levelCover hMN y)) x=
    inner ℂ (levelCover hMN y) (quotientNormalizerPullback N g x) at hs
  rw [←hs,normalizer_levelCover hMN g h he,
    ←ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (quotientNormalizerPullback M h y) (levelTrace hMN x)=0
  rw [hx,inner_zero_right]

#print axioms normalizer_levelCover
#print axioms normalizer_levelCover_range
#print axioms normalizer_levelTrace_kernel
end QuantitativeMaass
