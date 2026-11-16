module

public import QuantitativeMaassNormalizerCoverV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AsymptoticClassicalPetersson QuantitativeNinaMaass
namespace QuantitativeMaass

/-- The adjoint of the actual normalizer pullback is its inverse pullback. -/
theorem quotientNormalizerPullback_adjoint (N : ℕ) (g : quotientNormalizerGroup N) :
    (quotientNormalizerPullback N g).toContinuousLinearMap.adjoint=
      (quotientNormalizerPullback N g⁻¹).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hh := (quotientNormalizerPullback N g).inner_map_map y (quotientNormalizerPullback N g⁻¹ x)
  rw [←quotientNormalizerPullback_mul,inv_mul_cancel,quotientNormalizerPullback_one] at hh
  exact hh

/-- Trace intertwining holds for arbitrary matching normalizers, without
an involutivity or self-adjointness restriction. -/
theorem normalizer_levelTrace {M N : ℕ} [NeZero N] (hMN : M∣N)
    (g : quotientNormalizerGroup N) (h : quotientNormalizerGroup M) (he : g.val=h.val)
    (x : AutomorphicSpace N) :
    levelTrace hMN (quotientNormalizerPullback N g x)=
      quotientNormalizerPullback M h (levelTrace hMN x) := by
  have hc : (quotientNormalizerPullback N g⁻¹).toContinuousLinearMap.comp (levelCover hMN)=
      (levelCover hMN).comp (quotientNormalizerPullback M h⁻¹).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro y
    exact normalizer_levelCover hMN g⁻¹ h⁻¹ (congrArg Inv.inv he) y
  have hh := congrArg ContinuousLinearMap.adjoint hc
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,
    quotientNormalizerPullback_adjoint,quotientNormalizerPullback_adjoint,inv_inv,inv_inv] at hh
  exact DFunLike.congr_fun hh x

#print axioms quotientNormalizerPullback_adjoint
#print axioms normalizer_levelTrace
end QuantitativeMaass
