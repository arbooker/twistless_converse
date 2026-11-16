module

public import QuantitativeMaassCountingLocalExpressionV1
public import AsymptoticOrbitBranchAlgebraV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticCongruenceStrip AsymptoticNestedQuotients AsymptoticQuotientOperators
open AsymptoticRegularTrace QuantitativeNewGap ContinuousLinearMap
namespace QuantitativeMaass.Counting

/-- The literal Fricke-conjugate lower-level projection is exactly the
second old projection on the counting quotient. -/
theorem fricke_old_projection {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) :
    let W := normalizerOperator N (completedFrickeNormalizer N hN)
    W.comp ((space (gamma_le_of_dvd hMN)).starProjection.comp W)=
      (space (gamma_le_frickeOldGroup hN hMN)).starProjection := by
  intro W
  have hw : W=permutationOperator (globalFrickeEquiv N hN) := rfl
  rw [hw]
  apply eq_of_matrix_eq
  intro q r
  have hi : (globalFrickeEquiv N hN).symm r=globalFrickeEquiv N hN r := by
    apply (globalFrickeEquiv N hN).injective
    rw [Equiv.apply_symm_apply,globalFrickeEquiv_involutive]
  change ((space (gamma_le_of_dvd hMN)).starProjection
    (permutationOperator (globalFrickeEquiv N hN) (delta r)))
      (globalFrickeEquiv N hN q)=_
  rw [permutationOperator_delta,hi]
  exact globalFricke_old_swap N M hN hMN q r

/-- The old-pair expression uses the exact relative index, with neither
an omitted index nor an assumption about a single quotient branch. -/
theorem oldPair_projection_formula {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) :
    oldPair hN hMN=(((gamma N).subgroupOf (gamma M)).index:ℂ) •
      ((space (gamma_le_of_dvd hMN)).starProjection+
        (space (gamma_le_frickeOldGroup hN hMN)).starProjection) := by
  let W := normalizerOperator N (completedFrickeNormalizer N hN)
  have hw := fricke_old_projection hN hMN
  apply ContinuousLinearMap.ext
  intro x
  change (((gamma N).subgroupOf (gamma M)).index:ℂ) •
    (space (gamma_le_of_dvd hMN)).starProjection x+
    W ((((gamma N).subgroupOf (gamma M)).index:ℂ) •
      (space (gamma_le_of_dvd hMN)).starProjection (W x))=_
  rw [map_smul]
  have hh := DFunLike.congr_fun hw x
  change W ((space (gamma_le_of_dvd hMN)).starProjection (W x))=_ at hh
  rw [hh]
  simp only [smul_apply,add_apply,smul_add]

#print axioms fricke_old_projection
#print axioms oldPair_projection_formula
end QuantitativeMaass.Counting
