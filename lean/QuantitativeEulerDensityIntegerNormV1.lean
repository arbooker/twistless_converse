module

public import QuantitativeEulerDiamondRegionV1
public import AsymptoticCongruenceStripV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeEulerDensityGenerators

open Matrix UpperHalfPlane QuantitativeHolomorphic AsymptoticCongruenceLabels
open AsymptoticRationalBranches AsymptoticRationalFreeness QuantitativeEulerDiamondDecode
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups Classical

/-- The actual integral matrix itself is an integer representative of its
projective label. No compactness-selected height enters this statement. -/
theorem integerAction_integralLabel (γ : SL(2,ℤ)) :
    IntegerAction (integralLabel γ) γ.val := by
  constructor
  · rw [γ.property]
    norm_num
  · intro z
    change ((ofMatrix (rationalGL γ) (rationalGL_positive γ) • z : ℍ) : ℂ)=_
    rw [ofMatrix_action,coe_smul_of_det_pos (rationalGL_positive γ)]
    change (((((γ.val 0 0 : ℚ) : ℝ) : ℂ)*(z : ℂ)+(((γ.val 0 1 : ℚ) : ℝ) : ℂ))/
      ((((γ.val 1 0 : ℚ) : ℝ) : ℂ)*(z : ℂ)+(((γ.val 1 1 : ℚ) : ℝ) : ℂ)))=_
    norm_cast

/-- Right transport by an integral matrix has the explicit polynomial
height cost, uniformly in its entries, epsilon and the lower cutoff. -/
theorem compactAction_mul_integral_norm (γ : SL(2,ℤ)) (A : Ring)
    {s : Set ℍ} (hs : IsCompact s) {B H ε : ℝ}
    (hB : 0≤B) (hb : MatrixEntryBound γ.val B) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖compactAction hs hε t x (A*symbol (integralLabel γ)) v‖≤
      (integerCompactDistortion B H)^t*
        ‖compactAction (branchImage_compact (symbolBranch (integralLabel γ)) hs) hε t x A v‖ := by
  have hM : IntegerAction
      (ofMatrix (symbolBranch (integralLabel γ)).matrix (symbolBranch (integralLabel γ)).positive)
      γ.val := by
    rw [symbolBranch_label]
    exact integerAction_integralLabel γ
  simpa only [symbolBranch_label] using compactAction_mul_symbol_integer_norm
    (symbolBranch (integralLabel γ)) hs hM hB hb hε hre him t x A v

#print axioms integerAction_integralLabel
#print axioms compactAction_mul_integral_norm
end QuantitativeEulerDensityGenerators
