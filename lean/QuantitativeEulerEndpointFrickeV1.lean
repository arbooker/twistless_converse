module

public import QuantitativeEulerEndpointCompactV1
public import QuantitativeEulerDiamondFrickeV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open Matrix UpperHalfPlane QuantitativeArithmetic QuantitativeHolomorphic
open QuantitativeEulerDensityGenerators AsymptoticCongruenceLabels
open QuantitativeEulerDiamondDecode AsymptoticOrbitDecode AsymptoticRegularObservationRows
open AsymptoticFreshMatrices AsymptoticIntegralSubgroup
open AsymptoticRegularCompactBranch (Space)
open scoped MatrixGroups Classical

/-- Exact left periodicity of actual compact operators at every integral
translation; it comes from the strip fold, not a hypothesis on the vector. -/
theorem compactAction_translation (j : ℤ) (g : G) {s : Set ℍ} (hs : IsCompact s)
    {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x (symbol (translationLabel (j : ℚ)*g))=
      compactAction hs hε t x (symbol g) := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext a
  rw [compactAction_decode,compactAction_decode,decodedEvaluation_symbol,decodedEvaluation_symbol]
  rw [mul_assoc,decode_periodic ε t x v (g*a) j]

/-- The literal original untwisted observation in the rational projective
algebra. Unlike the integral matrix evaluation, this realizes Fricke. -/
def frickeRow (N : ℕ) (hN : 0<N) (w : ℂ) : Ring :=
  1-w • symbol (frickeLabel N hN)

private theorem frickeRow_mul (N : ℕ) (hN : 0<N) (w : ℂ) (g : G) :
    frickeRow N hN w*symbol g=symbol g-w • symbol (frickeLabel N hN*g) := by
  rw [frickeRow,sub_mul,one_mul,smul_mul_assoc,symbol.map_mul]

/-- Any lower-unipotent power is the difference of TWO transported
original Fricke residuals. There is no invariance or sign assumption and
no telescope length loss. All identities hold on the actual compact space. -/
theorem compact_lower_fricke_identity (N : ℕ) (hN : 0<N) (r : ℤ) (w : ℂ) (g : G)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) (x : ℍ) :
    compactAction hs hε t x ((symbol (integralLabel (lowerSL N r))-1)*symbol g)=
      compactAction hs hε t x (frickeRow N hN w*symbol (integralLabel (lowerSL N r)*g))-
        compactAction hs hε t x (frickeRow N hN w*symbol g) := by
  have hperiod : compactAction hs hε t x
      (symbol (frickeLabel N hN*(integralLabel (lowerSL N r)*g)))=
      compactAction hs hε t x (symbol (frickeLabel N hN*g)) := by
    rw [←mul_assoc,fricke_lower,mul_assoc]
    simpa only [Int.cast_neg] using compactAction_translation (-r) (frickeLabel N hN*g) hs hε t x
  have hdef : (symbol (integralLabel (lowerSL N r))-1)*symbol g=
      symbol (integralLabel (lowerSL N r)*g)-symbol g := by
    rw [symbol.map_mul,sub_mul,one_mul]
  rw [hdef,frickeRow_mul,frickeRow_mul]
  simp only [map_sub,map_smul]
  have hcancel (A B C D : Space →L[ℂ] Space) (h : C=D) : A-B=(A-C)-(B-D) := by
    rw [h]
    abel
  exact hcancel _ _ _ _ (congrArg (fun T : Space →L[ℂ] Space => w • T) hperiod)

/-- Two actual q=1 observations control every multiplied lower power,
with explicit polynomial height costs for both right multipliers. -/
theorem compact_lower_fricke_norm (N : ℕ) (hN : 0<N) (r : ℤ) (w : ℂ)
    (β : SL(2,ℤ)) {s : Set ℍ} (hs : IsCompact s) {B H ε : ℝ}
    (hB : 0≤B) (hb : MatrixEntryBound β.val B) (hε : 0<ε)
    (hre : ∀ z∈s, |z.re|≤1) (him : ∀ z∈s, z.im≤H)
    (t : ℕ) (x : ℍ) (v : Space) :
    ‖matrixCompactAction hs hε t x
      ((matrixSymbol (lowerUnipotent N r)-1)*matrixSymbol β.val) v‖≤
      (integerCompactDistortion (2*(1+(N : ℝ)*|(r : ℝ)|)*B) H)^t*
        ‖twist N 1 hN Nat.zero_lt_one w
          (branchImage_compact (symbolBranch (integralLabel (lowerSL N r*β))) hs) hε t x v‖+
      (integerCompactDistortion B H)^t*
        ‖twist N 1 hN Nat.zero_lt_one w
          (branchImage_compact (symbolBranch (integralLabel β)) hs) hε t x v‖ := by
  have hV : MatrixEntryBound (lowerSL N r).val (1+(N : ℝ)*|(r : ℝ)|) := by
    intro i j
    change |((lowerUnipotent (N : ℤ) r i j : ℤ) : ℝ)|≤_
    simpa only [Int.cast_natCast,Nat.abs_cast] using lowerUnipotent_entry_bound (N : ℤ) r i j
  have hprod := matrix_entry_bound_mul (by positivity) hV hb
  have hfirst := compactAction_mul_integral_norm (lowerSL N r*β) (frickeRow N hN w)
    hs (by positivity) hprod hε hre him t x v
  have hsecond := compactAction_mul_integral_norm β (frickeRow N hN w)
    hs hB hb hε hre him t x v
  rw [frickeRow,compactAction_untwisted] at hfirst hsecond
  have he := compact_lower_fricke_identity N hN r w (integralLabel β) hs hε t x
  rw [←integralLabel.map_mul] at he
  change ‖matrixCompactAction hs hε t x
    ((matrixSymbol (lowerSL N r).val-1)*matrixSymbol β.val) v‖≤_
  rw [matrixCompactAction_integral_defect,he,_root_.sub_apply]
  exact (norm_sub_le _ _).trans (add_le_add hfirst hsecond)

#print axioms compactAction_translation
#print axioms compact_lower_fricke_identity
#print axioms compact_lower_fricke_norm
end QuantitativeEulerEndpointPrepared
