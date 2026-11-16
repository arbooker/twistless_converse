module

public import QuantitativeArithmeticMaassCountingExpressionV1
public import QuantitativeMaassAmbientLocalExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticFiniteBranch QuantitativeNinaMaass AsymptoticNestedQuotients
open AsymptoticCongruenceStrip AsymptoticQuotientOperators QuantitativeNewGap
open scoped lp
namespace QuantitativeMaass.Counting

abbrev Space (N : ℕ) := ℓ²(Classes (gamma N),ℂ)

def normalizerOperator (N : ℕ) (g : quotientNormalizerGroup N) : Space N →L[ℂ] Space N :=
  permutationOperator (leftMulEquiv (gamma N) g.val
    (fun _ h => normalizer_conj_mem N g h)
    (fun _ h => normalizer_inv_conj_mem N g h))

theorem normalizerOperator_realizes (N : ℕ) (g : quotientNormalizerGroup N) :
    Realizes (gamma N) (quotientPullbackExpression g.val) (normalizerOperator N g) :=
  normalizer_realizes _ _ _ _

def coverTraceOperator {M N : ℕ} [NeZero N] (hMN : M∣N) : Space N →L[ℂ] Space N :=
  (((gamma N).subgroupOf (gamma M)).index:ℂ) •
    (space (AsymptoticCongruenceStrip.gamma_le_of_dvd hMN)).starProjection

def oldPair {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) : Space N →L[ℂ] Space N :=
  let B := coverTraceOperator hMN
  let W := normalizerOperator N (completedFrickeNormalizer N hN)
  B+W.comp (B.comp W)

def simpleNewFilter {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) (p m : ℕ) :
    Space N →L[ℂ] Space N :=
  (1-(1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • oldPair hN hMN))^m

def repeatedTwoNewFilter {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) :
    Space N →L[ℂ] Space N :=
  let B := coverTraceOperator hMN-1
  let W := normalizerOperator N (completedFrickeNormalizer N hN)
  let U := B+W.comp (B.comp W)
  (1/24:ℂ) • (U^4-(2:ℂ) • U^3-U^2+(2:ℂ) • U)

theorem ambientOldPairExpression_realizes {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) :
    Realizes (gamma N) (ambientOldPairExpression hN hMN) (oldPair hN hMN) :=
  (coverTrace_realizes hMN).add
    ((normalizerOperator_realizes N (completedFrickeNormalizer N hN)).mul ((coverTrace_realizes hMN).mul (normalizerOperator_realizes N (completedFrickeNormalizer N hN))))

theorem ambientSimpleBaseExpression_realizes {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) (p : ℕ) :
    Realizes (gamma N) (ambientSimpleBaseExpression hN hMN p)
      (1-(1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • oldPair hN hMN)) := by
  have hh := (Realizes.one (gamma N)).add
    ((((ambientOldPairExpression_realizes hN hMN).smul (((((p:ℝ)+1)⁻¹:ℝ):ℂ))).smul (1/2:ℂ)).smul (-1:ℂ))
  have he : (1:Space N→L[ℂ]Space N)+(-1:ℂ) •
      ((1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • oldPair hN hMN))=
      1-(1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • oldPair hN hMN) := by
    apply ContinuousLinearMap.ext
    intro x
    change x+(-1:ℂ) • ((1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • oldPair hN hMN x))=
      x-(1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • oldPair hN hMN x)
    module
  rw [he] at hh
  exact hh

theorem ambientSimpleNewExpression_realizes {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) (p m : ℕ) :
    Realizes (gamma N) (ambientSimpleNewExpression hN hMN p m) (simpleNewFilter hN hMN p m) :=
  (ambientSimpleBaseExpression_realizes hN hMN p).pow m

theorem ambientRepeatedBaseExpression_realizes {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) :
    Realizes (gamma N) (ambientRepeatedBaseExpression hN hMN)
      (let B := coverTraceOperator hMN-1
       let W := normalizerOperator N (completedFrickeNormalizer N hN)
       B+W.comp (B.comp W)) := by
  have hb := (coverTrace_realizes hMN).add ((Realizes.one (gamma N)).smul (-1:ℂ))
  have he : coverTraceOperator hMN+(-1:ℂ) • 1=
      coverTraceOperator hMN-1 := by
    apply ContinuousLinearMap.ext
    intro x
    change coverTraceOperator hMN x+(-1:ℂ) • x=coverTraceOperator hMN x-x
    module
  change Realizes (gamma N)
    (quotientCoverTraceExpression hMN++scaleExpression (-1:ℂ) [AsymptoticFiniteBranch.identity])
    (coverTraceOperator hMN+(-1:ℂ) • 1) at hb
  rw [he] at hb
  exact hb.add ((normalizerOperator_realizes N (completedFrickeNormalizer N hN)).mul (hb.mul (normalizerOperator_realizes N (completedFrickeNormalizer N hN))))

theorem ambientRepeatedTwoNewExpression_realizes {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) :
    Realizes (gamma N) (ambientRepeatedTwoNewExpression hN hMN) (repeatedTwoNewFilter hN hMN) := by
  have hu := ambientRepeatedBaseExpression_realizes hN hMN
  have hh := (((hu.pow 4).add ((hu.pow 3).smul (-2:ℂ))).add
    ((hu.pow 2).smul (-1:ℂ))).add (hu.smul (2:ℂ))
  have hs := hh.smul (1/24:ℂ)
  let B := coverTraceOperator hMN-1
  let W := normalizerOperator N (completedFrickeNormalizer N hN)
  let U := B+W.comp (B.comp W)
  change Realizes (gamma N) (ambientRepeatedTwoNewExpression hN hMN)
    ((1/24:ℂ) • (U^4+(-2:ℂ) • U^3+(-1:ℂ) • U^2+(2:ℂ) • U)) at hs
  have he : (1/24:ℂ) • (U^4+(-2:ℂ) • U^3+(-1:ℂ) • U^2+(2:ℂ) • U)=
      (1/24:ℂ) • (U^4-(2:ℂ) • U^3-U^2+(2:ℂ) • U) := by
    apply ContinuousLinearMap.ext
    intro x
    change (1/24:ℂ) • ((U^4) x+(-2:ℂ) • (U^3) x+(-1:ℂ) • (U^2) x+(2:ℂ) • U x)=
      (1/24:ℂ) • ((U^4) x-(2:ℂ) • (U^3) x-(U^2) x+(2:ℂ) • U x)
    module
  rw [he] at hs
  exact hs

#print axioms normalizerOperator_realizes
#print axioms ambientOldPairExpression_realizes
#print axioms ambientSimpleBaseExpression_realizes
#print axioms ambientSimpleNewExpression_realizes
#print axioms ambientRepeatedBaseExpression_realizes
#print axioms ambientRepeatedTwoNewExpression_realizes

end QuantitativeMaass.Counting
