module

public import QuantitativeMaassQuotientGeneratorExpressionV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AsymptoticFiniteBranch QuantitativeNinaMaass
namespace QuantitativeMaass

/-- The same finite rational branches as the full quotient old pair. -/
def ambientOldPairExpression {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) : Expression :=
  let E := quotientCoverTraceExpression hMN
  let W := quotientPullbackExpression (completedFrickeNormalizer N hN).val
  E++composeExpression W (composeExpression E W)

theorem ambientOldPairExpression_realizes {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) :
    QuotientRealizes N (ambientOldPairExpression hN hMN) (ambientDivisorOldPair hN hMN) :=
  (quotientCoverTrace_realizes hMN).add
    ((quotientFricke_realizes N hN).mul ((quotientCoverTrace_realizes hMN).mul (quotientFricke_realizes N hN)))

def ambientSimpleBaseExpression {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) (p : ℕ) : Expression :=
  [AsymptoticFiniteBranch.identity]++scaleExpression (-1:ℂ)
    (scaleExpression (1/2:ℂ) (scaleExpression (((((p:ℝ)+1)⁻¹:ℝ):ℂ)) (ambientOldPairExpression hN hMN)))

theorem ambientSimpleBaseExpression_realizes {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) (p : ℕ) :
    QuotientRealizes N (ambientSimpleBaseExpression hN hMN p)
      (1-(1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • ambientDivisorOldPair hN hMN)) := by
  have hh := (QuotientRealizes.one N).add
    ((((ambientOldPairExpression_realizes hN hMN).smul (((((p:ℝ)+1)⁻¹:ℝ):ℂ))).smul (1/2:ℂ)).smul (-1:ℂ))
  have he : (1:AutomorphicSpace N→L[ℂ]AutomorphicSpace N)+(-1:ℂ) •
      ((1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • ambientDivisorOldPair hN hMN))=
      1-(1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • ambientDivisorOldPair hN hMN) := by
    apply ContinuousLinearMap.ext
    intro x
    change x+(-1:ℂ) • ((1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • ambientDivisorOldPair hN hMN x))=
      x-(1/2:ℂ) • (((((p:ℝ)+1)⁻¹:ℝ):ℂ) • ambientDivisorOldPair hN hMN x)
    module
  rw [he] at hh
  exact hh

def ambientSimpleNewExpression {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) (p m : ℕ) : Expression :=
  powerExpression (ambientSimpleBaseExpression hN hMN p) m

theorem ambientSimpleNewExpression_realizes {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) (p m : ℕ) :
    QuotientRealizes N (ambientSimpleNewExpression hN hMN p m) (ambientSimpleNewFilter hN hMN p m) :=
  (ambientSimpleBaseExpression_realizes hN hMN p).pow m

def ambientRepeatedBaseExpression {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) : Expression :=
  let E := quotientCoverTraceExpression hMN++scaleExpression (-1:ℂ) [AsymptoticFiniteBranch.identity]
  let W := quotientPullbackExpression (completedFrickeNormalizer N hN).val
  E++composeExpression W (composeExpression E W)

theorem ambientRepeatedBaseExpression_realizes {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) :
    QuotientRealizes N (ambientRepeatedBaseExpression hN hMN)
      (let B := (levelCover hMN).comp (levelTrace hMN)-1
       let W := (frickeIsometry N hN).toContinuousLinearMap
       B+W.comp (B.comp W)) := by
  have hb := (quotientCoverTrace_realizes hMN).add ((QuotientRealizes.one N).smul (-1:ℂ))
  have he : (levelCover hMN).comp (levelTrace hMN)+(-1:ℂ) • 1=
      (levelCover hMN).comp (levelTrace hMN)-1 := by
    apply ContinuousLinearMap.ext
    intro x
    change levelCover hMN (levelTrace hMN x)+(-1:ℂ) • x=levelCover hMN (levelTrace hMN x)-x
    module
  rw [he] at hb
  exact hb.add ((quotientFricke_realizes N hN).mul (hb.mul (quotientFricke_realizes N hN)))

def ambientRepeatedTwoNewExpression {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) : Expression :=
  let U := ambientRepeatedBaseExpression hN hMN
  scaleExpression (1/24:ℂ)
    (((powerExpression U 4++scaleExpression (-2:ℂ) (powerExpression U 3))++
      scaleExpression (-1:ℂ) (powerExpression U 2))++scaleExpression (2:ℂ) U)

theorem ambientRepeatedTwoNewExpression_realizes {M N : ℕ} [NeZero N] (hN : 0<N) (hMN : M∣N) :
    QuotientRealizes N (ambientRepeatedTwoNewExpression hN hMN) (ambientRepeatedTwoNewFilter hN hMN) := by
  have hu := ambientRepeatedBaseExpression_realizes hN hMN
  have hh := (((hu.pow 4).add ((hu.pow 3).smul (-2:ℂ))).add
    ((hu.pow 2).smul (-1:ℂ))).add (hu.smul (2:ℂ))
  have hs := hh.smul (1/24:ℂ)
  let B := (levelCover hMN).comp (levelTrace hMN)-1
  let W := (frickeIsometry N hN).toContinuousLinearMap
  let U := B+W.comp (B.comp W)
  change QuotientRealizes N (ambientRepeatedTwoNewExpression hN hMN)
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

#print axioms ambientOldPairExpression_realizes
#print axioms ambientSimpleBaseExpression_realizes
#print axioms ambientSimpleNewExpression_realizes
#print axioms ambientRepeatedBaseExpression_realizes
#print axioms ambientRepeatedTwoNewExpression_realizes
end QuantitativeMaass
