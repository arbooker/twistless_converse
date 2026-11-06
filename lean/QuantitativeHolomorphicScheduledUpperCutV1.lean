module

public import QuantitativeHolomorphicUpperCutScalarRateV1
public import QuantitativeHolomorphicScheduledLowerModeV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic.Schedule

open FinitenessCertificate FinitenessGlobalHeight AsymptoticFourierNorm
open AsymptoticCylinderModeComparison AsymptoticCylinder

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def fixedMajorant (P : Parameters A) : ℝ :=
  majorantConstant ((AsymptoticReconstructedCount.parameters A P).s+4)
    (4*Real.pi) (AsymptoticReconstructedCount.parameters A P).ε

theorem fixedMajorant_nonneg (P : Parameters A) : 0≤fixedMajorant A P := by
  unfold fixedMajorant majorantConstant
  positivity

def sharpGrowthConstant (P : Parameters A) (C : ℝ) : ℝ :=
  (Real.sqrt (countGramLower A P))⁻¹^2+4*(newtonGrowthConstant A P C+2)^2

theorem sharpGrowthConstant_nonneg (P : Parameters A) (C : ℝ) :
    0≤sharpGrowthConstant A P C := by unfold sharpGrowthConstant; positivity

def upperScheduledHeightConstant (P : Parameters A) (C : ℝ) : ℝ :=
  24*sharpGrowthConstant A P C*upperHeightCoefficient (fixedMajorant A P)
    (upperMassCoefficient ((AsymptoticReconstructedCount.parameters A P).s+4) (4*Real.pi))

def upperScheduledGrowthConstant (P : Parameters A) (C : ℝ) : ℝ :=
  sharpGrowthConstant A P C*upperWeightCoefficient (fixedMajorant A P)+4

theorem upperScheduledGrowthConstant_nonneg (P : Parameters A) (C : ℝ) :
    0≤upperScheduledGrowthConstant A P C := by
  have hb := sharpGrowthConstant_nonneg A P C
  unfold upperScheduledGrowthConstant upperWeightCoefficient
  positivity

theorem scheduled_upper_cut_error (P : Parameters A) {C s : ℝ} (hC : 0≤C)
    (hs : 1≤s) (d h : ℕ) (hd : (d:ℝ)≤Real.exp (C*s^2)) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let n := newtonDepth A P (2*d+2) (Real.exp (-8*s))
    let B := (3/2:ℝ)^n
    upperCutError (B^2*(1+fixedMajorant A P)) B 1
      (massBound (2*h) (P'.s+4) (4*Real.pi) (Real.exp (16*s))/(2*h+2:ℝ))≤
      upperScheduledHeightConstant A P C*Real.exp (-3*s)+
      bridgeErrorThird (upperScheduledGrowthConstant A P C) (h+1) (Real.exp s) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let n := newtonDepth A P (2*d+2) (Real.exp (-8*s))
  let B := (3/2:ℝ)^n
  let M := fixedMajorant A P
  let a := upperMassCoefficient (P'.s+4) (4*Real.pi)
  let b := sharpGrowthConstant A P C
  let c := b*upperWeightCoefficient M
  have hb : 0≤b := sharpGrowthConstant_nonneg A P C
  have hc : 0≤c := by dsimp [c,upperWeightCoefficient]; positivity
  have hB2 : B^2≤b*s^4 := (le_max_right _ _).trans (growing_sharp_majorant A P hC hs d hd)
  have hsplit := upperCutError_split (by dsimp [B]; positivity) (fixedMajorant_nonneg A P)
    (upperMassCoefficient_nonneg _ (by positivity)) hb hs
    (show (1:ℝ)≤2*h+2 by nlinarith [(Nat.cast_nonneg h : (0:ℝ)≤h)]) hB2
    (scheduled_upper_mass h (P'.s+4) (by linarith))
  apply hsplit.trans
  apply add_le_add le_rfl
  have hcoeff : c*s^4≤Real.exp (Real.exp ((c+4)*s^2)) := by
    have hp : c*s^4≤Real.exp ((c+4)*s^2) := by
      simpa using polynomial_mul_exp_quadratic_le 4 (b:=c) (C:=0) hc hs
    apply hp.trans
    apply Real.exp_le_exp.mpr
    linarith [Real.add_one_le_exp ((c+4)*s^2)]
  have hm := mul_le_mul hcoeff (inverse_sqrt_weight_le_trace_power h) (by positivity) (Real.exp_nonneg _)
  exact hm.trans_eq (double_exp_mul_trace_power _ _ h)

#print axioms scheduled_upper_cut_error

end QuantitativeHolomorphic.Schedule
