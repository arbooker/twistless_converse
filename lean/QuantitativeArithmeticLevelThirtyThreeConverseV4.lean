module
public import QuantitativeArithmeticPrimitiveResiduePairV4

public import FinitenessFiniteOrderClosureV1
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.Group
public import QuantitativeArithmeticEntireQuotientV1
public import QuantitativeArithmeticExponentialDominanceV1
public import QuantitativeArithmeticMellinScaleV1
public import QuantitativeArithmeticNormalizedIndividualFrickeTheoryV4
public import QuantitativeArithmeticPrimePowerTorsionV1
public import QuantitativeArithmeticQuadraticTwistInversionTheoryV4
public import QuantitativeArithmeticQuadraticTwistReflectionTheoryV4
public import QuantitativeArithmeticComplexHornerBoundsTheoryV4
public import QuantitativeArithmeticRectangularContinuationTheoryV4
public import QuantitativeArithmeticAnalyticGermTheoryV4
public import QuantitativeArithmeticCoherentTaylorTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyThreeKnownWordsTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyThreeKnownWordsV1
public import QuantitativeArithmeticSmallLevelThirtyThreeMinorNonzeroV1
public import QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch1Link1V1
public import QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Link1V1
public import QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch2Link2V1
public import QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch3Link1V1
public import QuantitativeArithmeticSmallLevelThirtyThreeMinusBranch3Link2V1
public import QuantitativeArithmeticSmallLevelThirtyThreeMinusEliminationTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyThreeMinusMinorLinksV4
public import QuantitativeArithmeticSmallLevelThirtyThreePlusBranch1Link1V1
public import QuantitativeArithmeticSmallLevelThirtyThreePlusBranch2Link1V1
public import QuantitativeArithmeticSmallLevelThirtyThreePlusBranch2Link2V1
public import QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Link1V1
public import QuantitativeArithmeticSmallLevelThirtyThreePlusBranch3Link2V1
public import QuantitativeArithmeticSmallLevelThirtyThreePlusEliminationTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyThreePlusMinorLinksV4
public import QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftRationalTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftLinksBundleV4
public import QuantitativeArithmeticTranslatedFrickeTheoryV4
public import SmallLevelTaylorTheoryV4
public import SmallLevelAllowedSimplePoleTailV1
public import SmallLevelContinuedMeromorphicSourcesV1
public import SmallLevelContinuedRegularTailV1
public import SmallLevelFourPrimeRatesV1
public import SmallLevelMellinUnscaleV1
public import SmallLevelModularCriterionV1
public import SmallLevelPoleGridTheoryV4
public import SmallLevelQuadraticExponentialTheoryV4
public import SmallLevelRegularizedShiftKernelV1
public import SmallLevelSimplePoleTaylorTheoryV4
public import SmallLevelSixRootsV1
public import SmallLevelThirtyThreeTheoryV4
public import SmallLevelThreePairV1
public import SmallLevelTransversalV1

set_option Elab.async false

/-! Consolidated converse argument. Large exact certificates remain
in their own modules; declarations and proof bodies are preserved. -/

/-! ## ThirtyThreeRootData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds

def pCoefficient : ℕ→ℚ := fun j => match j with
  | 0 => (16767/704)
  | 1 => (-36693/704)
  | 2 => (405/8)
  | 3 => (-81/4)
  | 4 => (1197/44)
  | 5 => (48/11)
  | 6 => (127/11)
  | 7 => (1/1)
  | _ => 0
def centerQ : Fin 7→ℚ×ℚ := ![((-1423630476918569479/125000000000000000),(0/1)),((-455206957178540327/500000000000000000),(-293668034220005327/200000000000000000)),((-455206957178540327/500000000000000000),(734170085550013317/500000000000000000)),((6688155811805767/25000000000000000),(-1228363849182842981/1000000000000000000)),((6688155811805767/25000000000000000),(61418192459142149/50000000000000000)),((282341158415928551/500000000000000000),(-22046191071555161/62500000000000000)),((282341158415928551/500000000000000000),(14109562285795303/40000000000000000))]
def radiusQ : ℚ := (1/1000000000)
def p7 : ℂ[X] := hornerPolynomial (fun j => (pCoefficient j:ℂ)) 8 0

theorem p7_monic : p7.Monic := by
  norm_num [p7,hornerPolynomial,pCoefficient]
  monicity!

theorem p7_degree : p7.degree=(7:WithBot ℕ) := by
  norm_num [p7,hornerPolynomial,pCoefficient]
  compute_degree!

#print axioms p7_monic
#print axioms p7_degree

end QuantitativeArithmeticSmallLevelThirtyThreeRoot
end
end

/-! ## ThirtyThreeRootXData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds
def qCoefficient : ℕ→ℚ := fun j => match j with
  | 0 => (170471/963441)
  | 1 => (-332326/963441)
  | 2 => (-6718013/8670969)
  | 3 => (-9076516/8670969)
  | 4 => (-56173196/78038721)
  | 5 => (-30721400/78038721)
  | 6 => (-65606464/702348489)
  | 7 => (-3930080/702348489)
  | _ => 0
def xPoly : ℂ[X] := hornerPolynomial (fun j => (qCoefficient j:ℂ)) 8 0

end QuantitativeArithmeticSmallLevelThirtyThreeRoot
end
end

/-! ## ThirtyThreeAlgebraicLocus -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeLocus
open QuantitativeArithmeticSmallLevelThirtyThreeRoot QuantitativeArithmeticComplexHornerBounds

def InLocus (X Y A : ℂ) : Prop :=
  (A= -X ∧ X^2=Y+1) ∨
  (A= -X-1 ∧ (Y=3 ∨ p7.eval (-Y)=0) ∧ X=xPoly.eval (-Y))

theorem septic_expression (Y : ℂ) :
    704*(-Y)^7+8128*(-Y)^6+3072*(-Y)^5+19152*(-Y)^4-14256*(-Y)^3+
      35640*(-Y)^2-36693*(-Y)+16767=704*p7.eval (-Y) := by
  norm_num [p7,pCoefficient,hornerPolynomial]
  ring

theorem x_expression (Y : ℂ) :
    -(3930080*(-Y)^7+65606464*(-Y)^6+276492600*(-Y)^5+505558764*(-Y)^4+
      735197796*(-Y)^3+544159053*(-Y)^2+242265654*(-Y)-124273359)/702348489=
        xPoly.eval (-Y) := by
  norm_num [xPoly,qCoefficient,hornerPolynomial]
  ring

#print axioms septic_expression
#print axioms x_expression
end QuantitativeArithmeticSmallLevelThirtyThreeLocus
end
end

/-! ## ThirtyThreeCenters -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeCenters
open SmallLevelNormalized SmallLevelThirtyThree SmallLevelOriginal
  QuantitativeArithmeticTranslatedFricke Complex Filter Set MeasureTheory
  FinitenessPolynomialSeries FinitenessFourierConstruction Matrix UpperHalfPlane
open scoped Topology MatrixGroups ModularForm

def center (positive : Bool) : ℝ := if positive then 1/6 else -(1/6)

/-- The original level33 input supplies both individual denominator-six
Fricke laws, with one common sign, via the proved modulus-six invariance. -/
theorem original_centers (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ positive : Bool,
      (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center positive))
        ∣[((2*m:ℕ):ℤ)] fricke 396 (by decide)=
      χ • (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center positive)) := by
  obtain ⟨χ,hχ,hF⟩ := original_fricke_sign (by decide : 0<33) m hf
  let δ := FinitenessNormalizedTwistProduct.root 33 f 3
  have hδ : δ=1 ∨ δ= -1 := FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3
  have hχδ : χ*δ=1 ∨ χ*δ= -1 := by
    rcases hχ with h|h <;> rcases hδ with hd|hd <;> simp [h,hd]
  refine ⟨χ*δ,hχδ,?_⟩
  intro positive
  cases positive
  · exact translated_slash_eigen 33 396 (2*m) (by decide) (by decide) _ χ δ _ A A_det
      hF (SmallLevelSixEigen.thirty_three_A (by omega) hf) fricke_branch_neg
  · exact translated_slash_eigen 33 396 (2*m) (by decide) (by decide) _ χ δ _ B B_det
      hF (SmallLevelSixEigen.thirty_three_B (by omega) hf) fricke_branch_pos

def centeredMellin (m : ℕ) (f : ℕ → ℂ) (positive : Bool) : ℂ → ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 396
    (SmallLevelAdditive.coefficients (FinitenessOriginalFourier.fullCoefficients f (2*m)) (center positive)))

/-- Actual entire finite-order continuations and functional equations for
both denominator-six additive twists, obtained from original input alone. -/
theorem original_centers_entire (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ positive : Bool,
      Differentiable ℂ (centeredMellin m f positive) ∧
      FinitenessFiniteOrder.Bound (centeredMellin m f positive) ∧
      ∀ s : ℂ, centeredMellin m f positive s=
        (χ/(Complex.I^(2*m)))*centeredMellin m f positive ((2*m:ℕ)-s) := by
  obtain ⟨χ,hχ,hF⟩ := original_centers m hm hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  refine ⟨χ,hχ,fun positive => ?_⟩
  exact translated_mellin_entire 396 (2*m) (by decide) (by omega) _
    (FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m))
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)) (center positive) χ hχ
    (hF positive)

#print axioms original_centers
#print axioms original_centers_entire
end QuantitativeArithmeticSmallLevelThirtyThreeCenters
end
end

/-! ## ThirtyThreeChiThree -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeChiThree
open QuantitativeArithmeticSmallLevelThirtyThreeCenters QuantitativeArithmeticMellinScale
  SmallLevelAdditive SmallLevelTaylor Complex Filter Set MeasureTheory
  FinitenessFourierConstruction FinitenessOriginalFourier

/-- The entire numerator before division by the Hecke polynomial. -/
def numerator (m : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1
    (coefficients (fullCoefficients f (2*m)) (1/6))) s-
  mellin (FinitenessAllLevelAxisDecay.axis 1
    (coefficients (fullCoefficients f (2*m)) (-(1/6)))) s

def denominator (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  1+(((2:ℝ)^(((k:ℝ)+1)/2):ℝ):ℂ)*f 2*(2:ℂ)^(-s)+(2:ℂ)^k*(4:ℂ)^(-s)

theorem original_numerator_entire (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    Differentiable ℂ (numerator m f) := by
  obtain ⟨χ,_,h⟩ := original_centers_entire m hm hf
  exact (entire_at_one (by decide : 0<396) _ (h true).1).sub
    (entire_at_one (by decide : 0<396) _ (h false).1)

theorem denominator_entire (k : ℕ) (f : ℕ → ℂ) : Differentiable ℂ (denominator k f) := by
  unfold denominator
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (4:ℂ)≠0)]
  fun_prop

/-- An exact original-input Hecke identity, identifying the quadratic-twist
numerator on a half-plane. No division or continuation premise is used. -/
theorem original_hecke_identity (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ bound : ℝ, ∀ s : ℂ, bound<s.re →
      numerator m f s=denominator (2*m) f s*
        (original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) := by
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  obtain ⟨H,hH⟩ := original_additive_hecke hf (by decide : Nat.Prime 2) (by decide)
  refine ⟨max B H,?_⟩
  intro s hs
  have hsB := lt_of_le_of_lt (le_max_left B H) hs
  have hsH := lt_of_le_of_lt (le_max_right B H) hs
  have hper (r : ℝ) : original (2*m) f (r+1) s=original (2*m) f r s := by
    rw [← (hB (r+1) s hsB).2,← (hB r s hsB).2]
    congr 1
    funext y
    have hh := periodic (fullCoefficients f (2*m)) ((r:ℂ)+(y:ℂ)*I)
    have he : ((r+1:ℝ):ℂ)+(y:ℂ)*I=((r:ℂ)+(y:ℂ)*I)+1 := by
      push_cast
      ring1
    rw [he]
    exact hh
  have hp := hH (1/6) s hsH
  have hn := hH (-(1/6)) s hsH
  norm_num [Finset.sum_range_succ] at hp hn
  have h1 := hper (-(1/3))
  have h2 := hper (-(2/3))
  norm_num at h1 h2
  rw [h1] at hp
  rw [← h2] at hn
  have hnum : numerator m f s=original (2*m) f (1/6) s-original (2*m) f (-(1/6)) s := by
    unfold numerator
    have he (r : ℝ) : FinitenessAllLevelAxisDecay.axis 1 (coefficients (fullCoefficients f (2*m)) r)=
        (fun y : ℝ => fourier (fullCoefficients f (2*m)) ((r:ℂ)+(y:ℂ)*I)) :=
      funext (axis_one_translate (fullCoefficients f (2*m)) r)
    rw [he,he,(hB (1/6) s hsB).2,(hB (-(1/6)) s hsB).2]
  rw [hnum]
  unfold denominator
  push_cast
  linear_combination hp-hn

#print axioms original_numerator_entire
#print axioms denominator_entire
#print axioms original_hecke_identity
end QuantitativeArithmeticSmallLevelThirtyThreeChiThree
end
end

/-! ## ThirtyThreeChiThreeContinuation -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeChiThree
open Complex Filter Set SmallLevelAdditive
open scoped Topology

/-- Three fixed evaluations exclude an identically zero denominator for
every complex Hecke eigenvalue, including zero. -/
theorem denominator_nonzero (k : ℕ) (f : ℕ → ℂ) : ∃ s : ℂ, denominator k f s≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  norm_num [denominator,Complex.cpow_neg,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0-2*h1+(8/3:ℂ)*h2
  norm_num at hbad

/-- The actual odd additive combination modulo3 has a global meromorphic
continuation from the original hypotheses. Its only possible poles are
zeros of the explicit Hecke-2 denominator. Pole removal is still separate. -/
theorem original_continuation (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ (bound : ℝ) (G : ℂ → ℂ), (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) ∧
      (∀ s, denominator (2*m) f s≠0 → AnalyticAt ℂ G s) ∧
      (∀ x, G=ᶠ[𝓝[≠] x] (fun s => numerator m f s/denominator (2*m) f s)) := by
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  obtain ⟨H,hH⟩ := original_hecke_identity m hf
  obtain ⟨G,hG,hagree,hpole,hgerm⟩ := QuantitativeArithmeticEntireQuotient.continuation
    (numerator m f) (denominator (2*m) f)
    (fun s => original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) (max B H)
    (fun z => (original_numerator_entire m hm hf).analyticAt z)
    (fun z => (denominator_entire (2*m) f).analyticAt z)
    (denominator_nonzero (2*m) f)
    (fun z hz => (hB (1/3) z (lt_of_le_of_lt (le_max_left _ _) hz)).1.sub
      (hB (-(1/3)) z (lt_of_le_of_lt (le_max_left _ _) hz)).1)
    (fun z hz => hH z (lt_of_le_of_lt (le_max_right _ _) hz))
  exact ⟨max B H,G,hG,hagree,hpole,hgerm⟩

#print axioms denominator_nonzero
#print axioms original_continuation
end QuantitativeArithmeticSmallLevelThirtyThreeChiThree
end
end

/-! ## ThirtyThreeWeightDominanceMPP -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeWeightDominanceMPP
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination

def bases : Fin 13→ℝ := ![1,3,4,11,12,16,27,33,36,48,64,108,132]
def coefficients : Fin 13→ℝ := ![(-7/2:ℝ),(3/1:ℝ),(3/2:ℝ),(-3/2:ℝ),(-1/2:ℝ),(-2/1:ℝ),(-1/2:ℝ),(1/2:ℝ),(-2/1:ℝ),(-2/1:ℝ),(1/1:ℝ),(-1/1:ℝ),(1/1:ℝ)]
def value (m : ℕ) : ℝ := (144:ℝ)^m+∑ i : Fin 13,coefficients i*bases i^m

theorem value_ne_zero (m : ℕ) (hm : 2 ≤ m) : value m≠0 := by
  by_cases h5 : 5 ≤ m
  · exact QuantitativeArithmeticExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 144
      (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 5 m h5
      (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  · have hm5 : m < 5 := by omega
    interval_cases m <;> norm_num [value,coefficients,bases,Fin.sum_univ_succ]

theorem minor_value (m : ℕ) :
    eval ((4:ℂ)^m) ((1:ℂ)*(3:ℂ)^m) ((1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor16= -(value m:ℂ) := by
  unfold value
  push_cast
  norm_num [coefficients,bases,Fin.sum_univ_succ,minor16,eval,monomial]
  have hb12 : (12:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb16 : (16:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb27 : (27:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb33 : (33:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb36 : (36:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb48 : (48:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb64 : (64:ℂ)^m=((4:ℂ)^m)^3*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 3 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb108 : (108:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb132 : (132:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb144 : (144:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  rw [hb12,hb16,hb27,hb33,hb36,hb48,hb64,hb108,hb132,hb144]
  ring

theorem minor_ne_zero (m : ℕ) (hm : 2 ≤ m) :
    eval ((4:ℂ)^m) ((1:ℂ)*(3:ℂ)^m) ((1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor16≠0 := by
  rw [minor_value]
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (value_ne_zero m hm))

#print axioms minor_ne_zero
end QuantitativeArithmeticSmallLevelThirtyThreeWeightDominanceMPP
end
end

/-! ## ThirtyThreeWeightDominanceMPM -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeWeightDominanceMPM
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination

def bases : Fin 13→ℝ := ![1,3,4,11,12,16,27,33,36,48,64,108,132]
def coefficients : Fin 13→ℝ := ![(-7/2:ℝ),(3/1:ℝ),(3/2:ℝ),(3/2:ℝ),(-1/2:ℝ),(-2/1:ℝ),(-1/2:ℝ),(-1/2:ℝ),(-2/1:ℝ),(-2/1:ℝ),(1/1:ℝ),(-1/1:ℝ),(-1/1:ℝ)]
def value (m : ℕ) : ℝ := (144:ℝ)^m+∑ i : Fin 13,coefficients i*bases i^m

theorem value_ne_zero (m : ℕ) (hm : 2 ≤ m) : value m≠0 := by
  by_cases h5 : 5 ≤ m
  · exact QuantitativeArithmeticExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 144
      (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 5 m h5
      (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  · have hm5 : m < 5 := by omega
    interval_cases m <;> norm_num [value,coefficients,bases,Fin.sum_univ_succ]

theorem minor_value (m : ℕ) :
    eval ((4:ℂ)^m) ((1:ℂ)*(3:ℂ)^m) ((-1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor16= -(value m:ℂ) := by
  unfold value
  push_cast
  norm_num [coefficients,bases,Fin.sum_univ_succ,minor16,eval,monomial]
  have hb12 : (12:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb16 : (16:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb27 : (27:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb33 : (33:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb36 : (36:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb48 : (48:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb64 : (64:ℂ)^m=((4:ℂ)^m)^3*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 3 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb108 : (108:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb132 : (132:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb144 : (144:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  rw [hb12,hb16,hb27,hb33,hb36,hb48,hb64,hb108,hb132,hb144]
  ring

theorem minor_ne_zero (m : ℕ) (hm : 2 ≤ m) :
    eval ((4:ℂ)^m) ((1:ℂ)*(3:ℂ)^m) ((-1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor16≠0 := by
  rw [minor_value]
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (value_ne_zero m hm))

#print axioms minor_ne_zero
end QuantitativeArithmeticSmallLevelThirtyThreeWeightDominanceMPM
end
end

/-! ## ThirtyThreeWeightDominanceMMP -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeWeightDominanceMMP
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination

def bases : Fin 13→ℝ := ![1,3,4,11,12,16,27,33,36,48,64,108,132]
def coefficients : Fin 13→ℝ := ![(-7/2:ℝ),(-3/1:ℝ),(3/2:ℝ),(-3/2:ℝ),(1/2:ℝ),(-2/1:ℝ),(1/2:ℝ),(-1/2:ℝ),(-2/1:ℝ),(2/1:ℝ),(1/1:ℝ),(1/1:ℝ),(-1/1:ℝ)]
def value (m : ℕ) : ℝ := (144:ℝ)^m+∑ i : Fin 13,coefficients i*bases i^m

theorem value_ne_zero (m : ℕ) (hm : 2 ≤ m) : value m≠0 := by
  by_cases h5 : 5 ≤ m
  · exact QuantitativeArithmeticExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 144
      (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 5 m h5
      (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  · have hm5 : m < 5 := by omega
    interval_cases m <;> norm_num [value,coefficients,bases,Fin.sum_univ_succ]

theorem minor_value (m : ℕ) :
    eval ((4:ℂ)^m) ((-1:ℂ)*(3:ℂ)^m) ((1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor16= -(value m:ℂ) := by
  unfold value
  push_cast
  norm_num [coefficients,bases,Fin.sum_univ_succ,minor16,eval,monomial]
  have hb12 : (12:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb16 : (16:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb27 : (27:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb33 : (33:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb36 : (36:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb48 : (48:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb64 : (64:ℂ)^m=((4:ℂ)^m)^3*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 3 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb108 : (108:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb132 : (132:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb144 : (144:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  rw [hb12,hb16,hb27,hb33,hb36,hb48,hb64,hb108,hb132,hb144]
  ring

theorem minor_ne_zero (m : ℕ) (hm : 2 ≤ m) :
    eval ((4:ℂ)^m) ((-1:ℂ)*(3:ℂ)^m) ((1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor16≠0 := by
  rw [minor_value]
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (value_ne_zero m hm))

#print axioms minor_ne_zero
end QuantitativeArithmeticSmallLevelThirtyThreeWeightDominanceMMP
end
end

/-! ## ThirtyThreeWeightDominanceMMM -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeWeightDominanceMMM
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination

def bases : Fin 13→ℝ := ![1,3,4,11,12,16,27,33,36,48,64,108,132]
def coefficients : Fin 13→ℝ := ![(-7/2:ℝ),(-3/1:ℝ),(3/2:ℝ),(3/2:ℝ),(1/2:ℝ),(-2/1:ℝ),(1/2:ℝ),(1/2:ℝ),(-2/1:ℝ),(2/1:ℝ),(1/1:ℝ),(1/1:ℝ),(1/1:ℝ)]
def value (m : ℕ) : ℝ := (144:ℝ)^m+∑ i : Fin 13,coefficients i*bases i^m

theorem value_ne_zero (m : ℕ) (hm : 2 ≤ m) : value m≠0 := by
  by_cases h5 : 5 ≤ m
  · exact QuantitativeArithmeticExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 144
      (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 5 m h5
      (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  · have hm5 : m < 5 := by omega
    interval_cases m <;> norm_num [value,coefficients,bases,Fin.sum_univ_succ]

theorem minor_value (m : ℕ) :
    eval ((4:ℂ)^m) ((-1:ℂ)*(3:ℂ)^m) ((-1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor16= -(value m:ℂ) := by
  unfold value
  push_cast
  norm_num [coefficients,bases,Fin.sum_univ_succ,minor16,eval,monomial]
  have hb12 : (12:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb16 : (16:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb27 : (27:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb33 : (33:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb36 : (36:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb48 : (48:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb64 : (64:ℂ)^m=((4:ℂ)^m)^3*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 3 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb108 : (108:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb132 : (132:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb144 : (144:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  rw [hb12,hb16,hb27,hb33,hb36,hb48,hb64,hb108,hb132,hb144]
  ring

theorem minor_ne_zero (m : ℕ) (hm : 2 ≤ m) :
    eval ((4:ℂ)^m) ((-1:ℂ)*(3:ℂ)^m) ((-1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor16≠0 := by
  rw [minor_value]
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (value_ne_zero m hm))

#print axioms minor_ne_zero
end QuantitativeArithmeticSmallLevelThirtyThreeWeightDominanceMMM
end
end

/-! ## ThirtyThreeWeightDominancePPP -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeWeightDominancePPP
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreePlusElimination

def bases : Fin 13→ℝ := ![1,3,4,11,12,16,27,33,36,48,64,108,132]
def coefficients : Fin 13→ℝ := ![(-1/2:ℝ),(2/1:ℝ),(3/2:ℝ),(3/2:ℝ),(-5/2:ℝ),(-2/1:ℝ),(-1/2:ℝ),(-1/2:ℝ),(-2/1:ℝ),(-2/1:ℝ),(1/1:ℝ),(-1/1:ℝ),(-1/1:ℝ)]
def value (m : ℕ) : ℝ := (144:ℝ)^m+∑ i : Fin 13,coefficients i*bases i^m

theorem value_ne_zero (m : ℕ) (hm : 2 ≤ m) : value m≠0 := by
  by_cases h5 : 5 ≤ m
  · exact QuantitativeArithmeticExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 144
      (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 5 m h5
      (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  · have hm5 : m < 5 := by omega
    interval_cases m <;> norm_num [value,coefficients,bases,Fin.sum_univ_succ]

theorem minor_value (m : ℕ) :
    eval ((4:ℂ)^m) ((1:ℂ)*(3:ℂ)^m) ((1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor13= -(value m:ℂ) := by
  unfold value
  push_cast
  norm_num [coefficients,bases,Fin.sum_univ_succ,minor13,eval,monomial]
  have hb12 : (12:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb16 : (16:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb27 : (27:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb33 : (33:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb36 : (36:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb48 : (48:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb64 : (64:ℂ)^m=((4:ℂ)^m)^3*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 3 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb108 : (108:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb132 : (132:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb144 : (144:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  rw [hb12,hb16,hb27,hb33,hb36,hb48,hb64,hb108,hb132,hb144]
  ring

theorem minor_ne_zero (m : ℕ) (hm : 2 ≤ m) :
    eval ((4:ℂ)^m) ((1:ℂ)*(3:ℂ)^m) ((1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor13≠0 := by
  rw [minor_value]
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (value_ne_zero m hm))

#print axioms minor_ne_zero
end QuantitativeArithmeticSmallLevelThirtyThreeWeightDominancePPP
end
end

/-! ## ThirtyThreeWeightDominancePPM -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeWeightDominancePPM
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreePlusElimination

def bases : Fin 13→ℝ := ![1,3,4,11,12,16,27,33,36,48,64,108,132]
def coefficients : Fin 13→ℝ := ![(-1/2:ℝ),(2/1:ℝ),(3/2:ℝ),(-3/2:ℝ),(-5/2:ℝ),(-2/1:ℝ),(-1/2:ℝ),(1/2:ℝ),(-2/1:ℝ),(-2/1:ℝ),(1/1:ℝ),(-1/1:ℝ),(1/1:ℝ)]
def value (m : ℕ) : ℝ := (144:ℝ)^m+∑ i : Fin 13,coefficients i*bases i^m

theorem value_ne_zero (m : ℕ) (hm : 2 ≤ m) : value m≠0 := by
  by_cases h5 : 5 ≤ m
  · exact QuantitativeArithmeticExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 144
      (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 5 m h5
      (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  · have hm5 : m < 5 := by omega
    interval_cases m <;> norm_num [value,coefficients,bases,Fin.sum_univ_succ]

theorem minor_value (m : ℕ) :
    eval ((4:ℂ)^m) ((1:ℂ)*(3:ℂ)^m) ((-1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor13= -(value m:ℂ) := by
  unfold value
  push_cast
  norm_num [coefficients,bases,Fin.sum_univ_succ,minor13,eval,monomial]
  have hb12 : (12:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb16 : (16:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb27 : (27:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb33 : (33:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb36 : (36:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb48 : (48:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb64 : (64:ℂ)^m=((4:ℂ)^m)^3*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 3 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb108 : (108:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb132 : (132:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb144 : (144:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  rw [hb12,hb16,hb27,hb33,hb36,hb48,hb64,hb108,hb132,hb144]
  ring

theorem minor_ne_zero (m : ℕ) (hm : 2 ≤ m) :
    eval ((4:ℂ)^m) ((1:ℂ)*(3:ℂ)^m) ((-1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor13≠0 := by
  rw [minor_value]
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (value_ne_zero m hm))

#print axioms minor_ne_zero
end QuantitativeArithmeticSmallLevelThirtyThreeWeightDominancePPM
end
end

/-! ## ThirtyThreeWeightDominancePMP -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeWeightDominancePMP
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreePlusElimination

def bases : Fin 13→ℝ := ![1,3,4,11,12,16,27,33,36,48,64,108,132]
def coefficients : Fin 13→ℝ := ![(-1/2:ℝ),(-2/1:ℝ),(3/2:ℝ),(3/2:ℝ),(5/2:ℝ),(-2/1:ℝ),(1/2:ℝ),(1/2:ℝ),(-2/1:ℝ),(2/1:ℝ),(1/1:ℝ),(1/1:ℝ),(1/1:ℝ)]
def value (m : ℕ) : ℝ := (144:ℝ)^m+∑ i : Fin 13,coefficients i*bases i^m

theorem value_ne_zero (m : ℕ) (hm : 2 ≤ m) : value m≠0 := by
  by_cases h5 : 5 ≤ m
  · exact QuantitativeArithmeticExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 144
      (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 5 m h5
      (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  · have hm5 : m < 5 := by omega
    interval_cases m <;> norm_num [value,coefficients,bases,Fin.sum_univ_succ]

theorem minor_value (m : ℕ) :
    eval ((4:ℂ)^m) ((-1:ℂ)*(3:ℂ)^m) ((1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor13= -(value m:ℂ) := by
  unfold value
  push_cast
  norm_num [coefficients,bases,Fin.sum_univ_succ,minor13,eval,monomial]
  have hb12 : (12:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb16 : (16:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb27 : (27:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb33 : (33:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb36 : (36:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb48 : (48:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb64 : (64:ℂ)^m=((4:ℂ)^m)^3*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 3 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb108 : (108:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb132 : (132:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb144 : (144:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  rw [hb12,hb16,hb27,hb33,hb36,hb48,hb64,hb108,hb132,hb144]
  ring

theorem minor_ne_zero (m : ℕ) (hm : 2 ≤ m) :
    eval ((4:ℂ)^m) ((-1:ℂ)*(3:ℂ)^m) ((1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor13≠0 := by
  rw [minor_value]
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (value_ne_zero m hm))

#print axioms minor_ne_zero
end QuantitativeArithmeticSmallLevelThirtyThreeWeightDominancePMP
end
end

/-! ## ThirtyThreeWeightDominancePMM -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeWeightDominancePMM
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreePlusElimination

def bases : Fin 13→ℝ := ![1,3,4,11,12,16,27,33,36,48,64,108,132]
def coefficients : Fin 13→ℝ := ![(-1/2:ℝ),(-2/1:ℝ),(3/2:ℝ),(-3/2:ℝ),(5/2:ℝ),(-2/1:ℝ),(1/2:ℝ),(-1/2:ℝ),(-2/1:ℝ),(2/1:ℝ),(1/1:ℝ),(1/1:ℝ),(-1/1:ℝ)]
def value (m : ℕ) : ℝ := (144:ℝ)^m+∑ i : Fin 13,coefficients i*bases i^m

theorem value_ne_zero (m : ℕ) (hm : 2 ≤ m) : value m≠0 := by
  by_cases h5 : 5 ≤ m
  · exact QuantitativeArithmeticExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 144
      (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 5 m h5
      (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  · have hm5 : m < 5 := by omega
    interval_cases m <;> norm_num [value,coefficients,bases,Fin.sum_univ_succ]

theorem minor_value (m : ℕ) :
    eval ((4:ℂ)^m) ((-1:ℂ)*(3:ℂ)^m) ((-1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor13= -(value m:ℂ) := by
  unfold value
  push_cast
  norm_num [coefficients,bases,Fin.sum_univ_succ,minor13,eval,monomial]
  have hb12 : (12:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb16 : (16:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb27 : (27:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb33 : (33:ℂ)^m=((4:ℂ)^m)^0*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 0 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb36 : (36:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb48 : (48:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^1*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 1 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb64 : (64:ℂ)^m=((4:ℂ)^m)^3*((3:ℂ)^m)^0*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 3 0 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb108 : (108:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^3*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 3 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb132 : (132:ℂ)^m=((4:ℂ)^m)^1*((3:ℂ)^m)^1*((11:ℂ)^m)^1 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 1 1 1 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  have hb144 : (144:ℂ)^m=((4:ℂ)^m)^2*((3:ℂ)^m)^2*((11:ℂ)^m)^0 := by
    have hh := QuantitativeArithmeticExponentialDominance.three_powers (4:ℂ) 3 11 2 2 0 m
    norm_num only [pow_zero,pow_one,one_mul,mul_one] at hh ⊢
    convert hh.symm using 1
  rw [hb12,hb16,hb27,hb33,hb36,hb48,hb64,hb108,hb132,hb144]
  ring

theorem minor_ne_zero (m : ℕ) (hm : 2 ≤ m) :
    eval ((4:ℂ)^m) ((-1:ℂ)*(3:ℂ)^m) ((-1:ℂ)*(11:ℂ)^m) 1 (-((4:ℂ)^m)-1) 1 1
      (fun _ => 1) minor13≠0 := by
  rw [minor_value]
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (value_ne_zero m hm))

#print axioms minor_ne_zero
end QuantitativeArithmeticSmallLevelThirtyThreeWeightDominancePMM
end
end

/-! ## ThirtyThreeWeightMinor -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination
open QuantitativeArithmeticSevenLaurentRows

theorem weight_minor_zero (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hn : v 18≠0 ∨ v 42≠0)
    (hrows : ∀ i : Fin 22,eval x y z 1 a 1 1 v (reducedRow i)=0) :
    eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor16=0 := by
  have hh := two_coordinate_minor_zero x y z a (allRow 0) (allRow 16) v 18 42
    (by decide) (allRow_support 0) (allRow_support 16) hn (hrows 0) (hrows 16)
  rw [minor16_identity x y z a hx hy hz] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (zpow_ne_zero _ hx)
      · exact zpow_ne_zero _ hy
    · exact zpow_ne_zero _ hz)

#print axioms weight_minor_zero
end QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination
namespace QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
open QuantitativeArithmeticSevenLaurentRows

theorem weight_minor_zero (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hn : v 18≠0 ∨ v 42≠0)
    (hrows : ∀ i : Fin 22,eval x y z 1 a 1 1 v (reducedRow i)=0) :
    eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor13=0 := by
  have hh := two_coordinate_minor_zero x y z a (allRow 0) (allRow 16) v 18 42
    (by decide) (allRow_support 0) (allRow_support 16) hn (hrows 0) (hrows 16)
  rw [minor13_identity x y z a hx hy hz] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (zpow_ne_zero _ hx)
      · exact zpow_ne_zero _ hy
    · exact zpow_ne_zero _ hz)

#print axioms weight_minor_zero
end QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
end
end

/-! ## ThirtyThreeWeightKernel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeLaurent

theorem weight_kernel_zero (m : ℕ) (hm : 2 ≤ m) (u v a : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (ha : a*(2:ℂ)^m= -(4:ℂ)^m-1) (w : ℕ→ℂ)
    (hb : ∀ j,eval ((2:ℂ)^m) (u*(3:ℂ)^m) (v*(11:ℂ)^m)
      1 a 1 1 w (baseRows (-1) j)=0) :
    ∀ j : ℕ,j<66 → w j=0 := by
  have hx : (2:ℂ)^m≠0 := pow_ne_zero _ (by norm_num)
  have hy : u*(3:ℂ)^m≠0 := mul_ne_zero (by rcases hu with rfl|rfl <;> norm_num)
    (pow_ne_zero _ (by norm_num))
  have hz : v*(11:ℂ)^m≠0 := mul_ne_zero (by rcases hv with rfl|rfl <;> norm_num)
    (pow_ne_zero _ (by norm_num))
  by_cases hn : w 18=0 ∧ w 42=0
  · exact kernel_free_zero _ _ _ _ w hx hy hz hb hn.1 hn.2
  · have hn' : w 18≠0 ∨ w 42≠0 := by tauto
    have hr := reduced_rows_zero _ _ _ _ w hx hy hz hb
    have he := weight_minor_zero _ _ _ _ w hx hy hz hn' hr
    have hx2 : ((2:ℂ)^m)^2=(4:ℂ)^m := by
      rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
      norm_num
    rw [hx2,ha] at he
    exfalso
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
    · exact QuantitativeArithmeticSmallLevelThirtyThreeWeightDominanceMPP.minor_ne_zero m hm he
    · exact QuantitativeArithmeticSmallLevelThirtyThreeWeightDominanceMPM.minor_ne_zero m hm he
    · exact QuantitativeArithmeticSmallLevelThirtyThreeWeightDominanceMMP.minor_ne_zero m hm he
    · exact QuantitativeArithmeticSmallLevelThirtyThreeWeightDominanceMMM.minor_ne_zero m hm he

#print axioms weight_kernel_zero
end QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination
namespace QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeLaurent

theorem weight_kernel_zero (m : ℕ) (hm : 2 ≤ m) (u v a : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (ha : a*(2:ℂ)^m= -(4:ℂ)^m-1) (w : ℕ→ℂ)
    (hb : ∀ j,eval ((2:ℂ)^m) (u*(3:ℂ)^m) (v*(11:ℂ)^m)
      1 a 1 1 w (baseRows 1 j)=0) :
    ∀ j : ℕ,j<66 → w j=0 := by
  have hx : (2:ℂ)^m≠0 := pow_ne_zero _ (by norm_num)
  have hy : u*(3:ℂ)^m≠0 := mul_ne_zero (by rcases hu with rfl|rfl <;> norm_num)
    (pow_ne_zero _ (by norm_num))
  have hz : v*(11:ℂ)^m≠0 := mul_ne_zero (by rcases hv with rfl|rfl <;> norm_num)
    (pow_ne_zero _ (by norm_num))
  by_cases hn : w 18=0 ∧ w 42=0
  · exact kernel_free_zero _ _ _ _ w hx hy hz hb hn.1 hn.2
  · have hn' : w 18≠0 ∨ w 42≠0 := by tauto
    have hr := reduced_rows_zero _ _ _ _ w hx hy hz hb
    have he := weight_minor_zero _ _ _ _ w hx hy hz hn' hr
    have hx2 : ((2:ℂ)^m)^2=(4:ℂ)^m := by
      rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
      norm_num
    rw [hx2,ha] at he
    exfalso
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
    · exact QuantitativeArithmeticSmallLevelThirtyThreeWeightDominancePPP.minor_ne_zero m hm he
    · exact QuantitativeArithmeticSmallLevelThirtyThreeWeightDominancePPM.minor_ne_zero m hm he
    · exact QuantitativeArithmeticSmallLevelThirtyThreeWeightDominancePMP.minor_ne_zero m hm he
    · exact QuantitativeArithmeticSmallLevelThirtyThreeWeightDominancePMM.minor_ne_zero m hm he

#print axioms weight_kernel_zero
end QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
end
end

/-! ## ThirtyThreeWeightChainArithmetic -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeWeightChain

theorem last_factor_ne_zero (x y a : ℝ) (hx : 2 ≤ x) (ha : a*x ≤ 0)
    (hy : y ≤ -1 ∨ 1 ≤ y) : -a*x*y+a*x+x^2*y+x^2-2≠0 := by
  have hc : 0 ≤ x^2-a*x := by nlinarith [sq_nonneg x]
  rcases hy with hy|hy
  · have hmul := mul_nonpos_of_nonneg_of_nonpos hc (show y+1 ≤ 0 by linarith)
    nlinarith
  · have hmul := mul_nonneg hc (show 0 ≤ y-1 by linarith)
    nlinarith

/-- Real arithmetic for a pole chain ending at the weight point and
starting at least one integer to its left. The sole candidate is weight
two with one shift; a separate finite leading-rank check removes it. -/
theorem positive_gap_candidate (x r y a : ℝ)
    (hr : 2 ≤ r) (hx : r ≤ x) (hy : y ≤ -1 ∨ 1 ≤ y)
    (hd : a*x*r= -x^2-r^2)
    (hminor : (a+x)*(a*x+x^2+1)*(-a*x*y+a*x+x^2*y+x^2-2)=0) :
    x=2 ∧ r=2 ∧ a= -2 := by
  have hr0 : 0 < r := by linarith
  have hx0 : 0 < x := by linarith
  have hax : a*x ≤ 0 := by
    apply nonpos_of_mul_nonpos_right _ hr0
    nlinarith [sq_nonneg x,sq_nonneg r]
  have hlast := last_factor_ne_zero x y a (by linarith) hax hy
  have hfirst : a+x=0 ∨ a*x+x^2+1=0 := by
    exact mul_eq_zero.mp ((mul_eq_zero.mp hminor).resolve_right hlast)
  have hx2 : r^2 ≤ x^2 := by nlinarith
  have hsecond : a*x+x^2+1≠0 := by
    intro h
    have he : (r-1)*(x^2-r)=0 := by linear_combination r*h-hd
    have hpos : 0 < (r-1)*(x^2-r) := mul_pos (by linarith) (by nlinarith)
    linarith
  have ha0 := hfirst.resolve_right hsecond
  have he : x^2*(r-1)=r^2 := by linear_combination -hd+x*r*ha0
  have hcmp := mul_le_mul_of_nonneg_right hx2 (show 0 ≤ r-1 by linarith)
  rw [he] at hcmp
  have hrle : r-1 ≤ 1 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hr0)).mp
    simpa only [one_mul,mul_one,mul_comm] using hcmp
  have hr2 : r=2 := by linarith
  have hxEq : x=2 := by rw [hr2] at he; nlinarith
  refine ⟨hxEq,hr2,?_⟩
  linarith

#print axioms positive_gap_candidate
end QuantitativeArithmeticSmallLevelThirtyThreeWeightChain
end
end

/-! ## ThirtyThreeWeightChainParameters -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeWeightChain
open Complex QuantitativeArithmeticSmallLevelThirtyThreeMinor

theorem real_pow_ge_one (b : ℝ) (hb : 1 ≤ b) (n : ℕ) : 1 ≤ b^n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; nlinarith

theorem real_pow_mono (b : ℝ) (hb : 1 ≤ b) {n m : ℕ} (h : n ≤ m) : b^n ≤ b^m := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  nlinarith [real_pow_ge_one b hb n,real_pow_ge_one b hb d]

theorem two_pow_eq_two (n : ℕ) (h : (2:ℝ)^n=2) : n=1 := by
  cases n with
  | zero => norm_num at h
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [pow_succ] at h
      nlinarith [real_pow_ge_one 2 (by norm_num) n]

/-- The real positivity certificate applied to the actual integer powers
at a weight-point pole chain. The complex eigenvalue becomes real from
the denominator equation itself. -/
theorem positive_gap_parameters (m n : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (u : ℝ) (hu : u=1 ∨ u= -1) (a : ℂ)
    (hd : (2:ℂ)^(m-n)+((2:ℂ)^(m-n))⁻¹+a=0)
    (hminor : determinant ((2:ℂ)^m) ((u:ℂ)*(3:ℂ)^m) a=0) :
    m=1 ∧ n=1 ∧ a= -2 := by
  let x : ℝ := 2^m
  let r : ℝ := 2^n
  let t : ℝ := 2^(m-n)
  let A : ℝ := -t-t⁻¹
  have ht0 : t≠0 := pow_ne_zero _ (by norm_num)
  have hx0 : x≠0 := pow_ne_zero _ (by norm_num)
  have hx : t*r=x := by
    dsimp [t,r,x]
    rw [← pow_add,Nat.sub_add_cancel hnm]
  have ha : a=(A:ℂ) := by
    dsimp [A,t]
    push_cast
    linear_combination hd
  have hdR : A*x*r= -x^2-r^2 := by
    rw [← hx]
    dsimp [A]
    field_simp
  have hr : 2 ≤ r := by
    have hh := real_pow_mono 2 (by norm_num) (show 1 ≤ n by omega)
    simpa only [pow_one] using hh
  have hxr : r ≤ x := real_pow_mono 2 (by norm_num) hnm
  have hy : u*(3:ℝ)^m ≤ -1 ∨ 1 ≤ u*(3:ℝ)^m := by
    have hh := real_pow_ge_one 3 (by norm_num) m
    rcases hu with rfl|rfl
    · right; simpa only [one_mul] using hh
    · left; simp only [neg_one_mul]; linarith
  have hprod : (A+x)*(A*x+x^2+1)*(-A*x*(u*3^m)+A*x+x^2*(u*3^m)+x^2-2)=0 := by
    rw [ha] at hminor
    unfold determinant at hminor
    have hz : ((x:ℂ)^5)≠0 := pow_ne_zero _ (by exact_mod_cast hx0)
    have he := (div_eq_zero_iff).mp hminor
    have hp := he.resolve_right (by simpa only [x,Complex.ofReal_pow,Complex.ofReal_ofNat] using hz)
    dsimp only [x]
    exact_mod_cast hp
  obtain ⟨hx2,hr2,hA⟩ := positive_gap_candidate x r (u*3^m) A hr hxr hy hdR hprod
  refine ⟨two_pow_eq_two m hx2,two_pow_eq_two n hr2,?_⟩
  rw [ha,hA]
  norm_num

#print axioms positive_gap_parameters
end QuantitativeArithmeticSmallLevelThirtyThreeWeightChain
end
end

/-! ## ThirtyThreeMinusBranchCases -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination
open QuantitativeArithmeticSevenLaurentRows

theorem minor0_factored (x y z a : ℂ) :
    eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor0=
      (a*x+x^2)*(a*x+x^2+1)*(y-3/2) := by
  norm_num [minor0,eval,monomial]
  ring

theorem branch_cases (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hn : v 18≠0 ∨ v 42≠0)
    (hrows : ∀ i : Fin 23,eval x y z 1 a 1 1 v (allRow i)=0) :
    a*x= -x^2 ∨ a*x= -x^2-1 ∨ y=3/2 := by
  have hh := minor0_zero x y z a v hx hy hz hn hrows
  rw [minor0_factored] at hh
  rcases mul_eq_zero.mp hh with hh|hh
  · rcases mul_eq_zero.mp hh with hh|hh
    · left; linear_combination hh
    · right; left; linear_combination hh
  · right; right; exact sub_eq_zero.mp hh

#print axioms branch_cases
end QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination
end
end

/-! ## ThirtyThreeMinusReducedLocus -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeRoot QuantitativeArithmeticSmallLevelThirtyThreeLocus

theorem reduced_locus (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hn : v 18≠0 ∨ v 42≠0)
    (hrows : ∀ i : Fin 23,eval x y z 1 a 1 1 v (allRow i)=0) :
    InLocus (x^2) y (a*x) := by
  have h0 := minor0_zero x y z a v hx hy hz hn hrows
  have h3 := minor3_zero x y z a v hx hy hz hn hrows
  have h6 := minor6_zero x y z a v hx hy hz hn hrows
  have h12 := minor12_zero x y z a v hx hy hz hn hrows
  have h16 := minor16_zero x y z a v hx hy hz hn hrows
  have h25 := minor25_zero x y z a v hx hy hz hn hrows
  rcases branch_cases x y z a v hx hy hz hn hrows with hc|hc|hc
  · rw [hc] at h6 h12 h25
    have ht := branch1_target1 (x^2) y z h6 h12 h25
    exact Or.inl ⟨hc,by linear_combination ht⟩
  · rw [hc] at h3 h12 h16 h25
    have ht := branch2_target1 (x^2) y z h3 h12 h16 h25
    have hxv := branch2_target2 (x^2) y z h3 h12 h16 h25
    have hpoly : (3-y)*p7.eval (-y)=0 := by
      rw [septic_expression] at ht
      linear_combination ht/704
    have hr : y=3 ∨ p7.eval (-y)=0 := by
      rcases mul_eq_zero.mp hpoly with hh|hh
      · left; exact (sub_eq_zero.mp hh).symm
      · exact Or.inr hh
    have he : x^2=xPoly.eval (-y) := by
      rw [← x_expression]
      linear_combination hxv
    exact Or.inr ⟨hc,hr,he⟩
  · rw [hc] at h3 h6 h16 h25
    have ha := branch3_target1 (x^2) (a*x) z h3 h6 h16 h25
    have hxv := branch3_target2 (x^2) (a*x) z h3 h6 h16 h25
    left
    constructor
    · linear_combination ha
    · rw [hc]
      linear_combination hxv

#print axioms reduced_locus
end QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination
end
end

/-! ## ThirtyThreePlusBranchCases -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
open QuantitativeArithmeticSevenLaurentRows

theorem minor0_factored (x y z a : ℂ) :
    eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor0=
      (a*x+x^2)*(a*x+x^2+1)*(y-3/2) := by
  norm_num [minor0,eval,monomial]
  ring

theorem branch_cases (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hn : v 18≠0 ∨ v 42≠0)
    (hrows : ∀ i : Fin 23,eval x y z 1 a 1 1 v (allRow i)=0) :
    a*x= -x^2 ∨ a*x= -x^2-1 ∨ y=3/2 := by
  have hh := minor0_zero x y z a v hx hy hz hn hrows
  rw [minor0_factored] at hh
  rcases mul_eq_zero.mp hh with hh|hh
  · rcases mul_eq_zero.mp hh with hh|hh
    · left; linear_combination hh
    · right; left; linear_combination hh
  · right; right; exact sub_eq_zero.mp hh

#print axioms branch_cases
end QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
end
end

/-! ## ThirtyThreePlusReducedLocus -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeRoot QuantitativeArithmeticSmallLevelThirtyThreeLocus

theorem reduced_locus (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hn : v 18≠0 ∨ v 42≠0)
    (hrows : ∀ i : Fin 23,eval x y z 1 a 1 1 v (allRow i)=0) :
    InLocus (x^2) y (a*x) := by
  have h0 := minor0_zero x y z a v hx hy hz hn hrows
  have h3 := minor3_zero x y z a v hx hy hz hn hrows
  have h6 := minor6_zero x y z a v hx hy hz hn hrows
  have h12 := minor12_zero x y z a v hx hy hz hn hrows
  have h13 := minor13_zero x y z a v hx hy hz hn hrows
  have h25 := minor25_zero x y z a v hx hy hz hn hrows
  rcases branch_cases x y z a v hx hy hz hn hrows with hc|hc|hc
  · rw [hc] at h6 h12 h25
    have ht := branch1_target1 (x^2) y z h6 h12 h25
    exact Or.inl ⟨hc,by linear_combination ht⟩
  · rw [hc] at h3 h12 h13 h25
    have ht := branch2_target1 (x^2) y z h3 h12 h13 h25
    have hxv := branch2_target2 (x^2) y z h3 h12 h13 h25
    have hpoly : (3-y)*p7.eval (-y)=0 := by
      rw [septic_expression] at ht
      linear_combination ht/704
    have hr : y=3 ∨ p7.eval (-y)=0 := by
      rcases mul_eq_zero.mp hpoly with hh|hh
      · left; exact (sub_eq_zero.mp hh).symm
      · exact Or.inr hh
    have he : x^2=xPoly.eval (-y) := by
      rw [← x_expression]
      linear_combination hxv
    exact Or.inr ⟨hc,hr,he⟩
  · rw [hc] at h3 h6 h13 h25
    have ha := branch3_target1 (x^2) (a*x) z h3 h6 h13 h25
    have hxv := branch3_target2 (x^2) (a*x) z h3 h6 h13 h25
    left
    constructor
    · linear_combination ha
    · rw [hc]
      linear_combination hxv

#print axioms reduced_locus
end QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
end
end

/-! ## ThirtyThreeLeadingPole -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix QuantitativeArithmeticUniversalPoleVector

/-- At a rightmost pole, every original leading row annihilates the
nonzero leading Laurent vector. Lower shifted poles are not discarded. -/
theorem PoleSystem.rightmost_leading_kernel {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ) (v : Fin 66→ℂ)
    (hv : IsLeadingVector S.G x v)
    (hshift : ∀ n : ℕ,0 < n → ∀ j,0 ≤ meromorphicOrderAt (fun z => S.G z j) (x+n)) :
    fullLeadingMatrix m f ε x *ᵥ v=0 := by
  funext i
  exact hv.taylor_at S.meromorphic hshift S.B
    (fun z j => fullLeadingMatrix m f ε z i j)
    (fun n z j => fullShiftMatrix m f ε n z i j) (fun n z => S.E n z i)
    (fun j => fullLeadingMatrix_analytic m f ε i j x)
    (fun n j => fullShiftMatrix_analytic m f ε n i j x)
    (fun n hn => S.error n i x hn)
    (fun n hn => S.continued_rows n i x hn)

#print axioms PoleSystem.rightmost_leading_kernel
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeOriginalLocus -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelPrimeRates QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelThirtyThreeLaurent QuantitativeArithmeticUniversalPoleVector QuantitativeArithmeticSmallLevelThirtyThreeLocus

theorem original_base_kernel (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (ε s : ℂ) (hε : ε=1 ∨ ε= -1) (σ : ℚ)
    (hσ : (σ:ℂ)=phase m ε*badParameter f 3*badParameter f 11)
    (v : Fin 66→ℂ) (hv : fullLeadingMatrix m f ε s*ᵥv=0) :
    ∀ j,eval (parameter 2 m s) (badParameter f 3*parameter 3 m s)
      (badParameter f 11*parameter 11 m s) 1 (badParameter f 2) 1 1
      (fun i => v (gridIndex (i:ℤ))) (baseRows σ j)=0 := by
  rw [fullLeadingMatrix_mulVec] at hv
  intro j
  by_cases hj : j<775
  · rw [scaled_base_physical m hf ε s hε σ hσ v j hj,hv]
    rfl
  · rw [baseRows,dite_eq_right hj,eval_nil]

/-- The algebraic locus is now derived from the original pole system,
without assuming any finite algebraic equations separately. -/
theorem PoleSystem.leading_locus {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε)
    (s : ℂ) (v : Fin 66→ℂ) (hv : IsLeadingVector S.G s v)
    (hshift : ∀ n : ℕ,0 < n → ∀ j,0 ≤ meromorphicOrderAt (fun z => S.G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) :
    InLocus ((parameter 2 m s)^2) (badParameter f 3*parameter 3 m s)
      (badParameter f 2*parameter 2 m s) := by
  classical
  have hu : badParameter f 3≠0 := by
    rcases badParameter_three_sign hf.toEulerData with h|h <;> simp [h]
  have hw : badParameter f 11≠0 := by
    rcases badParameter_eleven_sign hf.toEulerData with h|h <;> simp [h]
  have hx := parameter_ne_zero 2 m (by decide) s
  have hy := mul_ne_zero hu (parameter_ne_zero 3 m (by decide) s)
  have hz := mul_ne_zero hw (parameter_ne_zero 11 m (by decide) s)
  have hk := S.rightmost_leading_kernel s v hv hshift
  rcases scaled_phase_sign m hf hε with hσ|hσ
  · have hh : ((1:ℚ):ℂ)=phase m ε*badParameter f 3*badParameter f 11 := by
      simpa only [Rat.cast_one,Rat.cast_neg] using hσ.symm
    have hb := original_base_kernel m hf ε s hε 1 hh v hk
    have hj := S.first_jet_polynomial hf hε s v hv hshift 1 hh hs
    rw [selectedOperations,ite_eq_left hσ] at hj
    have hn : v (gridIndex (18:ℤ))≠0 ∨ v (gridIndex (42:ℤ))≠0 := by
      by_contra hn
      push Not at hn
      have hzv := QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.kernel_free_zero (parameter 2 m s) (badParameter f 3*parameter 3 m s) (badParameter f 11*parameter 11 m s) (badParameter f 2) (fun i => v (gridIndex (i:ℤ))) hx hy hz hb hn.1 hn.2
      apply hv.1
      funext i
      simpa only [gridIndex_fin,Pi.zero_apply] using hzv i.val i.isLt
    exact QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reduced_locus (parameter 2 m s) (badParameter f 3*parameter 3 m s) (badParameter f 11*parameter 11 m s) (badParameter f 2) (fun i => v (gridIndex (i:ℤ))) hx hy hz hn
      (QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.allRow_zero _ _ _ _ _
        (QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reduced_rows_zero (parameter 2 m s) (badParameter f 3*parameter 3 m s) (badParameter f 11*parameter 11 m s) (badParameter f 2) (fun i => v (gridIndex (i:ℤ))) hx hy hz hb)
        (QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reduced_jet_zero (parameter 2 m s) (badParameter f 3*parameter 3 m s) (badParameter f 11*parameter 11 m s) (badParameter f 2) (fun i => v (gridIndex (i:ℤ))) hx hy hz hb hj))
  · have hh : (((-1):ℚ):ℂ)=phase m ε*badParameter f 3*badParameter f 11 := by
      simpa only [Rat.cast_one,Rat.cast_neg] using hσ.symm
    have hb := original_base_kernel m hf ε s hε (-1) hh v hk
    have hj := S.first_jet_polynomial hf hε s v hv hshift (-1) hh hs
    have hnσ : phase m ε*badParameter f 3*badParameter f 11≠1 := by
      rw [hσ]
      norm_num
    rw [selectedOperations,ite_eq_right hnσ] at hj
    have hn : v (gridIndex (18:ℤ))≠0 ∨ v (gridIndex (42:ℤ))≠0 := by
      by_contra hn
      push Not at hn
      have hzv := QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.kernel_free_zero (parameter 2 m s) (badParameter f 3*parameter 3 m s) (badParameter f 11*parameter 11 m s) (badParameter f 2) (fun i => v (gridIndex (i:ℤ))) hx hy hz hb hn.1 hn.2
      apply hv.1
      funext i
      simpa only [gridIndex_fin,Pi.zero_apply] using hzv i.val i.isLt
    exact QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reduced_locus (parameter 2 m s) (badParameter f 3*parameter 3 m s) (badParameter f 11*parameter 11 m s) (badParameter f 2) (fun i => v (gridIndex (i:ℤ))) hx hy hz hn
      (QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.allRow_zero _ _ _ _ _
        (QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reduced_rows_zero (parameter 2 m s) (badParameter f 3*parameter 3 m s) (badParameter f 11*parameter 11 m s) (badParameter f 2) (fun i => v (gridIndex (i:ℤ))) hx hy hz hb)
        (QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reduced_jet_zero (parameter 2 m s) (badParameter f 3*parameter 3 m s) (badParameter f 11*parameter 11 m s) (badParameter f 2) (fun i => v (gridIndex (i:ℤ))) hx hy hz hb hj))

theorem PoleSystem.rightmost_locus {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε) (s : ℂ)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) s < 0)
    (hshift : ∀ n : ℕ,0 < n → ∀ j,0 ≤ meromorphicOrderAt (fun z => S.G z j) (s+n))
    (hs : s≠((2*m:ℕ):ℂ)) :
    InLocus ((parameter 2 m s)^2) (badParameter f 3*parameter 3 m s)
      (badParameter f 2*parameter 2 m s) := by
  obtain ⟨v,hv⟩ := exists_leading_vector S.G s
    (fun j => (S.meromorphic j s).meromorphicAt) hpole
  exact S.leading_locus hf hε s v hv hshift hs

#print axioms PoleSystem.rightmost_locus
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeWeightTwoRank -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeWeightTwoRank
open QuantitativeArithmeticSevenLaurentRows

theorem mpp (v : ℕ→ℂ)
    (h : ∀ i : Fin 22,eval 2 (3) (11) 1 (-2) 1 1 v (QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reducedRow i)=0) :
    v 18=0 ∧ v 42=0 := by
  have h3 := h 3
  have h4 := h 4
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reducedRow,eval,monomial] at h3 h4
  constructor
  · linear_combination (-153/11:ℂ)*h3-(1/1:ℂ)*h4
  · linear_combination (169/11:ℂ)*h3+(1/1:ℂ)*h4

theorem mpm (v : ℕ→ℂ)
    (h : ∀ i : Fin 22,eval 2 (3) (-11) 1 (-2) 1 1 v (QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reducedRow i)=0) :
    v 18=0 ∧ v 42=0 := by
  have h3 := h 3
  have h4 := h 4
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reducedRow,eval,monomial] at h3 h4
  constructor
  · linear_combination (89/11:ℂ)*h3-(1/1:ℂ)*h4
  · linear_combination (-73/11:ℂ)*h3+(1/1:ℂ)*h4

theorem mmp (v : ℕ→ℂ)
    (h : ∀ i : Fin 22,eval 2 (-3) (11) 1 (-2) 1 1 v (QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reducedRow i)=0) :
    v 18=0 ∧ v 42=0 := by
  have h3 := h 3
  have h4 := h 4
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reducedRow,eval,monomial] at h3 h4
  constructor
  · linear_combination (230/39:ℂ)*h3-(-2/3:ℂ)*h4
  · linear_combination (-278/39:ℂ)*h3+(-2/3:ℂ)*h4

theorem mmm (v : ℕ→ℂ)
    (h : ∀ i : Fin 22,eval 2 (-3) (-11) 1 (-2) 1 1 v (QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reducedRow i)=0) :
    v 18=0 ∧ v 42=0 := by
  have h3 := h 3
  have h4 := h 4
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reducedRow,eval,monomial] at h3 h4
  constructor
  · linear_combination (802/39:ℂ)*h3-(-2/3:ℂ)*h4
  · linear_combination (-850/39:ℂ)*h3+(-2/3:ℂ)*h4

theorem ppp (v : ℕ→ℂ)
    (h : ∀ i : Fin 22,eval 2 (3) (11) 1 (-2) 1 1 v (QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reducedRow i)=0) :
    v 18=0 ∧ v 42=0 := by
  have h3 := h 3
  have h4 := h 4
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reducedRow,eval,monomial] at h3 h4
  constructor
  · linear_combination (111/11:ℂ)*h3-(1/1:ℂ)*h4
  · linear_combination (-95/11:ℂ)*h3+(1/1:ℂ)*h4

theorem ppm (v : ℕ→ℂ)
    (h : ∀ i : Fin 22,eval 2 (3) (-11) 1 (-2) 1 1 v (QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reducedRow i)=0) :
    v 18=0 ∧ v 42=0 := by
  have h3 := h 3
  have h4 := h 4
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reducedRow,eval,monomial] at h3 h4
  constructor
  · linear_combination (-131/11:ℂ)*h3-(1/1:ℂ)*h4
  · linear_combination (147/11:ℂ)*h3+(1/1:ℂ)*h4

theorem pmp (v : ℕ→ℂ)
    (h : ∀ i : Fin 22,eval 2 (-3) (11) 1 (-2) 1 1 v (QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reducedRow i)=0) :
    v 18=0 ∧ v 42=0 := by
  have h3 := h 3
  have h4 := h 4
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reducedRow,eval,monomial] at h3 h4
  constructor
  · linear_combination (854/39:ℂ)*h3-(-2/3:ℂ)*h4
  · linear_combination (-902/39:ℂ)*h3+(-2/3:ℂ)*h4

theorem pmm (v : ℕ→ℂ)
    (h : ∀ i : Fin 22,eval 2 (-3) (-11) 1 (-2) 1 1 v (QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reducedRow i)=0) :
    v 18=0 ∧ v 42=0 := by
  have h3 := h 3
  have h4 := h 4
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reducedRow,eval,monomial] at h3 h4
  constructor
  · linear_combination (94/13:ℂ)*h3-(-2/3:ℂ)*h4
  · linear_combination (-110/13:ℂ)*h3+(-2/3:ℂ)*h4

#print axioms pmm
end QuantitativeArithmeticSmallLevelThirtyThreeWeightTwoRank
end
end

/-! ## ThirtyThreeOriginalWeightTwoRank -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelPrimeRates QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelThirtyThreeLaurent

theorem weight_two_minus_two_kernel (f : ℕ→ℂ)
    (hf : FinitenessOriginalInput.IsSolution 33 2 f) (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (ha : badParameter f 2= -2) (v : Fin 66→ℂ)
    (hv : fullLeadingMatrix 1 f ε 2*ᵥv=0) : v=0 := by
  have hp (p : ℕ) : parameter p 1 2=(p:ℂ) := by norm_num [parameter]
  have hsol : FinitenessOriginalInput.IsSolution 33 (2*1) f := hf
  rcases badParameter_three_sign hf.toEulerData with h3|h3 <;>
    rcases badParameter_eleven_sign hf.toEulerData with h11|h11 <;>
      rcases scaled_phase_sign 1 hsol hε with hσ|hσ
  · have hs : ((1:ℚ):ℂ)=phase 1 ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
    have hb := original_base_kernel 1 hsol ε 2 hε 1 hs v hv
    simp only [hp,h3,h11,ha,one_mul,neg_one_mul,Nat.cast_ofNat] at hb
    have hr := QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reduced_rows_zero 2 (3) (11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb
    obtain ⟨h18,h42⟩ := QuantitativeArithmeticSmallLevelThirtyThreeWeightTwoRank.ppp _ hr
    have hz := QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.kernel_free_zero 2 (3) (11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb h18 h42
    funext i
    simpa only [gridIndex_fin,Pi.zero_apply] using hz i.val i.isLt
  · have hs : (((-1):ℚ):ℂ)=phase 1 ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
    have hb := original_base_kernel 1 hsol ε 2 hε (-1) hs v hv
    simp only [hp,h3,h11,ha,one_mul,neg_one_mul,Nat.cast_ofNat] at hb
    have hr := QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reduced_rows_zero 2 (3) (11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb
    obtain ⟨h18,h42⟩ := QuantitativeArithmeticSmallLevelThirtyThreeWeightTwoRank.mpp _ hr
    have hz := QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.kernel_free_zero 2 (3) (11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb h18 h42
    funext i
    simpa only [gridIndex_fin,Pi.zero_apply] using hz i.val i.isLt
  · have hs : ((1:ℚ):ℂ)=phase 1 ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
    have hb := original_base_kernel 1 hsol ε 2 hε 1 hs v hv
    simp only [hp,h3,h11,ha,one_mul,neg_one_mul,Nat.cast_ofNat] at hb
    have hr := QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reduced_rows_zero 2 (3) (-11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb
    obtain ⟨h18,h42⟩ := QuantitativeArithmeticSmallLevelThirtyThreeWeightTwoRank.ppm _ hr
    have hz := QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.kernel_free_zero 2 (3) (-11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb h18 h42
    funext i
    simpa only [gridIndex_fin,Pi.zero_apply] using hz i.val i.isLt
  · have hs : (((-1):ℚ):ℂ)=phase 1 ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
    have hb := original_base_kernel 1 hsol ε 2 hε (-1) hs v hv
    simp only [hp,h3,h11,ha,one_mul,neg_one_mul,Nat.cast_ofNat] at hb
    have hr := QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reduced_rows_zero 2 (3) (-11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb
    obtain ⟨h18,h42⟩ := QuantitativeArithmeticSmallLevelThirtyThreeWeightTwoRank.mpm _ hr
    have hz := QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.kernel_free_zero 2 (3) (-11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb h18 h42
    funext i
    simpa only [gridIndex_fin,Pi.zero_apply] using hz i.val i.isLt
  · have hs : ((1:ℚ):ℂ)=phase 1 ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
    have hb := original_base_kernel 1 hsol ε 2 hε 1 hs v hv
    simp only [hp,h3,h11,ha,one_mul,neg_one_mul,Nat.cast_ofNat] at hb
    have hr := QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reduced_rows_zero 2 (-3) (11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb
    obtain ⟨h18,h42⟩ := QuantitativeArithmeticSmallLevelThirtyThreeWeightTwoRank.pmp _ hr
    have hz := QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.kernel_free_zero 2 (-3) (11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb h18 h42
    funext i
    simpa only [gridIndex_fin,Pi.zero_apply] using hz i.val i.isLt
  · have hs : (((-1):ℚ):ℂ)=phase 1 ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
    have hb := original_base_kernel 1 hsol ε 2 hε (-1) hs v hv
    simp only [hp,h3,h11,ha,one_mul,neg_one_mul,Nat.cast_ofNat] at hb
    have hr := QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reduced_rows_zero 2 (-3) (11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb
    obtain ⟨h18,h42⟩ := QuantitativeArithmeticSmallLevelThirtyThreeWeightTwoRank.mmp _ hr
    have hz := QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.kernel_free_zero 2 (-3) (11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb h18 h42
    funext i
    simpa only [gridIndex_fin,Pi.zero_apply] using hz i.val i.isLt
  · have hs : ((1:ℚ):ℂ)=phase 1 ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
    have hb := original_base_kernel 1 hsol ε 2 hε 1 hs v hv
    simp only [hp,h3,h11,ha,one_mul,neg_one_mul,Nat.cast_ofNat] at hb
    have hr := QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reduced_rows_zero 2 (-3) (-11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb
    obtain ⟨h18,h42⟩ := QuantitativeArithmeticSmallLevelThirtyThreeWeightTwoRank.pmm _ hr
    have hz := QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.kernel_free_zero 2 (-3) (-11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb h18 h42
    funext i
    simpa only [gridIndex_fin,Pi.zero_apply] using hz i.val i.isLt
  · have hs : (((-1):ℚ):ℂ)=phase 1 ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
    have hb := original_base_kernel 1 hsol ε 2 hε (-1) hs v hv
    simp only [hp,h3,h11,ha,one_mul,neg_one_mul,Nat.cast_ofNat] at hb
    have hr := QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reduced_rows_zero 2 (-3) (-11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb
    obtain ⟨h18,h42⟩ := QuantitativeArithmeticSmallLevelThirtyThreeWeightTwoRank.mmm _ hr
    have hz := QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.kernel_free_zero 2 (-3) (-11) (-2)
      (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hb h18 h42
    funext i
    simpa only [gridIndex_fin,Pi.zero_apply] using hz i.val i.isLt

#print axioms weight_two_minus_two_kernel
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeRootNodeBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyThreeRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds

def node0Center : ℚ×ℚ := ((-1423630476918569479/125000000000000000),(0/1))
def node0R : ℚ := (12/1)
def node0Bound : ℚ := (8324722001434427001361/390625000000000000000000000)
def node0State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((-13801909275802449302363189376489/10000000000000000000000000000000000000000),(0/1))
  | 1 => ((20911993799619652112281696741648712457251/10000000000000000000000000000000000000000),(0/1))
  | 2 => ((-23800039272509582963972503966933072677927/5000000000000000000000000000000000000000),(0/1))
  | 3 => ((1945203082979161825107179423801503252097/400000000000000000000000000000000000000),(0/1))
  | 4 => ((-5512536459295229664977795898421695413831/2500000000000000000000000000000000000000),(0/1))
  | 5 => ((12911338526342951795461610276469697483639/5000000000000000000000000000000000000000),(0/1))
  | 6 => ((782053650529948112727272727272727272727/5000000000000000000000000000000000000000),(0/1))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node0Error : ℕ→ℚ := fun j => match j with
  | 0 => (187446104518057315566223441/1000000000000000000000000000000000000000000000000000000000000)
  | 1 => (15620505758492003383636917/1000000000000000000000000000000000000000000000000000000000000)
  | 2 => (508477883901053940209/390625000000000000000000000000000000000000000000000000000)
  | 3 => (2711763291953410492073/25000000000000000000000000000000000000000000000000000000000)
  | 4 => (903495973706308456051/100000000000000000000000000000000000000000000000000000000000)
  | 5 => (748493299019012136297/1000000000000000000000000000000000000000000000000000000000000)
  | 6 => (10909090909090909091/200000000000000000000000000000000000000000000000000000000000)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node0Distance : Fin 7→ℚ := ![(1/1),(5239/500),(5239/500),(1457/125),(1457/125),(11953/1000),(11953/1000)]
theorem node0_norm : |node0Center.1|+|node0Center.2|≤node0R := by decide +kernel
theorem node0_error_nonneg : ∀ j : Fin 9,0≤node0Error j.val := by decide +kernel
theorem node0_terminal : |(node0State 8).1|+|(node0State 8).2|≤node0Error 8 := by decide +kernel
theorem node0_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node0Center (node0State (j.val+1)) (node0State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node0Center (node0State (j.val+1)) (node0State j.val)).2|+
    node0R*node0Error (j.val+1)≤node0Error j.val := by decide +kernel
theorem node0_final : |(node0State 0).1|+|(node0State 0).2|+node0Error 0≤node0Bound := by decide +kernel

theorem node0_bound : ‖p7.eval (ratComplex (centerQ 0))‖≤(node0Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node0Center
    node0State node0Error node0R node0Bound 8
    node0_norm (fun j hj => node0_error_nonneg ⟨j,by omega⟩)
    node0_terminal (fun j hj => node0_steps ⟨j,hj⟩) node0_final

theorem node0_distance_positive : ∀ j : Fin 7,0<node0Distance j := by decide +kernel
theorem node0_distance_diagonal : node0Distance 0=1 := by decide +kernel
theorem node0_distance_lower : ∀ j : Fin 7,(0:Fin 7)≠j →
    node0Distance j≤max |(centerQ 0).1-(centerQ j).1| |(centerQ 0).2-(centerQ j).2| := by decide +kernel
theorem node0_bound_product : node0Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node0Distance j := by decide +kernel

#print axioms node0_bound
#print axioms node0_distance_lower

def node1Center : ℚ×ℚ := ((-455206957178540327/500000000000000000),(-293668034220005327/200000000000000000))
def node1R : ℚ := (3/1)
def node1Bound : ℚ := (81937514115714543/31250000000000000000000000)
def node1State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((583656840467072897134872809/625000000000000000000000000000000000000),(-2856280381592407111833878007/5000000000000000000000000000000000000000))
  | 1 => ((14528649345758456241778092641535903384391/2000000000000000000000000000000000000000),(-23432198398754848585125930657397667539407/2000000000000000000000000000000000000000))
  | 2 => ((-123495128349919816674489208519405142974319/10000000000000000000000000000000000000000),(327866089454384831445666077620485685547087/10000000000000000000000000000000000000000))
  | 3 => ((3848977586315487314507659153970972257171/1250000000000000000000000000000000000000),(-204895240962486970290734013388525972564213/5000000000000000000000000000000000000000))
  | 4 => ((26086153030980796254579279348690183932709/2000000000000000000000000000000000000000),(47950442421534423076571731205809296553713/2000000000000000000000000000000000000000))
  | 5 => ((-37373377323668660828689751052150868454091/5000000000000000000000000000000000000000),(-71395300285712329537254402906658716190909/5000000000000000000000000000000000000000))
  | 6 => ((53175203155487324002727272727272727272727/5000000000000000000000000000000000000000),(-293668034220005327/200000000000000000))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node1Error : ℕ→ℚ := fun j => match j with
  | 0 => (4422782852941516822483/50000000000000000000000000000000000000000000000000000000000)
  | 1 => (29457608942236349906341/1000000000000000000000000000000000000000000000000000000000000)
  | 2 => (1222530628272081320371/125000000000000000000000000000000000000000000000000000000000)
  | 3 => (50113290808106779629/15625000000000000000000000000000000000000000000000000000000)
  | 4 => (247043063728153737/244140625000000000000000000000000000000000000000000000000)
  | 5 => (146693293239739289701/500000000000000000000000000000000000000000000000000000000000)
  | 6 => (10909090909090909091/200000000000000000000000000000000000000000000000000000000000)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node1Distance : Fin 7→ℚ := ![(5239/500),(1/1),(367/125),(1177/1000),(337/125),(59/40),(1821/1000)]
theorem node1_norm : |node1Center.1|+|node1Center.2|≤node1R := by decide +kernel
theorem node1_error_nonneg : ∀ j : Fin 9,0≤node1Error j.val := by decide +kernel
theorem node1_terminal : |(node1State 8).1|+|(node1State 8).2|≤node1Error 8 := by decide +kernel
theorem node1_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node1Center (node1State (j.val+1)) (node1State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node1Center (node1State (j.val+1)) (node1State j.val)).2|+
    node1R*node1Error (j.val+1)≤node1Error j.val := by decide +kernel
theorem node1_final : |(node1State 0).1|+|(node1State 0).2|+node1Error 0≤node1Bound := by decide +kernel

theorem node1_bound : ‖p7.eval (ratComplex (centerQ 1))‖≤(node1Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node1Center
    node1State node1Error node1R node1Bound 8
    node1_norm (fun j hj => node1_error_nonneg ⟨j,by omega⟩)
    node1_terminal (fun j hj => node1_steps ⟨j,hj⟩) node1_final

theorem node1_distance_positive : ∀ j : Fin 7,0<node1Distance j := by decide +kernel
theorem node1_distance_diagonal : node1Distance 1=1 := by decide +kernel
theorem node1_distance_lower : ∀ j : Fin 7,(1:Fin 7)≠j →
    node1Distance j≤max |(centerQ 1).1-(centerQ j).1| |(centerQ 1).2-(centerQ j).2| := by decide +kernel
theorem node1_bound_product : node1Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node1Distance j := by decide +kernel

#print axioms node1_bound
#print axioms node1_distance_lower

def node2Center : ℚ×ℚ := ((-455206957178540327/500000000000000000),(734170085550013317/500000000000000000))
def node2R : ℚ := (3/1)
def node2Bound : ℚ := (81937514115714543/31250000000000000000000000)
def node2State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((9334090909969074829373503069/10000000000000000000000000000000000000000),(5710778624188157640168095107/10000000000000000000000000000000000000000))
  | 1 => ((72643246728792281751372478689057916471731/10000000000000000000000000000000000000000),(23432198398754849135654398168383082653477/2000000000000000000000000000000000000000))
  | 2 => ((-30873782087479953911651403291429886079933/2500000000000000000000000000000000000000),(-327866089454384832675726841491055334241471/10000000000000000000000000000000000000000))
  | 3 => ((6158364138104779547517005607532831915057/2000000000000000000000000000000000000000),(204895240962486970321599644519678871918971/5000000000000000000000000000000000000000))
  | 4 => ((65215382577451990765870825715360910833557/5000000000000000000000000000000000000000),(-119876106053836057588228544735948733037511/5000000000000000000000000000000000000000))
  | 5 => ((-37373377323668660814006349341150602109091/5000000000000000000000000000000000000000),(71395300285712329488631269322956795458181/5000000000000000000000000000000000000000))
  | 6 => ((53175203155487324002727272727272727272727/5000000000000000000000000000000000000000),(734170085550013317/500000000000000000))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node2Error : ℕ→ℚ := fun j => match j with
  | 0 => (4530382265304089781543/50000000000000000000000000000000000000000000000000000000000)
  | 1 => (30163813983047590105741/1000000000000000000000000000000000000000000000000000000000000)
  | 2 => (1250532060617573642221/125000000000000000000000000000000000000000000000000000000000)
  | 3 => (412126983263695451557/125000000000000000000000000000000000000000000000000000000000)
  | 4 => (131041713010584058619/125000000000000000000000000000000000000000000000000000000000)
  | 5 => (157511102088828746001/500000000000000000000000000000000000000000000000000000000000)
  | 6 => (10909090909090909091/200000000000000000000000000000000000000000000000000000000000)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node2Distance : Fin 7→ℚ := ![(5239/500),(367/125),(1/1),(337/125),(1177/1000),(1821/1000),(59/40)]
theorem node2_norm : |node2Center.1|+|node2Center.2|≤node2R := by decide +kernel
theorem node2_error_nonneg : ∀ j : Fin 9,0≤node2Error j.val := by decide +kernel
theorem node2_terminal : |(node2State 8).1|+|(node2State 8).2|≤node2Error 8 := by decide +kernel
theorem node2_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node2Center (node2State (j.val+1)) (node2State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node2Center (node2State (j.val+1)) (node2State j.val)).2|+
    node2R*node2Error (j.val+1)≤node2Error j.val := by decide +kernel
theorem node2_final : |(node2State 0).1|+|(node2State 0).2|+node2Error 0≤node2Bound := by decide +kernel

theorem node2_bound : ‖p7.eval (ratComplex (centerQ 2))‖≤(node2Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node2Center
    node2State node2Error node2R node2Bound 8
    node2_norm (fun j hj => node2_error_nonneg ⟨j,by omega⟩)
    node2_terminal (fun j hj => node2_steps ⟨j,hj⟩) node2_final

theorem node2_distance_positive : ∀ j : Fin 7,0<node2Distance j := by decide +kernel
theorem node2_distance_diagonal : node2Distance 2=1 := by decide +kernel
theorem node2_distance_lower : ∀ j : Fin 7,(2:Fin 7)≠j →
    node2Distance j≤max |(centerQ 2).1-(centerQ j).1| |(centerQ 2).2-(centerQ j).2| := by decide +kernel
theorem node2_bound_product : node2Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node2Distance j := by decide +kernel

#print axioms node2_bound
#print axioms node2_distance_lower

def node3Center : ℚ×ℚ := ((6688155811805767/25000000000000000),(-1228363849182842981/1000000000000000000))
def node3R : ℚ := (2/1)
def node3Bound : ℚ := (1963514898531417/1562500000000000000000000)
def node3State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((310945884213858397441167983/1000000000000000000000000000000000000000),(66111793706115360308116139/10000000000000000000000000000000000000000))
  | 1 => ((-40315203740743439814256014401581470169419/10000000000000000000000000000000000000000),(-185109842836479485174977915466505184556559/10000000000000000000000000000000000000000))
  | 2 => ((45054757374894207155620556469687454514541/2000000000000000000000000000000000000000),(17121373908285824853398793255314903280617/500000000000000000000000000000000000000))
  | 3 => ((-313704742655235481544202768091497989393277/10000000000000000000000000000000000000000),(-160418238737154326536105411003038398908123/10000000000000000000000000000000000000000))
  | 4 => ((26464296214252056170592535695909836207307/2500000000000000000000000000000000000000),(-113585495529654789175900837157580016566017/10000000000000000000000000000000000000000))
  | 5 => ((60150408594427045562923780414322960389999/10000000000000000000000000000000000000000),(-74196290456870214751325180681599479890909/5000000000000000000000000000000000000000))
  | 6 => ((59064903889633880672727272727272727272727/5000000000000000000000000000000000000000),(-1228363849182842981/1000000000000000000))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node3Error : ℕ→ℚ := fun j => match j with
  | 0 => (11327455632292729487751/1000000000000000000000000000000000000000000000000000000000000)
  | 1 => (5618100651318060031057/1000000000000000000000000000000000000000000000000000000000000)
  | 2 => (34778163156164690087/12500000000000000000000000000000000000000000000000000000000)
  | 3 => (67426918870762749989/50000000000000000000000000000000000000000000000000000000000)
  | 4 => (31578342926795154657/50000000000000000000000000000000000000000000000000000000000)
  | 5 => (243318415456942489147/1000000000000000000000000000000000000000000000000000000000000)
  | 6 => (10909090909090909091/200000000000000000000000000000000000000000000000000000000000)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node3Distance : Fin 7→ℚ := ![(1457/125),(1177/1000),(337/125),(1/1),(307/125),(7/8),(1581/1000)]
theorem node3_norm : |node3Center.1|+|node3Center.2|≤node3R := by decide +kernel
theorem node3_error_nonneg : ∀ j : Fin 9,0≤node3Error j.val := by decide +kernel
theorem node3_terminal : |(node3State 8).1|+|(node3State 8).2|≤node3Error 8 := by decide +kernel
theorem node3_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node3Center (node3State (j.val+1)) (node3State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node3Center (node3State (j.val+1)) (node3State j.val)).2|+
    node3R*node3Error (j.val+1)≤node3Error j.val := by decide +kernel
theorem node3_final : |(node3State 0).1|+|(node3State 0).2|+node3Error 0≤node3Bound := by decide +kernel

theorem node3_bound : ‖p7.eval (ratComplex (centerQ 3))‖≤(node3Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node3Center
    node3State node3Error node3R node3Bound 8
    node3_norm (fun j hj => node3_error_nonneg ⟨j,by omega⟩)
    node3_terminal (fun j hj => node3_steps ⟨j,hj⟩) node3_final

theorem node3_distance_positive : ∀ j : Fin 7,0<node3Distance j := by decide +kernel
theorem node3_distance_diagonal : node3Distance 3=1 := by decide +kernel
theorem node3_distance_lower : ∀ j : Fin 7,(3:Fin 7)≠j →
    node3Distance j≤max |(centerQ 3).1-(centerQ j).1| |(centerQ 3).2-(centerQ j).2| := by decide +kernel
theorem node3_bound_product : node3Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node3Distance j := by decide +kernel

#print axioms node3_bound
#print axioms node3_distance_lower

def node4Center : ℚ×ℚ := ((6688155811805767/25000000000000000),(61418192459142149/50000000000000000))
def node4R : ℚ := (2/1)
def node4Bound : ℚ := (1963514898531417/1562500000000000000000000)
def node4State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((777366654766631395758077507/2500000000000000000000000000000000000000),(-67627143466606854340794377/10000000000000000000000000000000000000000))
  | 1 => ((-40315203740743441053375410709453652391237/10000000000000000000000000000000000000000),(185109842836479485049474361380966768819037/10000000000000000000000000000000000000000))
  | 2 => ((225273786874471035703861515908837455865287/10000000000000000000000000000000000000000),(-171213739082858248177078034715914021405541/5000000000000000000000000000000000000000))
  | 3 => ((-313704742655235481272944691337882613641157/10000000000000000000000000000000000000000),(80209119368577163393108549778722800497389/5000000000000000000000000000000000000000))
  | 4 => ((105857184857008224985727695664659670861883/10000000000000000000000000000000000000000),(11358549552965478911360945821427460380403/1000000000000000000000000000000000000000))
  | 5 => ((60150408594427045587491057397979819999999/10000000000000000000000000000000000000000),(74196290456870214690922645629604445818181/5000000000000000000000000000000000000000))
  | 6 => ((59064903889633880672727272727272727272727/5000000000000000000000000000000000000000),(61418192459142149/50000000000000000))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node4Error : ℕ→ℚ := fun j => match j with
  | 0 => (11379304188464333309151/1000000000000000000000000000000000000000000000000000000000000)
  | 1 => (5670400393477342098757/1000000000000000000000000000000000000000000000000000000000000)
  | 2 => (34300202230418442707/12500000000000000000000000000000000000000000000000000000000)
  | 3 => (520953336122264613/390625000000000000000000000000000000000000000000000000000)
  | 4 => (15472387803982801641/25000000000000000000000000000000000000000000000000000000000)
  | 5 => (291133268273359618547/1000000000000000000000000000000000000000000000000000000000000)
  | 6 => (10909090909090909091/200000000000000000000000000000000000000000000000000000000000)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node4Distance : Fin 7→ℚ := ![(1457/125),(337/125),(1177/1000),(307/125),(1/1),(1581/1000),(7/8)]
theorem node4_norm : |node4Center.1|+|node4Center.2|≤node4R := by decide +kernel
theorem node4_error_nonneg : ∀ j : Fin 9,0≤node4Error j.val := by decide +kernel
theorem node4_terminal : |(node4State 8).1|+|(node4State 8).2|≤node4Error 8 := by decide +kernel
theorem node4_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node4Center (node4State (j.val+1)) (node4State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node4Center (node4State (j.val+1)) (node4State j.val)).2|+
    node4R*node4Error (j.val+1)≤node4Error j.val := by decide +kernel
theorem node4_final : |(node4State 0).1|+|(node4State 0).2|+node4Error 0≤node4Bound := by decide +kernel

theorem node4_bound : ‖p7.eval (ratComplex (centerQ 4))‖≤(node4Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node4Center
    node4State node4Error node4R node4Bound 8
    node4_norm (fun j hj => node4_error_nonneg ⟨j,by omega⟩)
    node4_terminal (fun j hj => node4_steps ⟨j,hj⟩) node4_final

theorem node4_distance_positive : ∀ j : Fin 7,0<node4Distance j := by decide +kernel
theorem node4_distance_diagonal : node4Distance 4=1 := by decide +kernel
theorem node4_distance_lower : ∀ j : Fin 7,(4:Fin 7)≠j →
    node4Distance j≤max |(centerQ 4).1-(centerQ j).1| |(centerQ 4).2-(centerQ j).2| := by decide +kernel
theorem node4_bound_product : node4Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node4Distance j := by decide +kernel

#print axioms node4_bound
#print axioms node4_distance_lower

def node5Center : ℚ×ℚ := ((282341158415928551/500000000000000000),(-22046191071555161/62500000000000000))
def node5R : ℚ := (1/1)
def node5Bound : ℚ := (2003954698130049/6400000000000000000000000)
def node5State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((-723563844376520143640476057/5000000000000000000000000000000000000000),(72544146884830592795409243/2500000000000000000000000000000000000000))
  | 1 => ((-60677546613814314958234145358988835732753/2000000000000000000000000000000000000000),(-189516653385788966708781389618480938133017/10000000000000000000000000000000000000000))
  | 2 => ((85654276149579987093294933140629713122919/2000000000000000000000000000000000000000),(-68088922200279199769230940415059750337577/10000000000000000000000000000000000000000))
  | 3 => ((-45152116572522234363704285820562092853693/10000000000000000000000000000000000000000),(-148784253949258225890031758167559302451093/10000000000000000000000000000000000000000))
  | 4 => ((159414015998793213716166715904685152326761/5000000000000000000000000000000000000000),(-12864279071053794816517850904917970977217/2000000000000000000000000000000000000000))
  | 5 => ((110775916617476651068980518955012608098181/10000000000000000000000000000000000000000),(-11177259416810123641103311239917364669091/2500000000000000000000000000000000000000))
  | 6 => ((60550684311432012782727272727272727272727/5000000000000000000000000000000000000000),(-22046191071555161/62500000000000000))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node5Error : ℕ→ℚ := fun j => match j with
  | 0 => (38349095134850608407/62500000000000000000000000000000000000000000000000000000000)
  | 1 => (19179986056638930499/40000000000000000000000000000000000000000000000000000000000)
  | 2 => (231912654278742111219/500000000000000000000000000000000000000000000000000000000000)
  | 3 => (192809149024921739819/500000000000000000000000000000000000000000000000000000000000)
  | 4 => (142375758000891742719/500000000000000000000000000000000000000000000000000000000000)
  | 5 => (40291682822450347373/250000000000000000000000000000000000000000000000000000000000)
  | 6 => (10909090909090909091/200000000000000000000000000000000000000000000000000000000000)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node5Distance : Fin 7→ℚ := ![(11953/1000),(59/40),(1821/1000),(7/8),(1581/1000),(1/1),(141/200)]
theorem node5_norm : |node5Center.1|+|node5Center.2|≤node5R := by decide +kernel
theorem node5_error_nonneg : ∀ j : Fin 9,0≤node5Error j.val := by decide +kernel
theorem node5_terminal : |(node5State 8).1|+|(node5State 8).2|≤node5Error 8 := by decide +kernel
theorem node5_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node5Center (node5State (j.val+1)) (node5State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node5Center (node5State (j.val+1)) (node5State j.val)).2|+
    node5R*node5Error (j.val+1)≤node5Error j.val := by decide +kernel
theorem node5_final : |(node5State 0).1|+|(node5State 0).2|+node5Error 0≤node5Bound := by decide +kernel

theorem node5_bound : ‖p7.eval (ratComplex (centerQ 5))‖≤(node5Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node5Center
    node5State node5Error node5R node5Bound 8
    node5_norm (fun j hj => node5_error_nonneg ⟨j,by omega⟩)
    node5_terminal (fun j hj => node5_steps ⟨j,hj⟩) node5_final

theorem node5_distance_positive : ∀ j : Fin 7,0<node5Distance j := by decide +kernel
theorem node5_distance_diagonal : node5Distance 5=1 := by decide +kernel
theorem node5_distance_lower : ∀ j : Fin 7,(5:Fin 7)≠j →
    node5Distance j≤max |(centerQ 5).1-(centerQ j).1| |(centerQ 5).2-(centerQ j).2| := by decide +kernel
theorem node5_bound_product : node5Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node5Distance j := by decide +kernel

#print axioms node5_bound
#print axioms node5_distance_lower

def node6Center : ℚ×ℚ := ((282341158415928551/500000000000000000),(14109562285795303/40000000000000000))
def node6R : ℚ := (1/1)
def node6Bound : ℚ := (2003954698130049/6400000000000000000000000)
def node6State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((-1446629528028188775438623097/10000000000000000000000000000000000000000),(-289958078886355348369603927/10000000000000000000000000000000000000000))
  | 1 => ((-75846933267267893616386959926046434958093/2500000000000000000000000000000000000000),(189516653385788966355062166746635943810439/10000000000000000000000000000000000000000))
  | 2 => ((428271380747899935853855300085438595283649/10000000000000000000000000000000000000000),(68088922200279199659271552629538895500769/10000000000000000000000000000000000000000))
  | 3 => ((-45152116572522234183196948512600413518069/10000000000000000000000000000000000000000),(18598031743657278187823311105363538492317/1250000000000000000000000000000000000000))
  | 4 => ((79707007999396606881433804326091109064501/2500000000000000000000000000000000000000),(64321395355268973902729372160928857990377/10000000000000000000000000000000000000000))
  | 5 => ((110775916617476651076035300097910259608181/10000000000000000000000000000000000000000),(11177259416810123609416263292121715522727/2500000000000000000000000000000000000000))
  | 6 => ((60550684311432012782727272727272727272727/5000000000000000000000000000000000000000),(14109562285795303/40000000000000000))
  | 7 => ((1/1),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def node6Error : ℕ→ℚ := fun j => match j with
  | 0 => (107970894510502295139/125000000000000000000000000000000000000000000000000000000000)
  | 1 => (29051891017422225863/40000000000000000000000000000000000000000000000000000000000)
  | 2 => (271775735722982009669/500000000000000000000000000000000000000000000000000000000000)
  | 3 => (220622694324734571719/500000000000000000000000000000000000000000000000000000000000)
  | 4 => (145412811608447002369/500000000000000000000000000000000000000000000000000000000000)
  | 5 => (48853344900317186223/250000000000000000000000000000000000000000000000000000000000)
  | 6 => (10909090909090909091/200000000000000000000000000000000000000000000000000000000000)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def node6Distance : Fin 7→ℚ := ![(11953/1000),(1821/1000),(59/40),(1581/1000),(7/8),(141/200),(1/1)]
theorem node6_norm : |node6Center.1|+|node6Center.2|≤node6R := by decide +kernel
theorem node6_error_nonneg : ∀ j : Fin 9,0≤node6Error j.val := by decide +kernel
theorem node6_terminal : |(node6State 8).1|+|(node6State 8).2|≤node6Error 8 := by decide +kernel
theorem node6_steps : ∀ j : Fin 8,
    |(ratResidual (pCoefficient j.val) node6Center (node6State (j.val+1)) (node6State j.val)).1|+
    |(ratResidual (pCoefficient j.val) node6Center (node6State (j.val+1)) (node6State j.val)).2|+
    node6R*node6Error (j.val+1)≤node6Error j.val := by decide +kernel
theorem node6_final : |(node6State 0).1|+|(node6State 0).2|+node6Error 0≤node6Bound := by decide +kernel

theorem node6_bound : ‖p7.eval (ratComplex (centerQ 6))‖≤(node6Bound:ℝ) := by
  exact polynomial_bound_of_rational_certificate pCoefficient node6Center
    node6State node6Error node6R node6Bound 8
    node6_norm (fun j hj => node6_error_nonneg ⟨j,by omega⟩)
    node6_terminal (fun j hj => node6_steps ⟨j,hj⟩) node6_final

theorem node6_distance_positive : ∀ j : Fin 7,0<node6Distance j := by decide +kernel
theorem node6_distance_diagonal : node6Distance 6=1 := by decide +kernel
theorem node6_distance_lower : ∀ j : Fin 7,(6:Fin 7)≠j →
    node6Distance j≤max |(centerQ 6).1-(centerQ j).1| |(centerQ 6).2-(centerQ j).2| := by decide +kernel
theorem node6_bound_product : node6Bound=(1/100:ℚ)*radiusQ*∏ j : Fin 7,node6Distance j := by decide +kernel

#print axioms node6_bound
#print axioms node6_distance_lower

end QuantitativeArithmeticSmallLevelThirtyThreeRoot
end
end

/-! ## ThirtyThreeRootGeometry -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds

def distanceQ (i : Fin 7) : Fin 7→ℚ :=
  ![node0Distance,node1Distance,node2Distance,node3Distance,node4Distance,node5Distance,node6Distance] i
def pBoundQ : Fin 7→ℚ := ![node0Bound,node1Bound,node2Bound,node3Bound,node4Bound,node5Bound,node6Bound]
theorem distance_positive (i : Fin 7) : ∀ j : Fin 7,0<distanceQ i j := by
  fin_cases i
  · exact node0_distance_positive
  · exact node1_distance_positive
  · exact node2_distance_positive
  · exact node3_distance_positive
  · exact node4_distance_positive
  · exact node5_distance_positive
  · exact node6_distance_positive

theorem distance_diagonal (i : Fin 7) : distanceQ i i=1 := by
  fin_cases i
  · exact node0_distance_diagonal
  · exact node1_distance_diagonal
  · exact node2_distance_diagonal
  · exact node3_distance_diagonal
  · exact node4_distance_diagonal
  · exact node5_distance_diagonal
  · exact node6_distance_diagonal

theorem distance_lower (i : Fin 7) : ∀ j : Fin 7,i≠j → distanceQ i j≤max |(centerQ i).1-(centerQ j).1| |(centerQ i).2-(centerQ j).2| := by
  fin_cases i
  · exact node0_distance_lower
  · exact node1_distance_lower
  · exact node2_distance_lower
  · exact node3_distance_lower
  · exact node4_distance_lower
  · exact node5_distance_lower
  · exact node6_distance_lower

theorem bound_product (i : Fin 7) : pBoundQ i=(1/100:ℚ)*radiusQ*∏ j : Fin 7,distanceQ i j := by
  fin_cases i
  · exact node0_bound_product
  · exact node1_bound_product
  · exact node2_bound_product
  · exact node3_bound_product
  · exact node4_bound_product
  · exact node5_bound_product
  · exact node6_bound_product

theorem all_P_value_bounds (i : Fin 7) : ‖p7.eval (ratComplex (centerQ i))‖≤(pBoundQ i:ℝ) := by
  fin_cases i
  · exact node0_bound
  · exact node1_bound
  · exact node2_bound
  · exact node3_bound
  · exact node4_bound
  · exact node5_bound
  · exact node6_bound


end QuantitativeArithmeticSmallLevelThirtyThreeRoot
end
end

/-! ## ThirtyThreeRootCover -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeRoot
open QuantitativeArithmeticComplexHornerBounds Polynomial Finset

theorem distance_le_norm (i j : Fin 7) (hij : i≠j) :
    (distanceQ i j:ℝ)≤‖ratComplex (centerQ i)-ratComplex (centerQ j)‖ := by
  have h : (distanceQ i j:ℝ)≤max |((centerQ i).1:ℝ)-((centerQ j).1:ℝ)|
      |((centerQ i).2:ℝ)-((centerQ j).2:ℝ)| := by
    exact_mod_cast distance_lower i j hij
  apply h.trans
  apply max_le
  · simpa using Complex.abs_re_le_norm (ratComplex (centerQ i)-ratComplex (centerQ j))
  · simpa using Complex.abs_im_le_norm (ratComplex (centerQ i)-ratComplex (centerQ j))

theorem center_injective : Function.Injective (fun i : Fin 7 => ratComplex (centerQ i)) := by
  intro i j hij
  change ratComplex (centerQ i)=ratComplex (centerQ j) at hij
  by_contra hne
  have h := distance_le_norm i j hne
  rw [hij,sub_self,norm_zero] at h
  have hp : 0<(distanceQ i j:ℝ) := by exact_mod_cast distance_positive i j
  exact (not_le_of_gt hp) h

theorem radius_positive : 0<(radiusQ:ℝ) := by
  exact_mod_cast (show (0:ℚ)<radiusQ by decide +kernel)

theorem p_bound_erase_product (i : Fin 7) : (pBoundQ i:ℝ)=
    (1/100:ℝ)*(radiusQ:ℝ)*∏ j ∈ (Finset.univ : Finset (Fin 7)).erase i,(distanceQ i j:ℝ) := by
  have h : (pBoundQ i:ℝ)=(1/100:ℝ)*(radiusQ:ℝ)*∏ j : Fin 7,(distanceQ i j:ℝ) := by
    have hq := congrArg (fun q : ℚ => (q:ℝ)) (bound_product i)
    simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_prod] using hq
  have hp : (∏ j ∈ (Finset.univ : Finset (Fin 7)).erase i,(distanceQ i j:ℝ))=
      ∏ j : Fin 7,(distanceQ i j:ℝ) := by
    simpa only [distance_diagonal,Rat.cast_one,mul_one] using
      Finset.prod_erase_mul Finset.univ (fun j : Fin 7 => (distanceQ i j:ℝ)) (Finset.mem_univ i)
  rw [hp]
  exact h

/-- Every root of the concrete degree-7 polynomial lies in a certified disk.
The proof uses only exact rational certificates and barycentric interpolation. -/
theorem p7_root_in_disk (z : ℂ) (hz : p7.eval z=0) :
    ∃ i : Fin 7,‖z-ratComplex (centerQ i)‖<(radiusQ:ℝ) := by
  have hsmall : ∑ i : Fin 7,
      ‖Lagrange.nodalWeight Finset.univ (fun j => ratComplex (centerQ j)) i*
        p7.eval (ratComplex (centerQ i))‖/(radiusQ:ℝ)<1 := by
    apply lt_of_le_of_lt _ (show (∑ _i : Fin 7,(1/100:ℝ))<1 by norm_num)
    apply Finset.sum_le_sum
    intro i _hi
    apply (div_le_iff₀ radius_positive).mpr
    apply QuantitativeArithmeticPolynomialRootCover.nodal_eval_bound_of_separations
      Finset.univ (fun j => ratComplex (centerQ j)) p7 i
      (fun j => (distanceQ i j:ℝ)) (1/100:ℝ) (radiusQ:ℝ)
    · intro j _hj
      exact_mod_cast distance_positive i j
    · intro j hj
      exact distance_le_norm i j (Finset.mem_erase.mp hj).1.symm
    · rw [← p_bound_erase_product]
      exact all_P_value_bounds i
  obtain ⟨i,_hi,h⟩ := QuantitativeArithmeticPolynomialRootCover.monic_root_cover
    Finset.univ (fun j => ratComplex (centerQ j)) (fun _ => (radiusQ:ℝ)) p7
    center_injective.injOn p7_monic (by simpa using p7_degree)
    (fun _ _ => radius_positive) hsmall z hz
  exact ⟨i,h⟩

#print axioms center_injective
#print axioms p7_root_in_disk
end QuantitativeArithmeticSmallLevelThirtyThreeRoot
end
end

/-! ## ThirtyThreeRootXNodeBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyThreeRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds

def nodeX0Center : ℚ×ℚ := ((-1423630476918569479/125000000000000000),(0/1))
def nodeX0V : ℕ→ℚ := fun j => match j with
  | 0 => (67979757/1)
  | 1 => (5229212/1)
  | 2 => (402247/1)
  | 3 => (30942/1)
  | 4 => (2380/1)
  | 5 => (183/1)
  | 6 => (14/1)
  | 7 => (1/1)
  | 8 => (0/1)
  | _ => 0
def nodeX0L : ℕ→ℚ := fun j => match j with
  | 0 => (36168055/1)
  | 1 => (2379911/1)
  | 2 => (152128/1)
  | 3 => (9322/1)
  | 4 => (534/1)
  | 5 => (27/1)
  | 6 => (1/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def nodeX0State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((-1525490477676053565881895458757/1000000000000000000000000000000),(0/1))
  | 1 => ((37369911057298252212340544141/250000000000000000000000000000),(0/1))
  | 2 => ((-43411561762342274385922880033/1000000000000000000000000000000),(0/1))
  | 3 => ((-64216029210033411650300263151/1000000000000000000000000000000),(0/1))
  | 4 => ((-17254383305523680448470129309/200000000000000000000000000000),(0/1))
  | 5 => ((-55627139733472500525017040469/1000000000000000000000000000000),(0/1))
  | 6 => ((-29681292134416406063875564199/1000000000000000000000000000000),(0/1))
  | 7 => ((-559562676015097115130264059/100000000000000000000000000000),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def nodeX0Error : ℕ→ℚ := fun j => match j with
  | 0 => (12667408841575929009970602933223/1170580815000000000000000000000000000000000000000000000)
  | 1 => (24360400045598508986473265563231/29264520375000000000000000000000000000000000000000000000)
  | 2 => (187387565540538405309623807413/2926452037500000000000000000000000000000000000000000000)
  | 3 => (144142393326115523450313851731/29264520375000000000000000000000000000000000000000000000)
  | 4 => (5543053884483364784444925491/14632260187500000000000000000000000000000000000000000000)
  | 5 => (852107966252651211066714913/29264520375000000000000000000000000000000000000000000000)
  | 6 => (6438995552387188197283543/2926452037500000000000000000000000000000000000000000000)
  | 7 => (9656851/70234848900000000000000000000000000000)
  | 8 => (0/1)
  | _ => 0
def nodeX0YLo : ℚ := (12971/100)
def nodeX0YHi : ℚ := (129711/1000)
def nodeX0XLo : ℚ := (443/200)
def nodeX0XHi : ℚ := (2439/1000)
def nodeX0DiskError : ℚ := radiusQ*nodeX0L 0+nodeX0Error 0
theorem nodeX0_norm : |nodeX0Center.1|+|nodeX0Center.2|≤12 := by decide +kernel
theorem nodeX0_Vstep : ∀ j : Fin 8,|qCoefficient j.val|+13*nodeX0V (j.val+1)≤nodeX0V j.val := by decide +kernel
theorem nodeX0_Lstep : ∀ j : Fin 8,nodeX0V (j.val+1)+13*nodeX0L (j.val+1)≤nodeX0L j.val := by decide +kernel
theorem nodeX0_lipschitz (z w : ℂ) (hz : ‖z‖≤13) (hw : ‖w‖≤13) :
    ‖xPoly.eval z-xPoly.eval w‖≤‖z-w‖*(nodeX0L 0:ℝ) := by
  exact polynomial_difference_of_rational_envelope qCoefficient z w 13
    nodeX0V nodeX0L 8 hz hw (by decide +kernel) (by decide +kernel)
    (fun j hj => nodeX0_Vstep ⟨j,hj⟩) (fun j hj => nodeX0_Lstep ⟨j,hj⟩)
theorem nodeX0_Enonneg : ∀ j : Fin 9,0≤nodeX0Error j.val := by decide +kernel
theorem nodeX0_steps : ∀ j : Fin 8,
    |(ratResidual (qCoefficient j.val) nodeX0Center (nodeX0State (j.val+1)) (nodeX0State j.val)).1|+
    |(ratResidual (qCoefficient j.val) nodeX0Center (nodeX0State (j.val+1)) (nodeX0State j.val)).2|+
    13*nodeX0Error (j.val+1)≤nodeX0Error j.val := by decide +kernel
theorem nodeX0_value : ‖xPoly.eval (ratComplex nodeX0Center)-ratComplex (nodeX0State 0)‖≤(nodeX0Error 0:ℝ) := by
  exact polynomial_error_of_rational_certificate qCoefficient nodeX0Center
    nodeX0State nodeX0Error 13 8 (by have hh:=nodeX0_norm; linarith)
    (fun j hj => nodeX0_Enonneg ⟨j,by omega⟩) (by decide +kernel)
    (fun j hj => nodeX0_steps ⟨j,hj⟩)
theorem nodeX0_ylo : nodeX0YLo≤nodeX0Center.1^2+nodeX0Center.2^2-radiusQ*(2*(|nodeX0Center.1|+|nodeX0Center.2|)+radiusQ) := by decide +kernel
theorem nodeX0_yhi : nodeX0Center.1^2+nodeX0Center.2^2+radiusQ*(2*(|nodeX0Center.1|+|nodeX0Center.2|)+radiusQ)≤nodeX0YHi := by decide +kernel
theorem nodeX0_xlo : nodeX0XLo≤(nodeX0State 0).1^2+(nodeX0State 0).2^2-nodeX0DiskError*(2*(|(nodeX0State 0).1|+|(nodeX0State 0).2|)+nodeX0DiskError) := by decide +kernel
theorem nodeX0_xhi : (nodeX0State 0).1^2+(nodeX0State 0).2^2+nodeX0DiskError*(2*(|(nodeX0State 0).1|+|(nodeX0State 0).2|)+nodeX0DiskError)≤nodeX0XHi := by decide +kernel

theorem nodeX0_disk (z : ℂ) (hd : ‖z-ratComplex (centerQ 0)‖<(radiusQ:ℝ)) :
    ‖z‖<1 ∨ ‖xPoly.eval z‖<‖z‖ := by
  have hc : ‖ratComplex nodeX0Center‖≤12 := by
    have hh : |(nodeX0Center.1:ℝ)|+|(nodeX0Center.2:ℝ)|≤12 := by exact_mod_cast nodeX0_norm
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by simpa using hh)
  have hd' : ‖z-ratComplex nodeX0Center‖≤(radiusQ:ℝ) := hd.le
  have hr : (radiusQ:ℝ)≤1 := by norm_num [radiusQ]
  have hz : ‖z‖≤13 := by
    have hh:=norm_add_le (z-ratComplex nodeX0Center) (ratComplex nodeX0Center)
    rw [sub_add_cancel] at hh
    linarith
  have herr:=polynomial_disk_error xPoly z (ratComplex nodeX0Center)
    (ratComplex (nodeX0State 0)) (radiusQ:ℝ) (nodeX0L 0:ℝ) (nodeX0Error 0:ℝ)
    (by exact_mod_cast (show (0:ℚ)≤nodeX0L 0 by decide +kernel)) hd'
    (nodeX0_lipschitz z _ hz (by linarith)) nodeX0_value
  have herr' : ‖xPoly.eval z-ratComplex (nodeX0State 0)‖≤(nodeX0DiskError:ℝ) := by
    simpa only [nodeX0DiskError,Rat.cast_add,Rat.cast_mul] using herr
  have hy := squared_norm_enclosure_of_rational_error z nodeX0Center radiusQ
    nodeX0YLo nodeX0YHi (by decide +kernel) hd' nodeX0_ylo nodeX0_yhi
  have hx := squared_norm_enclosure_of_rational_error (xPoly.eval z) (nodeX0State 0)
    nodeX0DiskError nodeX0XLo nodeX0XHi (by decide +kernel) herr' nodeX0_xlo nodeX0_xhi
  right
  have hh : (nodeX0XHi:ℝ)<(nodeX0YLo:ℝ) := by norm_num [nodeX0XHi,nodeX0YLo]
  nlinarith [norm_nonneg z,norm_nonneg (xPoly.eval z)]

#print axioms nodeX0_disk

def nodeX1Center : ℚ×ℚ := ((-455206957178540327/500000000000000000),(-293668034220005327/200000000000000000))
def nodeX1V : ℕ→ℚ := fun j => match j with
  | 0 => (21909/1)
  | 1 => (5477/1)
  | 2 => (1369/1)
  | 3 => (342/1)
  | 4 => (85/1)
  | 5 => (21/1)
  | 6 => (5/1)
  | 7 => (1/1)
  | 8 => (0/1)
  | _ => 0
def nodeX1L : ℕ→ℚ := fun j => match j with
  | 0 => (36457/1)
  | 1 => (7745/1)
  | 2 => (1594/1)
  | 3 => (313/1)
  | 4 => (57/1)
  | 5 => (9/1)
  | 6 => (1/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def nodeX1State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((-7205675336899080953253072251/100000000000000000000000000000),(-190218495916986409942897503139/200000000000000000000000000000))
  | 1 => ((271906935849671641999348698409/500000000000000000000000000000),(167603684171617753516584391967/1000000000000000000000000000000))
  | 2 => ((-176762758948686931321483725269/500000000000000000000000000000),(386079375241376458732731335843/1000000000000000000000000000000))
  | 3 => ((-63681254945788399180432002027/200000000000000000000000000000),(22366021484567958856733511831/250000000000000000000000000000))
  | 4 => ((-266167403342381798921729923841/1000000000000000000000000000000),(331014497773297413712135011011/1000000000000000000000000000000))
  | 5 => ((-75300112354204330173369028433/250000000000000000000000000000),(6109870461358234351545504411/50000000000000000000000000000))
  | 6 => ((-5519737126132651620124692829/62500000000000000000000000000),(2054070888602991170413409973/250000000000000000000000000000))
  | 7 => ((-559562676015097115130264059/100000000000000000000000000000),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def nodeX1Error : ℕ→ℚ := fun j => match j with
  | 0 => (2518077857797347349782571032767/234116163000000000000000000000000000000000000000000000000)
  | 1 => (629470987250923193145853008023/234116163000000000000000000000000000000000000000000000000)
  | 2 => (157301710215326164316191877057/234116163000000000000000000000000000000000000000000000000)
  | 3 => (28907187020643290646868691/172144237500000000000000000000000000000000000000000000)
  | 4 => (15293581810923646554179939/365806504687500000000000000000000000000000000000000000)
  | 5 => (598276176238179867907421561/58529040750000000000000000000000000000000000000000000000)
  | 6 => (57207656189633517326962313/23411616300000000000000000000000000000000000000000000000)
  | 7 => (9656851/70234848900000000000000000000000000000)
  | 8 => (0/1)
  | _ => 0
def nodeX1YLo : ℚ := (373/125)
def nodeX1YHi : ℚ := (597/200)
def nodeX1XLo : ℚ := (909/1000)
def nodeX1XHi : ℚ := (91/100)
def nodeX1DiskError : ℚ := radiusQ*nodeX1L 0+nodeX1Error 0
theorem nodeX1_norm : |nodeX1Center.1|+|nodeX1Center.2|≤3 := by decide +kernel
theorem nodeX1_Vstep : ∀ j : Fin 8,|qCoefficient j.val|+4*nodeX1V (j.val+1)≤nodeX1V j.val := by decide +kernel
theorem nodeX1_Lstep : ∀ j : Fin 8,nodeX1V (j.val+1)+4*nodeX1L (j.val+1)≤nodeX1L j.val := by decide +kernel
theorem nodeX1_lipschitz (z w : ℂ) (hz : ‖z‖≤4) (hw : ‖w‖≤4) :
    ‖xPoly.eval z-xPoly.eval w‖≤‖z-w‖*(nodeX1L 0:ℝ) := by
  exact polynomial_difference_of_rational_envelope qCoefficient z w 4
    nodeX1V nodeX1L 8 hz hw (by decide +kernel) (by decide +kernel)
    (fun j hj => nodeX1_Vstep ⟨j,hj⟩) (fun j hj => nodeX1_Lstep ⟨j,hj⟩)
theorem nodeX1_Enonneg : ∀ j : Fin 9,0≤nodeX1Error j.val := by decide +kernel
theorem nodeX1_steps : ∀ j : Fin 8,
    |(ratResidual (qCoefficient j.val) nodeX1Center (nodeX1State (j.val+1)) (nodeX1State j.val)).1|+
    |(ratResidual (qCoefficient j.val) nodeX1Center (nodeX1State (j.val+1)) (nodeX1State j.val)).2|+
    4*nodeX1Error (j.val+1)≤nodeX1Error j.val := by decide +kernel
theorem nodeX1_value : ‖xPoly.eval (ratComplex nodeX1Center)-ratComplex (nodeX1State 0)‖≤(nodeX1Error 0:ℝ) := by
  exact polynomial_error_of_rational_certificate qCoefficient nodeX1Center
    nodeX1State nodeX1Error 4 8 (by have hh:=nodeX1_norm; linarith)
    (fun j hj => nodeX1_Enonneg ⟨j,by omega⟩) (by decide +kernel)
    (fun j hj => nodeX1_steps ⟨j,hj⟩)
theorem nodeX1_ylo : nodeX1YLo≤nodeX1Center.1^2+nodeX1Center.2^2-radiusQ*(2*(|nodeX1Center.1|+|nodeX1Center.2|)+radiusQ) := by decide +kernel
theorem nodeX1_yhi : nodeX1Center.1^2+nodeX1Center.2^2+radiusQ*(2*(|nodeX1Center.1|+|nodeX1Center.2|)+radiusQ)≤nodeX1YHi := by decide +kernel
theorem nodeX1_xlo : nodeX1XLo≤(nodeX1State 0).1^2+(nodeX1State 0).2^2-nodeX1DiskError*(2*(|(nodeX1State 0).1|+|(nodeX1State 0).2|)+nodeX1DiskError) := by decide +kernel
theorem nodeX1_xhi : (nodeX1State 0).1^2+(nodeX1State 0).2^2+nodeX1DiskError*(2*(|(nodeX1State 0).1|+|(nodeX1State 0).2|)+nodeX1DiskError)≤nodeX1XHi := by decide +kernel

theorem nodeX1_disk (z : ℂ) (hd : ‖z-ratComplex (centerQ 1)‖<(radiusQ:ℝ)) :
    ‖z‖<1 ∨ ‖xPoly.eval z‖<‖z‖ := by
  have hc : ‖ratComplex nodeX1Center‖≤3 := by
    have hh : |(nodeX1Center.1:ℝ)|+|(nodeX1Center.2:ℝ)|≤3 := by exact_mod_cast nodeX1_norm
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by simpa using hh)
  have hd' : ‖z-ratComplex nodeX1Center‖≤(radiusQ:ℝ) := hd.le
  have hr : (radiusQ:ℝ)≤1 := by norm_num [radiusQ]
  have hz : ‖z‖≤4 := by
    have hh:=norm_add_le (z-ratComplex nodeX1Center) (ratComplex nodeX1Center)
    rw [sub_add_cancel] at hh
    linarith
  have herr:=polynomial_disk_error xPoly z (ratComplex nodeX1Center)
    (ratComplex (nodeX1State 0)) (radiusQ:ℝ) (nodeX1L 0:ℝ) (nodeX1Error 0:ℝ)
    (by exact_mod_cast (show (0:ℚ)≤nodeX1L 0 by decide +kernel)) hd'
    (nodeX1_lipschitz z _ hz (by linarith)) nodeX1_value
  have herr' : ‖xPoly.eval z-ratComplex (nodeX1State 0)‖≤(nodeX1DiskError:ℝ) := by
    simpa only [nodeX1DiskError,Rat.cast_add,Rat.cast_mul] using herr
  have hy := squared_norm_enclosure_of_rational_error z nodeX1Center radiusQ
    nodeX1YLo nodeX1YHi (by decide +kernel) hd' nodeX1_ylo nodeX1_yhi
  have hx := squared_norm_enclosure_of_rational_error (xPoly.eval z) (nodeX1State 0)
    nodeX1DiskError nodeX1XLo nodeX1XHi (by decide +kernel) herr' nodeX1_xlo nodeX1_xhi
  right
  have hh : (nodeX1XHi:ℝ)<(nodeX1YLo:ℝ) := by norm_num [nodeX1XHi,nodeX1YLo]
  nlinarith [norm_nonneg z,norm_nonneg (xPoly.eval z)]

#print axioms nodeX1_disk

def nodeX2Center : ℚ×ℚ := ((-455206957178540327/500000000000000000),(734170085550013317/500000000000000000))
def nodeX2V : ℕ→ℚ := fun j => match j with
  | 0 => (21909/1)
  | 1 => (5477/1)
  | 2 => (1369/1)
  | 3 => (342/1)
  | 4 => (85/1)
  | 5 => (21/1)
  | 6 => (5/1)
  | 7 => (1/1)
  | 8 => (0/1)
  | _ => 0
def nodeX2L : ℕ→ℚ := fun j => match j with
  | 0 => (36457/1)
  | 1 => (7745/1)
  | 2 => (1594/1)
  | 3 => (313/1)
  | 4 => (57/1)
  | 5 => (9/1)
  | 6 => (1/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def nodeX2State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((-72056753368990810919023400227/1000000000000000000000000000000),(237773119896233011647949542933/250000000000000000000000000000))
  | 1 => ((271906935849671641550925943937/500000000000000000000000000000),(-167603684171617752130400410913/1000000000000000000000000000000))
  | 2 => ((-176762758948686930989593511919/500000000000000000000000000000),(-386079375241376458796441915097/1000000000000000000000000000000))
  | 3 => ((-318406274728941996319879762749/1000000000000000000000000000000),(-89464085938271835680926034261/1000000000000000000000000000000))
  | 4 => ((-266167403342381799151164304551/1000000000000000000000000000000),(-165507248886648706755414566463/500000000000000000000000000000))
  | 5 => ((-7530011235420433017747717021/25000000000000000000000000000),(-15274676153395585868461078833/125000000000000000000000000000))
  | 6 => ((-5519737126132651620124692829/62500000000000000000000000000),(-8216283554411964676058013133/1000000000000000000000000000000))
  | 7 => ((-559562676015097115130264059/100000000000000000000000000000),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def nodeX2Error : ℕ→ℚ := fun j => match j with
  | 0 => (137650757989413240037789051223/14632260187500000000000000000000000000000000000000000000)
  | 1 => (2150681082538153810431410039/914516261718750000000000000000000000000000000000000000)
  | 2 => (34398478931818986513015147221/58529040750000000000000000000000000000000000000000000000)
  | 3 => (101026206659739695347382141/688576950000000000000000000000000000000000000000000000)
  | 4 => (132637990831401283507951631/3658065046875000000000000000000000000000000000000000000)
  | 5 => (258499737035122772966101849/29264520375000000000000000000000000000000000000000000000)
  | 6 => (2056113442827427089501517/1170580815000000000000000000000000000000000000000000000)
  | 7 => (9656851/70234848900000000000000000000000000000)
  | 8 => (0/1)
  | _ => 0
def nodeX2YLo : ℚ := (373/125)
def nodeX2YHi : ℚ := (597/200)
def nodeX2XLo : ℚ := (909/1000)
def nodeX2XHi : ℚ := (91/100)
def nodeX2DiskError : ℚ := radiusQ*nodeX2L 0+nodeX2Error 0
theorem nodeX2_norm : |nodeX2Center.1|+|nodeX2Center.2|≤3 := by decide +kernel
theorem nodeX2_Vstep : ∀ j : Fin 8,|qCoefficient j.val|+4*nodeX2V (j.val+1)≤nodeX2V j.val := by decide +kernel
theorem nodeX2_Lstep : ∀ j : Fin 8,nodeX2V (j.val+1)+4*nodeX2L (j.val+1)≤nodeX2L j.val := by decide +kernel
theorem nodeX2_lipschitz (z w : ℂ) (hz : ‖z‖≤4) (hw : ‖w‖≤4) :
    ‖xPoly.eval z-xPoly.eval w‖≤‖z-w‖*(nodeX2L 0:ℝ) := by
  exact polynomial_difference_of_rational_envelope qCoefficient z w 4
    nodeX2V nodeX2L 8 hz hw (by decide +kernel) (by decide +kernel)
    (fun j hj => nodeX2_Vstep ⟨j,hj⟩) (fun j hj => nodeX2_Lstep ⟨j,hj⟩)
theorem nodeX2_Enonneg : ∀ j : Fin 9,0≤nodeX2Error j.val := by decide +kernel
theorem nodeX2_steps : ∀ j : Fin 8,
    |(ratResidual (qCoefficient j.val) nodeX2Center (nodeX2State (j.val+1)) (nodeX2State j.val)).1|+
    |(ratResidual (qCoefficient j.val) nodeX2Center (nodeX2State (j.val+1)) (nodeX2State j.val)).2|+
    4*nodeX2Error (j.val+1)≤nodeX2Error j.val := by decide +kernel
theorem nodeX2_value : ‖xPoly.eval (ratComplex nodeX2Center)-ratComplex (nodeX2State 0)‖≤(nodeX2Error 0:ℝ) := by
  exact polynomial_error_of_rational_certificate qCoefficient nodeX2Center
    nodeX2State nodeX2Error 4 8 (by have hh:=nodeX2_norm; linarith)
    (fun j hj => nodeX2_Enonneg ⟨j,by omega⟩) (by decide +kernel)
    (fun j hj => nodeX2_steps ⟨j,hj⟩)
theorem nodeX2_ylo : nodeX2YLo≤nodeX2Center.1^2+nodeX2Center.2^2-radiusQ*(2*(|nodeX2Center.1|+|nodeX2Center.2|)+radiusQ) := by decide +kernel
theorem nodeX2_yhi : nodeX2Center.1^2+nodeX2Center.2^2+radiusQ*(2*(|nodeX2Center.1|+|nodeX2Center.2|)+radiusQ)≤nodeX2YHi := by decide +kernel
theorem nodeX2_xlo : nodeX2XLo≤(nodeX2State 0).1^2+(nodeX2State 0).2^2-nodeX2DiskError*(2*(|(nodeX2State 0).1|+|(nodeX2State 0).2|)+nodeX2DiskError) := by decide +kernel
theorem nodeX2_xhi : (nodeX2State 0).1^2+(nodeX2State 0).2^2+nodeX2DiskError*(2*(|(nodeX2State 0).1|+|(nodeX2State 0).2|)+nodeX2DiskError)≤nodeX2XHi := by decide +kernel

theorem nodeX2_disk (z : ℂ) (hd : ‖z-ratComplex (centerQ 2)‖<(radiusQ:ℝ)) :
    ‖z‖<1 ∨ ‖xPoly.eval z‖<‖z‖ := by
  have hc : ‖ratComplex nodeX2Center‖≤3 := by
    have hh : |(nodeX2Center.1:ℝ)|+|(nodeX2Center.2:ℝ)|≤3 := by exact_mod_cast nodeX2_norm
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by simpa using hh)
  have hd' : ‖z-ratComplex nodeX2Center‖≤(radiusQ:ℝ) := hd.le
  have hr : (radiusQ:ℝ)≤1 := by norm_num [radiusQ]
  have hz : ‖z‖≤4 := by
    have hh:=norm_add_le (z-ratComplex nodeX2Center) (ratComplex nodeX2Center)
    rw [sub_add_cancel] at hh
    linarith
  have herr:=polynomial_disk_error xPoly z (ratComplex nodeX2Center)
    (ratComplex (nodeX2State 0)) (radiusQ:ℝ) (nodeX2L 0:ℝ) (nodeX2Error 0:ℝ)
    (by exact_mod_cast (show (0:ℚ)≤nodeX2L 0 by decide +kernel)) hd'
    (nodeX2_lipschitz z _ hz (by linarith)) nodeX2_value
  have herr' : ‖xPoly.eval z-ratComplex (nodeX2State 0)‖≤(nodeX2DiskError:ℝ) := by
    simpa only [nodeX2DiskError,Rat.cast_add,Rat.cast_mul] using herr
  have hy := squared_norm_enclosure_of_rational_error z nodeX2Center radiusQ
    nodeX2YLo nodeX2YHi (by decide +kernel) hd' nodeX2_ylo nodeX2_yhi
  have hx := squared_norm_enclosure_of_rational_error (xPoly.eval z) (nodeX2State 0)
    nodeX2DiskError nodeX2XLo nodeX2XHi (by decide +kernel) herr' nodeX2_xlo nodeX2_xhi
  right
  have hh : (nodeX2XHi:ℝ)<(nodeX2YLo:ℝ) := by norm_num [nodeX2XHi,nodeX2YLo]
  nlinarith [norm_nonneg z,norm_nonneg (xPoly.eval z)]

#print axioms nodeX2_disk

def nodeX3Center : ℚ×ℚ := ((6688155811805767/25000000000000000),(-1228363849182842981/1000000000000000000))
def nodeX3V : ℕ→ℚ := fun j => match j with
  | 0 => (3307/1)
  | 1 => (1102/1)
  | 2 => (367/1)
  | 3 => (122/1)
  | 4 => (40/1)
  | 5 => (13/1)
  | 6 => (4/1)
  | 7 => (1/1)
  | 8 => (0/1)
  | _ => 0
def nodeX3L : ℕ→ℚ := fun j => match j with
  | 0 => (7135/1)
  | 1 => (2011/1)
  | 2 => (548/1)
  | 3 => (142/1)
  | 4 => (34/1)
  | 5 => (7/1)
  | 6 => (1/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def nodeX3State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((315131791851898136714663778331/1000000000000000000000000000000),(-1147936224932057120861468247597/1000000000000000000000000000000))
  | 1 => ((457798462985147414851106673967/500000000000000000000000000000),(-4345379597423328864779513443/50000000000000000000000000000))
  | 2 => ((140460142664475437899119745093/500000000000000000000000000000),(241251791147755619423781978813/250000000000000000000000000000))
  | 3 => ((-285664209423197029147289435019/500000000000000000000000000000),(491929308085029429764352000113/500000000000000000000000000000))
  | 4 => ((-684200342105013165754968504733/1000000000000000000000000000000),(268032874766053224769934269679/500000000000000000000000000000))
  | 5 => ((-410615700539705209084899546347/1000000000000000000000000000000),(23683858430991813910385856107/200000000000000000000000000000))
  | 6 => ((-94907107425576684555029205737/1000000000000000000000000000000),(3436732812844783910945724267/500000000000000000000000000000))
  | 7 => ((-559562676015097115130264059/100000000000000000000000000000),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def nodeX3Error : ℕ→ℚ := fun j => match j with
  | 0 => (60085846568080643176952189/53524500000000000000000000000000000000000000000000000)
  | 1 => (270242130839347195251833839/722580750000000000000000000000000000000000000000000000)
  | 2 => (539369620156841430574464539/4335484500000000000000000000000000000000000000000000000)
  | 3 => (6644252306266865408810831/160573500000000000000000000000000000000000000000000000)
  | 4 => (13773795483081849555808891/1040516280000000000000000000000000000000000000000000000)
  | 5 => (958202708020123420578028703/234116163000000000000000000000000000000000000000000000000)
  | 6 => (75840845399769493109524151/70234848900000000000000000000000000000000000000000000000)
  | 7 => (9656851/70234848900000000000000000000000000000)
  | 8 => (0/1)
  | _ => 0
def nodeX3YLo : ℚ := (79/50)
def nodeX3YHi : ℚ := (1581/1000)
def nodeX3XLo : ℚ := (1417/1000)
def nodeX3XHi : ℚ := (709/500)
def nodeX3DiskError : ℚ := radiusQ*nodeX3L 0+nodeX3Error 0
theorem nodeX3_norm : |nodeX3Center.1|+|nodeX3Center.2|≤2 := by decide +kernel
theorem nodeX3_Vstep : ∀ j : Fin 8,|qCoefficient j.val|+3*nodeX3V (j.val+1)≤nodeX3V j.val := by decide +kernel
theorem nodeX3_Lstep : ∀ j : Fin 8,nodeX3V (j.val+1)+3*nodeX3L (j.val+1)≤nodeX3L j.val := by decide +kernel
theorem nodeX3_lipschitz (z w : ℂ) (hz : ‖z‖≤3) (hw : ‖w‖≤3) :
    ‖xPoly.eval z-xPoly.eval w‖≤‖z-w‖*(nodeX3L 0:ℝ) := by
  exact polynomial_difference_of_rational_envelope qCoefficient z w 3
    nodeX3V nodeX3L 8 hz hw (by decide +kernel) (by decide +kernel)
    (fun j hj => nodeX3_Vstep ⟨j,hj⟩) (fun j hj => nodeX3_Lstep ⟨j,hj⟩)
theorem nodeX3_Enonneg : ∀ j : Fin 9,0≤nodeX3Error j.val := by decide +kernel
theorem nodeX3_steps : ∀ j : Fin 8,
    |(ratResidual (qCoefficient j.val) nodeX3Center (nodeX3State (j.val+1)) (nodeX3State j.val)).1|+
    |(ratResidual (qCoefficient j.val) nodeX3Center (nodeX3State (j.val+1)) (nodeX3State j.val)).2|+
    3*nodeX3Error (j.val+1)≤nodeX3Error j.val := by decide +kernel
theorem nodeX3_value : ‖xPoly.eval (ratComplex nodeX3Center)-ratComplex (nodeX3State 0)‖≤(nodeX3Error 0:ℝ) := by
  exact polynomial_error_of_rational_certificate qCoefficient nodeX3Center
    nodeX3State nodeX3Error 3 8 (by have hh:=nodeX3_norm; linarith)
    (fun j hj => nodeX3_Enonneg ⟨j,by omega⟩) (by decide +kernel)
    (fun j hj => nodeX3_steps ⟨j,hj⟩)
theorem nodeX3_ylo : nodeX3YLo≤nodeX3Center.1^2+nodeX3Center.2^2-radiusQ*(2*(|nodeX3Center.1|+|nodeX3Center.2|)+radiusQ) := by decide +kernel
theorem nodeX3_yhi : nodeX3Center.1^2+nodeX3Center.2^2+radiusQ*(2*(|nodeX3Center.1|+|nodeX3Center.2|)+radiusQ)≤nodeX3YHi := by decide +kernel
theorem nodeX3_xlo : nodeX3XLo≤(nodeX3State 0).1^2+(nodeX3State 0).2^2-nodeX3DiskError*(2*(|(nodeX3State 0).1|+|(nodeX3State 0).2|)+nodeX3DiskError) := by decide +kernel
theorem nodeX3_xhi : (nodeX3State 0).1^2+(nodeX3State 0).2^2+nodeX3DiskError*(2*(|(nodeX3State 0).1|+|(nodeX3State 0).2|)+nodeX3DiskError)≤nodeX3XHi := by decide +kernel

theorem nodeX3_disk (z : ℂ) (hd : ‖z-ratComplex (centerQ 3)‖<(radiusQ:ℝ)) :
    ‖z‖<1 ∨ ‖xPoly.eval z‖<‖z‖ := by
  have hc : ‖ratComplex nodeX3Center‖≤2 := by
    have hh : |(nodeX3Center.1:ℝ)|+|(nodeX3Center.2:ℝ)|≤2 := by exact_mod_cast nodeX3_norm
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by simpa using hh)
  have hd' : ‖z-ratComplex nodeX3Center‖≤(radiusQ:ℝ) := hd.le
  have hr : (radiusQ:ℝ)≤1 := by norm_num [radiusQ]
  have hz : ‖z‖≤3 := by
    have hh:=norm_add_le (z-ratComplex nodeX3Center) (ratComplex nodeX3Center)
    rw [sub_add_cancel] at hh
    linarith
  have herr:=polynomial_disk_error xPoly z (ratComplex nodeX3Center)
    (ratComplex (nodeX3State 0)) (radiusQ:ℝ) (nodeX3L 0:ℝ) (nodeX3Error 0:ℝ)
    (by exact_mod_cast (show (0:ℚ)≤nodeX3L 0 by decide +kernel)) hd'
    (nodeX3_lipschitz z _ hz (by linarith)) nodeX3_value
  have herr' : ‖xPoly.eval z-ratComplex (nodeX3State 0)‖≤(nodeX3DiskError:ℝ) := by
    simpa only [nodeX3DiskError,Rat.cast_add,Rat.cast_mul] using herr
  have hy := squared_norm_enclosure_of_rational_error z nodeX3Center radiusQ
    nodeX3YLo nodeX3YHi (by decide +kernel) hd' nodeX3_ylo nodeX3_yhi
  have hx := squared_norm_enclosure_of_rational_error (xPoly.eval z) (nodeX3State 0)
    nodeX3DiskError nodeX3XLo nodeX3XHi (by decide +kernel) herr' nodeX3_xlo nodeX3_xhi
  right
  have hh : (nodeX3XHi:ℝ)<(nodeX3YLo:ℝ) := by norm_num [nodeX3XHi,nodeX3YLo]
  nlinarith [norm_nonneg z,norm_nonneg (xPoly.eval z)]

#print axioms nodeX3_disk

def nodeX4Center : ℚ×ℚ := ((6688155811805767/25000000000000000),(61418192459142149/50000000000000000))
def nodeX4V : ℕ→ℚ := fun j => match j with
  | 0 => (3307/1)
  | 1 => (1102/1)
  | 2 => (367/1)
  | 3 => (122/1)
  | 4 => (40/1)
  | 5 => (13/1)
  | 6 => (4/1)
  | 7 => (1/1)
  | 8 => (0/1)
  | _ => 0
def nodeX4L : ℕ→ℚ := fun j => match j with
  | 0 => (7135/1)
  | 1 => (2011/1)
  | 2 => (548/1)
  | 3 => (142/1)
  | 4 => (34/1)
  | 5 => (7/1)
  | 6 => (1/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def nodeX4State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((9847868495371816876665616521/31250000000000000000000000000),(229587244986411423678823659997/200000000000000000000000000000))
  | 1 => ((915596925970294829046579845567/1000000000000000000000000000000),(2172689798711664362639911807/25000000000000000000000000000))
  | 2 => ((280920285328950873900493049319/1000000000000000000000000000000),(-241251791147755619590074445471/250000000000000000000000000000))
  | 3 => ((-114265683769278811882062467283/200000000000000000000000000000),(-30745581755314339344616015463/31250000000000000000000000000))
  | 4 => ((-684200342105013165995484753767/1000000000000000000000000000000),(-536065749532106449120348450717/1000000000000000000000000000000))
  | 5 => ((-410615700539705209098646477597/1000000000000000000000000000000),(-23683858430991813891105039233/200000000000000000000000000000))
  | 6 => ((-94907107425576684555029205737/1000000000000000000000000000000),(-274938625027582712651832871/40000000000000000000000000000))
  | 7 => ((-559562676015097115130264059/100000000000000000000000000000),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def nodeX4Error : ℕ→ℚ := fun j => match j with
  | 0 => (7700532063319079184022049/5352450000000000000000000000000000000000000000000000)
  | 1 => (3463626712736068127978377/7225807500000000000000000000000000000000000000000000)
  | 2 => (69253205188768438414254089/433548450000000000000000000000000000000000000000000000)
  | 3 => (425688451704427434879607/8028675000000000000000000000000000000000000000000000)
  | 4 => (5645317542783573550266173/325161337500000000000000000000000000000000000000000000)
  | 5 => (3961994676617661151443067/731613009375000000000000000000000000000000000000000000)
  | 6 => (5409395108453956013567767/3511742445000000000000000000000000000000000000000000000)
  | 7 => (9656851/70234848900000000000000000000000000000)
  | 8 => (0/1)
  | _ => 0
def nodeX4YLo : ℚ := (79/50)
def nodeX4YHi : ℚ := (1581/1000)
def nodeX4XLo : ℚ := (1417/1000)
def nodeX4XHi : ℚ := (709/500)
def nodeX4DiskError : ℚ := radiusQ*nodeX4L 0+nodeX4Error 0
theorem nodeX4_norm : |nodeX4Center.1|+|nodeX4Center.2|≤2 := by decide +kernel
theorem nodeX4_Vstep : ∀ j : Fin 8,|qCoefficient j.val|+3*nodeX4V (j.val+1)≤nodeX4V j.val := by decide +kernel
theorem nodeX4_Lstep : ∀ j : Fin 8,nodeX4V (j.val+1)+3*nodeX4L (j.val+1)≤nodeX4L j.val := by decide +kernel
theorem nodeX4_lipschitz (z w : ℂ) (hz : ‖z‖≤3) (hw : ‖w‖≤3) :
    ‖xPoly.eval z-xPoly.eval w‖≤‖z-w‖*(nodeX4L 0:ℝ) := by
  exact polynomial_difference_of_rational_envelope qCoefficient z w 3
    nodeX4V nodeX4L 8 hz hw (by decide +kernel) (by decide +kernel)
    (fun j hj => nodeX4_Vstep ⟨j,hj⟩) (fun j hj => nodeX4_Lstep ⟨j,hj⟩)
theorem nodeX4_Enonneg : ∀ j : Fin 9,0≤nodeX4Error j.val := by decide +kernel
theorem nodeX4_steps : ∀ j : Fin 8,
    |(ratResidual (qCoefficient j.val) nodeX4Center (nodeX4State (j.val+1)) (nodeX4State j.val)).1|+
    |(ratResidual (qCoefficient j.val) nodeX4Center (nodeX4State (j.val+1)) (nodeX4State j.val)).2|+
    3*nodeX4Error (j.val+1)≤nodeX4Error j.val := by decide +kernel
theorem nodeX4_value : ‖xPoly.eval (ratComplex nodeX4Center)-ratComplex (nodeX4State 0)‖≤(nodeX4Error 0:ℝ) := by
  exact polynomial_error_of_rational_certificate qCoefficient nodeX4Center
    nodeX4State nodeX4Error 3 8 (by have hh:=nodeX4_norm; linarith)
    (fun j hj => nodeX4_Enonneg ⟨j,by omega⟩) (by decide +kernel)
    (fun j hj => nodeX4_steps ⟨j,hj⟩)
theorem nodeX4_ylo : nodeX4YLo≤nodeX4Center.1^2+nodeX4Center.2^2-radiusQ*(2*(|nodeX4Center.1|+|nodeX4Center.2|)+radiusQ) := by decide +kernel
theorem nodeX4_yhi : nodeX4Center.1^2+nodeX4Center.2^2+radiusQ*(2*(|nodeX4Center.1|+|nodeX4Center.2|)+radiusQ)≤nodeX4YHi := by decide +kernel
theorem nodeX4_xlo : nodeX4XLo≤(nodeX4State 0).1^2+(nodeX4State 0).2^2-nodeX4DiskError*(2*(|(nodeX4State 0).1|+|(nodeX4State 0).2|)+nodeX4DiskError) := by decide +kernel
theorem nodeX4_xhi : (nodeX4State 0).1^2+(nodeX4State 0).2^2+nodeX4DiskError*(2*(|(nodeX4State 0).1|+|(nodeX4State 0).2|)+nodeX4DiskError)≤nodeX4XHi := by decide +kernel

theorem nodeX4_disk (z : ℂ) (hd : ‖z-ratComplex (centerQ 4)‖<(radiusQ:ℝ)) :
    ‖z‖<1 ∨ ‖xPoly.eval z‖<‖z‖ := by
  have hc : ‖ratComplex nodeX4Center‖≤2 := by
    have hh : |(nodeX4Center.1:ℝ)|+|(nodeX4Center.2:ℝ)|≤2 := by exact_mod_cast nodeX4_norm
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by simpa using hh)
  have hd' : ‖z-ratComplex nodeX4Center‖≤(radiusQ:ℝ) := hd.le
  have hr : (radiusQ:ℝ)≤1 := by norm_num [radiusQ]
  have hz : ‖z‖≤3 := by
    have hh:=norm_add_le (z-ratComplex nodeX4Center) (ratComplex nodeX4Center)
    rw [sub_add_cancel] at hh
    linarith
  have herr:=polynomial_disk_error xPoly z (ratComplex nodeX4Center)
    (ratComplex (nodeX4State 0)) (radiusQ:ℝ) (nodeX4L 0:ℝ) (nodeX4Error 0:ℝ)
    (by exact_mod_cast (show (0:ℚ)≤nodeX4L 0 by decide +kernel)) hd'
    (nodeX4_lipschitz z _ hz (by linarith)) nodeX4_value
  have herr' : ‖xPoly.eval z-ratComplex (nodeX4State 0)‖≤(nodeX4DiskError:ℝ) := by
    simpa only [nodeX4DiskError,Rat.cast_add,Rat.cast_mul] using herr
  have hy := squared_norm_enclosure_of_rational_error z nodeX4Center radiusQ
    nodeX4YLo nodeX4YHi (by decide +kernel) hd' nodeX4_ylo nodeX4_yhi
  have hx := squared_norm_enclosure_of_rational_error (xPoly.eval z) (nodeX4State 0)
    nodeX4DiskError nodeX4XLo nodeX4XHi (by decide +kernel) herr' nodeX4_xlo nodeX4_xhi
  right
  have hh : (nodeX4XHi:ℝ)<(nodeX4YLo:ℝ) := by norm_num [nodeX4XHi,nodeX4YLo]
  nlinarith [norm_nonneg z,norm_nonneg (xPoly.eval z)]

#print axioms nodeX4_disk

def nodeX5Center : ℚ×ℚ := ((282341158415928551/500000000000000000),(-22046191071555161/62500000000000000))
def nodeX5V : ℕ→ℚ := fun j => match j with
  | 0 => (263/1)
  | 1 => (131/1)
  | 2 => (65/1)
  | 3 => (32/1)
  | 4 => (15/1)
  | 5 => (7/1)
  | 6 => (3/1)
  | 7 => (1/1)
  | 8 => (0/1)
  | _ => 0
def nodeX5L : ℕ→ℚ := fun j => match j with
  | 0 => (781/1)
  | 1 => (325/1)
  | 2 => (130/1)
  | 3 => (49/1)
  | 4 => (17/1)
  | 5 => (5/1)
  | 6 => (1/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def nodeX5State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((3636753071280206619278473979/500000000000000000000000000000),(864841734732128052262589661047/1000000000000000000000000000000))
  | 1 => ((-904306685701309950726565487963/1000000000000000000000000000000),(966662901913699940026660313427/1000000000000000000000000000000))
  | 2 => ((-1481749574473143656797427303087/1000000000000000000000000000000),(786268563499957719127604954677/1000000000000000000000000000000))
  | 3 => ((-381558694722934870407604591239/250000000000000000000000000000),(27438652143698949355390826927/62500000000000000000000000000))
  | 4 => ((-48005022822974438590415909979/50000000000000000000000000000),(177716747154973409864440284397/1000000000000000000000000000000))
  | 5 => ((-89500749210735749361795837449/200000000000000000000000000000),(17589268435610338913020445449/500000000000000000000000000000))
  | 6 => ((-96569881963161089621747815849/1000000000000000000000000000000),(493449026877581890222476153/250000000000000000000000000000))
  | 7 => ((-559562676015097115130264059/100000000000000000000000000000),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def nodeX5Error : ℕ→ℚ := fun j => match j with
  | 0 => (15357177837555453722048840921/87793561125000000000000000000000000000000000000000000000)
  | 1 => (15205063315423783842424445627/175587122250000000000000000000000000000000000000000000000)
  | 2 => (7434847754671242003960535399/175587122250000000000000000000000000000000000000000000000)
  | 3 => (7175742837829085765224163809/351174244500000000000000000000000000000000000000000000000)
  | 4 => (3354066106290857923341803141/351174244500000000000000000000000000000000000000000000000)
  | 5 => (1519567734189623764437874249/351174244500000000000000000000000000000000000000000000000)
  | 6 => (58787043410374290180811187/35117424450000000000000000000000000000000000000000000000)
  | 7 => (9656851/70234848900000000000000000000000000000)
  | 8 => (0/1)
  | _ => 0
def nodeX5YLo : ℚ := (443/1000)
def nodeX5YHi : ℚ := (111/250)
def nodeX5XLo : ℚ := (187/250)
def nodeX5XHi : ℚ := (749/1000)
def nodeX5DiskError : ℚ := radiusQ*nodeX5L 0+nodeX5Error 0
theorem nodeX5_norm : |nodeX5Center.1|+|nodeX5Center.2|≤1 := by decide +kernel
theorem nodeX5_Vstep : ∀ j : Fin 8,|qCoefficient j.val|+2*nodeX5V (j.val+1)≤nodeX5V j.val := by decide +kernel
theorem nodeX5_Lstep : ∀ j : Fin 8,nodeX5V (j.val+1)+2*nodeX5L (j.val+1)≤nodeX5L j.val := by decide +kernel
theorem nodeX5_lipschitz (z w : ℂ) (hz : ‖z‖≤2) (hw : ‖w‖≤2) :
    ‖xPoly.eval z-xPoly.eval w‖≤‖z-w‖*(nodeX5L 0:ℝ) := by
  exact polynomial_difference_of_rational_envelope qCoefficient z w 2
    nodeX5V nodeX5L 8 hz hw (by decide +kernel) (by decide +kernel)
    (fun j hj => nodeX5_Vstep ⟨j,hj⟩) (fun j hj => nodeX5_Lstep ⟨j,hj⟩)
theorem nodeX5_Enonneg : ∀ j : Fin 9,0≤nodeX5Error j.val := by decide +kernel
theorem nodeX5_steps : ∀ j : Fin 8,
    |(ratResidual (qCoefficient j.val) nodeX5Center (nodeX5State (j.val+1)) (nodeX5State j.val)).1|+
    |(ratResidual (qCoefficient j.val) nodeX5Center (nodeX5State (j.val+1)) (nodeX5State j.val)).2|+
    2*nodeX5Error (j.val+1)≤nodeX5Error j.val := by decide +kernel
theorem nodeX5_value : ‖xPoly.eval (ratComplex nodeX5Center)-ratComplex (nodeX5State 0)‖≤(nodeX5Error 0:ℝ) := by
  exact polynomial_error_of_rational_certificate qCoefficient nodeX5Center
    nodeX5State nodeX5Error 2 8 (by have hh:=nodeX5_norm; linarith)
    (fun j hj => nodeX5_Enonneg ⟨j,by omega⟩) (by decide +kernel)
    (fun j hj => nodeX5_steps ⟨j,hj⟩)
theorem nodeX5_ylo : nodeX5YLo≤nodeX5Center.1^2+nodeX5Center.2^2-radiusQ*(2*(|nodeX5Center.1|+|nodeX5Center.2|)+radiusQ) := by decide +kernel
theorem nodeX5_yhi : nodeX5Center.1^2+nodeX5Center.2^2+radiusQ*(2*(|nodeX5Center.1|+|nodeX5Center.2|)+radiusQ)≤nodeX5YHi := by decide +kernel
theorem nodeX5_xlo : nodeX5XLo≤(nodeX5State 0).1^2+(nodeX5State 0).2^2-nodeX5DiskError*(2*(|(nodeX5State 0).1|+|(nodeX5State 0).2|)+nodeX5DiskError) := by decide +kernel
theorem nodeX5_xhi : (nodeX5State 0).1^2+(nodeX5State 0).2^2+nodeX5DiskError*(2*(|(nodeX5State 0).1|+|(nodeX5State 0).2|)+nodeX5DiskError)≤nodeX5XHi := by decide +kernel

theorem nodeX5_disk (z : ℂ) (hd : ‖z-ratComplex (centerQ 5)‖<(radiusQ:ℝ)) :
    ‖z‖<1 ∨ ‖xPoly.eval z‖<‖z‖ := by
  have hc : ‖ratComplex nodeX5Center‖≤1 := by
    have hh : |(nodeX5Center.1:ℝ)|+|(nodeX5Center.2:ℝ)|≤1 := by exact_mod_cast nodeX5_norm
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by simpa using hh)
  have hd' : ‖z-ratComplex nodeX5Center‖≤(radiusQ:ℝ) := hd.le
  have hr : (radiusQ:ℝ)≤1 := by norm_num [radiusQ]
  have hz : ‖z‖≤2 := by
    have hh:=norm_add_le (z-ratComplex nodeX5Center) (ratComplex nodeX5Center)
    rw [sub_add_cancel] at hh
    linarith
  have herr:=polynomial_disk_error xPoly z (ratComplex nodeX5Center)
    (ratComplex (nodeX5State 0)) (radiusQ:ℝ) (nodeX5L 0:ℝ) (nodeX5Error 0:ℝ)
    (by exact_mod_cast (show (0:ℚ)≤nodeX5L 0 by decide +kernel)) hd'
    (nodeX5_lipschitz z _ hz (by linarith)) nodeX5_value
  have herr' : ‖xPoly.eval z-ratComplex (nodeX5State 0)‖≤(nodeX5DiskError:ℝ) := by
    simpa only [nodeX5DiskError,Rat.cast_add,Rat.cast_mul] using herr
  have hy := squared_norm_enclosure_of_rational_error z nodeX5Center radiusQ
    nodeX5YLo nodeX5YHi (by decide +kernel) hd' nodeX5_ylo nodeX5_yhi
  have hx := squared_norm_enclosure_of_rational_error (xPoly.eval z) (nodeX5State 0)
    nodeX5DiskError nodeX5XLo nodeX5XHi (by decide +kernel) herr' nodeX5_xlo nodeX5_xhi
  left
  have hh : (nodeX5YHi:ℝ)<1 := by norm_num [nodeX5YHi]
  nlinarith [norm_nonneg z]

#print axioms nodeX5_disk

def nodeX6Center : ℚ×ℚ := ((282341158415928551/500000000000000000),(14109562285795303/40000000000000000))
def nodeX6V : ℕ→ℚ := fun j => match j with
  | 0 => (263/1)
  | 1 => (131/1)
  | 2 => (65/1)
  | 3 => (32/1)
  | 4 => (15/1)
  | 5 => (7/1)
  | 6 => (3/1)
  | 7 => (1/1)
  | 8 => (0/1)
  | _ => 0
def nodeX6L : ℕ→ℚ := fun j => match j with
  | 0 => (781/1)
  | 1 => (325/1)
  | 2 => (130/1)
  | 3 => (49/1)
  | 4 => (17/1)
  | 5 => (5/1)
  | 6 => (1/1)
  | 7 => (0/1)
  | 8 => (0/1)
  | _ => 0
def nodeX6State : ℕ→ℚ×ℚ := fun j => match j with
  | 0 => ((7273506142560410266431592221/1000000000000000000000000000000),(-43242086736606402541534552333/50000000000000000000000000000))
  | 1 => ((-904306685701309952861386604821/1000000000000000000000000000000),(-60416431369606246109924324777/62500000000000000000000000000))
  | 2 => ((-370437393618285914472432554061/250000000000000000000000000000),(-786268563499957717053129789953/1000000000000000000000000000000))
  | 3 => ((-76311738944586974101317441477/50000000000000000000000000000),(-219509217149591594234022607639/500000000000000000000000000000))
  | 4 => ((-24002511411487219297022610221/25000000000000000000000000000),(-17771674715497340936201344783/100000000000000000000000000000))
  | 5 => ((-22375187302683937340646338973/50000000000000000000000000000),(-17589268435610338863155628727/500000000000000000000000000000))
  | 6 => ((-96569881963161089621747815849/1000000000000000000000000000000),(-1973796107510327555294277853/1000000000000000000000000000000))
  | 7 => ((-559562676015097115130264059/100000000000000000000000000000),(0/1))
  | 8 => ((0/1),(0/1))
  | _ => (0,0)
def nodeX6Error : ℕ→ℚ := fun j => match j with
  | 0 => (113152803290608844368592625769/702348489000000000000000000000000000000000000000000000000)
  | 1 => (56237689519963940713704539489/702348489000000000000000000000000000000000000000000000000)
  | 2 => (2804422741579305636799495819/70234848900000000000000000000000000000000000000000000000)
  | 3 => (6862751985362229253220056561/351174244500000000000000000000000000000000000000000000000)
  | 4 => (3375455363036609789256074033/351174244500000000000000000000000000000000000000000000000)
  | 5 => (731019545564149822014979451/175587122250000000000000000000000000000000000000000000000)
  | 6 => (110065928287291347473422873/70234848900000000000000000000000000000000000000000000000)
  | 7 => (9656851/70234848900000000000000000000000000000)
  | 8 => (0/1)
  | _ => 0
def nodeX6YLo : ℚ := (443/1000)
def nodeX6YHi : ℚ := (111/250)
def nodeX6XLo : ℚ := (187/250)
def nodeX6XHi : ℚ := (749/1000)
def nodeX6DiskError : ℚ := radiusQ*nodeX6L 0+nodeX6Error 0
theorem nodeX6_norm : |nodeX6Center.1|+|nodeX6Center.2|≤1 := by decide +kernel
theorem nodeX6_Vstep : ∀ j : Fin 8,|qCoefficient j.val|+2*nodeX6V (j.val+1)≤nodeX6V j.val := by decide +kernel
theorem nodeX6_Lstep : ∀ j : Fin 8,nodeX6V (j.val+1)+2*nodeX6L (j.val+1)≤nodeX6L j.val := by decide +kernel
theorem nodeX6_lipschitz (z w : ℂ) (hz : ‖z‖≤2) (hw : ‖w‖≤2) :
    ‖xPoly.eval z-xPoly.eval w‖≤‖z-w‖*(nodeX6L 0:ℝ) := by
  exact polynomial_difference_of_rational_envelope qCoefficient z w 2
    nodeX6V nodeX6L 8 hz hw (by decide +kernel) (by decide +kernel)
    (fun j hj => nodeX6_Vstep ⟨j,hj⟩) (fun j hj => nodeX6_Lstep ⟨j,hj⟩)
theorem nodeX6_Enonneg : ∀ j : Fin 9,0≤nodeX6Error j.val := by decide +kernel
theorem nodeX6_steps : ∀ j : Fin 8,
    |(ratResidual (qCoefficient j.val) nodeX6Center (nodeX6State (j.val+1)) (nodeX6State j.val)).1|+
    |(ratResidual (qCoefficient j.val) nodeX6Center (nodeX6State (j.val+1)) (nodeX6State j.val)).2|+
    2*nodeX6Error (j.val+1)≤nodeX6Error j.val := by decide +kernel
theorem nodeX6_value : ‖xPoly.eval (ratComplex nodeX6Center)-ratComplex (nodeX6State 0)‖≤(nodeX6Error 0:ℝ) := by
  exact polynomial_error_of_rational_certificate qCoefficient nodeX6Center
    nodeX6State nodeX6Error 2 8 (by have hh:=nodeX6_norm; linarith)
    (fun j hj => nodeX6_Enonneg ⟨j,by omega⟩) (by decide +kernel)
    (fun j hj => nodeX6_steps ⟨j,hj⟩)
theorem nodeX6_ylo : nodeX6YLo≤nodeX6Center.1^2+nodeX6Center.2^2-radiusQ*(2*(|nodeX6Center.1|+|nodeX6Center.2|)+radiusQ) := by decide +kernel
theorem nodeX6_yhi : nodeX6Center.1^2+nodeX6Center.2^2+radiusQ*(2*(|nodeX6Center.1|+|nodeX6Center.2|)+radiusQ)≤nodeX6YHi := by decide +kernel
theorem nodeX6_xlo : nodeX6XLo≤(nodeX6State 0).1^2+(nodeX6State 0).2^2-nodeX6DiskError*(2*(|(nodeX6State 0).1|+|(nodeX6State 0).2|)+nodeX6DiskError) := by decide +kernel
theorem nodeX6_xhi : (nodeX6State 0).1^2+(nodeX6State 0).2^2+nodeX6DiskError*(2*(|(nodeX6State 0).1|+|(nodeX6State 0).2|)+nodeX6DiskError)≤nodeX6XHi := by decide +kernel

theorem nodeX6_disk (z : ℂ) (hd : ‖z-ratComplex (centerQ 6)‖<(radiusQ:ℝ)) :
    ‖z‖<1 ∨ ‖xPoly.eval z‖<‖z‖ := by
  have hc : ‖ratComplex nodeX6Center‖≤1 := by
    have hh : |(nodeX6Center.1:ℝ)|+|(nodeX6Center.2:ℝ)|≤1 := by exact_mod_cast nodeX6_norm
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by simpa using hh)
  have hd' : ‖z-ratComplex nodeX6Center‖≤(radiusQ:ℝ) := hd.le
  have hr : (radiusQ:ℝ)≤1 := by norm_num [radiusQ]
  have hz : ‖z‖≤2 := by
    have hh:=norm_add_le (z-ratComplex nodeX6Center) (ratComplex nodeX6Center)
    rw [sub_add_cancel] at hh
    linarith
  have herr:=polynomial_disk_error xPoly z (ratComplex nodeX6Center)
    (ratComplex (nodeX6State 0)) (radiusQ:ℝ) (nodeX6L 0:ℝ) (nodeX6Error 0:ℝ)
    (by exact_mod_cast (show (0:ℚ)≤nodeX6L 0 by decide +kernel)) hd'
    (nodeX6_lipschitz z _ hz (by linarith)) nodeX6_value
  have herr' : ‖xPoly.eval z-ratComplex (nodeX6State 0)‖≤(nodeX6DiskError:ℝ) := by
    simpa only [nodeX6DiskError,Rat.cast_add,Rat.cast_mul] using herr
  have hy := squared_norm_enclosure_of_rational_error z nodeX6Center radiusQ
    nodeX6YLo nodeX6YHi (by decide +kernel) hd' nodeX6_ylo nodeX6_yhi
  have hx := squared_norm_enclosure_of_rational_error (xPoly.eval z) (nodeX6State 0)
    nodeX6DiskError nodeX6XLo nodeX6XHi (by decide +kernel) herr' nodeX6_xlo nodeX6_xhi
  left
  have hh : (nodeX6YHi:ℝ)<1 := by norm_num [nodeX6YHi]
  nlinarith [norm_nonneg z]

#print axioms nodeX6_disk

end QuantitativeArithmeticSmallLevelThirtyThreeRoot
end
end

/-! ## ThirtyThreeRootModulus -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeRoot
open Complex Polynomial Finset QuantitativeArithmeticComplexHornerBounds
/-- Every septic root violates the physical modulus inequalities. -/
theorem root_modulus_excluded (z : ℂ) (hz : p7.eval z=0) :
    ‖z‖<1 ∨ ‖xPoly.eval z‖<‖z‖ := by
  obtain ⟨i,hi⟩ := p7_root_in_disk z hz
  fin_cases i
  · exact nodeX0_disk z hi
  · exact nodeX1_disk z hi
  · exact nodeX2_disk z hi
  · exact nodeX3_disk z hi
  · exact nodeX4_disk z hi
  · exact nodeX5_disk z hi
  · exact nodeX6_disk z hi

#print axioms root_modulus_excluded

end QuantitativeArithmeticSmallLevelThirtyThreeRoot
end
end

/-! ## ThirtyThreeRootPhysical -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeRoot

/-- The septic branch cannot meet the original exponential curve on the
right of the central line. The separate pole-to-branch linkage is not assumed here. -/
theorem no_physical_septic (h u : ℂ) (hu : u=1 ∨ u= -1) (hh : 0 ≤ h.re)
    (hp : p7.eval (-u*(3:ℂ)^h)=0)
    (hx : xPoly.eval (-u*(3:ℂ)^h)=(4:ℂ)^h) : False := by
  have hY : ‖-u*(3:ℂ)^h‖=(3:ℝ)^h.re := by
    have h3 : ‖(3:ℂ)^h‖=(3:ℝ)^h.re := by
      simpa only [Nat.cast_ofNat] using Complex.norm_natCast_cpow_of_pos (by decide : 0<3) h
    rcases hu with hu|hu <;> simp [hu,h3]
  have hX : ‖(4:ℂ)^h‖=(4:ℝ)^h.re := by
    simpa only [Nat.cast_ofNat] using Complex.norm_natCast_cpow_of_pos (by decide : 0<4) h
  have hy := Real.one_le_rpow (x:=(3:ℝ)) (by norm_num) hh
  have hxy := Real.rpow_le_rpow (x:=(3:ℝ)) (y:=4) (by norm_num) (by norm_num) hh
  rcases root_modulus_excluded _ hp with he|he
  · rw [hY] at he
    exact (not_lt_of_ge hy) he
  · rw [hx,hY,hX] at he
    exact (not_lt_of_ge hxy) he

#print axioms no_physical_septic
end QuantitativeArithmeticSmallLevelThirtyThreeRoot
end
end

/-! ## ThirtyThreePhysicalLocus -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeLocus
open Complex QuantitativeArithmeticSmallLevelThirtyThreeRoot QuantitativeArithmeticComplexHornerBounds

theorem square_two (h : ℂ) : ((2:ℂ)^h)^2=(4:ℂ)^h := by
  have hh := Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤2)
    (by norm_num : (0:ℝ)≤2) h
  norm_num only [Complex.ofReal_ofNat,show (2:ℂ)*2=4 by norm_num] at hh
  simpa only [pow_two] using hh.symm

theorem x_at_minus_three : xPoly.eval (-3)=4 := by
  norm_num [xPoly,qCoefficient,hornerPolynomial]

theorem first_branch_impossible (h u : ℂ) (hu : u=1 ∨ u= -1) (hh : 1 ≤ h.re)
    (he : ((4:ℂ)^h)^2=u*(3:ℂ)^h+1) : False := by
  have h4 : ‖(4:ℂ)^h‖=(4:ℝ)^h.re := by
    simpa only [Nat.cast_ofNat] using Complex.norm_natCast_cpow_of_pos (by decide : 0<4) h
  have h3 : ‖u*(3:ℂ)^h‖=(3:ℝ)^h.re := by
    have hp : ‖(3:ℂ)^h‖=(3:ℝ)^h.re := by
      simpa only [Nat.cast_ofNat] using Complex.norm_natCast_cpow_of_pos (by decide : 0<3) h
    rcases hu with hu|hu <;> simp [hu,hp]
  have hnorm := norm_add_le (u*(3:ℂ)^h) 1
  rw [← he,norm_pow,h4,h3,norm_one] at hnorm
  have hcmp := Real.rpow_le_rpow (x:=(3:ℝ)) (y:=4) (by norm_num) (by norm_num) (by linarith : 0 ≤ h.re)
  have hbound : (4:ℝ) ≤ (4:ℝ)^h.re := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4) hh
  nlinarith

theorem second_branch_physical (h u A : ℂ) (hu : u=1 ∨ u= -1) (hh : 0 ≤ h.re)
    (ha : A= -(4:ℂ)^h-1)
    (hp : u*(3:ℂ)^h=3 ∨ p7.eval (-(u*(3:ℂ)^h))=0)
    (hx : (4:ℂ)^h=xPoly.eval (-(u*(3:ℂ)^h))) :
    h=1 ∧ u=1 ∧ A= -5 := by
  have hy : u*(3:ℂ)^h=3 := by
    rcases hp with hp|hp
    · exact hp
    · exact False.elim (no_physical_septic h u hu hh
        (by simpa only [neg_mul] using hp)
        (by simpa only [neg_mul] using hx.symm))
  have hx4 : (4:ℂ)^h=4 := by rw [hy,x_at_minus_three] at hx; exact hx
  have hp2 : ((2:ℂ)^(h-1))^2=1 := by
    rw [Complex.cpow_sub _ _ (by norm_num : (2:ℂ)≠0),Complex.cpow_one,div_pow,square_two,hx4]
    norm_num
  have hp3 : ((3:ℂ)^(h-1))^2=1 := by
    rw [Complex.cpow_sub _ _ (by norm_num : (3:ℂ)≠0),Complex.cpow_one,div_pow]
    rcases hu with hu|hu <;> rw [hu] at hy <;> norm_num at hy ⊢
    · rw [hy]; norm_num
    · have he : (3:ℂ)^h= -3 := by linear_combination -hy
      rw [he]; norm_num
  have he := QuantitativeArithmeticPrimePowerTorsion.distinct_primes_cpow_torsion
    (by decide : Nat.Prime 2) (by decide : Nat.Prime 3) (by decide : (2:ℕ)≠3)
    (h-1) 2 2 (by decide) (by decide) hp2 hp3
  have hh1 : h=1 := sub_eq_zero.mp he
  refine ⟨hh1,?_,?_⟩
  · rw [hh1,Complex.cpow_one] at hy
    linear_combination hy/3
  · rw [hx4] at ha
    norm_num at ha
    exact ha

/-- To the right of real part one in the shifted variable, the entire
algebraic locus consists of a single possible point. -/
theorem locus_above_one (h u A : ℂ) (hu : u=1 ∨ u= -1) (hh : 1 ≤ h.re)
    (hl : InLocus ((4:ℂ)^h) (u*(3:ℂ)^h) A) : h=1 ∧ u=1 ∧ A= -5 := by
  rcases hl with ⟨_,he⟩|⟨ha,hp,hx⟩
  · exact False.elim (first_branch_impossible h u hu hh he)
  · exact second_branch_physical h u A hu (by linarith) ha hp hx

#print axioms locus_above_one
#print axioms second_branch_physical
end QuantitativeArithmeticSmallLevelThirtyThreeLocus
end
end

/-! ## ThirtyThreePoleChainLocus -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeLocus
open Complex

/-- The prime-two denominator at the bottom of an integer pole chain,
together with the algebraic locus at its top, leaves only the unshifted
exceptional point. This does not assume equal pole orders along the chain. -/
theorem pole_chain_locus (h u a : ℂ) (n : ℕ)
    (hu : u=1 ∨ u= -1) (hh : 0 ≤ h.re)
    (hd : (2:ℂ)^h+((2:ℂ)^h)⁻¹+a=0)
    (hl : InLocus ((4:ℂ)^(h+n)) (u*(3:ℂ)^(h+n)) (a*(2:ℂ)^(h+n))) :
    n=0 ∧ h=1 ∧ u=1 ∧ a= -5/2 := by
  have hn : n=0 := by
    by_contra hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hh1 : 1 ≤ (h+(n:ℂ)).re := by simp only [add_re,natCast_re]; linarith
    obtain ⟨he,_,ha⟩ := locus_above_one (h+n) u (a*(2:ℂ)^(h+n)) hu hh1 hl
    have hre := congrArg Complex.re he
    simp only [add_re,natCast_re,one_re] at hre
    have hnle : n ≤ 1 := by exact_mod_cast (show (n:ℝ) ≤ 1 by linarith)
    have hnEq : n=1 := by omega
    subst n
    have hh0 : h=0 := by linear_combination he
    rw [he,Complex.cpow_one] at ha
    norm_num [hh0] at hd
    have : (1:ℂ)=0 := by linear_combination ha-2*hd
    exact one_ne_zero this
  subst n
  simp only [Nat.cast_zero,add_zero] at hl
  have hx : (2:ℂ)^h≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have ha : a*(2:ℂ)^h= -(4:ℂ)^h-1 := by
    rw [← square_two]
    field_simp at hd ⊢
    linear_combination hd
  have hb : u*(3:ℂ)^h=3 ∨ QuantitativeArithmeticSmallLevelThirtyThreeRoot.p7.eval (-(u*(3:ℂ)^h))=0 := by
    rcases hl with ⟨ha',_⟩|⟨_,hp,_⟩
    · have : (1:ℂ)=0 := by linear_combination ha-ha'
      exact False.elim (one_ne_zero this)
    · exact hp
  have hc : (4:ℂ)^h=QuantitativeArithmeticSmallLevelThirtyThreeRoot.xPoly.eval (-(u*(3:ℂ)^h)) := by
    rcases hl with ⟨ha',_⟩|⟨_,_,hp⟩
    · have : (1:ℂ)=0 := by linear_combination ha-ha'
      exact False.elim (one_ne_zero this)
    · exact hp
  obtain ⟨he,hu1,ha1⟩ := second_branch_physical h u (a*(2:ℂ)^h) hu hh ha hb hc
  refine ⟨rfl,he,hu1,?_⟩
  rw [he,Complex.cpow_one] at ha1
  linear_combination ha1/2

#print axioms pole_chain_locus
end QuantitativeArithmeticSmallLevelThirtyThreeLocus
end
end

/-! ## ThirtyThreeContinuedHecke -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Filter Matrix SmallLevelPrimeRates
open scoped Topology

theorem original_hecke_germ (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (BG : ℝ) (G : ℂ→Fin 66→ℂ)
    (hG : ∀ i z,MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z,BG<z.re → G z=gridVector (2*m) f z)
    (i : Fin 61) (x : ℂ) :
    (fun z => gridHeckeLeading m f z (G z) i)=ᶠ[𝓝[≠] x] (fun _ => 0) := by
  obtain ⟨B,hB⟩ := original_grid_hecke_row m hm hf i
  apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) (max B BG) _ _ _ x (by linarith)
  · intro z _
    have he : (fun s => gridHeckeLeading m f s (G s) i)=
        (fun s => ∑ j,fullLeadingMatrix m f 1 s (.hecke i) j*G s j) := by
      funext s
      exact (congrFun (fullLeadingMatrix_mulVec m f 1 s (G s)) (.hecke i)).symm
    rw [he]
    exact MeromorphicAt.fun_sum (fun j _ =>
      (fullLeadingMatrix_analytic m f 1 (.hecke i) j z).meromorphicAt.mul
        (hG j z).meromorphicAt)
  · intro z _
    exact analyticAt_const.meromorphicAt
  · intro z hz
    dsimp only
    rw [hGF z (lt_of_le_of_lt (le_max_right B BG) hz),gridHeckeLeading_grid]
    exact hB z (lt_of_le_of_lt (le_max_left B BG) hz)

/-- Subtract the two prime-2 rows. This is the precise denominator that
can obstruct regularity of the odd third-denominator twist. -/
theorem third_sixth_algebra (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (w : Fin 66→ℂ)
    (h11 : gridHeckeLeading m f s w 11=0)
    (h22 : gridHeckeLeading m f s w 22=0) :
    (parameter 2 m s+(parameter 2 m s)⁻¹+(Real.sqrt 2:ℂ)*f 2)*(w 22-w 44)=
      parameter 2 m s*(w 11-w 55) := by
  have hx := parameter_ne_zero 2 m (by decide) s
  norm_num [gridHeckeLeading,gridHeckeP,gridHeckeT,gridHeckeSpecs,
    Finset.sum_range_succ,gridIndex] at h11 h22
  field_simp at h11 h22 ⊢
  linear_combination h22-h11

theorem original_third_sixth_germ (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (BG : ℝ) (G : ℂ→Fin 66→ℂ)
    (hG : ∀ i z,MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z,BG<z.re → G z=gridVector (2*m) f z) (x : ℂ) :
    (fun s => (parameter 2 m s+(parameter 2 m s)⁻¹+(Real.sqrt 2:ℂ)*f 2)*(G s 22-G s 44))
      =ᶠ[𝓝[≠] x] (fun s => parameter 2 m s*(G s 11-G s 55)) := by
  filter_upwards [original_hecke_germ m hm hf BG G hG hGF 11 x,
    original_hecke_germ m hm hf BG G hG hGF 22 x] with s h11 h22
  exact third_sixth_algebra m f s (G s) h11 h22

#print axioms original_third_sixth_germ
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeContinuedInfinity -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Filter SmallLevelAdditive
open scoped Topology

theorem original_infinity_germ (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (BG : ℝ) (G : ℂ→Fin 66→ℂ)
    (hG : ∀ i z,MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z,BG<z.re → G z=gridVector (2*m) f z)
    (i : Fin 46) :
    (∀ x,AnalyticAt ℂ (sourceEntire m f (((gridInfinityIndex i:ℕ):ℝ)/66)) x) ∧
    ∀ x,(fun s => G s (gridInfinityIndex i))=ᶠ[𝓝[≠] x]
      sourceEntire m f (((gridInfinityIndex i:ℕ):ℝ)/66) := by
  obtain ⟨ε,hε,hlaw⟩ := original_grid_fricke_laws hf
  have hE := grid_infinity_entire_of_fricke m hm hf (grid_physical_sign m hε)
    (grid_fricke_of_laws m hε hlaw) i
  obtain ⟨B,hB⟩ := sourceEntire_initial m hf
  refine ⟨fun x => hE.analyticAt x,?_⟩
  intro x
  apply SmallLevelContinuation.halfplane_germ_identity
    (x.re-1) (max B BG) _ _ _ x (by linarith)
  · intro z _
    exact (hG (gridInfinityIndex i) z).meromorphicAt
  · intro z _
    exact (hE.analyticAt z).meromorphicAt
  · intro z hz
    dsimp only
    rw [hGF z (lt_of_le_of_lt (le_max_right B BG) hz)]
    simpa only [gridVector,grid,Int.cast_natCast,Nat.cast_ofNat] using
      (hB (((gridInfinityIndex i:ℕ):ℝ)/66) z
        (lt_of_le_of_lt (le_max_left B BG) hz)).symm

def sixthOddEntire (m : ℕ) (f : ℕ→ℂ) (s : ℂ) : ℂ :=
  sourceEntire m f (11/66) s-sourceEntire m f (55/66) s

/-- The odd sixth-denominator transform has an entire representative,
derived from known matrix words and the original hypotheses. -/
theorem original_sixth_odd_entire (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (BG : ℝ) (G : ℂ→Fin 66→ℂ)
    (hG : ∀ i z,MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z,BG<z.re → G z=gridVector (2*m) f z) :
    (∀ x,AnalyticAt ℂ (sixthOddEntire m f) x) ∧
    ∀ x,(fun s => G s 11-G s 55)=ᶠ[𝓝[≠] x] sixthOddEntire m f := by
  have h11 := original_infinity_germ m hm hf BG G hG hGF 10
  have h55 := original_infinity_germ m hm hf BG G hG hGF 9
  have e11 : gridInfinityIndex 10=(11:Fin 66) := rfl
  have e55 : gridInfinityIndex 9=(55:Fin 66) := rfl
  simp only [e11,e55] at h11 h55
  exact ⟨fun x => (h11.1 x).sub (h55.1 x),fun x => (h11.2 x).sub (h55.2 x)⟩

#print axioms original_sixth_odd_entire
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeThirdPole -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Filter SmallLevelPrimeRates
open scoped Topology

def thirdDenominator (m : ℕ) (f : ℕ→ℂ) (s : ℂ) : ℂ :=
  parameter 2 m s+(parameter 2 m s)⁻¹+(Real.sqrt 2:ℂ)*f 2

theorem thirdDenominator_analytic (m : ℕ) (f : ℕ→ℂ) (x : ℂ) :
    AnalyticAt ℂ (thirdDenominator m f) x :=
  ((parameter_analytic 2 m (by decide) x).add
    ((parameter_analytic 2 m (by decide) x).inv
      (parameter_ne_zero 2 m (by decide) x))).add analyticAt_const

/-- Without assuming regularity of the third twist, every one of its poles
must be a zero of the explicit prime-2 denominator. -/
theorem original_third_pole_denominator (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (BG : ℝ) (G : ℂ→Fin 66→ℂ)
    (hG : ∀ i z,MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z,BG<z.re → G z=gridVector (2*m) f z) (x : ℂ)
    (hpole : meromorphicOrderAt (fun s => G s 22-G s 44) x < 0) :
    thirdDenominator m f x=0 := by
  by_contra hd
  obtain ⟨hD,hDG⟩ := original_sixth_odd_entire m hm hf BG G hG hGF
  have hA := thirdDenominator_analytic m f x
  have hQ : AnalyticAt ℂ
      (fun s => parameter 2 m s*sixthOddEntire m f s/thirdDenominator m f s) x :=
    ((parameter_analytic 2 m (by decide) x).mul (hD x)).div hA hd
  have he : (fun s => G s 22-G s 44)=ᶠ[𝓝[≠] x]
      (fun s => parameter 2 m s*sixthOddEntire m f s/thirdDenominator m f s) := by
    filter_upwards [original_third_sixth_germ m hm hf BG G hG hGF x,hDG x,
      (hA.continuousAt.eventually_ne hd).filter_mono nhdsWithin_le_nhds] with s hs hDs hds
    change thirdDenominator m f s*(G s 22-G s 44)=_ at hs
    rw [hDs] at hs
    exact (eq_div_iff hds).mpr (by simpa only [mul_comm] using hs)
  rw [meromorphicOrderAt_congr he] at hpole
  exact (not_lt_of_ge hQ.meromorphicOrderAt_nonneg) hpole

#print axioms original_third_pole_denominator
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeOriginalPoleChain -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex SmallLevelPrimeRates QuantitativeArithmeticSmallLevelThirtyThreeLocus

/-- From the original Euler and Fricke hypotheses: if a pole of the odd
third twist in the right half-plane has a rightmost grid pole away from
the weight point, that pole cannot be a positive integer translate. -/
theorem PoleSystem.original_pole_chain {m : ℕ} (hm : 0 < m) {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε) (s : ℂ) (n : ℕ)
    (hs : (m:ℝ) ≤ s.re)
    (hpole : meromorphicOrderAt (fun z => S.G z 22-S.G z 44) s < 0)
    (htop : ∃ j,meromorphicOrderAt (fun z => S.G z j) (s+n) < 0)
    (hshift : ∀ r : ℕ,0 < r → ∀ j,0 ≤ meromorphicOrderAt (fun z => S.G z j) (s+n+r))
    (hweight : s+n≠((2*m:ℕ):ℂ)) :
    n=0 ∧ s=(m:ℂ)+1 ∧ badParameter f 3=1 ∧ badParameter f 2= -5/2 := by
  have hd := original_third_pole_denominator m hm hf S.B S.G S.meromorphic S.agreement s hpole
  have hl := S.rightmost_locus hf hε (s+n) htop hshift hweight
  have hh : 0 ≤ (s-(m:ℂ)).re := by simp only [sub_re,natCast_re]; linarith
  have he : s+(n:ℂ)-(m:ℂ)=s-(m:ℂ)+n := by ring
  have hl' : InLocus ((4:ℂ)^(s-(m:ℂ)+n))
      (badParameter f 3*(3:ℂ)^(s-(m:ℂ)+n))
      (badParameter f 2*(2:ℂ)^(s-(m:ℂ)+n)) := by
    simpa only [parameter,Nat.cast_ofNat,he,square_two] using hl
  obtain ⟨hn,he1,hu,ha⟩ := pole_chain_locus (s-(m:ℂ)) (badParameter f 3)
    (badParameter f 2) n (badParameter_three_sign hf.toEulerData) hh hd hl'
  refine ⟨hn,?_,hu,ha⟩
  linear_combination he1

#print axioms PoleSystem.original_pole_chain
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeExceptionalSigns -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeExceptionalSigns
open QuantitativeArithmeticSevenLaurentRows

theorem minus_positive (v : ℕ→ℂ)
    (h : ∀ i : Fin 22,eval 2 3 (11) 1 (-5/2) 1 1 v (QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reducedRow i)=0) :
    v 18=0 ∧ v 42=0 := by
  have h0 := h 0
  have h4 := h 4
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reducedRow,eval,monomial] at h0 h4
  constructor
  · linear_combination (437/36)*h0-(-14/3)*h4
  · linear_combination (-307/18)*h0+(-20/3)*h4

theorem minus_negative (v : ℕ→ℂ)
    (h : ∀ i : Fin 22,eval 2 3 (-11) 1 (-5/2) 1 1 v (QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reducedRow i)=0) :
    v 18=0 ∧ v 42=0 := by
  have h0 := h 0
  have h4 := h 4
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reducedRow,eval,monomial] at h0 h4
  constructor
  · linear_combination (289/360)*h0-(7/15)*h4
  · linear_combination (-31/36)*h0+(2/3)*h4

theorem plus_positive (v : ℕ→ℂ)
    (h : ∀ i : Fin 22,eval 2 3 (11) 1 (-5/2) 1 1 v (QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reducedRow i)=0) :
    v 18=0 ∧ v 42=0 := by
  have h0 := h 0
  have h4 := h 4
  norm_num [QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reducedRow,eval,monomial] at h0 h4
  constructor
  · linear_combination (355/396)*h0-(14/33)*h4
  · linear_combination (-197/198)*h0+(20/33)*h4

#print axioms plus_positive
end QuantitativeArithmeticSmallLevelThirtyThreeExceptionalSigns
end
end

/-! ## ThirtyThreeOriginalExceptionalSigns -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelPrimeRates QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelThirtyThreeLaurent

theorem exceptional_kernel_signs (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (v : Fin 66→ℂ) (hv0 : v≠0)
    (hv : fullLeadingMatrix m f ε ((m:ℂ)+1)*ᵥv=0)
    (hu : badParameter f 3=1) (ha : badParameter f 2= -5/2) :
    phase m ε= -1 ∧ badParameter f 11= -1 := by
  have hp (p : ℕ) : parameter p m ((m:ℂ)+1)=(p:ℂ) := by
    rw [parameter,show (m:ℂ)+1-(m:ℂ)=1 by ring,Complex.cpow_one]
  have hb (σ : ℚ) (hσ : (σ:ℂ)=phase m ε*badParameter f 3*badParameter f 11) :=
    original_base_kernel m hf ε ((m:ℂ)+1) hε σ hσ v hv
  simp only [hp,hu,ha,one_mul,Nat.cast_ofNat] at hb
  have hzero (he : ∀ i : ℕ,i<66 → v (gridIndex (i:ℤ))=0) : False := by
    apply hv0
    funext i
    simpa only [gridIndex_fin,Pi.zero_apply] using he i.val i.isLt
  rcases scaled_phase_sign m hf hε with hσ|hσ
  · have hs : ((1:ℚ):ℂ)=phase m ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
    have hbase := hb 1 (by simpa only [hu] using hs)
    rcases badParameter_eleven_sign hf.toEulerData with hz|hz
    · rw [hz] at hbase
      simp only [one_mul] at hbase
      have hr := QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.reduced_rows_zero 2 3 11 (-5/2)
        (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hbase
      obtain ⟨h18,h42⟩ := QuantitativeArithmeticSmallLevelThirtyThreeExceptionalSigns.plus_positive _ hr
      exact False.elim (hzero (QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.kernel_free_zero
        2 3 11 (-5/2) (fun i => v (gridIndex (i:ℤ)))
        (by norm_num) (by norm_num) (by norm_num) hbase h18 h42))
    · refine ⟨?_,hz⟩
      rw [hu,hz] at hσ
      linear_combination -hσ
  · have hs : (((-1):ℚ):ℂ)=phase m ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
    have hbase := hb (-1) (by simpa only [hu] using hs)
    rcases badParameter_eleven_sign hf.toEulerData with hz|hz
    · rw [hz] at hbase
      simp only [one_mul] at hbase
      have hr := QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reduced_rows_zero 2 3 (11) (-5/2)
        (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hbase
      obtain ⟨h18,h42⟩ := QuantitativeArithmeticSmallLevelThirtyThreeExceptionalSigns.minus_positive _ hr
      exact False.elim (hzero (QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.kernel_free_zero
        2 3 (11) (-5/2) (fun i => v (gridIndex (i:ℤ)))
        (by norm_num) (by norm_num) (by norm_num) hbase h18 h42))
    · rw [hz] at hbase
      simp only [neg_one_mul] at hbase
      have hr := QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.reduced_rows_zero 2 3 (-11) (-5/2)
        (fun i => v (gridIndex (i:ℤ))) (by norm_num) (by norm_num) (by norm_num) hbase
      obtain ⟨h18,h42⟩ := QuantitativeArithmeticSmallLevelThirtyThreeExceptionalSigns.minus_negative _ hr
      exact False.elim (hzero (QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.kernel_free_zero
        2 3 (-11) (-5/2) (fun i => v (gridIndex (i:ℤ)))
        (by norm_num) (by norm_num) (by norm_num) hbase h18 h42))

#print axioms exceptional_kernel_signs
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeThirdShiftLinksBenchmark -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftLinks
open QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftRational QuantitativeArithmeticSmallLevelThirtyThreeKnownWords QuantitativeArithmeticSmallLevelThirtyThreeLaurent
open SmallLevelFiniteShift QuantitativeArithmeticSevenLaurentRows

theorem row000_link (w : Fin 264→ℂ) :
    jetBlockRow 0 (sourceIndex 0) w=row000 w := by
  have hd : rowDerivative (sourceIndex 0)=(66/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 0)=v 0 := rfl
  have hs : sourceRows 0=[((1/1:ℚ),0,(0,0,0,0,0,0,0)),((-1/1:ℚ),65,(2,1,1,1,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 0=sourceKind 0 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (0 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row000] <;> ring

theorem row231_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 668) w=row231 w := by
  have hd : rowDerivative (sourceIndex 668)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 668)=0 := rfl
  have hs : sourceRows 668=[((1/1:ℚ),22,(0,0,0,0,0,0,0)),((1/1:ℚ),44,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 668=sourceKind 668 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (668 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row231] <;> ring

theorem row263_link (w : Fin 264→ℂ) :
    jetBlockRow 3 (sourceIndex 740) w=row263 w := by
  have hd : rowDerivative (sourceIndex 740)=(0/1:ℚ) := by decide +kernel
  have hh (v : Fin 66→ℂ) : rowHead v (sourceIndex 740)=0 := rfl
  have hs : sourceRows 740=[((1/1:ℚ),26,(0,0,0,0,0,0,0)),((1/1:ℚ),38,(-2,0,0,0,0,0,0)),((-1/1:ℚ),52,(-1,0,0,0,1,0,0)),((1/1:ℚ),59,(0,0,0,0,0,0,0))] := rfl
  unfold jetBlockRow
  simp only [hd,hh,jetLead]
  have hi : sourceIndex 740=sourceKind 740 := rfl
  simp_rw [hi,← (QuantitativeArithmeticSmallLevelThirtyThreeLaurent.source_match (i := (740 : Fin 775))),hs]
  norm_num [eval,QuantitativeArithmeticSevenLaurentRows.monomial,jetSlice,finProdFinEquiv,
    lowerIndex,Finset.sum_range_succ,gridSample,FinitenessRamanujanSum.residues,gridIndex,row263] <;> ring

#print axioms row263_link
end QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftLinks
end
end

/-! ## ThirtyThreeThirdShiftRationalKernel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftRational

theorem kernel_zero (w : Fin 264→ℂ) (hw : ∀ i,rows w i=0) : w=0 := by
  funext i
  fin_cases i
  · exact coordinate000_zero w hw
  · exact coordinate001_zero w hw
  · exact coordinate002_zero w hw
  · exact coordinate003_zero w hw
  · exact coordinate004_zero w hw
  · exact coordinate005_zero w hw
  · exact coordinate006_zero w hw
  · exact coordinate007_zero w hw
  · exact coordinate008_zero w hw
  · exact coordinate009_zero w hw
  · exact coordinate010_zero w hw
  · exact coordinate011_zero w hw
  · exact coordinate012_zero w hw
  · exact coordinate013_zero w hw
  · exact coordinate014_zero w hw
  · exact coordinate015_zero w hw
  · exact coordinate016_zero w hw
  · exact coordinate017_zero w hw
  · exact coordinate018_zero w hw
  · exact coordinate019_zero w hw
  · exact coordinate020_zero w hw
  · exact coordinate021_zero w hw
  · exact coordinate022_zero w hw
  · exact coordinate023_zero w hw
  · exact coordinate024_zero w hw
  · exact coordinate025_zero w hw
  · exact coordinate026_zero w hw
  · exact coordinate027_zero w hw
  · exact coordinate028_zero w hw
  · exact coordinate029_zero w hw
  · exact coordinate030_zero w hw
  · exact coordinate031_zero w hw
  · exact coordinate032_zero w hw
  · exact coordinate033_zero w hw
  · exact coordinate034_zero w hw
  · exact coordinate035_zero w hw
  · exact coordinate036_zero w hw
  · exact coordinate037_zero w hw
  · exact coordinate038_zero w hw
  · exact coordinate039_zero w hw
  · exact coordinate040_zero w hw
  · exact coordinate041_zero w hw
  · exact coordinate042_zero w hw
  · exact coordinate043_zero w hw
  · exact coordinate044_zero w hw
  · exact coordinate045_zero w hw
  · exact coordinate046_zero w hw
  · exact coordinate047_zero w hw
  · exact coordinate048_zero w hw
  · exact coordinate049_zero w hw
  · exact coordinate050_zero w hw
  · exact coordinate051_zero w hw
  · exact coordinate052_zero w hw
  · exact coordinate053_zero w hw
  · exact coordinate054_zero w hw
  · exact coordinate055_zero w hw
  · exact coordinate056_zero w hw
  · exact coordinate057_zero w hw
  · exact coordinate058_zero w hw
  · exact coordinate059_zero w hw
  · exact coordinate060_zero w hw
  · exact coordinate061_zero w hw
  · exact coordinate062_zero w hw
  · exact coordinate063_zero w hw
  · exact coordinate064_zero w hw
  · exact coordinate065_zero w hw
  · exact coordinate066_zero w hw
  · exact coordinate067_zero w hw
  · exact coordinate068_zero w hw
  · exact coordinate069_zero w hw
  · exact coordinate070_zero w hw
  · exact coordinate071_zero w hw
  · exact coordinate072_zero w hw
  · exact coordinate073_zero w hw
  · exact coordinate074_zero w hw
  · exact coordinate075_zero w hw
  · exact coordinate076_zero w hw
  · exact coordinate077_zero w hw
  · exact coordinate078_zero w hw
  · exact coordinate079_zero w hw
  · exact coordinate080_zero w hw
  · exact coordinate081_zero w hw
  · exact coordinate082_zero w hw
  · exact coordinate083_zero w hw
  · exact coordinate084_zero w hw
  · exact coordinate085_zero w hw
  · exact coordinate086_zero w hw
  · exact coordinate087_zero w hw
  · exact coordinate088_zero w hw
  · exact coordinate089_zero w hw
  · exact coordinate090_zero w hw
  · exact coordinate091_zero w hw
  · exact coordinate092_zero w hw
  · exact coordinate093_zero w hw
  · exact coordinate094_zero w hw
  · exact coordinate095_zero w hw
  · exact coordinate096_zero w hw
  · exact coordinate097_zero w hw
  · exact coordinate098_zero w hw
  · exact coordinate099_zero w hw
  · exact coordinate100_zero w hw
  · exact coordinate101_zero w hw
  · exact coordinate102_zero w hw
  · exact coordinate103_zero w hw
  · exact coordinate104_zero w hw
  · exact coordinate105_zero w hw
  · exact coordinate106_zero w hw
  · exact coordinate107_zero w hw
  · exact coordinate108_zero w hw
  · exact coordinate109_zero w hw
  · exact coordinate110_zero w hw
  · exact coordinate111_zero w hw
  · exact coordinate112_zero w hw
  · exact coordinate113_zero w hw
  · exact coordinate114_zero w hw
  · exact coordinate115_zero w hw
  · exact coordinate116_zero w hw
  · exact coordinate117_zero w hw
  · exact coordinate118_zero w hw
  · exact coordinate119_zero w hw
  · exact coordinate120_zero w hw
  · exact coordinate121_zero w hw
  · exact coordinate122_zero w hw
  · exact coordinate123_zero w hw
  · exact coordinate124_zero w hw
  · exact coordinate125_zero w hw
  · exact coordinate126_zero w hw
  · exact coordinate127_zero w hw
  · exact coordinate128_zero w hw
  · exact coordinate129_zero w hw
  · exact coordinate130_zero w hw
  · exact coordinate131_zero w hw
  · exact coordinate132_zero w hw
  · exact coordinate133_zero w hw
  · exact coordinate134_zero w hw
  · exact coordinate135_zero w hw
  · exact coordinate136_zero w hw
  · exact coordinate137_zero w hw
  · exact coordinate138_zero w hw
  · exact coordinate139_zero w hw
  · exact coordinate140_zero w hw
  · exact coordinate141_zero w hw
  · exact coordinate142_zero w hw
  · exact coordinate143_zero w hw
  · exact coordinate144_zero w hw
  · exact coordinate145_zero w hw
  · exact coordinate146_zero w hw
  · exact coordinate147_zero w hw
  · exact coordinate148_zero w hw
  · exact coordinate149_zero w hw
  · exact coordinate150_zero w hw
  · exact coordinate151_zero w hw
  · exact coordinate152_zero w hw
  · exact coordinate153_zero w hw
  · exact coordinate154_zero w hw
  · exact coordinate155_zero w hw
  · exact coordinate156_zero w hw
  · exact coordinate157_zero w hw
  · exact coordinate158_zero w hw
  · exact coordinate159_zero w hw
  · exact coordinate160_zero w hw
  · exact coordinate161_zero w hw
  · exact coordinate162_zero w hw
  · exact coordinate163_zero w hw
  · exact coordinate164_zero w hw
  · exact coordinate165_zero w hw
  · exact coordinate166_zero w hw
  · exact coordinate167_zero w hw
  · exact coordinate168_zero w hw
  · exact coordinate169_zero w hw
  · exact coordinate170_zero w hw
  · exact coordinate171_zero w hw
  · exact coordinate172_zero w hw
  · exact coordinate173_zero w hw
  · exact coordinate174_zero w hw
  · exact coordinate175_zero w hw
  · exact coordinate176_zero w hw
  · exact coordinate177_zero w hw
  · exact coordinate178_zero w hw
  · exact coordinate179_zero w hw
  · exact coordinate180_zero w hw
  · exact coordinate181_zero w hw
  · exact coordinate182_zero w hw
  · exact coordinate183_zero w hw
  · exact coordinate184_zero w hw
  · exact coordinate185_zero w hw
  · exact coordinate186_zero w hw
  · exact coordinate187_zero w hw
  · exact coordinate188_zero w hw
  · exact coordinate189_zero w hw
  · exact coordinate190_zero w hw
  · exact coordinate191_zero w hw
  · exact coordinate192_zero w hw
  · exact coordinate193_zero w hw
  · exact coordinate194_zero w hw
  · exact coordinate195_zero w hw
  · exact coordinate196_zero w hw
  · exact coordinate197_zero w hw
  · exact coordinate198_zero w hw
  · exact coordinate199_zero w hw
  · exact coordinate200_zero w hw
  · exact coordinate201_zero w hw
  · exact coordinate202_zero w hw
  · exact coordinate203_zero w hw
  · exact coordinate204_zero w hw
  · exact coordinate205_zero w hw
  · exact coordinate206_zero w hw
  · exact coordinate207_zero w hw
  · exact coordinate208_zero w hw
  · exact coordinate209_zero w hw
  · exact coordinate210_zero w hw
  · exact coordinate211_zero w hw
  · exact coordinate212_zero w hw
  · exact coordinate213_zero w hw
  · exact coordinate214_zero w hw
  · exact coordinate215_zero w hw
  · exact coordinate216_zero w hw
  · exact coordinate217_zero w hw
  · exact coordinate218_zero w hw
  · exact coordinate219_zero w hw
  · exact coordinate220_zero w hw
  · exact coordinate221_zero w hw
  · exact coordinate222_zero w hw
  · exact coordinate223_zero w hw
  · exact coordinate224_zero w hw
  · exact coordinate225_zero w hw
  · exact coordinate226_zero w hw
  · exact coordinate227_zero w hw
  · exact coordinate228_zero w hw
  · exact coordinate229_zero w hw
  · exact coordinate230_zero w hw
  · exact coordinate231_zero w hw
  · exact coordinate232_zero w hw
  · exact coordinate233_zero w hw
  · exact coordinate234_zero w hw
  · exact coordinate235_zero w hw
  · exact coordinate236_zero w hw
  · exact coordinate237_zero w hw
  · exact coordinate238_zero w hw
  · exact coordinate239_zero w hw
  · exact coordinate240_zero w hw
  · exact coordinate241_zero w hw
  · exact coordinate242_zero w hw
  · exact coordinate243_zero w hw
  · exact coordinate244_zero w hw
  · exact coordinate245_zero w hw
  · exact coordinate246_zero w hw
  · exact coordinate247_zero w hw
  · exact coordinate248_zero w hw
  · exact coordinate249_zero w hw
  · exact coordinate250_zero w hw
  · exact coordinate251_zero w hw
  · exact coordinate252_zero w hw
  · exact coordinate253_zero w hw
  · exact coordinate254_zero w hw
  · exact coordinate255_zero w hw
  · exact coordinate256_zero w hw
  · exact coordinate257_zero w hw
  · exact coordinate258_zero w hw
  · exact coordinate259_zero w hw
  · exact coordinate260_zero w hw
  · exact coordinate261_zero w hw
  · exact coordinate262_zero w hw
  · exact coordinate263_zero w hw

#print axioms kernel_zero
end QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftRational
end
end

/-! ## ThirtyThreeThirdShiftBlockKernel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftLinks

theorem jetBlock_kernel_zero (w : Fin 264→ℂ) (h : ∀ n r,jetBlockRow n r w=0) : w=0 := by
  apply QuantitativeArithmeticSmallLevelThirtyThreeThirdShiftRational.kernel_zero w
  intro i
  fin_cases i
  · exact (row000_link w).symm.trans (h 0 (sourceIndex 0))
  · exact (row001_link w).symm.trans (h 0 (sourceIndex 1))
  · exact (row002_link w).symm.trans (h 0 (sourceIndex 2))
  · exact (row003_link w).symm.trans (h 0 (sourceIndex 3))
  · exact (row004_link w).symm.trans (h 0 (sourceIndex 4))
  · exact (row005_link w).symm.trans (h 0 (sourceIndex 5))
  · exact (row006_link w).symm.trans (h 0 (sourceIndex 6))
  · exact (row007_link w).symm.trans (h 0 (sourceIndex 7))
  · exact (row008_link w).symm.trans (h 0 (sourceIndex 8))
  · exact (row009_link w).symm.trans (h 0 (sourceIndex 9))
  · exact (row010_link w).symm.trans (h 0 (sourceIndex 10))
  · exact (row011_link w).symm.trans (h 0 (sourceIndex 11))
  · exact (row012_link w).symm.trans (h 0 (sourceIndex 12))
  · exact (row013_link w).symm.trans (h 0 (sourceIndex 43))
  · exact (row014_link w).symm.trans (h 0 (sourceIndex 44))
  · exact (row015_link w).symm.trans (h 0 (sourceIndex 45))
  · exact (row016_link w).symm.trans (h 0 (sourceIndex 48))
  · exact (row017_link w).symm.trans (h 0 (sourceIndex 52))
  · exact (row018_link w).symm.trans (h 0 (sourceIndex 53))
  · exact (row019_link w).symm.trans (h 0 (sourceIndex 54))
  · exact (row020_link w).symm.trans (h 0 (sourceIndex 55))
  · exact (row021_link w).symm.trans (h 0 (sourceIndex 57))
  · exact (row022_link w).symm.trans (h 0 (sourceIndex 65))
  · exact (row023_link w).symm.trans (h 0 (sourceIndex 66))
  · exact (row024_link w).symm.trans (h 0 (sourceIndex 67))
  · exact (row025_link w).symm.trans (h 0 (sourceIndex 68))
  · exact (row026_link w).symm.trans (h 0 (sourceIndex 69))
  · exact (row027_link w).symm.trans (h 0 (sourceIndex 70))
  · exact (row028_link w).symm.trans (h 0 (sourceIndex 71))
  · exact (row029_link w).symm.trans (h 0 (sourceIndex 72))
  · exact (row030_link w).symm.trans (h 0 (sourceIndex 73))
  · exact (row031_link w).symm.trans (h 0 (sourceIndex 77))
  · exact (row032_link w).symm.trans (h 0 (sourceIndex 78))
  · exact (row033_link w).symm.trans (h 0 (sourceIndex 79))
  · exact (row034_link w).symm.trans (h 0 (sourceIndex 668))
  · exact (row035_link w).symm.trans (h 0 (sourceIndex 669))
  · exact (row036_link w).symm.trans (h 0 (sourceIndex 670))
  · exact (row037_link w).symm.trans (h 0 (sourceIndex 671))
  · exact (row038_link w).symm.trans (h 0 (sourceIndex 672))
  · exact (row039_link w).symm.trans (h 0 (sourceIndex 673))
  · exact (row040_link w).symm.trans (h 0 (sourceIndex 674))
  · exact (row041_link w).symm.trans (h 0 (sourceIndex 686))
  · exact (row042_link w).symm.trans (h 0 (sourceIndex 687))
  · exact (row043_link w).symm.trans (h 0 (sourceIndex 688))
  · exact (row044_link w).symm.trans (h 0 (sourceIndex 689))
  · exact (row045_link w).symm.trans (h 0 (sourceIndex 690))
  · exact (row046_link w).symm.trans (h 0 (sourceIndex 691))
  · exact (row047_link w).symm.trans (h 0 (sourceIndex 716))
  · exact (row048_link w).symm.trans (h 0 (sourceIndex 718))
  · exact (row049_link w).symm.trans (h 0 (sourceIndex 719))
  · exact (row050_link w).symm.trans (h 0 (sourceIndex 720))
  · exact (row051_link w).symm.trans (h 0 (sourceIndex 721))
  · exact (row052_link w).symm.trans (h 0 (sourceIndex 722))
  · exact (row053_link w).symm.trans (h 0 (sourceIndex 723))
  · exact (row054_link w).symm.trans (h 0 (sourceIndex 724))
  · exact (row055_link w).symm.trans (h 0 (sourceIndex 726))
  · exact (row056_link w).symm.trans (h 0 (sourceIndex 727))
  · exact (row057_link w).symm.trans (h 0 (sourceIndex 728))
  · exact (row058_link w).symm.trans (h 0 (sourceIndex 729))
  · exact (row059_link w).symm.trans (h 0 (sourceIndex 730))
  · exact (row060_link w).symm.trans (h 0 (sourceIndex 731))
  · exact (row061_link w).symm.trans (h 0 (sourceIndex 732))
  · exact (row062_link w).symm.trans (h 0 (sourceIndex 733))
  · exact (row063_link w).symm.trans (h 0 (sourceIndex 734))
  · exact (row064_link w).symm.trans (h 0 (sourceIndex 740))
  · exact (row065_link w).symm.trans (h 1 (sourceIndex 0))
  · exact (row066_link w).symm.trans (h 1 (sourceIndex 1))
  · exact (row067_link w).symm.trans (h 1 (sourceIndex 2))
  · exact (row068_link w).symm.trans (h 1 (sourceIndex 3))
  · exact (row069_link w).symm.trans (h 1 (sourceIndex 4))
  · exact (row070_link w).symm.trans (h 1 (sourceIndex 5))
  · exact (row071_link w).symm.trans (h 1 (sourceIndex 6))
  · exact (row072_link w).symm.trans (h 1 (sourceIndex 7))
  · exact (row073_link w).symm.trans (h 1 (sourceIndex 8))
  · exact (row074_link w).symm.trans (h 1 (sourceIndex 9))
  · exact (row075_link w).symm.trans (h 1 (sourceIndex 10))
  · exact (row076_link w).symm.trans (h 1 (sourceIndex 11))
  · exact (row077_link w).symm.trans (h 1 (sourceIndex 12))
  · exact (row078_link w).symm.trans (h 1 (sourceIndex 43))
  · exact (row079_link w).symm.trans (h 1 (sourceIndex 44))
  · exact (row080_link w).symm.trans (h 1 (sourceIndex 45))
  · exact (row081_link w).symm.trans (h 1 (sourceIndex 48))
  · exact (row082_link w).symm.trans (h 1 (sourceIndex 52))
  · exact (row083_link w).symm.trans (h 1 (sourceIndex 53))
  · exact (row084_link w).symm.trans (h 1 (sourceIndex 54))
  · exact (row085_link w).symm.trans (h 1 (sourceIndex 55))
  · exact (row086_link w).symm.trans (h 1 (sourceIndex 57))
  · exact (row087_link w).symm.trans (h 1 (sourceIndex 65))
  · exact (row088_link w).symm.trans (h 1 (sourceIndex 66))
  · exact (row089_link w).symm.trans (h 1 (sourceIndex 67))
  · exact (row090_link w).symm.trans (h 1 (sourceIndex 68))
  · exact (row091_link w).symm.trans (h 1 (sourceIndex 69))
  · exact (row092_link w).symm.trans (h 1 (sourceIndex 70))
  · exact (row093_link w).symm.trans (h 1 (sourceIndex 71))
  · exact (row094_link w).symm.trans (h 1 (sourceIndex 72))
  · exact (row095_link w).symm.trans (h 1 (sourceIndex 73))
  · exact (row096_link w).symm.trans (h 1 (sourceIndex 77))
  · exact (row097_link w).symm.trans (h 1 (sourceIndex 78))
  · exact (row098_link w).symm.trans (h 1 (sourceIndex 79))
  · exact (row099_link w).symm.trans (h 1 (sourceIndex 668))
  · exact (row100_link w).symm.trans (h 1 (sourceIndex 669))
  · exact (row101_link w).symm.trans (h 1 (sourceIndex 670))
  · exact (row102_link w).symm.trans (h 1 (sourceIndex 671))
  · exact (row103_link w).symm.trans (h 1 (sourceIndex 672))
  · exact (row104_link w).symm.trans (h 1 (sourceIndex 673))
  · exact (row105_link w).symm.trans (h 1 (sourceIndex 674))
  · exact (row106_link w).symm.trans (h 1 (sourceIndex 686))
  · exact (row107_link w).symm.trans (h 1 (sourceIndex 687))
  · exact (row108_link w).symm.trans (h 1 (sourceIndex 688))
  · exact (row109_link w).symm.trans (h 1 (sourceIndex 689))
  · exact (row110_link w).symm.trans (h 1 (sourceIndex 690))
  · exact (row111_link w).symm.trans (h 1 (sourceIndex 691))
  · exact (row112_link w).symm.trans (h 1 (sourceIndex 716))
  · exact (row113_link w).symm.trans (h 1 (sourceIndex 717))
  · exact (row114_link w).symm.trans (h 1 (sourceIndex 718))
  · exact (row115_link w).symm.trans (h 1 (sourceIndex 719))
  · exact (row116_link w).symm.trans (h 1 (sourceIndex 720))
  · exact (row117_link w).symm.trans (h 1 (sourceIndex 721))
  · exact (row118_link w).symm.trans (h 1 (sourceIndex 722))
  · exact (row119_link w).symm.trans (h 1 (sourceIndex 723))
  · exact (row120_link w).symm.trans (h 1 (sourceIndex 724))
  · exact (row121_link w).symm.trans (h 1 (sourceIndex 726))
  · exact (row122_link w).symm.trans (h 1 (sourceIndex 727))
  · exact (row123_link w).symm.trans (h 1 (sourceIndex 728))
  · exact (row124_link w).symm.trans (h 1 (sourceIndex 729))
  · exact (row125_link w).symm.trans (h 1 (sourceIndex 730))
  · exact (row126_link w).symm.trans (h 1 (sourceIndex 731))
  · exact (row127_link w).symm.trans (h 1 (sourceIndex 732))
  · exact (row128_link w).symm.trans (h 1 (sourceIndex 733))
  · exact (row129_link w).symm.trans (h 1 (sourceIndex 734))
  · exact (row130_link w).symm.trans (h 1 (sourceIndex 740))
  · exact (row131_link w).symm.trans (h 2 (sourceIndex 0))
  · exact (row132_link w).symm.trans (h 2 (sourceIndex 1))
  · exact (row133_link w).symm.trans (h 2 (sourceIndex 2))
  · exact (row134_link w).symm.trans (h 2 (sourceIndex 3))
  · exact (row135_link w).symm.trans (h 2 (sourceIndex 4))
  · exact (row136_link w).symm.trans (h 2 (sourceIndex 5))
  · exact (row137_link w).symm.trans (h 2 (sourceIndex 6))
  · exact (row138_link w).symm.trans (h 2 (sourceIndex 7))
  · exact (row139_link w).symm.trans (h 2 (sourceIndex 8))
  · exact (row140_link w).symm.trans (h 2 (sourceIndex 9))
  · exact (row141_link w).symm.trans (h 2 (sourceIndex 10))
  · exact (row142_link w).symm.trans (h 2 (sourceIndex 11))
  · exact (row143_link w).symm.trans (h 2 (sourceIndex 12))
  · exact (row144_link w).symm.trans (h 2 (sourceIndex 43))
  · exact (row145_link w).symm.trans (h 2 (sourceIndex 44))
  · exact (row146_link w).symm.trans (h 2 (sourceIndex 45))
  · exact (row147_link w).symm.trans (h 2 (sourceIndex 48))
  · exact (row148_link w).symm.trans (h 2 (sourceIndex 52))
  · exact (row149_link w).symm.trans (h 2 (sourceIndex 53))
  · exact (row150_link w).symm.trans (h 2 (sourceIndex 54))
  · exact (row151_link w).symm.trans (h 2 (sourceIndex 55))
  · exact (row152_link w).symm.trans (h 2 (sourceIndex 57))
  · exact (row153_link w).symm.trans (h 2 (sourceIndex 65))
  · exact (row154_link w).symm.trans (h 2 (sourceIndex 66))
  · exact (row155_link w).symm.trans (h 2 (sourceIndex 67))
  · exact (row156_link w).symm.trans (h 2 (sourceIndex 68))
  · exact (row157_link w).symm.trans (h 2 (sourceIndex 69))
  · exact (row158_link w).symm.trans (h 2 (sourceIndex 70))
  · exact (row159_link w).symm.trans (h 2 (sourceIndex 71))
  · exact (row160_link w).symm.trans (h 2 (sourceIndex 72))
  · exact (row161_link w).symm.trans (h 2 (sourceIndex 73))
  · exact (row162_link w).symm.trans (h 2 (sourceIndex 77))
  · exact (row163_link w).symm.trans (h 2 (sourceIndex 78))
  · exact (row164_link w).symm.trans (h 2 (sourceIndex 79))
  · exact (row165_link w).symm.trans (h 2 (sourceIndex 668))
  · exact (row166_link w).symm.trans (h 2 (sourceIndex 669))
  · exact (row167_link w).symm.trans (h 2 (sourceIndex 670))
  · exact (row168_link w).symm.trans (h 2 (sourceIndex 671))
  · exact (row169_link w).symm.trans (h 2 (sourceIndex 672))
  · exact (row170_link w).symm.trans (h 2 (sourceIndex 673))
  · exact (row171_link w).symm.trans (h 2 (sourceIndex 674))
  · exact (row172_link w).symm.trans (h 2 (sourceIndex 686))
  · exact (row173_link w).symm.trans (h 2 (sourceIndex 687))
  · exact (row174_link w).symm.trans (h 2 (sourceIndex 688))
  · exact (row175_link w).symm.trans (h 2 (sourceIndex 689))
  · exact (row176_link w).symm.trans (h 2 (sourceIndex 690))
  · exact (row177_link w).symm.trans (h 2 (sourceIndex 691))
  · exact (row178_link w).symm.trans (h 2 (sourceIndex 716))
  · exact (row179_link w).symm.trans (h 2 (sourceIndex 718))
  · exact (row180_link w).symm.trans (h 2 (sourceIndex 719))
  · exact (row181_link w).symm.trans (h 2 (sourceIndex 720))
  · exact (row182_link w).symm.trans (h 2 (sourceIndex 721))
  · exact (row183_link w).symm.trans (h 2 (sourceIndex 722))
  · exact (row184_link w).symm.trans (h 2 (sourceIndex 723))
  · exact (row185_link w).symm.trans (h 2 (sourceIndex 724))
  · exact (row186_link w).symm.trans (h 2 (sourceIndex 726))
  · exact (row187_link w).symm.trans (h 2 (sourceIndex 727))
  · exact (row188_link w).symm.trans (h 2 (sourceIndex 728))
  · exact (row189_link w).symm.trans (h 2 (sourceIndex 729))
  · exact (row190_link w).symm.trans (h 2 (sourceIndex 730))
  · exact (row191_link w).symm.trans (h 2 (sourceIndex 731))
  · exact (row192_link w).symm.trans (h 2 (sourceIndex 732))
  · exact (row193_link w).symm.trans (h 2 (sourceIndex 733))
  · exact (row194_link w).symm.trans (h 2 (sourceIndex 734))
  · exact (row195_link w).symm.trans (h 2 (sourceIndex 740))
  · exact (row196_link w).symm.trans (h 2 (sourceIndex 750))
  · exact (row197_link w).symm.trans (h 3 (sourceIndex 0))
  · exact (row198_link w).symm.trans (h 3 (sourceIndex 1))
  · exact (row199_link w).symm.trans (h 3 (sourceIndex 2))
  · exact (row200_link w).symm.trans (h 3 (sourceIndex 3))
  · exact (row201_link w).symm.trans (h 3 (sourceIndex 4))
  · exact (row202_link w).symm.trans (h 3 (sourceIndex 5))
  · exact (row203_link w).symm.trans (h 3 (sourceIndex 6))
  · exact (row204_link w).symm.trans (h 3 (sourceIndex 7))
  · exact (row205_link w).symm.trans (h 3 (sourceIndex 8))
  · exact (row206_link w).symm.trans (h 3 (sourceIndex 9))
  · exact (row207_link w).symm.trans (h 3 (sourceIndex 10))
  · exact (row208_link w).symm.trans (h 3 (sourceIndex 11))
  · exact (row209_link w).symm.trans (h 3 (sourceIndex 12))
  · exact (row210_link w).symm.trans (h 3 (sourceIndex 43))
  · exact (row211_link w).symm.trans (h 3 (sourceIndex 44))
  · exact (row212_link w).symm.trans (h 3 (sourceIndex 45))
  · exact (row213_link w).symm.trans (h 3 (sourceIndex 48))
  · exact (row214_link w).symm.trans (h 3 (sourceIndex 52))
  · exact (row215_link w).symm.trans (h 3 (sourceIndex 53))
  · exact (row216_link w).symm.trans (h 3 (sourceIndex 54))
  · exact (row217_link w).symm.trans (h 3 (sourceIndex 55))
  · exact (row218_link w).symm.trans (h 3 (sourceIndex 57))
  · exact (row219_link w).symm.trans (h 3 (sourceIndex 65))
  · exact (row220_link w).symm.trans (h 3 (sourceIndex 66))
  · exact (row221_link w).symm.trans (h 3 (sourceIndex 67))
  · exact (row222_link w).symm.trans (h 3 (sourceIndex 68))
  · exact (row223_link w).symm.trans (h 3 (sourceIndex 69))
  · exact (row224_link w).symm.trans (h 3 (sourceIndex 70))
  · exact (row225_link w).symm.trans (h 3 (sourceIndex 71))
  · exact (row226_link w).symm.trans (h 3 (sourceIndex 72))
  · exact (row227_link w).symm.trans (h 3 (sourceIndex 73))
  · exact (row228_link w).symm.trans (h 3 (sourceIndex 77))
  · exact (row229_link w).symm.trans (h 3 (sourceIndex 78))
  · exact (row230_link w).symm.trans (h 3 (sourceIndex 79))
  · exact (row231_link w).symm.trans (h 3 (sourceIndex 668))
  · exact (row232_link w).symm.trans (h 3 (sourceIndex 669))
  · exact (row233_link w).symm.trans (h 3 (sourceIndex 670))
  · exact (row234_link w).symm.trans (h 3 (sourceIndex 671))
  · exact (row235_link w).symm.trans (h 3 (sourceIndex 672))
  · exact (row236_link w).symm.trans (h 3 (sourceIndex 673))
  · exact (row237_link w).symm.trans (h 3 (sourceIndex 674))
  · exact (row238_link w).symm.trans (h 3 (sourceIndex 686))
  · exact (row239_link w).symm.trans (h 3 (sourceIndex 687))
  · exact (row240_link w).symm.trans (h 3 (sourceIndex 688))
  · exact (row241_link w).symm.trans (h 3 (sourceIndex 689))
  · exact (row242_link w).symm.trans (h 3 (sourceIndex 690))
  · exact (row243_link w).symm.trans (h 3 (sourceIndex 691))
  · exact (row244_link w).symm.trans (h 3 (sourceIndex 716))
  · exact (row245_link w).symm.trans (h 3 (sourceIndex 717))
  · exact (row246_link w).symm.trans (h 3 (sourceIndex 718))
  · exact (row247_link w).symm.trans (h 3 (sourceIndex 719))
  · exact (row248_link w).symm.trans (h 3 (sourceIndex 720))
  · exact (row249_link w).symm.trans (h 3 (sourceIndex 721))
  · exact (row250_link w).symm.trans (h 3 (sourceIndex 722))
  · exact (row251_link w).symm.trans (h 3 (sourceIndex 723))
  · exact (row252_link w).symm.trans (h 3 (sourceIndex 724))
  · exact (row253_link w).symm.trans (h 3 (sourceIndex 726))
  · exact (row254_link w).symm.trans (h 3 (sourceIndex 727))
  · exact (row255_link w).symm.trans (h 3 (sourceIndex 728))
  · exact (row256_link w).symm.trans (h 3 (sourceIndex 729))
  · exact (row257_link w).symm.trans (h 3 (sourceIndex 730))
  · exact (row258_link w).symm.trans (h 3 (sourceIndex 731))
  · exact (row259_link w).symm.trans (h 3 (sourceIndex 732))
  · exact (row260_link w).symm.trans (h 3 (sourceIndex 733))
  · exact (row261_link w).symm.trans (h 3 (sourceIndex 734))
  · exact (row262_link w).symm.trans (h 3 (sourceIndex 738))
  · exact (row263_link w).symm.trans (h 3 (sourceIndex 740))

#print axioms jetBlock_kernel_zero
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeOffWeightPoleExclusion -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelFiniteShift QuantitativeArithmeticUniversalPoleVector
open SmallLevelTwentyOneKnownWords (jetScale jetScale_ne_zero)

/-- The finite four-layer certificate excludes the exceptional tuple at
every weight above two, retaining arbitrary pole orders at lower points. -/
theorem PoleSystem.exceptional_pole_impossible {m : ℕ} (hm : 2 ≤ m) {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε)
    (hE : phase m ε= -1) (hu : badParameter f 3=1) (hv : badParameter f 11= -1)
    (ha : badParameter f 2= -5/2)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) ((m:ℂ)+1) < 0)
    (hshift : ∀ r : ℕ,0 < r → ∀ j,0 ≤ meromorphicOrderAt (fun z => S.G z j) ((m:ℂ)+1+r)) :
    False := by
  obtain ⟨v,hv0,hvk⟩ := continued_block_kernel S.B S.G (fullLeadingMatrix m f ε)
    (fullShiftMatrix m f ε) S.E ((m:ℂ)+1) 3 S.meromorphic
    (fun z i j => fullLeadingMatrix_analytic m f ε i j z)
    (fun n z i j => fullShiftMatrix_analytic m f ε n i j z)
    S.error hshift S.continued_rows hpole
  let e : (Fin 4×Fin 66) ≃ Fin 264 := finProdFinEquiv
  let u : Fin 264→ℂ := fun i => v (e.symm i)/jetScale (1-(m:ℂ)) (e.symm i).1
  have hrepr : scaledJetStack m u=v := by
    funext b
    simp only [scaledJetStack,u,e,Equiv.symm_apply_apply]
    field_simp [jetScale_ne_zero m hm b.1]
  have huk (n : Fin 4) (r : GridSource) : jetBlockRow n r u=0 := by
    have hh := hvk (n,r)
    rw [← hrepr,actual_jetBlockRow m hf ε hε hE hu hv ha] at hh
    exact (mul_eq_zero.mp hh).resolve_left (jetScale_ne_zero m hm n)
  have hu0 := jetBlock_kernel_zero u huk
  apply hv0
  rw [← hrepr,hu0]
  funext b
  simp [scaledJetStack]

/-- For an odd-third pole in the right half-plane, the top of its integer
grid pole chain must be the weight point. Every off-weight case is removed
using only the original Euler-product and Fricke hypotheses. -/
theorem PoleSystem.third_chain_top_at_weight {m : ℕ} (hm : 0 < m) {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε) (s : ℂ) (n : ℕ)
    (hs : (m:ℝ) ≤ s.re)
    (hpole : meromorphicOrderAt (fun z => S.G z 22-S.G z 44) s < 0)
    (htop : ∃ j,meromorphicOrderAt (fun z => S.G z j) (s+n) < 0)
    (hshift : ∀ r : ℕ,0 < r → ∀ j,0 ≤ meromorphicOrderAt (fun z => S.G z j) (s+n+r)) :
    s+n=((2*m:ℕ):ℂ) := by
  by_contra hweight
  obtain ⟨hn,he,hu,ha⟩ := S.original_pole_chain hm hf hε s n hs hpole htop hshift hweight
  subst n
  simp only [Nat.cast_zero,add_zero] at htop hshift hweight
  rw [he] at htop hshift hweight
  obtain ⟨v,hv⟩ := exists_leading_vector S.G ((m:ℂ)+1)
    (fun j => (S.meromorphic j _).meromorphicAt) htop
  have hk := S.rightmost_leading_kernel _ v hv hshift
  obtain ⟨hE,hv11⟩ := exceptional_kernel_signs m hf ε hε v hv.1 hk hu ha
  have hm2 : 2 ≤ m := by
    have hm1 : m≠1 := by intro hm1; subst m; norm_num at hweight
    omega
  exact S.exceptional_pole_impossible hm2 hf hε hE hu hv11 ha htop hshift

#print axioms PoleSystem.third_chain_top_at_weight
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeRightmost -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Filter SmallLevelAdditive
open scoped Topology

theorem PoleSystem.right_halfplane {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) (S : PoleSystem m f ε) :
    ∃ B : ℝ,∀ j z,B<z.re → AnalyticAt ℂ (fun w => S.G w j) z := by
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  refine ⟨max B S.B,?_⟩
  intro j z hz
  have ha : AnalyticAt ℂ (fun w => gridVector (2*m) f w j) z :=
    (hB (((j:ℕ):ℝ)/66) z (lt_of_le_of_lt (le_max_left _ _) hz)).1
  have he : (fun w => gridVector (2*m) f w j)=ᶠ[𝓝 z] (fun w => S.G w j) := by
    have hne : ∀ᶠ w : ℂ in 𝓝 z,S.B<w.re :=
      (isOpen_lt continuous_const continuous_re).mem_nhds
        (lt_of_le_of_lt (le_max_right _ _) hz)
    filter_upwards [hne] with w hw
    exact (congrFun (S.agreement w hw) j).symm
  exact ha.congr he

theorem PoleSystem.third_pole_has_rightmost {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) (S : PoleSystem m f ε) (s : ℂ)
    (hpole : meromorphicOrderAt (fun z => S.G z 22-S.G z 44) s < 0) :
    ∃ n : ℕ,(∃ j,meromorphicOrderAt (fun z => S.G z j) (s+n) < 0) ∧
      ∀ r : ℕ,0 < r → ∀ j,0 ≤ meromorphicOrderAt (fun z => S.G z j) (s+n+r) := by
  obtain ⟨B,hB⟩ := S.right_halfplane hf
  have hp : ∃ j,meromorphicOrderAt (fun z => S.G z j) s < 0 := by
    by_contra! h
    have h22 := (S.meromorphic 22 s).meromorphicOrderAt_nonneg_iff_analyticAt.mp (h 22)
    have h44 := (S.meromorphic 44 s).meromorphicOrderAt_nonneg_iff_analyticAt.mp (h 44)
    exact (not_lt_of_ge (h22.sub h44).meromorphicOrderAt_nonneg) hpole
  exact SmallLevelPoleGrid.rightmost_pole (fun j z => S.G z j) hp B hB

#print axioms PoleSystem.third_pole_has_rightmost
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeChiThreeReflection -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeChiThree
open Complex SmallLevelAdditive QuantitativeArithmeticSmallLevelThirtyThreeCenters
open FinitenessOriginalFourier
def scaleTwo (k : ℕ) (s : ℂ) : ℂ := (2:ℂ)^((k:ℂ)-2*s)
def reflectionMultiplier (k : ℕ) (ε s : ℂ) : ℂ := ε*(Real.sqrt 99:ℂ)^((k:ℂ)-2*s)

theorem scaleTwo_ne_zero (k : ℕ) (s : ℂ) : scaleTwo k s≠0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

theorem scaleTwo_eq (k : ℕ) (s : ℂ) : scaleTwo k s=(2:ℂ)^k*(4:ℂ)^(-s) := by
  have h4 : (4:ℂ)^(-s)=(2:ℂ)^(-2*s) := by
    have h := Complex.natCast_cpow_natCast_mul 2 2 (-s)
    norm_num only [Nat.cast_ofNat] at h
    rw [← h]
    congr 1
    ring
  rw [h4,← Complex.cpow_natCast,← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
  unfold scaleTwo
  congr 1
  ring

theorem scaleTwo_product (k : ℕ) (s : ℂ) : scaleTwo k s*scaleTwo k ((k:ℂ)-s)=1 := by
  unfold scaleTwo
  rw [← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
  rw [show (k:ℂ)-2*s+((k:ℂ)-2*((k:ℂ)-s))=0 by ring,Complex.cpow_zero]

theorem center_conductor_factor (k : ℕ) (s : ℂ) :
    (Real.sqrt 396:ℂ)^((k:ℂ)-2*s)=scaleTwo k s*(Real.sqrt 99:ℂ)^((k:ℂ)-2*s) := by
  have hs : Real.sqrt 396=2*Real.sqrt 99 := by
    rw [show (396:ℝ)=4*99 by norm_num,Real.sqrt_mul (by norm_num)]
    norm_num
  rw [hs,Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤2) (Real.sqrt_nonneg _) _

theorem reflectionMultiplier_entire (k : ℕ) (ε : ℂ) : Differentiable ℂ (reflectionMultiplier k ε) := by
  have hn : (Real.sqrt 99:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold reflectionMultiplier
  simp_rw [Complex.cpow_def_of_ne_zero hn]
  fun_prop

theorem reflectionMultiplier_ne_zero (k : ℕ) {ε : ℂ} (hε : ε≠0) (s : ℂ) :
    reflectionMultiplier k ε s≠0 := by
  apply mul_ne_zero hε
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by norm_num)).ne'))

theorem reflectionMultiplier_even (m : ℕ) (ε s : ℂ) :
    reflectionMultiplier (2*m) ε s=ε*(99:ℂ)^((m:ℂ)-s) := by
  have hn : (Real.sqrt 99:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs : (Real.sqrt 99:ℂ)*(Real.sqrt 99:ℂ)=99 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ)≤99)
  have hp := Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg 99) (Real.sqrt_nonneg 99) ((m:ℂ)-s)
  rw [hs] at hp
  unfold reflectionMultiplier
  rw [show ((2*m:ℕ):ℂ)-2*s=((m:ℂ)-s)+((m:ℂ)-s) by push_cast; ring,
    Complex.cpow_add _ _ hn,← hp]


theorem denominator_reflection (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    denominator k f s=scaleTwo k s*denominator k f ((k:ℂ)-s) := by
  have hp : scaleTwo k s*(2:ℂ)^(-((k:ℂ)-s))=(2:ℂ)^(-s) := by
    unfold scaleTwo
    rw [← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    ring
  have hq := scaleTwo_product k s
  unfold denominator
  rw [← scaleTwo_eq,← scaleTwo_eq]
  linear_combination -hq - (((2:ℝ)^(((k:ℝ)+1)/2):ℝ):ℂ)*f 2*hp

theorem original_numerator_reflection (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∀ s : ℂ,
      numerator m f s=scaleTwo (2*m) s*reflectionMultiplier (2*m) ε s*
        numerator m f ((2*m:ℕ)-s) := by
  obtain ⟨χ,hχ,hc⟩ := original_centers_entire m hm hf
  let ε : ℂ := χ/I^(2*m)
  have hε : ε=1 ∨ ε= -1 := by
    have hi : I^(2*m)=(-1:ℂ)^m := by rw [pow_mul,I_sq]
    rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hχ with rfl|rfl <;> simp [ε,hi,h]
  have hp (positive : Bool) (s : ℂ) :=
    QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection
      (by decide : 0<396)
      (coefficients (fullCoefficients f (2*m)) (center positive)) ε (hc positive).2.2 s
  refine ⟨ε,hε,fun s => ?_⟩
  have hpos := hp true s
  have hneg := hp false s
  norm_num only [center,Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat] at hpos hneg
  rw [center_conductor_factor] at hpos hneg
  unfold numerator reflectionMultiplier
  linear_combination hpos-hneg

theorem original_quadratic_functional_equation (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ (ε : ℂ) (bound : ℝ) (G : ℂ → ℂ), (ε=1 ∨ ε= -1) ∧
      (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) ∧
      (∀ s, G s=ε*(99:ℂ)^((m:ℂ)-s)*G ((2*m:ℕ)-s)) ∧
      (∀ s, denominator (2*m) f s≠0 → AnalyticAt ℂ G s) := by
  obtain ⟨ε,hε,hN⟩ := original_numerator_reflection m hm hf
  obtain ⟨B,G,hG,hagree,hpole,hgerm⟩ := original_continuation m hm hf
  have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
  have hraw (s : ℂ) : numerator m f s/denominator (2*m) f s=
      reflectionMultiplier (2*m) ε s*(numerator m f ((2*m:ℕ)-s)/denominator (2*m) f ((2*m:ℕ)-s)) := by
    rw [hN s,denominator_reflection (2*m) f s,mul_assoc,
      mul_div_mul_left _ _ (scaleTwo_ne_zero (2*m) s)]
    ring
  have hfe := QuantitativeArithmeticQuadraticTwistReflection.normal_form_reflection
    (fun s => numerator m f s/denominator (2*m) f s) G
    (reflectionMultiplier (2*m) ε) ((2*m:ℕ):ℂ) hG
    (fun s => (reflectionMultiplier_entire (2*m) ε).analyticAt s)
    (reflectionMultiplier_ne_zero (2*m) hε0) hgerm hraw
  refine ⟨ε,B,G,hε,hG,hagree,?_,hpole⟩
  intro s
  simpa only [reflectionMultiplier_even] using hfe s
#print axioms original_quadratic_functional_equation
end QuantitativeArithmeticSmallLevelThirtyThreeChiThree
end
end

/-! ## ThirtyThreeFinitePoleLocations -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Filter SmallLevelAdditive
open scoped Topology

/-- Every pole in the right half-plane lies in a finite real integer
segment. There are no continuation, rightmost-pole, or algebraic-locus
assumptions beyond the original solution and its constructed grid. -/
theorem PoleSystem.third_pole_finite {m : ℕ} (hm : 0 < m) {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε) (s : ℂ)
    (hs : (m:ℝ) ≤ s.re)
    (hpole : meromorphicOrderAt (fun z => S.G z 22-S.G z 44) s < 0) :
    ∃ n : ℕ,n ≤ m ∧ s=((2*m:ℕ):ℂ)-n := by
  obtain ⟨n,htop,hshift⟩ := S.third_pole_has_rightmost hf s hpole
  have he := S.third_chain_top_at_weight hm hf hε s n hs hpole htop hshift
  refine ⟨n,?_,?_⟩
  · have hre := congrArg Complex.re he
    norm_num [Complex.add_re,Complex.mul_re] at hre
    exact_mod_cast (show (n:ℝ) ≤ m by linarith)
  · linear_combination he

/-- Identify the reflected quadratic continuation with the actual odd
third difference in any original pole system. -/
theorem PoleSystem.quadratic_reflection {m : ℕ} (hm : 0 < m) {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) (S : PoleSystem m f ε) :
    ∃ (ω : ℂ) (H : ℂ→ℂ),(ω=1 ∨ ω= -1) ∧
      (∀ s,MeromorphicNFAt H s) ∧
      (∀ s,H s=ω*(99:ℂ)^((m:ℂ)-s)*H (((2*m:ℕ):ℂ)-s)) ∧
      (∀ s,(fun z => S.G z 22-S.G z 44)=ᶠ[𝓝[≠] s] H) := by
  obtain ⟨ω,B,H,hω,hH,hagree,hfe,_⟩ :=
    QuantitativeArithmeticSmallLevelThirtyThreeChiThree.original_quadratic_functional_equation m hm hf
  refine ⟨ω,H,hω,hH,hfe,?_⟩
  intro s
  apply SmallLevelContinuation.halfplane_germ_identity (s.re-1) (max S.B B) _ _ _ s (by linarith)
  · intro z _
    exact (S.meromorphic 22 z).meromorphicAt.sub (S.meromorphic 44 z).meromorphicAt
  · intro z _
    exact (hH z).meromorphicAt
  · intro z hz
    change S.G z (gridIndex 22)-S.G z (gridIndex (-22))=H z
    rw [S.agreement z (lt_of_le_of_lt (le_max_left _ _) hz),
      hagree z (lt_of_le_of_lt (le_max_right _ _) hz),gridVector_index,gridVector_index]
    norm_num [SmallLevelAdditive.grid]

/-- The functional equation reflects the finite right-hand list. Thus
the actual quadratic twist has poles only at integer points between zero
and the weight; this theorem does not yet assert their removability. -/
theorem PoleSystem.quadratic_finite_poles {m : ℕ} (hm : 0 < m) {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε) :
    ∃ (ω : ℂ) (H : ℂ→ℂ),(ω=1 ∨ ω= -1) ∧
      (∀ s,MeromorphicNFAt H s) ∧
      (∀ s,H s=ω*(99:ℂ)^((m:ℂ)-s)*H (((2*m:ℕ):ℂ)-s)) ∧
      (∀ s,(fun z => S.G z 22-S.G z 44)=ᶠ[𝓝[≠] s] H) ∧
      (∀ s,meromorphicOrderAt H s < 0 → ∃ j : ℕ,j ≤ 2*m ∧ s=(j:ℂ)) := by
  obtain ⟨ω,H,hω,hH,hfe,hgrid⟩ := S.quadratic_reflection hm hf
  refine ⟨ω,H,hω,hH,hfe,hgrid,?_⟩
  intro s hp
  have hright (z : ℂ) (hz : (m:ℝ) ≤ z.re) (hpz : meromorphicOrderAt H z < 0) :
      ∃ n : ℕ,n ≤ m ∧ z=((2*m:ℕ):ℂ)-n := by
    apply S.third_pole_finite hm hf hε z hz
    rwa [meromorphicOrderAt_congr (hgrid z)]
  by_cases hs : (m:ℝ) ≤ s.re
  · obtain ⟨n,hn,he⟩ := hright s hs hp
    refine ⟨2*m-n,Nat.sub_le _ _,?_⟩
    rw [Nat.cast_sub (by omega : n ≤ 2*m)]
    exact he
  · have ht : (m:ℝ) ≤ (((2*m:ℕ):ℂ)-s).re := by
      norm_num [Complex.sub_re,Complex.mul_re]
      linarith
    have hpt : meromorphicOrderAt H (((2*m:ℕ):ℂ)-s) < 0 := by
      by_contra! hnp
      have hat := (hH _).meromorphicOrderAt_nonneg_iff_analyticAt.mp hnp
      have hac := hat.comp (f:=fun z : ℂ => ((2*m:ℕ):ℂ)-z)
        (analyticAt_const.sub analyticAt_id)
      have hcoef : AnalyticAt ℂ (fun z : ℂ => ω*(99:ℂ)^((m:ℂ)-z)) s := by
        fun_prop (disch := norm_num)
      have has : AnalyticAt ℂ H s := by
        convert hcoef.mul hac using 1
        funext z
        exact hfe z
      exact (not_lt_of_ge has.meromorphicOrderAt_nonneg) hp
    obtain ⟨n,hn,he⟩ := hright _ ht hpt
    refine ⟨n,by omega,?_⟩
    linear_combination -he

#print axioms PoleSystem.quadratic_finite_poles
#print axioms PoleSystem.third_pole_finite
#print axioms PoleSystem.quadratic_reflection
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreePoleMinor -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelPrimeRates QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelThirtyThreeLaurent QuantitativeArithmeticUniversalPoleVector

theorem kernel_minor_zero (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    {ε : ℂ} (hε : ε=1 ∨ ε= -1) (s : ℂ) (w : Fin 66→ℂ)
    (hw0 : w≠0) (hw : fullLeadingMatrix m f ε s *ᵥ w=0) :
    QuantitativeArithmeticSmallLevelThirtyThreeMinor.determinant
      (parameter 2 m s) (badParameter f 3*parameter 3 m s) (badParameter f 2)=0 := by
  have hu := badParameter_three_sign hf.toEulerData
  have hv := badParameter_eleven_sign hf.toEulerData
  by_contra hd
  apply hw0
  rw [fullLeadingMatrix_mulVec] at hw
  have hsource (i : Fin 775) :
      eval (parameter 2 m s) (parameter 3 m s) (parameter 11 m s)
        (phase m ε) (badParameter f 2) (badParameter f 3) (badParameter f 11)
        (fun j => w (gridIndex (j:ℤ))) (sourceRows i)=0 := by
    rw [physical_source_match m hf ε s hε w i,hw]
    rfl
  have hh := all_signs_kernel _ _ _ _ _ _ _ _
    (parameter_ne_zero 2 m (by decide) s) (parameter_ne_zero 3 m (by decide) s)
    (parameter_ne_zero 11 m (by decide) s) (grid_physical_sign m hε) hu hv hd hsource
  funext j
  simpa only [gridIndex_fin,Pi.zero_apply] using hh j.val j.isLt

/-- Every rightmost pole of the original grid lies on the explicit minor divisor. -/
theorem PoleSystem.rightmost_minor_zero {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε) (s : ℂ)
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) s < 0)
    (hshift : ∀ n : ℕ,0 < n → ∀ j,0 ≤ meromorphicOrderAt (fun z => S.G z j) (s+n)) :
    QuantitativeArithmeticSmallLevelThirtyThreeMinor.determinant
      (parameter 2 m s) (badParameter f 3*parameter 3 m s) (badParameter f 2)=0 := by
  obtain ⟨v,hv⟩ := exists_leading_vector S.G s
    (fun j => (S.meromorphic j s).meromorphicAt) hpole
  exact kernel_minor_zero m hf hε s v hv.1 (S.rightmost_leading_kernel s v hv hshift)

#print axioms PoleSystem.rightmost_minor_zero
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreePositiveGapExclusion -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelPrimeRates QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyThreeWeightChain

theorem parameter_at_weight (p m : ℕ) :
    parameter p m ((2*m:ℕ):ℂ)=(p:ℂ)^m := by
  rw [parameter,show ((2*m:ℕ):ℂ)-(m:ℂ)=(m:ℂ) by push_cast; ring,Complex.cpow_natCast]

theorem parameter_below_weight (p m n : ℕ) (hn : n ≤ m) :
    parameter p m (((2*m:ℕ):ℂ)-n)=(p:ℂ)^(m-n) := by
  have he : ((2*m:ℕ):ℂ)-(n:ℂ)-(m:ℂ)=((m-n:ℕ):ℂ) := by
    rw [Nat.cast_sub hn]
    push_cast
    ring
  rw [parameter,he,Complex.cpow_natCast]

theorem PoleSystem.positive_gap_impossible {m : ℕ} (hm : 0 < m) {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε) (n : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (hpole : meromorphicOrderAt (fun z => S.G z 22-S.G z 44) (((2*m:ℕ):ℂ)-n) < 0)
    (htop : ∃ j,meromorphicOrderAt (fun z => S.G z j) ((2*m:ℕ):ℂ) < 0)
    (hshift : ∀ r : ℕ,0 < r → ∀ j,0 ≤ meromorphicOrderAt (fun z => S.G z j) (((2*m:ℕ):ℂ)+r)) :
    False := by
  have hd := original_third_pole_denominator m hm hf S.B S.G S.meromorphic S.agreement _ hpole
  change parameter 2 m (((2*m:ℕ):ℂ)-n)+(parameter 2 m (((2*m:ℕ):ℂ)-n))⁻¹+badParameter f 2=0 at hd
  rw [parameter_below_weight 2 m n hnm] at hd
  have hminor := S.rightmost_minor_zero hf hε _ htop hshift
  simp only [parameter_at_weight,Nat.cast_ofNat] at hminor
  have hc : m=1 ∧ n=1 ∧ badParameter f 2= -2 := by
    rcases badParameter_three_sign hf.toEulerData with hu|hu
    · apply positive_gap_parameters m n hn hnm 1 (Or.inl rfl) (badParameter f 2) hd
      simpa only [hu,Complex.ofReal_one] using hminor
    · apply positive_gap_parameters m n hn hnm (-1) (Or.inr rfl) (badParameter f 2) hd
      simpa only [hu,Complex.ofReal_neg,Complex.ofReal_one] using hminor
  rcases hc with ⟨rfl,_,ha⟩
  obtain ⟨v,hv⟩ := exists_leading_vector S.G 2
    (fun j => (S.meromorphic j 2).meromorphicAt) htop
  exact hv.1 (weight_two_minus_two_kernel f hf ε hε ha v
    (S.rightmost_leading_kernel 2 v hv hshift))

/-- Only the weight itself can be a right-half-plane pole of the odd
third twist; all positive gaps in its grid pole chain are impossible. -/
theorem PoleSystem.third_pole_is_weight {m : ℕ} (hm : 0 < m) {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε) (s : ℂ)
    (hs : (m:ℝ) ≤ s.re)
    (hpole : meromorphicOrderAt (fun z => S.G z 22-S.G z 44) s < 0) :
    s=((2*m:ℕ):ℂ) := by
  obtain ⟨n,htop,hshift⟩ := S.third_pole_has_rightmost hf s hpole
  have he := S.third_chain_top_at_weight hm hf hε s n hs hpole htop hshift
  have hnm : n ≤ m := by
    have hre := congrArg Complex.re he
    norm_num [Complex.add_re,Complex.mul_re] at hre
    exact_mod_cast (show (n:ℝ) ≤ m by linarith)
  by_cases hn : n=0
  · simpa only [hn,Nat.cast_zero,add_zero] using he
  · have hs' : s=((2*m:ℕ):ℂ)-n := by linear_combination he
    rw [he] at htop hshift
    rw [hs'] at hpole
    exact False.elim (S.positive_gap_impossible hm hf hε n (by omega) hnm hpole htop hshift)

#print axioms PoleSystem.third_pole_is_weight
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeOriginalWeightKernel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelPrimeRates QuantitativeArithmeticSevenLaurentRows
open QuantitativeArithmeticSmallLevelThirtyThreeLaurent QuantitativeArithmeticUniversalPoleVector

theorem weight_kernel_zero (m : ℕ) (hm : 2 ≤ m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (v : Fin 66→ℂ)
    (hv : fullLeadingMatrix m f ε ((2*m:ℕ):ℂ)*ᵥv=0)
    (ha : badParameter f 2*(2:ℂ)^m= -(4:ℂ)^m-1) : v=0 := by
  have hb (σ : ℚ) (hσ : (σ:ℂ)=phase m ε*badParameter f 3*badParameter f 11) :=
    original_base_kernel m hf ε ((2*m:ℕ):ℂ) hε σ hσ v hv
  simp only [parameter_at_weight,Nat.cast_ofNat] at hb
  have hu := badParameter_three_sign hf.toEulerData
  have hw := badParameter_eleven_sign hf.toEulerData
  have hend (he : ∀ i : ℕ,i<66 → v (gridIndex (i:ℤ))=0) : v=0 := by
    funext i
    simpa only [gridIndex_fin,Pi.zero_apply] using he i.val i.isLt
  rcases scaled_phase_sign m hf hε with hσ|hσ
  · have hs : ((1:ℚ):ℂ)=phase m ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
    exact hend (QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.weight_kernel_zero
      m hm _ _ _ hu hw ha _ (hb 1 hs))
  · have hs : (((-1):ℚ):ℂ)=phase m ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
    exact hend (QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.weight_kernel_zero
      m hm _ _ _ hu hw ha _ (hb (-1) hs))

/-- For weight at least four the odd third twist has no poles in the
closed right half-plane. All equations come from the original input. -/
theorem PoleSystem.third_right_regular {m : ℕ} (hm : 2 ≤ m) {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε) (s : ℂ)
    (hs : (m:ℝ) ≤ s.re) :
    0 ≤ meromorphicOrderAt (fun z => S.G z 22-S.G z 44) s := by
  by_contra hn
  have hpole := lt_of_not_ge hn
  have hpos : 0 < m := by omega
  have he := S.third_pole_is_weight hpos hf hε s hs hpole
  obtain ⟨n,htop,hshift⟩ := S.third_pole_has_rightmost hf s hpole
  have he' := S.third_chain_top_at_weight hpos hf hε s n hs hpole htop hshift
  rw [he'] at htop hshift
  rw [he] at hpole
  have hd := original_third_pole_denominator m hpos hf S.B S.G S.meromorphic S.agreement _ hpole
  change parameter 2 m ((2*m:ℕ):ℂ)+(parameter 2 m ((2*m:ℕ):ℂ))⁻¹+badParameter f 2=0 at hd
  rw [parameter_at_weight] at hd
  have hx : (2:ℂ)^m≠0 := pow_ne_zero _ (by norm_num)
  have hx2 : ((2:ℂ)^m)^2=(4:ℂ)^m := by
    rw [← pow_mul,Nat.mul_comm m 2,pow_mul]
    norm_num
  have ha : badParameter f 2*(2:ℂ)^m= -(4:ℂ)^m-1 := by
    have hi : ((2:ℂ)^m)⁻¹*(2:ℂ)^m=1 := inv_mul_cancel₀ hx
    linear_combination (2:ℂ)^m*hd-hi-hx2
  obtain ⟨v,hv⟩ := exists_leading_vector S.G ((2*m:ℕ):ℂ)
    (fun j => (S.meromorphic j _).meromorphicAt) htop
  exact hv.1 (weight_kernel_zero m hm hf ε hε v
    (S.rightmost_leading_kernel _ v hv hshift) ha)

#print axioms PoleSystem.third_right_regular
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeRegularizedTaylor -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelPrimeRates SmallLevelFiniteShift
-- Elementary scale identities from Min's regularized weight-two construction.
-- Kept separate from its level-21 matrix computations.
def weightOneChooseQuot (n : Fin 4) (z : ℂ) : ℂ :=
  (![0,1,(z-3)/2,(z-3)*(z-4)/6] : Fin 4 → ℂ) n

theorem weightOneChoose_factor (n : Fin 4) (hn : n≠0) (z : ℂ) :
    Ring.choose (z-2) n.val=(z-2)*weightOneChooseQuot n z := by
  fin_cases n <;> norm_num at hn
  all_goals
    norm_num [weightOneChooseQuot,Ring.choose_eq_smul,← Polynomial.aeval_eq_smeval,
      descPochhammer_succ_right] <;> ring_nf <;> norm_num [map_ofNat] <;> ring

def regularizedJetScale (n : Fin 4) : ℂ := (![1,I,-I^2,2*I^3] : Fin 4 → ℂ) n

theorem regularizedJetScale_ne_zero (n : Fin 4) : regularizedJetScale n≠0 := by
  fin_cases n <;> norm_num [regularizedJetScale,I_sq,I_ne_zero,pow_succ]

theorem regularizedJetScale_top (n : Fin 4) (hn : n≠0) :
    I^n.val*weightOneChooseQuot n 2=regularizedJetScale n/(n.val.factorial:ℂ) := by
  fin_cases n <;> norm_num at hn
  all_goals norm_num [weightOneChooseQuot,regularizedJetScale,I_sq,pow_succ] <;> ring

theorem regularizedJetScale_lower (n : Fin 4) (a : ℕ) (ha : a<n.val-1) :
    I^(a+1)*Ring.choose (-((n.val:ℂ))+((a+1:ℕ):ℂ)) (a+1)*
      regularizedJetScale (lowerIndex n a)=regularizedJetScale n/((a+1).factorial:ℂ) := by
  have ha2 : a≤1 := by omega
  interval_cases a <;> fin_cases n <;> norm_num at ha
  all_goals norm_num [regularizedJetScale,lowerIndex,Ring.choose_eq_smul,
    ← Polynomial.aeval_eq_smeval,descPochhammer_succ_right,I_sq,pow_succ] <;> ring


def weightOneTaylorQuot (f : ℕ→ℂ) (ε : ℂ) (n : Fin 4) (z : ℂ) :
    Matrix GridSource (Fin 66) ℂ := fun r j =>
  I^n.val*weightOneChooseQuot n z*(rowDerivative r:ℂ)^n.val*
    (rowHead (Pi.single j 1) r-fullLeadingMatrix 1 f ε (z-n.val) r j)

theorem weightOneTaylorQuot_analytic (f : ℕ→ℂ) (ε : ℂ) (n : Fin 4)
    (s : ℂ) (r : GridSource) (j : Fin 66) :
    AnalyticAt ℂ (fun z => weightOneTaylorQuot f ε n z r j) s := by
  have hq : AnalyticAt ℂ (fun z => weightOneChooseQuot n z) s := by
    fin_cases n
    · exact analyticAt_const
    · exact analyticAt_const
    · exact (analyticAt_id.sub analyticAt_const).div_const
    · exact ((analyticAt_id.sub analyticAt_const).mul
        (analyticAt_id.sub analyticAt_const)).div_const
  exact ((analyticAt_const.mul hq).mul analyticAt_const).mul
    (analyticAt_const.sub ((fullLeadingMatrix_analytic 1 f ε r j (s-n.val)).comp
      (f:=fun z : ℂ => z-(n.val:ℂ)) (analyticAt_id.sub analyticAt_const)))

theorem weightOneTaylorQuot_factor (f : ℕ→ℂ) (ε : ℂ) (n : Fin 4) (hn : n≠0)
    (z : ℂ) (r : GridSource) (j : Fin 66) :
    fullShiftMatrix 1 f ε (n.val-1) (z-n.val) r j=(z-2)*weightOneTaylorQuot f ε n z r j := by
  have hnval : n.val-1+1=n.val := by have := Fin.pos_iff_ne_zero.mpr hn; omega
  change gridShiftRows 1 f ε (n.val-1) (z-n.val) (Pi.single j 1) r=_
  rw [higher_shift_from_leading,hnval]
  have he : z-(n.val:ℂ)+(n.val:ℂ)-((2*1:ℕ):ℂ)=z-2 := by norm_num
  rw [he,weightOneChoose_factor n hn]
  change _=(z-2)*(I^n.val*weightOneChooseQuot n z*(rowDerivative r:ℂ)^n.val*
    (rowHead (Pi.single j 1) r-gridLeadingRows 1 f ε (z-n.val) (Pi.single j 1) r))
  ring

theorem rowHead_matrix (w : Fin 66→ℂ) (r : GridSource) :
    (∑ j,rowHead (Pi.single j 1) r*w j)=rowHead w r := by
  cases r with
  | word i => simp [rowHead,Pi.single_apply]
  | taylor i =>
    simp only [rowHead,gridSample]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [Pi.single_apply]
  | entire i => simp [rowHead]
  | hecke i => simp [rowHead]
  | infinity i => simp [rowHead]

theorem weightOneTaylorQuot_apply (f : ℕ→ℂ) (ε : ℂ) (n : Fin 4) (z : ℂ)
    (r : GridSource) (w : Fin 66→ℂ) :
    (∑ j,weightOneTaylorQuot f ε n z r j*w j)=
      I^n.val*weightOneChooseQuot n z*(rowDerivative r:ℂ)^n.val*
        (rowHead w r-gridLeadingRows 1 f ε (z-n.val) w r) := by
  simp only [weightOneTaylorQuot,mul_assoc,← Finset.mul_sum,sub_mul,Finset.sum_sub_distrib]
  rw [rowHead_matrix]
  rw [← fullLeadingMatrix_mulVec 1 f ε (z-n.val) w]
  rfl

#print axioms weightOneTaylorQuot_factor
#print axioms weightOneTaylorQuot_apply
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeRegularizedBlockModel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelPrimeRates SmallLevelFiniteShift

def regularizedScaledStack (w : Fin 264→ℂ) (b : Fin 4×Fin 66) : ℂ :=
  regularizedJetScale b.1*w (finProdFinEquiv b)

theorem rowHead_scale (c : ℂ) (w : Fin 66→ℂ) (r : GridSource) :
    rowHead (fun j => c*w j) r=c*rowHead w r := by
  cases r <;> simp [rowHead,gridSample,Finset.mul_sum]

theorem actual_regularizedBlockRow {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 2 f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hE : phase 1 ε= -1)
    (hu : badParameter f 3=1) (hv : badParameter f 11= -1)
    (ha : badParameter f 2= -5/2) (n : Fin 4) (r : GridSource) (w : Fin 264→ℂ) :
    (∑ b,regularizedBlock 3 (fullLeadingMatrix 1 f ε) (fullShiftMatrix 1 f ε)
      (weightOneTaylorQuot f ε) 2 (n,r) b*regularizedScaledStack w b)=
        regularizedJetScale n*jetBlockRow n r w := by
  have hp (n : Fin 4) (v : Fin 66→ℂ) :
      gridLeadingRows 1 f ε (2-n.val) v r=jetLead n v r := by
    simpa only [Nat.cast_one,one_add_one_eq_two] using physical_jetLead 1 hf ε hε hE hu hv ha n v r
  have hl (n : Fin 4) (c : ℂ) (v : Fin 66→ℂ) :
      (∑ j,fullLeadingMatrix 1 f ε (2-n.val) r j*(c*v j))=c*jetLead n v r := by
    change (fullLeadingMatrix 1 f ε (2-n.val)*ᵥ(fun j => c*v j)) r=_
    rw [fullLeadingMatrix_mulVec,leading_rows_scale,hp]
  have hc (n : Fin 4) (a : ℕ) (c : ℂ) (v : Fin 66→ℂ) :
      (∑ j,fullShiftMatrix 1 f ε a (2-n.val) r j*(c*v j))=
        c*(I^(a+1)*Ring.choose (-(n.val:ℂ)+((a+1:ℕ):ℂ)) (a+1)*
          (rowDerivative r:ℂ)^(a+1)*(rowHead v r-jetLead n v r)) := by
    change (fullShiftMatrix 1 f ε a (2-n.val)*ᵥ(fun j => c*v j)) r=_
    rw [fullShiftMatrix_mulVec,shift_rows_scale,higher_shift_from_leading,hp]
    rw [show (2:ℂ)-(n.val:ℂ)+((a+1:ℕ):ℂ)-((2*1:ℕ):ℂ)=
      -(n.val:ℂ)+((a+1:ℕ):ℂ) by push_cast; ring]
  have hq (n : Fin 4) (c : ℂ) (v : Fin 66→ℂ) :
      (∑ j,weightOneTaylorQuot f ε n 2 r j*(c*v j))=
        c*(I^n.val*weightOneChooseQuot n 2*(rowDerivative r:ℂ)^n.val*
          (rowHead v r-jetLead n v r)) := by
    rw [weightOneTaylorQuot_apply,rowHead_scale,leading_rows_scale,hp]
    ring
  rw [regularizedBlock_apply]
  simp only [regularizedScaledStack]
  have hl0 (c : ℂ) (v : Fin 66→ℂ) :
      (∑ j,fullLeadingMatrix 1 f ε 2 r j*(c*v j))=c*jetLead 0 v r := by
    simpa only [Fin.val_zero,Nat.cast_zero,sub_zero] using hl 0 c v
  simp only [hl,hl0,hc,hq]
  have hslice (n : Fin 4) : jetSlice w n=(fun j => w (finProdFinEquiv (n,j))) := rfl
  fin_cases n <;>
    norm_num [jetBlockRow,jetSlice,regularizedJetScale,weightOneChooseQuot,
      Finset.sum_range_succ,lowerIndex,Ring.choose_eq_smul,← Polynomial.aeval_eq_smeval,
      descPochhammer_succ_right,I_sq,pow_succ]
  all_goals simp only [hslice]
  all_goals ring_nf
  all_goals norm_num [I_sq]
  all_goals ring

#print axioms actual_regularizedBlockRow
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeWeightTwoPoleOrder -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelFiniteShift QuantitativeArithmeticAnalyticGerm

/-- Even in the exceptional weight-two case the full original grid has
at most simple poles at the rightmost weight point. -/
theorem PoleSystem.exceptional_weight_two_order {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 2 f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem 1 f ε)
    (hE : phase 1 ε= -1) (hu : badParameter f 3=1) (hv : badParameter f 11= -1)
    (ha : badParameter f 2= -5/2)
    (hshift : ∀ r : ℕ,0 < r → ∀ j,0 ≤ meromorphicOrderAt (fun z => S.G z j) (2+r)) :
    ∀ j,(-1:WithTop ℤ) ≤ meromorphicOrderAt (fun z => S.G z j) 2 := by
  intro j
  apply (regularized_order_nonneg_iff (S.meromorphic j 2).meromorphicAt).mp
  by_contra h
  have hpole : ∃ j,meromorphicOrderAt (fun z => (z-2)*S.G z j) 2 < 0 :=
    ⟨j,lt_of_not_ge h⟩
  obtain ⟨v,hv0,hvk⟩ := regularized_block_kernel S.B S.G (fullLeadingMatrix 1 f ε)
    (fullShiftMatrix 1 f ε) S.E 2 3 (weightOneTaylorQuot f ε) S.meromorphic
    (fun z i j => fullLeadingMatrix_analytic 1 f ε i j z)
    (fun n z i j => fullShiftMatrix_analytic 1 f ε n i j z)
    (fun n i j => weightOneTaylorQuot_analytic f ε n 2 i j)
    (weightOneTaylorQuot_factor f ε) S.error hshift S.continued_rows hpole
  let e : (Fin 4×Fin 66) ≃ Fin 264 := finProdFinEquiv
  let u : Fin 264→ℂ := fun i => v (e.symm i)/regularizedJetScale (e.symm i).1
  have hrepr : regularizedScaledStack u=v := by
    funext b
    simp only [regularizedScaledStack,u,e,Equiv.symm_apply_apply]
    field_simp [regularizedJetScale_ne_zero b.1]
  have huk (n : Fin 4) (r : GridSource) : jetBlockRow n r u=0 := by
    have hh := hvk (n,r)
    rw [← hrepr,actual_regularizedBlockRow hf ε hε hE hu hv ha] at hh
    exact (mul_eq_zero.mp hh).resolve_left (regularizedJetScale_ne_zero n)
  have hu0 := jetBlock_kernel_zero u huk
  apply hv0
  rw [← hrepr,hu0]
  funext b
  simp [regularizedScaledStack]

#print axioms PoleSystem.exceptional_weight_two_order
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeLowerMinorEvaluation -/
section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
open QuantitativeArithmeticSevenLaurentRows

theorem minor13_expansion (X Y Z A : ℂ) :
    eval X Y Z 1 A 1 1 (fun _ => 1) minor13=
    (-2/1:ℂ)*A^1 + (-1/2:ℂ)*A^2 + (1/1:ℂ)*A^3 + (1/1:ℂ)*Z^1*A^1 + (-1/2:ℂ)*Z^1*A^2 + (2/1:ℂ)*Y^1*A^1 + (-1/1:ℂ)*Y^1*A^2 + (-1/1:ℂ)*Y^1*A^3 + (1/2:ℂ)*Y^1*Z^1*A^2 + (1/1:ℂ)*Y^2*A^1 + (1/1:ℂ)*Y^2*A^2 + (1/2:ℂ)*Y^3*A^2 + (-2/1:ℂ)*X^1 + (5/2:ℂ)*X^1*A^2 + (1/1:ℂ)*X^1*Z^1 + (-1/1:ℂ)*X^1*Z^1*A^1 + (2/1:ℂ)*X^1*Y^1 + (-1/1:ℂ)*X^1*Y^1*A^1 + (1/2:ℂ)*X^1*Y^1*A^2 + (1/1:ℂ)*X^1*Y^2 + (1/2:ℂ)*X^2 + (-1/2:ℂ)*X^2*Z^1 + (2/1:ℂ)*X^2*Y^1*A^1 + (-1/2:ℂ)*X^2*Y^1*Z^1 + (-1/1:ℂ)*X^2*Y^2 + (1/1:ℂ)*X^2*Y^2*A^1 + (-1/2:ℂ)*X^2*Y^3 + (-3/2:ℂ)*X^3 + (1/1:ℂ)*X^3*A^1 + (1/2:ℂ)*X^3*Y^1 + (1/1:ℂ)*X^3*Y^2 + (1/1:ℂ)*X^4 := by
  norm_num [minor13,eval,monomial]
  ring

theorem minor13_at_zero : eval (1/4) (1/3) (-1/11) 1 (-5/4) 1 1 (fun _ => 1) minor13=(49/6336:ℂ) := by
  rw [minor13_expansion]
  ring

#print axioms minor13_at_zero
end QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
end
end

/-! ## ThirtyThreeWeightTwoLowerKernel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeLaurent

theorem lower_one_kernel (w : ℕ→ℂ)
    (hb : ∀ j,eval 1 1 (-1) 1 (-5/2) 1 1 w (baseRows 1 j)=0) :
    ∀ j : ℕ,j<66 → w j=0 := by
  have hx : 1≠(0:ℂ) := by norm_num
  have hy : 1≠(0:ℂ) := by norm_num
  have hz : (-1)≠(0:ℂ) := by norm_num
  by_cases hn : w 18=0 ∧ w 42=0
  · exact kernel_free_zero _ _ _ _ w hx hy hz hb hn.1 hn.2
  · have hn' : w 18≠0 ∨ w 42≠0 := by tauto
    have hr := reduced_rows_zero _ _ _ _ w hx hy hz hb
    have he := weight_minor_zero _ _ _ _ w hx hy hz hn' hr
    norm_num [minor13,eval,monomial] at he

theorem lower_zero_kernel (w : ℕ→ℂ)
    (hb : ∀ j,eval (1/2:ℂ) (1/3:ℂ) (-1/11:ℂ) 1 (-5/2) 1 1 w (baseRows 1 j)=0) :
    ∀ j : ℕ,j<66 → w j=0 := by
  have hx : (1/2:ℂ)≠(0:ℂ) := by norm_num
  have hy : (1/3:ℂ)≠(0:ℂ) := by norm_num
  have hz : (-1/11:ℂ)≠(0:ℂ) := by norm_num
  by_cases hn : w 18=0 ∧ w 42=0
  · exact kernel_free_zero _ _ _ _ w hx hy hz hb hn.1 hn.2
  · have hn' : w 18≠0 ∨ w 42≠0 := by tauto
    have hr := reduced_rows_zero _ _ _ _ w hx hy hz hb
    have he := weight_minor_zero _ _ _ _ w hx hy hz hn' hr
    have he' : eval (1/4) (1/3) (-1/11) 1 (-5/4) 1 1 (fun _ => 1) minor13=0 := by
      convert he using 1
      norm_num
    rw [minor13_at_zero] at he'
    norm_num at he'
end QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelPrimeRates QuantitativeArithmeticSmallLevelThirtyThreeLaurent

theorem weight_two_lower_kernel {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 2 f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hE : phase 1 ε= -1)
    (hu : badParameter f 3=1) (hv : badParameter f 11= -1)
    (ha : badParameter f 2= -5/2) (s : ℂ) (hs : s=1 ∨ s=0)
    (v : Fin 66→ℂ) (hk : fullLeadingMatrix 1 f ε s*ᵥv=0) : v=0 := by
  have hσ : ((1:ℚ):ℂ)=phase 1 ε*badParameter f 3*badParameter f 11 := by rw [hE,hu,hv]; norm_num
  have hb := original_base_kernel 1 hf ε s hε 1 hσ v hk
  have hend (he : ∀ i : ℕ,i<66 → v (gridIndex (i:ℤ))=0) : v=0 := by
    funext i
    simpa only [gridIndex_fin,Pi.zero_apply] using he i.val i.isLt
  rcases hs with rfl|rfl
  · simp only [parameter,Nat.cast_one,Nat.cast_ofNat,sub_self,Complex.cpow_zero,
      hu,hv,ha,mul_one] at hb
    exact hend (QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.lower_one_kernel _ hb)
  · simp only [parameter,Nat.cast_one,Nat.cast_ofNat,zero_sub,Complex.cpow_neg_one,
      hu,hv,ha,one_mul,neg_one_mul,← one_div,← neg_div] at hb
    exact hend (QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.lower_zero_kernel _ hb)

#print axioms weight_two_lower_kernel
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeRegularTail -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix Filter SmallLevelFiniteShift QuantitativeArithmeticUniversalPoleVector
open scoped Topology

theorem fullShiftMatrix_zero_at_weight (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (n : ℕ) (s : ℂ) (hs : s+((n:ℂ)+1)=((2*m:ℕ):ℂ)) (r : GridSource) (j : Fin 66) :
    fullShiftMatrix m f ε n s r j=0 := by
  change gridShiftRows m f ε n s (Pi.single j 1) r=0
  rw [higher_shift_from_leading]
  have he : s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=0 := by
    simpa only [Nat.cast_add,Nat.cast_one] using sub_eq_zero.mpr hs
  rw [he,Ring.choose_zero_succ,mul_zero,zero_mul,zero_mul]

/-- A simple upper pole at the weight contributes an analytic germ to
all lower Taylor equations, because their coefficients vanish there. -/
theorem PoleSystem.regular_leading_kernel {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ) (v : Fin 66→ℂ)
    (hv : IsLeadingVector S.G x v)
    (hshift : ∀ n : ℕ,0<n → x+n≠((2*m:ℕ):ℂ) → ∀ j,
      0≤meromorphicOrderAt (fun z => S.G z j) (x+n))
    (hk : ∀ j,(-1:WithTop ℤ)≤meromorphicOrderAt (fun z => S.G z j) ((2*m:ℕ):ℂ)) :
    fullLeadingMatrix m f ε x*ᵥv=0 := by
  have htail (a : ℕ) (r : GridSource) (j : Fin 66) :=
    allowed_simple_pole_tail (fullShiftMatrix m f ε) ((2*m:ℕ):ℂ)
      (fun n z i j => fullShiftMatrix_analytic m f ε n i j z)
      (fullShiftMatrix_zero_at_weight m f ε) S.G S.meromorphic x 0 hshift hk
      a (Nat.zero_le a) r j
  simp only [Nat.cast_zero,sub_zero] at htail
  obtain ⟨R,hR,he⟩ := continued_regular_tail S.B S.G (fullLeadingMatrix m f ε)
    (fullShiftMatrix m f ε) S.E x 0 S.error (fun a _ r j => htail a r j) S.continued_rows
  simp only [Finset.range_zero,Finset.sum_empty,add_zero] at he
  funext r
  exact hv.2 (fun z j => fullLeadingMatrix m f ε z r j) (fun z => R z r)
    (fun j => fullLeadingMatrix_analytic m f ε r j x) (hR r) (he r)

#print axioms PoleSystem.regular_leading_kernel
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeWeightTwoLowerRegular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix QuantitativeArithmeticUniversalPoleVector

/-- The simple possible pole at two cancels out of the Taylor tails.
The injective leading systems at one and zero then force regularity there. -/
theorem PoleSystem.weight_two_lower_regular {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 2 f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem 1 f ε)
    (hE : phase 1 ε= -1) (hu : badParameter f 3=1) (hv : badParameter f 11= -1)
    (ha : badParameter f 2= -5/2)
    (hshift : ∀ r : ℕ,0<r → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (2+r))
    (hk : ∀ j,(-1:WithTop ℤ)≤meromorphicOrderAt (fun z => S.G z j) 2) :
    (∀ j,0≤meromorphicOrderAt (fun z => S.G z j) 1) ∧
      (∀ j,0≤meromorphicOrderAt (fun z => S.G z j) 0) := by
  have hnat (n : ℕ) (hn : 3≤n) (j : Fin 66) :
      0≤meromorphicOrderAt (fun z => S.G z j) (n:ℂ) := by
    have he : (2:ℂ)+((n-2:ℕ):ℂ)=(n:ℂ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    simpa only [he] using hshift (n-2) (by omega) j
  have hregular (x : ℂ) (hx : x=1 ∨ x=0)
      (hs : ∀ n : ℕ,0<n → x+n≠2 → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n)) :
      ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) x := by
    intro j
    by_contra! hj
    obtain ⟨v,hv0⟩ := exists_leading_vector S.G x
      (fun i => (S.meromorphic i x).meromorphicAt) ⟨j,hj⟩
    have hker := S.regular_leading_kernel x v hv0 (by simpa only [Nat.mul_one,Nat.cast_ofNat] using hs)
      (by simpa only [Nat.mul_one,Nat.cast_ofNat] using hk)
    exact hv0.1 (weight_two_lower_kernel hf ε hε hE hu hv ha x hx v hker)
  have h1 : ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) 1 := by
    apply hregular 1 (Or.inl rfl)
    intro n hn hne j
    have hn1 : n≠1 := by intro h; subst n; norm_num at hne
    simpa only [Nat.cast_add,Nat.cast_one,add_comm] using hnat (n+1) (by omega) j
  refine ⟨h1,?_⟩
  apply hregular 0 (Or.inr rfl)
  intro n hn hne j
  simp only [zero_add] at hne ⊢
  by_cases hn1 : n=1
  · simpa only [hn1,Nat.cast_one] using h1 j
  · have hn2 : n≠2 := by intro h; subst n; norm_num at hne
    exact hnat n (by omega) j

#print axioms PoleSystem.weight_two_lower_regular
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeWeightTwoSigns -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeLaurent

theorem negative_three_weight_two_kernel (v : ℂ) (hv : v=1 ∨ v= -1) (w : ℕ→ℂ)
    (hb : ∀ j,eval 2 (-3) (v*11) 1 (-5/2) 1 1 w (baseRows (-1) j)=0) :
    ∀ j : ℕ,j<66 → w j=0 := by
  have hx : (2:ℂ)≠0 := by norm_num
  have hy : (-3:ℂ)≠0 := by norm_num
  have hz : v*11≠0 := by rcases hv with rfl|rfl <;> norm_num
  by_cases hn : w 18=0 ∧ w 42=0
  · exact kernel_free_zero _ _ _ _ w hx hy hz hb hn.1 hn.2
  · have hn' : w 18≠0 ∨ w 42≠0 := by tauto
    have hr := reduced_rows_zero _ _ _ _ w hx hy hz hb
    have he := weight_minor_zero _ _ _ _ w hx hy hz hn' hr
    exfalso
    rcases hv with rfl|rfl <;> norm_num [minor16,eval,monomial] at he
end QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination
namespace QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
open QuantitativeArithmeticSevenLaurentRows QuantitativeArithmeticSmallLevelThirtyThreeLaurent

theorem negative_three_weight_two_kernel (v : ℂ) (hv : v=1 ∨ v= -1) (w : ℕ→ℂ)
    (hb : ∀ j,eval 2 (-3) (v*11) 1 (-5/2) 1 1 w (baseRows 1 j)=0) :
    ∀ j : ℕ,j<66 → w j=0 := by
  have hx : (2:ℂ)≠0 := by norm_num
  have hy : (-3:ℂ)≠0 := by norm_num
  have hz : v*11≠0 := by rcases hv with rfl|rfl <;> norm_num
  by_cases hn : w 18=0 ∧ w 42=0
  · exact kernel_free_zero _ _ _ _ w hx hy hz hb hn.1 hn.2
  · have hn' : w 18≠0 ∨ w 42≠0 := by tauto
    have hr := reduced_rows_zero _ _ _ _ w hx hy hz hb
    have he := weight_minor_zero _ _ _ _ w hx hy hz hn' hr
    exfalso
    rcases hv with rfl|rfl <;> norm_num [minor13,eval,monomial] at he
end QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix SmallLevelPrimeRates
open QuantitativeArithmeticSmallLevelThirtyThreeLaurent

theorem weight_two_kernel_signs {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 2 f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (v : Fin 66→ℂ) (hv0 : v≠0)
    (hv : fullLeadingMatrix 1 f ε 2*ᵥv=0)
    (ha : badParameter f 2= -5/2) :
    phase 1 ε= -1 ∧ badParameter f 3=1 ∧ badParameter f 11= -1 := by
  have hu : badParameter f 3=1 := by
    rcases badParameter_three_sign hf.toEulerData with hu|hu
    · exact hu
    · exfalso
      have hp (p : ℕ) : parameter p 1 2=(p:ℂ) := by
        rw [parameter,Nat.cast_one,show (2:ℂ)-1=1 by norm_num,Complex.cpow_one]
      have hb (σ : ℚ) (hσ : (σ:ℂ)=phase 1 ε*badParameter f 3*badParameter f 11) :=
        original_base_kernel 1 hf ε 2 hε σ hσ v hv
      simp only [hp,hu,ha,neg_one_mul,Nat.cast_ofNat] at hb
      have hend (he : ∀ i : ℕ,i<66 → v (gridIndex (i:ℤ))=0) : False := by
        apply hv0
        funext i
        simpa only [gridIndex_fin,Pi.zero_apply] using he i.val i.isLt
      rcases scaled_phase_sign 1 hf hε with hσ|hσ
      · have hs : ((1:ℚ):ℂ)=phase 1 ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
        exact hend (QuantitativeArithmeticSmallLevelThirtyThreePlusElimination.negative_three_weight_two_kernel
          _ (badParameter_eleven_sign hf.toEulerData) _ (hb 1 (by simpa only [hu] using hs)))
      · have hs : (((-1):ℚ):ℂ)=phase 1 ε*badParameter f 3*badParameter f 11 := by simpa using hσ.symm
        exact hend (QuantitativeArithmeticSmallLevelThirtyThreeMinusElimination.negative_three_weight_two_kernel
          _ (badParameter_eleven_sign hf.toEulerData) _ (hb (-1) (by simpa only [hu] using hs)))
  have he := exceptional_kernel_signs 1 hf ε hε v hv0 (by simpa only [Nat.cast_one,one_add_one_eq_two] using hv) hu ha
  exact ⟨he.1,hu,he.2⟩

#print axioms weight_two_kernel_signs
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeChiThreeWeightTwoRegular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Matrix Filter SmallLevelPrimeRates QuantitativeArithmeticUniversalPoleVector
open scoped Topology

/-- The only possible weight-two pole is simple, but its reflection at zero
is regular by the lower Taylor equations. This removes the final case. -/
theorem PoleSystem.third_right_regular_weight_two {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 2 f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem 1 f ε) (s : ℂ)
    (hs : 1≤s.re) : 0≤meromorphicOrderAt (fun z => S.G z 22-S.G z 44) s := by
  by_contra hn
  have hpole := lt_of_not_ge hn
  have he := S.third_pole_is_weight (by decide) hf hε s (by simpa using hs) hpole
  obtain ⟨n,htop,hshift⟩ := S.third_pole_has_rightmost hf s hpole
  have he' := S.third_chain_top_at_weight (by decide) hf hε s n (by simpa using hs) hpole htop hshift
  have hs2 : s=2 := by simpa only [Nat.mul_one,Nat.cast_ofNat] using he
  have ht2 : s+(n:ℂ)=2 := by simpa only [Nat.mul_one,Nat.cast_ofNat] using he'
  rw [ht2] at htop hshift
  rw [hs2] at hpole
  have hd := original_third_pole_denominator 1 (by decide) hf S.B S.G S.meromorphic S.agreement 2 hpole
  change parameter 2 1 2+(parameter 2 1 2)⁻¹+badParameter f 2=0 at hd
  have hp : parameter 2 1 2=2 := by
    simpa only [Nat.mul_one,Nat.cast_ofNat,pow_one] using parameter_at_weight 2 1
  rw [hp] at hd
  have ha : badParameter f 2= -5/2 := by linear_combination hd
  obtain ⟨v,hv⟩ := exists_leading_vector S.G 2
    (fun j => (S.meromorphic j 2).meromorphicAt) htop
  obtain ⟨hE,hu,hv11⟩ := weight_two_kernel_signs hf ε hε v hv.1
    (S.rightmost_leading_kernel 2 v hv hshift) ha
  have horder := S.exceptional_weight_two_order hf hε hE hu hv11 ha hshift
  have hzero := (S.weight_two_lower_regular hf hε hE hu hv11 ha hshift horder).2
  obtain ⟨ω,H,hω,hH,hfe,hgrid⟩ := S.quadratic_reflection (by decide) hf
  have hH0 : AnalyticAt ℂ H 0 := by
    apply (hH 0).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [← meromorphicOrderAt_congr (hgrid 0)]
    exact (((S.meromorphic 22 0).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hzero 22)).sub
      ((S.meromorphic 44 0).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hzero 44))).meromorphicOrderAt_nonneg
  have hat : AnalyticAt ℂ H ((2:ℂ)-2) := by simpa using hH0
  have hac := hat.comp (f:=fun z : ℂ => 2-z) (analyticAt_const.sub analyticAt_id)
  have hcoef : AnalyticAt ℂ (fun z : ℂ => ω*(99:ℂ)^(1-z)) 2 := by
    fun_prop (disch := norm_num)
  have hH2 : AnalyticAt ℂ H 2 := by
    convert hcoef.mul hac using 1
    funext z
    simpa only [Nat.mul_one,Nat.cast_one,Nat.cast_ofNat,Pi.mul_apply,Function.comp_apply] using hfe z
  rw [meromorphicOrderAt_congr (hgrid 2)] at hpole
  exact (not_lt_of_ge hH2.meromorphicOrderAt_nonneg) hpole

#print axioms PoleSystem.third_right_regular_weight_two
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeChiThreeEntire -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
open Complex Filter SmallLevelAdditive
open scoped Topology

/-- Original quadratic continuation is entire in every positive even weight. No separately postulated continuation or pole constraints are used. -/
theorem PoleSystem.quadratic_entire {m : ℕ} (hm : 0 < m) {f : ℕ→ℂ} {ε : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (S : PoleSystem m f ε) :
    ∃ (ω : ℂ) (H : ℂ→ℂ),(ω=1 ∨ ω= -1) ∧
      Differentiable ℂ H ∧
      (∀ s,H s=ω*(99:ℂ)^((m:ℂ)-s)*H (((2*m:ℕ):ℂ)-s)) ∧
      (∀ s,(fun z => S.G z 22-S.G z 44)=ᶠ[𝓝[≠] s] H) := by
  obtain ⟨ω,H,hω,hH,hfe,hgrid⟩ := S.quadratic_reflection (by omega) hf
  refine ⟨ω,H,hω,?_,hfe,hgrid⟩
  have hregular (z : ℂ) (hz : (m:ℝ) ≤ z.re) :
      0≤meromorphicOrderAt (fun t => S.G t 22-S.G t 44) z := by
    by_cases hm1 : m=1
    · subst m
      exact S.third_right_regular_weight_two hf hε z (by simpa only [Nat.cast_one] using hz)
    · exact S.third_right_regular (by omega) hf hε z hz
  have hright (z : ℂ) (hz : (m:ℝ) ≤ z.re) : AnalyticAt ℂ H z := by
    apply (hH z).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [← meromorphicOrderAt_congr (hgrid z)]
    exact hregular z hz
  intro s
  apply AnalyticAt.differentiableAt
  by_cases hs : (m:ℝ) ≤ s.re
  · exact hright s hs
  · have ht : (m:ℝ) ≤ (((2*m:ℕ):ℂ)-s).re := by
      norm_num [Complex.sub_re,Complex.mul_re]
      linarith
    have hac := (hright _ ht).comp (f:=fun z : ℂ => ((2*m:ℕ):ℂ)-z)
      (analyticAt_const.sub analyticAt_id)
    have hcoef : AnalyticAt ℂ (fun z : ℂ => ω*(99:ℂ)^((m:ℂ)-z)) s := by
      fun_prop (disch := norm_num)
    convert hcoef.mul hac using 1
    funext z
    exact hfe z

theorem original_quadratic_entire (m : ℕ) (hm : 0 < m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ (ω : ℂ) (B : ℝ) (H : ℂ→ℂ),(ω=1 ∨ ω= -1) ∧
      Differentiable ℂ H ∧
      (∀ s,H s=ω*(99:ℂ)^((m:ℂ)-s)*H (((2*m:ℕ):ℂ)-s)) ∧
      (∀ s,B<s.re → H s=original (2*m) f (1/3) s-original (2*m) f (-1/3) s) := by
  obtain ⟨ε,hε,⟨S⟩⟩ := original_pole_system m (by omega) hf
  obtain ⟨ω,H,hω,hH,hfe,hgrid⟩ := S.quadratic_entire hm hf hε
  obtain ⟨ω',B,H',hω',hH',hagree,hfe',hden⟩ :=
    QuantitativeArithmeticSmallLevelThirtyThreeChiThree.original_quadratic_functional_equation m (by omega) hf
  -- Identify the entire normal form with the original quadratic continuation.
  have he : H=H' := by
    apply funext
    intro s
    apply (((hH.analyticAt s).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hH' s)).mp ?_).eq_of_nhds
    apply (hgrid s).symm.trans
    apply SmallLevelContinuation.halfplane_germ_identity (s.re-1) (max S.B B) _ _ _ s (by linarith)
    · intro z _
      exact (S.meromorphic 22 z).meromorphicAt.sub (S.meromorphic 44 z).meromorphicAt
    · intro z _
      exact (hH' z).meromorphicAt
    · intro z hz
      change S.G z (gridIndex 22)-S.G z (gridIndex (-22))=H' z
      rw [S.agreement z (lt_of_le_of_lt (le_max_left _ _) hz),
        hagree z (lt_of_le_of_lt (le_max_right _ _) hz),gridVector_index,gridVector_index]
      norm_num [SmallLevelAdditive.grid]
  refine ⟨ω,B,H,hω,hH,hfe,?_⟩
  intro s hs
  rw [he]
  simpa only [neg_div] using hagree s hs

#print axioms PoleSystem.quadratic_entire
#print axioms original_quadratic_entire
end QuantitativeArithmeticSmallLevelThirtyThreeKnownWords
end
end

/-! ## ThirtyThreeChiThreeFiniteOrder -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeChiThree
open Complex Filter SmallLevelAdditive SmallLevelTaylor QuantitativeArithmeticSmallLevelThirtyThreeCenters
open scoped Topology

theorem original_numerator_bound (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    FinitenessFiniteOrder.Bound (numerator m f) := by
  obtain ⟨χ,_hχ,hcent⟩ := original_centers_entire m hm hf
  exact FinitenessFiniteOrderClosure.sub
    (SmallLevelMellinUnscale.finite_order_at_one (by decide : 0<396) _ (hcent true).2.1)
    (SmallLevelMellinUnscale.finite_order_at_one (by decide : 0<396) _ (hcent false).2.1)

theorem denominator_quadratic (m : ℕ) (f : ℕ→ℂ) (s : ℂ) :
    denominator (2*m) f s=1+((Real.sqrt 2:ℂ)*f 2)*(2:ℂ)^((m:ℂ)-s)+
      ((2:ℂ)^((m:ℂ)-s))^2 := by
  have hfirst := SmallLevelTaylor.hecke_first_scalar (by decide : 0<2) m (f 2) s
  have hsecond := SmallLevelTaylor.hecke_second_scalar (by decide : 0<2) m s
  unfold denominator
  norm_num only [Nat.cast_mul,Nat.cast_ofNat,show (2:ℂ)^2=4 by norm_num] at hfirst hsecond ⊢
  rw [hfirst,hsecond]

theorem uniform_product_identity {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    {G : ℂ→ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s,B<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) :
    ∀ s,denominator (2*m) f s*G s=numerator m f s := by
  obtain ⟨C,hC⟩ := original_hecke_identity m hf
  have hleft := (denominator_entire (2*m) f).mul hG
  have hright := original_numerator_entire m hm hf
  intro s
  have he : (fun z => denominator (2*m) f z*G z)=ᶠ[𝓝[≠] s] numerator m f := by
    apply SmallLevelContinuation.halfplane_germ_identity (s.re-1) (max B C)
    · exact fun z _ => (hleft.analyticAt z).meromorphicAt
    · exact fun z _ => (hright.analyticAt z).meromorphicAt
    · intro z hz
      dsimp only
      rw [hGF z (lt_of_le_of_lt (le_max_left _ _) hz)]
      exact (hC z (lt_of_le_of_lt (le_max_right _ _) hz)).symm
    · linarith
  exact (((hleft.analyticAt s).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hright.analyticAt s).meromorphicNFAt).mp he).eq_of_nhds

theorem uniform_finiteOrder {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    {G : ℂ→ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s,B<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) :
    FinitenessOriginalInput.FiniteOrder G := by
  apply SmallLevelQuadraticExponential.finiteOrder_of_quadratic
    ((Real.sqrt 2:ℂ)*f 2) (m:ℂ)
    (original_numerator_entire m hm hf).continuous
    (FinitenessInputBounds.bound_finiteOrder (original_numerator_bound m hm hf)) hG
  intro s
  rw [← denominator_quadratic]
  exact uniform_product_identity hm hf hG B hGF s

#print axioms uniform_finiteOrder
end QuantitativeArithmeticSmallLevelThirtyThreeChiThree
end
end

/-! ## ThirtyThreeCoherentCenters -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeCenters
open SmallLevelNormalized SmallLevelThirtyThree SmallLevelOriginal
  QuantitativeArithmeticTranslatedFricke Complex Filter Set MeasureTheory
  FinitenessPolynomialSeries FinitenessFourierConstruction Matrix UpperHalfPlane
open scoped Topology MatrixGroups ModularForm

/-- The two denominator-six centers have the root belonging to the fixed
original Fricke law, rather than independently chosen signs. -/
theorem coherent_centers_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 33 (2*m) f ε) :
    ∀ positive : Bool,Differentiable ℂ (centeredMellin m f positive) ∧
      FinitenessFiniteOrder.Bound (centeredMellin m f positive) ∧
      ∀ s : ℂ,centeredMellin m f positive s=
        (ε*FinitenessNormalizedTwistProduct.root 33 f 3)*
          centeredMellin m f positive ((2*m:ℕ)-s) := by
  obtain ⟨hχ,hF⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<33) m ε hε hlaw
  let χ : ℂ := ε*Complex.I^(2*m)
  let δ := FinitenessNormalizedTwistProduct.root 33 f 3
  have hδ : δ=1 ∨ δ= -1 := FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3
  have hχδ : χ*δ=1 ∨ χ*δ= -1 := by
    rcases hχ with h|h <;> rcases hδ with hd|hd <;> simp [χ,h,hd]
  have hcenter (positive : Bool) :
      (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center positive))
        ∣[((2*m:ℕ):ℤ)] fricke 396 (by decide)=
      (χ*δ) • (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center positive)) := by
    cases positive
    · exact translated_slash_eigen 33 396 (2*m) (by decide) (by decide) _ χ δ _ A A_det
        hF (SmallLevelSixEigen.thirty_three_A (by omega) hf) fricke_branch_neg
    · exact translated_slash_eigen 33 396 (2*m) (by decide) (by decide) _ χ δ _ B B_det
        hF (SmallLevelSixEigen.thirty_three_B (by omega) hf) fricke_branch_pos
  obtain ⟨τ,_,hg⟩ := hf.growth
  intro positive
  obtain ⟨hhol,hbound,hfe⟩ := translated_mellin_entire 396 (2*m) (by decide) (by omega) _
    (FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m))
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)) (center positive)
    (χ*δ) hχδ (hcenter positive)
  have he : χ*δ/(Complex.I^(2*m))=ε*δ := by
    dsimp only [χ]
    field_simp [Complex.I_ne_zero]
  exact ⟨hhol,hbound,by simpa only [he,centeredMellin,δ] using hfe⟩

#print axioms coherent_centers_entire
end QuantitativeArithmeticSmallLevelThirtyThreeCenters
end
end

/-! ## ThirtyThreeCoherentQuadraticLaws -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeChiThree
open Complex Filter SmallLevelAdditive QuantitativeArithmeticSmallLevelThirtyThreeCenters
open FinitenessOriginalFourier
open scoped Topology

theorem coherent_numerator_reflection (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 33 (2*m) f ε) (s : ℂ) :
    numerator m f s=scaleTwo (2*m) s*
      reflectionMultiplier (2*m) (ε*FinitenessNormalizedTwistProduct.root 33 f 3) s*
        numerator m f (((2*m:ℕ):ℂ)-s) := by
  have hc := coherent_centers_entire m hm hf ε hε hlaw
  have hp (positive : Bool) :=
    QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection
      (by decide : 0<396)
      (coefficients (fullCoefficients f (2*m)) (center positive))
      (ε*FinitenessNormalizedTwistProduct.root 33 f 3) (hc positive).2.2 s
  have hpos := hp true
  have hneg := hp false
  norm_num only [center,Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat] at hpos hneg
  rw [center_conductor_factor] at hpos hneg
  unfold numerator reflectionMultiplier
  linear_combination hpos-hneg

/-- The original odd third twist is entire of finite order and has the
same fixed root as the original Ramanujan-three transformation. -/
theorem original_coherent_quadratic_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 33 (2*m) f ε) :
    ∃ (B : ℝ) (G : ℂ→ℂ),Differentiable ℂ G ∧ FinitenessOriginalInput.FiniteOrder G ∧
      (∀ s,B<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) ∧
      ∀ s,G s=(ε*FinitenessNormalizedTwistProduct.root 33 f 3)*
        (99:ℂ)^((m:ℂ)-s)*G (((2*m:ℕ):ℂ)-s) := by
  obtain ⟨ω,BE,E,_hω,hE,_hEFE,hEF⟩ :=
    QuantitativeArithmeticSmallLevelThirtyThreeKnownWords.original_quadratic_entire m hm hf
  obtain ⟨B,G,hG,hGF,_hregular,hgerm⟩ := original_continuation m hm hf
  have hent : Differentiable ℂ G := by
    intro s
    apply AnalyticAt.differentiableAt
    exact SmallLevelSimplePoleTaylor.analyticAt_of_model
      (fun s => original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s)
      G E E B BE (s.re-1) s hG hGF
      (fun z _ => (hE.analyticAt z).meromorphicAt) (by simpa only [neg_div] using hEF)
      (by linarith) (hE.analyticAt s) Filter.EventuallyEq.rfl
  have hfinite := uniform_finiteOrder hm hf hent B hGF
  let η : ℂ := ε*FinitenessNormalizedTwistProduct.root 33 f 3
  have hη : η≠0 := by
    rcases hε with rfl|rfl <;>
      rcases FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3 with h|h <;> simp [η,h]
  have hraw (s : ℂ) : numerator m f s/denominator (2*m) f s=
      reflectionMultiplier (2*m) η s*
        (numerator m f (((2*m:ℕ):ℂ)-s)/denominator (2*m) f (((2*m:ℕ):ℂ)-s)) := by
    rw [coherent_numerator_reflection m hm hf ε hε hlaw s,denominator_reflection,mul_assoc,
      mul_div_mul_left _ _ (scaleTwo_ne_zero (2*m) s)]
    ring
  have he := QuantitativeArithmeticQuadraticTwistReflection.normal_form_reflection
    (fun s => numerator m f s/denominator (2*m) f s) G
    (reflectionMultiplier (2*m) η) (((2*m:ℕ):ℂ)) hG
    (fun s => (reflectionMultiplier_entire (2*m) η).analyticAt s)
    (reflectionMultiplier_ne_zero (2*m) hη) hgerm hraw
  refine ⟨B,G,hent,hfinite,hGF,?_⟩
  simpa only [reflectionMultiplier_even] using he

#print axioms original_coherent_quadratic_entire
end QuantitativeArithmeticSmallLevelThirtyThreeChiThree
end
end

/-! ## ThirtyThreeChiThreeFricke -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeChiThree
open Complex FinitenessOriginalFourier FinitenessFourierConstruction
open SmallLevelNormalized SmallLevelOriginal
open scoped ModularForm

def quadraticFourier (k : ℕ) (f : ℕ → ℂ) (z : ℂ) : ℂ :=
  fourier (fullCoefficients f k) (z+(1/3:ℝ))-
  fourier (fullCoefficients f k) (z+(-1/3:ℝ))

/-- The quadratic-three Fourier law, retaining the same sign as the
untwisted Fricke law. All analytic continuation is derived from original input. -/
theorem original_quadratic_fricke {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 33 (2*m) f ε ∧
      fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 33 (by decide)=
        (ε*I^(2*m)) • fourierFunction (2*m) f ∧
      ∀ z : ℂ, 0<z.im → quadraticFourier (2*m) f z=
        ((ε*FinitenessNormalizedTwistProduct.root 33 f 3)*I^(2*m))/(((Real.sqrt 99:ℂ)*z)^(2*m))*
          quadraticFourier (2*m) f (-1/((99:ℂ)*z)) := by
  obtain ⟨ε,hε,hlaw⟩ := QuantitativeArithmeticCoherentTaylor.original_coherent_law
    (by decide : 0<33) hf
  obtain ⟨_hχ,hW⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<33) m ε hε hlaw
  obtain ⟨B,G,hent,hfinite,hGF,hFE⟩ := original_coherent_quadratic_entire m hm hf ε hε hlaw
  obtain ⟨σ,_hσ,hgrowth⟩ := hf.growth
  refine ⟨ε,hε,hlaw,hW,?_⟩
  have h := QuantitativeArithmeticQuadraticTwistInversion.four_translate_fricke
    (k := 2*m) (ε := ε*FinitenessNormalizedTwistProduct.root 33 f 3) (B := B)
    (by decide : 0<99) hf.zero hgrowth (1/3) 0 (-1/3) 0 G hent hfinite
    (by
      intro s hs
      rw [hGF s hs]
      simp only [neg_div]
      ring)
    (by rcases hε with rfl|rfl <;>
      rcases FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3 with h|h <;>
      norm_num [h])
    (by
      have he : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
      simpa only [Nat.cast_ofNat,he] using hFE)
  intro z hz
  dsimp only at h
  unfold quadraticFourier
  convert h z hz using 1 <;> ring

#print axioms original_quadratic_fricke
end QuantitativeArithmeticSmallLevelThirtyThreeChiThree
end
end

/-! ## ThirtyThreeChiThreeIndividual -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeChiThree
open Complex FinitenessOriginalFourier FinitenessFourierConstruction

/-- The Ramanujan-three and quadratic-three equations separate into the
two individual additive equations without dividing by a Hecke eigenvalue. -/
theorem individual_laws {k : ℕ} {f : ℕ → ℂ} (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 33 k f ε)
    (hquad : ∀ z : ℂ, 0<z.im → quadraticFourier k f z=
      ((ε*FinitenessNormalizedTwistProduct.root 33 f 3)*I^k)/(((Real.sqrt 99:ℂ)*z)^k)*quadraticFourier k f (-1/((99:ℂ)*z))) :
    ∀ z : ℂ, 0<z.im →
      (fourier (fullCoefficients f k) (z+1/3)=
        ((ε*FinitenessNormalizedTwistProduct.root 33 f 3)*I^k)/(((Real.sqrt 99:ℂ)*z)^k)*
          fourier (fullCoefficients f k) (-1/((99:ℂ)*z)+1/3)) ∧
      (fourier (fullCoefficients f k) (z-1/3)=
        ((ε*FinitenessNormalizedTwistProduct.root 33 f 3)*I^k)/(((Real.sqrt 99:ℂ)*z)^k)*
          fourier (fullCoefficients f k) (-1/((99:ℂ)*z)-1/3)) := by
  intro z hz
  have hr := hlaw 3 (by decide) z hz
  rw [show Nat.lcm 33 (3^2)=99 by decide,
    SmallLevelThree.twist_three _ (periodic _),
    SmallLevelThree.twist_three _ (periodic _)] at hr
  rw [mul_comm (FinitenessNormalizedTwistProduct.root 33 f 3) ε] at hr
  norm_num only [Nat.cast_ofNat] at hr
  have hc := hquad z hz
  norm_num only [quadraticFourier,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_ofNat,Complex.ofReal_one] at hc
  simp only [sub_eq_add_neg] at hr hc ⊢
  constructor
  · linear_combination (hr+hc)/2
  · linear_combination (hr-hc)/2

#print axioms individual_laws
end QuantitativeArithmeticSmallLevelThirtyThreeChiThree
end
end

/-! ## ThirtyThreeChiThreeMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeChiThree
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

def Cplus : GL (Fin 2) ℝ := matrix (3/Real.sqrt 3) (-1/Real.sqrt 3)
    (-33/Real.sqrt 3) (12/Real.sqrt 3) (by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  field_simp [SmallLevelThirtyThree.sqrt_three_ne]
  nlinarith)

def Cminus : GL (Fin 2) ℝ := matrix (3/Real.sqrt 3) (1/Real.sqrt 3)
    (33/Real.sqrt 3) (12/Real.sqrt 3) (by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  field_simp [SmallLevelThirtyThree.sqrt_three_ne]
  nlinarith)

theorem Cplus_det : (GeneralLinearGroup.det Cplus:ℝ)=1 := matrix_det _ _ _ _ _
theorem Cminus_det : (GeneralLinearGroup.det Cminus:ℝ)=1 := matrix_det _ _ _ _ _

theorem sqrt_three_conductor : Real.sqrt 99=Real.sqrt 33*Real.sqrt 3 := by
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ)≤33)]
  norm_num

theorem plus_branch : fricke 33 (by decide)*Cplus*translation (1/3)=
    translation (1/3)*fricke 99 (by decide) := by
  have ht : (Real.sqrt 33)^2=33 := Real.sq_sqrt (by norm_num)
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 33≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Cplus,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two,sqrt_three_conductor] <;>
    field_simp [hn,SmallLevelThirtyThree.sqrt_three_ne] <;> norm_num [ht,hs]

theorem plus_conjugate : (fricke 33 (by decide))⁻¹*translation (1/3)*fricke 99 (by decide)*
    (translation (1/3))⁻¹=Cplus := by
  calc
    _=(fricke 33 (by decide))⁻¹*(translation (1/3)*fricke 99 (by decide))*(translation (1/3))⁻¹ := by group
    _=(fricke 33 (by decide))⁻¹*(fricke 33 (by decide)*Cplus*translation (1/3))*(translation (1/3))⁻¹ := by rw [plus_branch]
    _=_ := by group

theorem minus_branch : fricke 33 (by decide)*Cminus*translation (-1/3)=
    translation (-1/3)*fricke 99 (by decide) := by
  have ht : (Real.sqrt 33)^2=33 := Real.sq_sqrt (by norm_num)
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 33≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Cminus,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two,sqrt_three_conductor] <;>
    field_simp [hn,SmallLevelThirtyThree.sqrt_three_ne] <;> norm_num [ht,hs]

theorem minus_conjugate : (fricke 33 (by decide))⁻¹*translation (-1/3)*fricke 99 (by decide)*
    (translation (-1/3))⁻¹=Cminus := by
  calc
    _=(fricke 33 (by decide))⁻¹*(translation (-1/3)*fricke 99 (by decide))*(translation (-1/3))⁻¹ := by group
    _=(fricke 33 (by decide))⁻¹*(fricke 33 (by decide)*Cminus*translation (-1/3))*(translation (-1/3))⁻¹ := by rw [minus_branch]
    _=_ := by group

#print axioms plus_conjugate
#print axioms minus_conjugate
end QuantitativeArithmeticSmallLevelThirtyThreeChiThree
end
end

/-! ## ThirtyThreeChiThreeTransformations -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeChiThree
open Complex Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

/-- Original Euler/Fricke input forces both denominator-three matrices,
including the zero Hecke-eigenvalue cases. -/
theorem original_C_plus_minus {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Cplus=FinitenessNormalizedTwistProduct.root 33 f 3 • fourierFunction (2*m) f ∧
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Cminus=FinitenessNormalizedTwistProduct.root 33 f 3 • fourierFunction (2*m) f := by
  obtain ⟨ε,_hε,hlaw,_hW,hquad⟩ := original_quadratic_fricke hm hf
  have hF : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients f (2*m)) z=
      (ε*Complex.I^(2*m))/(((Real.sqrt 33:ℂ)*z)^(2*m))*
        fourier (fullCoefficients f (2*m)) (-1/((33:ℂ)*z)) := by
    intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  have hind := individual_laws ε hlaw hquad
  constructor
  · have h := QuantitativeArithmeticNormalizedIndividualFricke.single_eigen_of_fricke
      33 99 (2*m) (by decide) (by decide) (1/3) _ _ _ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3) hF
      (by
        intro z hz
        simpa only [Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_one,
          Complex.ofReal_ofNat,mul_assoc,mul_comm,mul_left_comm] using (hind z hz).1)
    rw [plus_conjugate] at h
    exact h
  · have h := QuantitativeArithmeticNormalizedIndividualFricke.single_eigen_of_fricke
      33 99 (2*m) (by decide) (by decide) (-1/3) _ _ _ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3) hF
      (by
        intro z hz
        simpa only [Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat,
          Complex.ofReal_one,sub_eq_add_neg,neg_div,mul_assoc,mul_comm,mul_left_comm] using (hind z hz).2)
    rw [minus_conjugate] at h
    exact h

#print axioms original_C_plus_minus
end QuantitativeArithmeticSmallLevelThirtyThreeChiThree
end
end

/-! ## ThirtyThreeGroupData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section

namespace QuantitativeArithmeticSmallLevelThirtyThreeGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

def kernel (i : Fin 19) : SL(2,ℤ) :=
  match i.val with
  | 0 => ⟨!![1,1;0,1],by decide⟩
  | 1 => ⟨!![2,-1;-33,17],by decide⟩
  | 2 => ⟨!![13,1;-66,-5],by decide⟩
  | 3 => ⟨!![23,2;264,23],by decide⟩
  | 4 => ⟨!![1,0;-33,1],by decide⟩
  | 5 => ⟨!![17,1;33,2],by decide⟩
  | 6 => ⟨!![59,5;165,14],by decide⟩
  | 7 => ⟨!![-1,0;0,-1],by decide⟩
  | 8 => ⟨!![35,3;198,17],by decide⟩
  | 9 => ⟨!![37,3;-99,-8],by decide⟩
  | 10 => ⟨!![34,3;-363,-32],by decide⟩
  | 11 => ⟨!![-64,-7;759,83],by decide⟩
  | 12 => ⟨!![14,-5;-165,59],by decide⟩
  | 13 => ⟨!![17,-3;-198,35],by decide⟩
  | 14 => ⟨!![-8,-3;99,37],by decide⟩
  | 15 => ⟨!![133,11;-1584,-131],by decide⟩
  | 16 => ⟨!![83,7;-759,-64],by decide⟩
  | 17 => ⟨!![-5,-1;66,13],by decide⟩
  | _ => ⟨!![23,-2;-264,23],by decide⟩

def letter : Fin 39 → SL(2,ℤ)
  | 0 => kernel 0
  | 1 => kernel 1
  | 2 => kernel 2
  | 3 => kernel 3
  | 4 => kernel 4
  | 5 => kernel 5
  | 6 => kernel 6
  | 7 => kernel 7
  | 8 => kernel 8
  | 9 => kernel 9
  | 10 => kernel 10
  | 11 => kernel 11
  | 12 => kernel 12
  | 13 => kernel 13
  | 14 => kernel 14
  | 15 => kernel 15
  | 16 => kernel 16
  | 17 => kernel 17
  | 18 => kernel 18
  | 19 => (kernel 0)⁻¹
  | 20 => (kernel 1)⁻¹
  | 21 => (kernel 2)⁻¹
  | 22 => (kernel 3)⁻¹
  | 23 => (kernel 4)⁻¹
  | 24 => (kernel 5)⁻¹
  | 25 => (kernel 6)⁻¹
  | 26 => (kernel 7)⁻¹
  | 27 => (kernel 8)⁻¹
  | 28 => (kernel 9)⁻¹
  | 29 => (kernel 10)⁻¹
  | 30 => (kernel 11)⁻¹
  | 31 => (kernel 12)⁻¹
  | 32 => (kernel 13)⁻¹
  | 33 => (kernel 14)⁻¹
  | 34 => (kernel 15)⁻¹
  | 35 => (kernel 16)⁻¹
  | 36 => (kernel 17)⁻¹
  | 37 => (kernel 18)⁻¹
  | _ => -1

def word (w : List (Fin 39)) : SL(2,ℤ) := (w.map letter).prod

theorem word_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 19, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (w : List (Fin 39)) : word w∈K := by
  have hl (i : Fin 39) : letter i∈K := by
    fin_cases i
    · exact hK 0
    · exact hK 1
    · exact hK 2
    · exact hK 3
    · exact hK 4
    · exact hK 5
    · exact hK 6
    · exact hK 7
    · exact hK 8
    · exact hK 9
    · exact hK 10
    · exact hK 11
    · exact hK 12
    · exact hK 13
    · exact hK 14
    · exact hK 15
    · exact hK 16
    · exact hK 17
    · exact hK 18
    · exact K.inv_mem (hK 0)
    · exact K.inv_mem (hK 1)
    · exact K.inv_mem (hK 2)
    · exact K.inv_mem (hK 3)
    · exact K.inv_mem (hK 4)
    · exact K.inv_mem (hK 5)
    · exact K.inv_mem (hK 6)
    · exact K.inv_mem (hK 7)
    · exact K.inv_mem (hK 8)
    · exact K.inv_mem (hK 9)
    · exact K.inv_mem (hK 10)
    · exact K.inv_mem (hK 11)
    · exact K.inv_mem (hK 12)
    · exact K.inv_mem (hK 13)
    · exact K.inv_mem (hK 14)
    · exact K.inv_mem (hK 15)
    · exact K.inv_mem (hK 16)
    · exact K.inv_mem (hK 17)
    · exact K.inv_mem (hK 18)
    · exact hZ
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hl i)

def rowClass (c d : ZMod 33) : ℕ :=
  (if c.val%3=0 then 3 else (d.val%3*([0,1,2] : List ℕ).getD (c.val%3) 0)%3)*12+
  (if c.val%11=0 then 11 else (d.val%11*([0,1,6,4,3,9,2,8,7,5,10] : List ℕ).getD (c.val%11) 0)%11)

def repRow (c d : ZMod 33) : SL(2,ℤ) :=
  match rowClass c d with
  | 0 => ⟨!![0,-1;1,0],by decide⟩
  | 13 => ⟨!![0,-1;1,1],by decide⟩
  | 34 => ⟨!![0,-1;1,-1],by decide⟩
  | 26 => ⟨!![0,-1;1,2],by decide⟩
  | 21 => ⟨!![0,-1;1,-2],by decide⟩
  | 17 => ⟨!![-1,0;2,-1],by decide⟩
  | 3 => ⟨!![0,-1;1,3],by decide⟩
  | 30 => ⟨!![-1,0;-2,-1],by decide⟩
  | 8 => ⟨!![0,-1;1,-3],by decide⟩
  | 4 => ⟨!![-1,1;2,-3],by decide⟩
  | 43 => ⟨!![-1,0;3,-1],by decide⟩
  | 16 => ⟨!![0,-1;1,4],by decide⟩
  | 7 => ⟨!![-1,-1;-2,-3],by decide⟩
  | 40 => ⟨!![-1,0;-3,-1],by decide⟩
  | 31 => ⟨!![0,-1;1,-4],by decide⟩
  | 44 => ⟨!![1,1;-3,-2],by decide⟩
  | 27 => ⟨!![-1,2;2,-5],by decide⟩
  | 42 => ⟨!![-1,1;3,-4],by decide⟩
  | 32 => ⟨!![-1,0;4,-1],by decide⟩
  | 29 => ⟨!![0,-1;1,5],by decide⟩
  | 39 => ⟨!![-1,1;-3,2],by decide⟩
  | 20 => ⟨!![-1,-2;-2,-5],by decide⟩
  | 41 => ⟨!![-1,-1;-3,-4],by decide⟩
  | 15 => ⟨!![-1,0;-4,-1],by decide⟩
  | 18 => ⟨!![0,-1;1,-5],by decide⟩
  | 45 => ⟨!![1,2;-3,-5],by decide⟩
  | 19 => ⟨!![2,1;-5,-2],by decide⟩
  | 14 => ⟨!![-1,3;2,-7],by decide⟩
  | 9 => ⟨!![1,1;-4,-3],by decide⟩
  | 6 => ⟨!![0,-1;1,6],by decide⟩
  | 38 => ⟨!![-1,2;-3,5],by decide⟩
  | 28 => ⟨!![-2,1;-5,2],by decide⟩
  | 33 => ⟨!![-1,-3;-2,-7],by decide⟩
  | 2 => ⟨!![-1,1;-4,3],by decide⟩
  | 5 => ⟨!![0,-1;1,-6],by decide⟩
  | 46 => ⟨!![1,3;-3,-8],by decide⟩
  | 1 => ⟨!![-1,4;2,-9],by decide⟩
  | 22 => ⟨!![1,2;-4,-7],by decide⟩
  | 37 => ⟨!![-1,3;-3,8],by decide⟩
  | 10 => ⟨!![-1,-4;-2,-9],by decide⟩
  | 25 => ⟨!![-1,2;-4,7],by decide⟩
  | 36 => ⟨!![1,4;-3,-11],by decide⟩
  | 24 => ⟨!![-1,5;2,-11],by decide⟩
  | 12 => ⟨!![-1,-5;-2,-11],by decide⟩
  | 11 => ⟨!![4,-1;-11,3],by decide⟩
  | 23 => ⟨!![5,1;-11,-2],by decide⟩
  | 35 => ⟨!![-5,1;-11,2],by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 33) : List (Fin 39) :=
  match rowClass c d with
  | 0 => [7]
  | 13 => [19]
  | 34 => [0, 7]
  | 17 => [7]
  | 30 => [7]
  | 43 => [7]
  | 40 => [7]
  | 44 => [7]
  | 32 => [7]
  | 29 => [2, 1, 7, 0]
  | 39 => [7]
  | 15 => [7]
  | 18 => [8, 18, 23, 7, 1]
  | 45 => [9, 17]
  | 19 => [7]
  | 14 => [19, 5, 17]
  | 9 => [7]
  | 6 => [2, 7, 14]
  | 38 => [6, 7, 13]
  | 28 => [7]
  | 33 => [5, 4, 3, 13]
  | 2 => [7]
  | 5 => [8, 12]
  | 46 => [9, 1, 0]
  | 1 => [19, 5, 14, 7]
  | 22 => [9, 34, 12, 7]
  | 37 => [6, 18, 23, 1]
  | 10 => [5, 4, 3, 12, 7]
  | 25 => [6, 15, 14]
  | 11 => [7]
  | 23 => [7]
  | 35 => [7]
  | _ => []

def edgeTRow (c d : ZMod 33) : List (Fin 39) :=
  match rowClass c d with
  | 47 => [0]
  | 17 => [7, 19]
  | 43 => [7]
  | 32 => [7]
  | 41 => [6, 15, 14, 7]
  | 15 => [8, 18, 23, 1]
  | 19 => [19, 5, 17, 7]
  | 6 => [2, 14]
  | 28 => [6, 13]
  | 22 => [9, 34, 11, 1, 0]
  | 36 => [9, 12]
  | 12 => [5, 4, 3, 29, 16, 12, 7]
  | 11 => [7, 9, 1, 0]
  | 23 => [19, 5, 10, 18, 23, 7, 1]
  | 35 => [5, 4, 3, 14]
  | _ => []

def rep (g : SL(2,ZMod 33)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)
theorem row_primitive (g : SL(2,ZMod 33)) :
    ∃ a b : ZMod 33, a*g.1 1 1-b*g.1 1 0=1 := by
  refine ⟨g.1 0 0,g.1 0 1,?_⟩
  exact (det_fin_two g.1).symm.trans g.det_coe

end QuantitativeArithmeticSmallLevelThirtyThreeGroup
end
end

/-! ## ThirtyThreeGroupEdgesSFamilyV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace QuantitativeArithmeticSmallLevelThirtyThreeGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups















































end QuantitativeArithmeticSmallLevelThirtyThreeGroup
end
end
end

/-! ## ThirtyThreeGroupEdgesTFamilyV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace QuantitativeArithmeticSmallLevelThirtyThreeGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups















































end QuantitativeArithmeticSmallLevelThirtyThreeGroup
end
end
end

/-! ## ThirtyThreeGroupEigenData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open QuantitativeArithmeticSmallLevelThirtyThreeChiThree
open scoped MatrixGroups ModularForm

def seed : Fin 6 → GL (Fin 2) ℝ
  | 0 => SpecialLinearGroup.mapGL ℝ T
  | 1 => SpecialLinearGroup.mapGL ℝ ((oddMatrix 33 17 (by decide))⁻¹)
  | 2 => Cplus
  | 3 => fricke 33 (by decide)
  | 4 => SmallLevelThirtyThree.B
  | _ => Cminus

def classRep : Fin 4 → GL (Fin 2) ℝ
  | 0 => 1
  | 1 => fricke 33 (by decide)
  | 2 => Cplus
  | _ => Cplus*fricke 33 (by decide)

def seedSign (χ δ : ℂ) : Fin 6 → ℂ
  | 0 => 1
  | 1 => 1
  | 2 => δ
  | 3 => χ
  | 4 => δ
  | _ => δ

def classSign (χ δ : ℂ) : Fin 4 → ℂ
  | 0 => 1
  | 1 => χ
  | 2 => δ
  | _ => δ*χ

def fromClass (i : Fin 19) : Fin 4 :=
  match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 2
  | 11 => 2
  | 12 => 2
  | 13 => 2
  | 14 => 2
  | 15 => 3
  | 16 => 3
  | 17 => 3
  | _ => 3

def toClass (i : Fin 19) : Fin 4 :=
  match i.val with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 1
  | 6 => 3
  | 7 => 0
  | 8 => 3
  | 9 => 3
  | 10 => 2
  | 11 => 2
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 3
  | 16 => 3
  | 17 => 1
  | _ => 1

def seedIndex (i : Fin 19) : Fin 6 :=
  match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | 8 => 4
  | 9 => 5
  | 10 => 0
  | 11 => 1
  | 12 => 2
  | 13 => 4
  | 14 => 5
  | 15 => 0
  | 16 => 1
  | 17 => 4
  | _ => 5

theorem seed_det (i : Fin 6) : (GeneralLinearGroup.det (seed i):ℝ)=1 := by
  fin_cases i
  · simp [seed,SpecialLinearGroup.det_mapGL]
  · simp [seed,SpecialLinearGroup.det_mapGL]
  · exact Cplus_det
  · exact fricke_det 33 (by decide)
  · exact SmallLevelThirtyThree.B_det
  · exact Cminus_det

theorem classRep_det (i : Fin 4) : (GeneralLinearGroup.det (classRep i):ℝ)=1 := by
  fin_cases i
  · simp [classRep]
  · exact fricke_det 33 (by decide)
  · exact Cplus_det
  · simpa [classRep] using congrArg₂ (fun x y : ℝ => x*y) Cplus_det (fricke_det 33 (by decide))

theorem signs_match {χ δ : ℂ} (hχ : χ=1 ∨ χ= -1) (hδ : δ=1 ∨ δ= -1) (i : Fin 19) :
    classSign χ δ (fromClass i)*seedSign χ δ (seedIndex i)=classSign χ δ (toClass i) := by
  rcases hχ with rfl|rfl <;> rcases hδ with rfl|rfl <;> fin_cases i <;>
    norm_num [classSign,seedSign,fromClass,toClass,seedIndex]

end QuantitativeArithmeticSmallLevelThirtyThreeGroup
end
end

/-! ## ThirtyThreeGroupEigenMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open QuantitativeArithmeticSmallLevelThirtyThreeChiThree
open scoped MatrixGroups ModularForm

/-- Exact identities behind all nineteen integral generators. -/
theorem kernel_identity (i : Fin 19) :
    SpecialLinearGroup.mapGL ℝ (kernel i)*classRep (toClass i)=
      classRep (fromClass i)*seed (seedIndex i) := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 33)^2=33 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 33≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ho : (oddMatrix 33 17 (by decide))⁻¹=kernel 1 := by decide
  fin_cases i <;>
    simp only [seedIndex,seed,ho] <;>
    apply Units.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [kernel,classRep,seed,fromClass,toClass,seedIndex,Cplus,Cminus,
      SmallLevelThirtyThree.B,fricke,matrix,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Matrix.vecMul,dotProduct,
      Fin.sum_univ_two,SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two] <;>
    (try field_simp [hn,SmallLevelThirtyThree.sqrt_three_ne]) <;> norm_num [hs,ht]
#print axioms kernel_identity

end QuantitativeArithmeticSmallLevelThirtyThreeGroup
end
end

/-! ## ThirtyThreeGroupGenerators -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section

namespace QuantitativeArithmeticSmallLevelThirtyThreeGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

theorem edgeSRow_checked : ∀ c d : ZMod 33, (∃ a b : ZMod 33, a*d-b*c=1) →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 33,
    Nat.gcd (Nat.gcd c.val d.val) 33 = 1 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeTRow_checked : ∀ c d : ZMod 33, (∃ a b : ZMod 33, a*d-b*c=1) →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 33,
    Nat.gcd (Nat.gcd c.val d.val) 33 = 1 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeS_checked (g : SL(2,ZMod 33)) :
    rep g*S*(rep (g*reduction 33 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 33 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 33 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 33)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_primitive g)

theorem edgeT_checked (g : SL(2,ZMod 33)) :
    rep g*T*(rep (g*reduction 33 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 33 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 33 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 33)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_primitive g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 33)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 33, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 19, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 33) : γ∈K := by
  apply transversal_mem (reduction 33) rep K
  · intro g
    rw [edgeS_checked]
    exact word_mem K hK hZ _
  · intro g
    rw [edgeT_checked]
    exact word_mem K hK hZ _
  · exact rep_one
  · apply rep_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ
#print axioms gamma0_mem

end QuantitativeArithmeticSmallLevelThirtyThreeGroup
end
end

/-! ## ThirtyThreeGroupOriginalEigen -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized SmallLevelOriginal
open QuantitativeArithmeticSmallLevelThirtyThreeChiThree
open scoped MatrixGroups ModularForm

/-- All six generating transformations have coherent signs determined by
one original Fricke sign and the prescribed ramified-three root. -/
theorem original_seed_eigen {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ i : Fin 6,
      fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] seed i=
        seedSign χ (FinitenessNormalizedTwistProduct.root 33 f 3) i • fourierFunction (2*m) f := by
  obtain ⟨χ,hχ,hknown⟩ := QuantitativeArithmeticSmallLevelThirtyThreeKnownWords.original_seeds hm hf
  obtain ⟨hCp,hCm⟩ := original_C_plus_minus hm hf
  refine ⟨χ,hχ,?_⟩
  intro i
  fin_cases i
  · exact hknown 0
  · exact hknown 2
  · exact hCp
  · exact hknown 3
  · exact hknown 4
  · exact hCm

theorem class_eigen (F : ℍ → ℂ) (k : ℤ) (χ δ : ℂ)
    (hseed : ∀ i : Fin 6, F ∣[k] seed i=seedSign χ δ i • F) (i : Fin 4) :
    F ∣[k] classRep i=classSign χ δ i • F := by
  fin_cases i
  · change F ∣[k] (1 : GL (Fin 2) ℝ)=(1:ℂ) • F
    simp only [SlashAction.slash_one,one_smul]
  · exact hseed 3
  · exact hseed 2
  · change F ∣[k] (Cplus*fricke 33 (by decide))=(δ*χ) • F
    have hp : F ∣[k] Cplus=δ • F := hseed 2
    have hw : F ∣[k] fricke 33 (by decide)=χ • F := hseed 3
    rw [SlashAction.slash_mul,hp,det_one_smul _ (fricke_det 33 (by decide)),hw,mul_smul]

/-- The finite sign quotient disappears on each integral kernel generator. -/
theorem kernel_invariant (F : ℍ → ℂ) (k : ℤ) {χ δ : ℂ}
    (hχ : χ=1 ∨ χ= -1) (hδ : δ=1 ∨ δ= -1)
    (hseed : ∀ i : Fin 6, F ∣[k] seed i=seedSign χ δ i • F) (i : Fin 19) :
    F ∣[k] kernel i=F := by
  have hh : (F ∣[k] kernel i) ∣[k] classRep (toClass i)=F ∣[k] classRep (toClass i) := by
    change (F ∣[k] SpecialLinearGroup.mapGL ℝ (kernel i)) ∣[k] classRep (toClass i)=_
    rw [← SlashAction.slash_mul,kernel_identity,SlashAction.slash_mul,
      class_eigen F k χ δ hseed (fromClass i),det_one_smul _ (seed_det _),hseed,
      ← mul_smul,signs_match hχ hδ]
    exact (class_eigen F k χ δ hseed (toClass i)).symm
  have he := congrArg (fun G : ℍ → ℂ => G ∣[k] (classRep (toClass i))⁻¹) hh
  simpa only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] using he

theorem original_all_generators {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f) (i : Fin 19) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel i=fourierFunction (2*m) f := by
  obtain ⟨χ,hχ,hseed⟩ := original_seed_eigen hm hf
  exact kernel_invariant _ _ hχ (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 3) hseed i
#print axioms original_all_generators
end QuantitativeArithmeticSmallLevelThirtyThreeGroup
end
end

/-! ## ThirtyThreeModular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelOriginal
open scoped MatrixGroups ModularForm
theorem original_gamma0 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 33) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  exact gamma0_mem (slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f))
    (original_all_generators hm hf) (SmallLevelThirtySix.slash_neg_one_even _ m) γ hγ

/-- The level33 converse theorem, from the literal original Euler-product
and entire Fricke hypotheses, including holomorphy at every cusp. -/
theorem level_thirty_three {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 33 k f) : IsModular 33 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  exact modular_of_transformations (by decide) hf (original_gamma0 (by omega) hf)

#print axioms original_gamma0
#print axioms level_thirty_three
end QuantitativeArithmeticSmallLevelThirtyThreeGroup
end
end
