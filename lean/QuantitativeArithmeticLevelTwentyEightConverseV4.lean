module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.LSeries.Linearity
public import QuantitativeArithmeticEntireQuotientV1
public import QuantitativeArithmeticLevelTwentyTwoConverseV4
public import QuantitativeArithmeticPrimePowerTorsionV1
public import QuantitativeArithmeticRectangularContinuationTheoryV4
public import SmallLevelAdditiveTheoryV4
public import SmallLevelAdditiveMellinV1
public import SmallLevelAllowedSimplePoleTailV1
public import SmallLevelContinuationTheoryV4
public import SmallLevelTaylorTheoryV4
public import SmallLevelEvenDescentV1
public import SmallLevelMellinUnscaleV1
public import SmallLevelModularCriterionV1
public import SmallLevelPoleGridTheoryV4
public import SmallLevelQuadraticExponentialTheoryV4
public import SmallLevelRegularPoleTailV1
public import SmallLevelRegularTailBlockKernelV1
public import SmallLevelRegularizedShiftBlockV1
public import SmallLevelRegularizedShiftKernelV1
public import SmallLevelSelectedRegularFirstShiftV1
public import SmallLevelSevenGeneratorsV1
public import SmallLevelTaylorRowCoefficientsV1
public import SmallLevelPrimeRatesTheoryV4
public import SmallLevelTwentyEightFirstJetAlgebraV1
public import SmallLevelTwentyEightGridSourceFourierV1
public import SmallLevelTwentyEightJetBlockTheoryV4
public import SmallLevelTwentyEightLaurentTheoryV4
public import SmallLevelTwentyEightThirdJetTriangularKernel0V1
public import SmallLevelTwentyEightTriangularTheoryV4
public import SmallLevelTwentyEightTwelfthCentersV1
public import SmallLevelTwentyOneKnownWordsTheoryV4
public import SmallLevelUniversalFactoredFirstShiftV1
public import SmallLevelUniversalHigherPoleVectorV1
public import SmallLevelUniversalPoleDetectionV1
public import SmallLevelUniversalRegularTailLeadingV1

/-! Consolidated converse argument. Large exact certificates remain
in their own modules; declarations and proof bodies are preserved. -/

/-! ## TwentyEightModularCriterion -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyEight

open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelEvenScale
open scoped MatrixGroups ModularForm

/-- The sole remaining analytic transformation in the level-28 endgame.
For g(z)=F(z/2), this is g|[2,-1;-7,4]=-g, equivalently
F|[4,-1;-28,8]=-F with the determinant-normalized weight action.
This definition is an explicit missing transformation, not an assertion
that the original hypotheses already imply it. -/
def QuarterTransformation (k : ℕ) (f : ℕ → ℂ) : Prop :=
  scaledFunction k f ∣[(k:ℤ)] (oddMatrix 7 4 (by decide))⁻¹ =
    -scaledFunction k f

theorem quarter_matrix : (oddMatrix 7 4 (by decide))⁻¹ =
    (⟨!![2,-1;-7,4],by decide⟩ : SL(2,ℤ)) := by decide

theorem sign_lower_seven : ∀ A : SL(2,ZMod 2),
    signTwo (A*reduction 2 (lower 7))= -signTwo A := by decide

theorem sign_odd_seven : ∀ A : SL(2,ZMod 2),
    signTwo (A*reduction 2 (oddMatrix 7 4 (by decide)))= -signTwo A := by decide

/-- Exact signed generation of Gamma0(7), using the existing finite
Schreier certificate and the sign of reduction modulo two. -/
theorem seven_signed (m : ℕ) (g : ℍ → ℂ)
    (hT : g ∣[((2*m:ℕ):ℤ)] T= -g)
    (hU : g ∣[((2*m:ℕ):ℤ)] lower 7= -g)
    (hA : g ∣[((2*m:ℕ):ℤ)] oddMatrix 7 4 (by decide)= -g)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 7) :
    g ∣[((2*m:ℕ):ℤ)] γ=(signTwo (reduction 2 γ):ℂ) • g := by
  let w : SL(2,ℤ) → ℍ → ℂ := fun M => (signTwo (reduction 2 M):ℂ) • g
  have ht (M : SL(2,ℤ)) (_hM : M∈CongruenceSubgroup.Gamma0 7) :
      w M ∣[((2*m:ℕ):ℤ)] T=w (M*T) := by
    simp only [w, ModularForm.SL_smul_slash, hT, map_mul, signTwo_T,
      Int.cast_neg, _root_.neg_smul, smul_neg]
  have hu (M : SL(2,ℤ)) (_hM : M∈CongruenceSubgroup.Gamma0 7) :
      w M ∣[((2*m:ℕ):ℤ)] lower 7=w (M*lower 7) := by
    simp only [w, ModularForm.SL_smul_slash, hU, map_mul, sign_lower_seven,
      Int.cast_neg, _root_.neg_smul, smul_neg]
  have hz (M : SL(2,ℤ)) (_hM : M∈CongruenceSubgroup.Gamma0 7) :
      w M ∣[((2*m:ℕ):ℤ)] (-1 : SL(2,ℤ))=w (M*(-1)) := by
    simp only [w, ModularForm.SL_smul_slash, SmallLevelThirtySix.slash_neg_one_even,
      map_mul, signTwo_Z]
  have ha (M : SL(2,ℤ)) (_hM : M∈CongruenceSubgroup.Gamma0 7) :
      w M ∣[((2*m:ℕ):ℤ)] oddMatrix 7 4 (by decide)=
        w (M*oddMatrix 7 4 (by decide)) := by
    simp only [w, ModularForm.SL_smul_slash, hA, map_mul, sign_odd_seven,
      Int.cast_neg, _root_.neg_smul, smul_neg]
  have hh := (gamma0_7_mem
    (orbitSubgroup (CongruenceSubgroup.Gamma0 7) ((2*m:ℕ):ℤ) w)
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,ht⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hu⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,hz⟩
    ⟨by apply CongruenceSubgroup.Gamma0_mem.mpr; decide,ha⟩ γ hγ).2 1 (Subgroup.one_mem _)
  simpa only [w, map_one, signTwo_one, Int.cast_one, one_smul, one_mul] using hh

theorem rescaled_sign (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 1 0=4*(7:ℤ)*c) :
    signTwo (reduction 2 (rescaledMatrix 7 γ c hc))=1 := by
  apply signTwo_diagonal
  · change ((2*γ 0 1:ℤ):ZMod 2)=0
    push_cast
    rw [show (2:ZMod 2)=0 by decide, zero_mul]
  · change ((14*c:ℤ):ZMod 2)=0
    push_cast
    rw [show (14:ZMod 2)=0 by decide, zero_mul]

theorem odd_action_of_quarter {k : ℕ} {f : ℕ → ℂ}
    (hq : QuarterTransformation k f) :
    scaledFunction k f ∣[(k:ℤ)] oddMatrix 7 4 (by decide)= -scaledFunction k f := by
  have hh := congrArg (fun g : ℍ → ℂ => g ∣[(k:ℤ)] oddMatrix 7 4 (by decide)) hq
  simp only [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one,
    SlashAction.neg_slash] at hh
  exact neg_eq_iff_eq_neg.mp hh.symm

/-- All original level-28 transformations, conditional solely on the
quarter-twist transformation; cusp boundedness is supplied separately by
the generic original-input modularity criterion. -/
theorem gamma_zero_of_quarter (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f)
    (hq : QuarterTransformation (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 28) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  have hc : (28:ℤ)∣γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 28).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨c,hc⟩ := hc
  have hc' : γ 1 0=4*(7:ℤ)*c := by simpa using hc
  apply descend_invariance (2*m) f 7 γ c hc'
  have hh := seven_signed m (scaledFunction (2*m) f)
    (scaled_T (L:=7) hf.toEulerData) (scaled_lower (L:=7) (by decide) hf)
    (odd_action_of_quarter hq) (rescaledMatrix 7 γ c hc') (rescaled_mem 7 γ c hc')
  simpa only [rescaled_sign, Int.cast_one, one_smul] using hh

/-- Conditional endpoint: the original level-28 input plus one explicit
quarter transformation implies genuine modularity. No level-28 pole
elimination or quarter-twist continuation is claimed in this file. -/
theorem modular_of_quarter {k : ℕ} (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 k f)
    (hq : QuarterTransformation k f) : SmallLevelOriginal.IsModular 28 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf hq ⊢
  exact SmallLevelOriginal.modular_of_transformations (by decide) hf
    (gamma_zero_of_quarter m hf hq)

#print axioms quarter_matrix
#print axioms seven_signed
#print axioms odd_action_of_quarter
#print axioms gamma_zero_of_quarter
#print axioms modular_of_quarter

end QuantitativeArithmeticSmallLevelTwentyEight
end
end

/-! ## TwentyEightQuotient -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelTwentyEight

open Complex Matrix

/-- The constant odd mode in the 84-grid. -/
def oddMode (j : Fin 84) : ℂ :=
  if j.val∈({11,17,25,31} : Finset ℕ) then -1
  else if j.val∈({53,59,67,73} : Finset ℕ) then 1 else 0

theorem oddMode_at_gauge : oddMode 53=1 := by norm_num [oddMode]

def evenIndex (j : Fin 42) : Fin 84 := ⟨2*j.val,by omega⟩

theorem oddMode_even : ∀ j : Fin 42, oddMode (evenIndex j)=0 := by
  intro j
  fin_cases j <;> norm_num [oddMode,evenIndex]

/-- Quotient chosen in the original half-plane, with no continuation of
its subtracted 53-coordinate assumed. -/
def quotientVector (v : Fin 84 → ℂ) : Fin 84 → ℂ := v-v 53 • oddMode

theorem quotient_apply (v : Fin 84 → ℂ) (j : Fin 84) :
    quotientVector v j=v j-v 53*oddMode j := rfl

theorem quotient_gauge (v : Fin 84 → ℂ) : quotientVector v 53=0 := by
  simp [quotient_apply,oddMode_at_gauge]

theorem quotient_even (v : Fin 84 → ℂ) (j : Fin 42) :
    quotientVector v (evenIndex j)=v (evenIndex j) := by
  simp [quotient_apply,oddMode_even]

/-- Any linear row annihilating the constant mode is unchanged by this
projection. This applies to both the leading and every shifted Taylor row. -/
theorem linear_row_quotient (L : (Fin 84 → ℂ) →ₗ[ℂ] ℂ)
    (hL : L oddMode=0) (v : Fin 84 → ℂ) : L (quotientVector v)=L v := by
  simp [quotientVector,map_sub,map_smul,hL]

theorem matrix_quotient {ι : Type*} (A : Matrix ι (Fin 84) ℂ)
    (hA : A *ᵥ oddMode=0) (v : Fin 84 → ℂ) : A *ᵥ quotientVector v=A *ᵥ v := by
  rw [quotientVector,Matrix.mulVec_sub,Matrix.mulVec_smul,hA,smul_zero,sub_zero]

def grid84 (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (j : Fin 84) : ℂ :=
  SmallLevelAdditive.original k f ((j.val:ℝ)/84) s

def quotientGrid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : Fin 84 → ℂ :=
  quotientVector (grid84 k f s)

theorem quotientGrid_even (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (j : Fin 42) :
    quotientGrid k f s (evenIndex j)=SmallLevelAdditive.original k f ((j.val:ℝ)/42) s := by
  rw [quotientGrid,quotient_even]
  unfold grid84 evenIndex
  have h : ((2*j.val:ℕ):ℝ)/84=(j.val:ℝ)/42 := by push_cast; ring
  rw [h]

theorem original_quotient_halfplane {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 k f) :
    ∃ B : ℝ, ∀ j : Fin 84, ∀ s : ℂ, B<s.re →
      AnalyticAt ℂ (fun z => quotientGrid k f z j) s := by
  obtain ⟨B,hB⟩ := SmallLevelAdditive.original_common_halfplane hf
  refine ⟨B,fun j s hs => ?_⟩
  change AnalyticAt ℂ (fun z => SmallLevelAdditive.original k f ((j.val:ℝ)/84) z-
    SmallLevelAdditive.original k f ((53:ℝ)/84) z*oddMode j) s
  exact ((hB _ s hs).1).sub (((hB _ s hs).1).mul analyticAt_const)

#print axioms oddMode_even
#print axioms linear_row_quotient
#print axioms matrix_quotient
#print axioms quotientGrid_even
#print axioms original_quotient_halfplane

end QuantitativeArithmeticSmallLevelTwentyEight
end
end

/-! ## TwentyEightJetBlockKernel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightJetBlock
open Complex SmallLevelFiniteShift SmallLevelTwentyEightLaurent SmallLevelTwentyEightThirdJet

theorem kernel_zero (w : Fin 336→ℂ) (hw : ∀ n i, jetBlockRow n i w=0) : w=0 := by
  apply SmallLevelTwentyEightThirdJetTriangular.kernel0 w
  intro r
  fin_cases r
  · exact (link0_0 w).symm.trans (hw 0 0)
  · exact (link0_1 w).symm.trans (hw 0 1)
  · exact (link0_2 w).symm.trans (hw 0 2)
  · exact (link0_3 w).symm.trans (hw 0 3)
  · exact (link0_4 w).symm.trans (hw 0 4)
  · exact (link0_5 w).symm.trans (hw 0 5)
  · exact (link0_6 w).symm.trans (hw 0 6)
  · exact (link0_7 w).symm.trans (hw 0 7)
  · exact (link0_8 w).symm.trans (hw 0 8)
  · exact (link0_9 w).symm.trans (hw 0 9)
  · exact (link0_10 w).symm.trans (hw 0 10)
  · exact (link0_11 w).symm.trans (hw 0 11)
  · exact (link0_12 w).symm.trans (hw 0 12)
  · exact (link0_13 w).symm.trans (hw 0 13)
  · exact (link0_14 w).symm.trans (hw 0 14)
  · exact (link0_15 w).symm.trans (hw 0 15)
  · exact (link0_16 w).symm.trans (hw 0 16)
  · exact (link0_17 w).symm.trans (hw 0 17)
  · exact (link0_18 w).symm.trans (hw 0 18)
  · exact (link0_19 w).symm.trans (hw 0 19)
  · exact (link0_20 w).symm.trans (hw 0 20)
  · exact (link0_21 w).symm.trans (hw 0 21)
  · exact (link0_22 w).symm.trans (hw 0 22)
  · exact (link0_23 w).symm.trans (hw 0 23)
  · exact (link0_24 w).symm.trans (hw 0 24)
  · exact (link0_25 w).symm.trans (hw 0 25)
  · exact (link0_26 w).symm.trans (hw 0 26)
  · exact (link0_27 w).symm.trans (hw 0 27)
  · exact (link0_28 w).symm.trans (hw 0 28)
  · exact (link0_29 w).symm.trans (hw 0 29)
  · exact (link0_30 w).symm.trans (hw 0 30)
  · exact (link0_31 w).symm.trans (hw 0 31)
  · exact (link0_32 w).symm.trans (hw 0 32)
  · exact (link0_33 w).symm.trans (hw 0 33)
  · exact (link0_34 w).symm.trans (hw 0 34)
  · exact (link0_35 w).symm.trans (hw 0 35)
  · exact (link0_36 w).symm.trans (hw 0 36)
  · exact (link0_37 w).symm.trans (hw 0 37)
  · exact (link0_38 w).symm.trans (hw 0 38)
  · exact (link0_39 w).symm.trans (hw 0 39)
  · exact (link0_40 w).symm.trans (hw 0 40)
  · exact (link0_41 w).symm.trans (hw 0 41)
  · exact (link0_42 w).symm.trans (hw 0 42)
  · exact (link0_43 w).symm.trans (hw 0 43)
  · exact (link0_44 w).symm.trans (hw 0 44)
  · exact (link0_45 w).symm.trans (hw 0 45)
  · exact (link0_46 w).symm.trans (hw 0 46)
  · exact (link0_47 w).symm.trans (hw 0 47)
  · exact (link0_48 w).symm.trans (hw 0 48)
  · exact (link0_49 w).symm.trans (hw 0 49)
  · exact (link0_50 w).symm.trans (hw 0 50)
  · exact (link0_51 w).symm.trans (hw 0 51)
  · exact (link0_52 w).symm.trans (hw 0 52)
  · exact (link0_53 w).symm.trans (hw 0 53)
  · exact (link0_54 w).symm.trans (hw 0 54)
  · exact (link0_55 w).symm.trans (hw 0 55)
  · exact (link0_56 w).symm.trans (hw 0 56)
  · exact (link0_57 w).symm.trans (hw 0 57)
  · exact (link0_58 w).symm.trans (hw 0 58)
  · exact (link0_59 w).symm.trans (hw 0 59)
  · exact (link0_60 w).symm.trans (hw 0 60)
  · exact (link0_61 w).symm.trans (hw 0 61)
  · exact (link0_62 w).symm.trans (hw 0 62)
  · exact (link0_63 w).symm.trans (hw 0 63)
  · exact (link0_64 w).symm.trans (hw 0 64)
  · exact (link0_65 w).symm.trans (hw 0 65)
  · exact (link0_66 w).symm.trans (hw 0 66)
  · exact (link0_67 w).symm.trans (hw 0 67)
  · exact (link0_68 w).symm.trans (hw 0 68)
  · exact (link0_69 w).symm.trans (hw 0 69)
  · exact (link0_70 w).symm.trans (hw 0 70)
  · exact (link0_71 w).symm.trans (hw 0 71)
  · exact (link0_72 w).symm.trans (hw 0 72)
  · exact (link0_73 w).symm.trans (hw 0 73)
  · exact (link0_74 w).symm.trans (hw 0 74)
  · exact (link0_75 w).symm.trans (hw 0 75)
  · exact (link0_76 w).symm.trans (hw 0 76)
  · exact (link0_77 w).symm.trans (hw 0 77)
  · exact (link0_78 w).symm.trans (hw 0 78)
  · exact (link0_79 w).symm.trans (hw 0 79)
  · exact (link0_80 w).symm.trans (hw 0 80)
  · exact (link0_81 w).symm.trans (hw 0 81)
  · exact (link0_82 w).symm.trans (hw 0 82)
  · exact (link0_83 w).symm.trans (hw 0 83)
  · exact (link0_84 w).symm.trans (hw 0 84)
  · exact (link0_85 w).symm.trans (hw 0 85)
  · exact (link0_86 w).symm.trans (hw 1 0)
  · exact (link0_87 w).symm.trans (hw 1 1)
  · exact (link0_88 w).symm.trans (hw 1 2)
  · exact (link0_89 w).symm.trans (hw 1 3)
  · exact (link0_90 w).symm.trans (hw 1 4)
  · exact (link0_91 w).symm.trans (hw 1 5)
  · exact (link0_92 w).symm.trans (hw 1 6)
  · exact (link0_93 w).symm.trans (hw 1 7)
  · exact (link0_94 w).symm.trans (hw 1 8)
  · exact (link0_95 w).symm.trans (hw 1 9)
  · exact (link0_96 w).symm.trans (hw 1 10)
  · exact (link0_97 w).symm.trans (hw 1 11)
  · exact (link0_98 w).symm.trans (hw 1 12)
  · exact (link0_99 w).symm.trans (hw 1 13)
  · exact (link0_100 w).symm.trans (hw 1 14)
  · exact (link0_101 w).symm.trans (hw 1 15)
  · exact (link0_102 w).symm.trans (hw 1 16)
  · exact (link0_103 w).symm.trans (hw 1 17)
  · exact (link0_104 w).symm.trans (hw 1 18)
  · exact (link0_105 w).symm.trans (hw 1 19)
  · exact (link0_106 w).symm.trans (hw 1 20)
  · exact (link0_107 w).symm.trans (hw 1 21)
  · exact (link0_108 w).symm.trans (hw 1 22)
  · exact (link0_109 w).symm.trans (hw 1 23)
  · exact (link0_110 w).symm.trans (hw 1 24)
  · exact (link0_111 w).symm.trans (hw 1 25)
  · exact (link0_112 w).symm.trans (hw 1 26)
  · exact (link0_113 w).symm.trans (hw 1 27)
  · exact (link0_114 w).symm.trans (hw 1 28)
  · exact (link0_115 w).symm.trans (hw 1 29)
  · exact (link0_116 w).symm.trans (hw 1 30)
  · exact (link0_117 w).symm.trans (hw 1 31)
  · exact (link0_118 w).symm.trans (hw 1 32)
  · exact (link0_119 w).symm.trans (hw 1 33)
  · exact (link0_120 w).symm.trans (hw 1 34)
  · exact (link0_121 w).symm.trans (hw 1 35)
  · exact (link0_122 w).symm.trans (hw 1 36)
  · exact (link0_123 w).symm.trans (hw 1 37)
  · exact (link0_124 w).symm.trans (hw 1 38)
  · exact (link0_125 w).symm.trans (hw 1 39)
  · exact (link0_126 w).symm.trans (hw 1 40)
  · exact (link0_127 w).symm.trans (hw 1 41)
  · exact (link0_128 w).symm.trans (hw 1 42)
  · exact (link0_129 w).symm.trans (hw 1 43)
  · exact (link0_130 w).symm.trans (hw 1 44)
  · exact (link0_131 w).symm.trans (hw 1 45)
  · exact (link0_132 w).symm.trans (hw 1 46)
  · exact (link0_133 w).symm.trans (hw 1 47)
  · exact (link0_134 w).symm.trans (hw 1 48)
  · exact (link0_135 w).symm.trans (hw 1 49)
  · exact (link0_136 w).symm.trans (hw 1 50)
  · exact (link0_137 w).symm.trans (hw 1 51)
  · exact (link0_138 w).symm.trans (hw 1 52)
  · exact (link0_139 w).symm.trans (hw 1 53)
  · exact (link0_140 w).symm.trans (hw 1 54)
  · exact (link0_141 w).symm.trans (hw 1 55)
  · exact (link0_142 w).symm.trans (hw 1 56)
  · exact (link0_143 w).symm.trans (hw 1 57)
  · exact (link0_144 w).symm.trans (hw 1 58)
  · exact (link0_145 w).symm.trans (hw 1 59)
  · exact (link0_146 w).symm.trans (hw 1 60)
  · exact (link0_147 w).symm.trans (hw 1 61)
  · exact (link0_148 w).symm.trans (hw 1 62)
  · exact (link0_149 w).symm.trans (hw 1 63)
  · exact (link0_150 w).symm.trans (hw 1 64)
  · exact (link0_151 w).symm.trans (hw 1 65)
  · exact (link0_152 w).symm.trans (hw 1 66)
  · exact (link0_153 w).symm.trans (hw 1 67)
  · exact (link0_154 w).symm.trans (hw 1 68)
  · exact (link0_155 w).symm.trans (hw 1 69)
  · exact (link0_156 w).symm.trans (hw 1 70)
  · exact (link0_157 w).symm.trans (hw 1 71)
  · exact (link0_158 w).symm.trans (hw 1 72)
  · exact (link0_159 w).symm.trans (hw 1 73)
  · exact (link0_160 w).symm.trans (hw 1 74)
  · exact (link0_161 w).symm.trans (hw 1 75)
  · exact (link0_162 w).symm.trans (hw 1 76)
  · exact (link0_163 w).symm.trans (hw 1 77)
  · exact (link0_164 w).symm.trans (hw 1 78)
  · exact (link0_165 w).symm.trans (hw 1 79)
  · exact (link0_166 w).symm.trans (hw 1 80)
  · exact (link0_167 w).symm.trans (hw 1 81)
  · exact (link0_168 w).symm.trans (hw 1 82)
  · exact (link0_169 w).symm.trans (hw 1 83)
  · exact (link0_170 w).symm.trans (hw 1 84)
  · exact (link0_171 w).symm.trans (hw 1 85)
  · exact (link0_172 w).symm.trans (hw 2 0)
  · exact (link0_173 w).symm.trans (hw 2 1)
  · exact (link0_174 w).symm.trans (hw 2 2)
  · exact (link0_175 w).symm.trans (hw 2 3)
  · exact (link0_176 w).symm.trans (hw 2 4)
  · exact (link0_177 w).symm.trans (hw 2 5)
  · exact (link0_178 w).symm.trans (hw 2 6)
  · exact (link0_179 w).symm.trans (hw 2 7)
  · exact (link0_180 w).symm.trans (hw 2 8)
  · exact (link0_181 w).symm.trans (hw 2 9)
  · exact (link0_182 w).symm.trans (hw 2 10)
  · exact (link0_183 w).symm.trans (hw 2 11)
  · exact (link0_184 w).symm.trans (hw 2 12)
  · exact (link0_185 w).symm.trans (hw 2 13)
  · exact (link0_186 w).symm.trans (hw 2 14)
  · exact (link0_187 w).symm.trans (hw 2 15)
  · exact (link0_188 w).symm.trans (hw 2 16)
  · exact (link0_189 w).symm.trans (hw 2 17)
  · exact (link0_190 w).symm.trans (hw 2 18)
  · exact (link0_191 w).symm.trans (hw 2 19)
  · exact (link0_192 w).symm.trans (hw 2 20)
  · exact (link0_193 w).symm.trans (hw 2 21)
  · exact (link0_194 w).symm.trans (hw 2 22)
  · exact (link0_195 w).symm.trans (hw 2 23)
  · exact (link0_196 w).symm.trans (hw 2 24)
  · exact (link0_197 w).symm.trans (hw 2 25)
  · exact (link0_198 w).symm.trans (hw 2 26)
  · exact (link0_199 w).symm.trans (hw 2 27)
  · exact (link0_200 w).symm.trans (hw 2 28)
  · exact (link0_201 w).symm.trans (hw 2 29)
  · exact (link0_202 w).symm.trans (hw 2 30)
  · exact (link0_203 w).symm.trans (hw 2 31)
  · exact (link0_204 w).symm.trans (hw 2 32)
  · exact (link0_205 w).symm.trans (hw 2 33)
  · exact (link0_206 w).symm.trans (hw 2 34)
  · exact (link0_207 w).symm.trans (hw 2 35)
  · exact (link0_208 w).symm.trans (hw 2 36)
  · exact (link0_209 w).symm.trans (hw 2 37)
  · exact (link0_210 w).symm.trans (hw 2 38)
  · exact (link0_211 w).symm.trans (hw 2 39)
  · exact (link0_212 w).symm.trans (hw 2 40)
  · exact (link0_213 w).symm.trans (hw 2 41)
  · exact (link0_214 w).symm.trans (hw 2 42)
  · exact (link0_215 w).symm.trans (hw 2 43)
  · exact (link0_216 w).symm.trans (hw 2 44)
  · exact (link0_217 w).symm.trans (hw 2 45)
  · exact (link0_218 w).symm.trans (hw 2 46)
  · exact (link0_219 w).symm.trans (hw 2 47)
  · exact (link0_220 w).symm.trans (hw 2 48)
  · exact (link0_221 w).symm.trans (hw 2 49)
  · exact (link0_222 w).symm.trans (hw 2 50)
  · exact (link0_223 w).symm.trans (hw 2 51)
  · exact (link0_224 w).symm.trans (hw 2 52)
  · exact (link0_225 w).symm.trans (hw 2 53)
  · exact (link0_226 w).symm.trans (hw 2 54)
  · exact (link0_227 w).symm.trans (hw 2 55)
  · exact (link0_228 w).symm.trans (hw 2 56)
  · exact (link0_229 w).symm.trans (hw 2 57)
  · exact (link0_230 w).symm.trans (hw 2 58)
  · exact (link0_231 w).symm.trans (hw 2 59)
  · exact (link0_232 w).symm.trans (hw 2 60)
  · exact (link0_233 w).symm.trans (hw 2 61)
  · exact (link0_234 w).symm.trans (hw 2 62)
  · exact (link0_235 w).symm.trans (hw 2 63)
  · exact (link0_236 w).symm.trans (hw 2 64)
  · exact (link0_237 w).symm.trans (hw 2 65)
  · exact (link0_238 w).symm.trans (hw 2 66)
  · exact (link0_239 w).symm.trans (hw 2 67)
  · exact (link0_240 w).symm.trans (hw 2 68)
  · exact (link0_241 w).symm.trans (hw 2 69)
  · exact (link0_242 w).symm.trans (hw 2 70)
  · exact (link0_243 w).symm.trans (hw 2 71)
  · exact (link0_244 w).symm.trans (hw 2 72)
  · exact (link0_245 w).symm.trans (hw 2 73)
  · exact (link0_246 w).symm.trans (hw 2 74)
  · exact (link0_247 w).symm.trans (hw 2 75)
  · exact (link0_248 w).symm.trans (hw 2 76)
  · exact (link0_249 w).symm.trans (hw 2 77)
  · exact (link0_250 w).symm.trans (hw 2 78)
  · exact (link0_251 w).symm.trans (hw 2 79)
  · exact (link0_252 w).symm.trans (hw 2 80)
  · exact (link0_253 w).symm.trans (hw 2 81)
  · exact (link0_254 w).symm.trans (hw 2 82)
  · exact (link0_255 w).symm.trans (hw 2 83)
  · exact (link0_256 w).symm.trans (hw 2 84)
  · exact (link0_257 w).symm.trans (hw 2 85)
  · exact (link0_258 w).symm.trans (hw 3 0)
  · exact (link0_259 w).symm.trans (hw 3 1)
  · exact (link0_260 w).symm.trans (hw 3 2)
  · exact (link0_261 w).symm.trans (hw 3 3)
  · exact (link0_262 w).symm.trans (hw 3 4)
  · exact (link0_263 w).symm.trans (hw 3 5)
  · exact (link0_264 w).symm.trans (hw 3 6)
  · exact (link0_265 w).symm.trans (hw 3 7)
  · exact (link0_266 w).symm.trans (hw 3 8)
  · exact (link0_267 w).symm.trans (hw 3 9)
  · exact (link0_268 w).symm.trans (hw 3 10)
  · exact (link0_269 w).symm.trans (hw 3 11)
  · exact (link0_270 w).symm.trans (hw 3 12)
  · exact (link0_271 w).symm.trans (hw 3 13)
  · exact (link0_272 w).symm.trans (hw 3 14)
  · exact (link0_273 w).symm.trans (hw 3 15)
  · exact (link0_274 w).symm.trans (hw 3 16)
  · exact (link0_275 w).symm.trans (hw 3 17)
  · exact (link0_276 w).symm.trans (hw 3 18)
  · exact (link0_277 w).symm.trans (hw 3 19)
  · exact (link0_278 w).symm.trans (hw 3 20)
  · exact (link0_279 w).symm.trans (hw 3 21)
  · exact (link0_280 w).symm.trans (hw 3 22)
  · exact (link0_281 w).symm.trans (hw 3 23)
  · exact (link0_282 w).symm.trans (hw 3 24)
  · exact (link0_283 w).symm.trans (hw 3 25)
  · exact (link0_284 w).symm.trans (hw 3 26)
  · exact (link0_285 w).symm.trans (hw 3 27)
  · exact (link0_286 w).symm.trans (hw 3 28)
  · exact (link0_287 w).symm.trans (hw 3 29)
  · exact (link0_288 w).symm.trans (hw 3 30)
  · exact (link0_289 w).symm.trans (hw 3 31)
  · exact (link0_290 w).symm.trans (hw 3 32)
  · exact (link0_291 w).symm.trans (hw 3 33)
  · exact (link0_292 w).symm.trans (hw 3 34)
  · exact (link0_293 w).symm.trans (hw 3 35)
  · exact (link0_294 w).symm.trans (hw 3 36)
  · exact (link0_295 w).symm.trans (hw 3 37)
  · exact (link0_296 w).symm.trans (hw 3 38)
  · exact (link0_297 w).symm.trans (hw 3 39)
  · exact (link0_298 w).symm.trans (hw 3 40)
  · exact (link0_299 w).symm.trans (hw 3 41)
  · exact (link0_300 w).symm.trans (hw 3 42)
  · exact (link0_301 w).symm.trans (hw 3 43)
  · exact (link0_302 w).symm.trans (hw 3 44)
  · exact (link0_303 w).symm.trans (hw 3 45)
  · exact (link0_304 w).symm.trans (hw 3 46)
  · exact (link0_305 w).symm.trans (hw 3 47)
  · exact (link0_306 w).symm.trans (hw 3 48)
  · exact (link0_307 w).symm.trans (hw 3 49)
  · exact (link0_308 w).symm.trans (hw 3 50)
  · exact (link0_309 w).symm.trans (hw 3 51)
  · exact (link0_310 w).symm.trans (hw 3 52)
  · exact (link0_311 w).symm.trans (hw 3 53)
  · exact (link0_312 w).symm.trans (hw 3 54)
  · exact (link0_313 w).symm.trans (hw 3 55)
  · exact (link0_314 w).symm.trans (hw 3 56)
  · exact (link0_315 w).symm.trans (hw 3 57)
  · exact (link0_316 w).symm.trans (hw 3 58)
  · exact (link0_317 w).symm.trans (hw 3 59)
  · exact (link0_318 w).symm.trans (hw 3 60)
  · exact (link0_319 w).symm.trans (hw 3 61)
  · exact (link0_320 w).symm.trans (hw 3 62)
  · exact (link0_321 w).symm.trans (hw 3 63)
  · exact (link0_322 w).symm.trans (hw 3 64)
  · exact (link0_323 w).symm.trans (hw 3 65)
  · exact (link0_324 w).symm.trans (hw 3 66)
  · exact (link0_325 w).symm.trans (hw 3 67)
  · exact (link0_326 w).symm.trans (hw 3 68)
  · exact (link0_327 w).symm.trans (hw 3 69)
  · exact (link0_328 w).symm.trans (hw 3 70)
  · exact (link0_329 w).symm.trans (hw 3 71)
  · exact (link0_330 w).symm.trans (hw 3 72)
  · exact (link0_331 w).symm.trans (hw 3 73)
  · exact (link0_332 w).symm.trans (hw 3 74)
  · exact (link0_333 w).symm.trans (hw 3 75)
  · exact (link0_334 w).symm.trans (hw 3 76)
  · exact (link0_335 w).symm.trans (hw 3 77)
  · exact (link0_336 w).symm.trans (hw 3 78)
  · exact (link0_337 w).symm.trans (hw 3 79)
  · exact (link0_338 w).symm.trans (hw 3 80)
  · exact (link0_339 w).symm.trans (hw 3 81)
  · exact (link0_340 w).symm.trans (hw 3 82)
  · exact (link0_341 w).symm.trans (hw 3 83)
  · exact (link0_342 w).symm.trans (hw 3 84)
  · exact (link0_343 w).symm.trans (hw 3 85)

#print axioms kernel_zero
end SmallLevelTwentyEightJetBlock
end
end

/-! ## TwentyEightGridSourceTaylor -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightGrid
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct SmallLevelAdditive Complex Set
open SmallLevelTwentyEightGenerators (W)
open scoped MatrixGroups ModularForm

def gridSourceRate (i : Fin 10) (j : ℝ) : ℝ :=
  (((gridSourceRaw i) 1 0:ℝ)*j+((gridSourceRaw i) 1 1:ℝ))^2/(gridSourceDet i)

def gridSourceDerivative (i : Fin 10) (j : ℝ) : ℝ :=
  ((gridSourceRaw i) 1 0:ℝ)*(((gridSourceRaw i) 1 0:ℝ)*j+((gridSourceRaw i) 1 1:ℝ))/(gridSourceDet i)

def gridSourcePartner (i : Fin 10) (j : ℝ) : ℝ :=
  (((gridSourceRaw i) 0 0:ℝ)*j+((gridSourceRaw i) 0 1:ℝ))/
    (((gridSourceRaw i) 1 0:ℝ)*j+((gridSourceRaw i) 1 1:ℝ))

/-- The nine non-affine raw-matrix system, with a prescribed original Fricke sign.
The sign can consequently be shared with the Ramanujan Taylor system. -/
theorem grid_source_taylor_of_fricke (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 28 (2*m) f)
    {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (i : Fin 10) (hi : i≠9) (j : ℝ)
    (hj : ((gridSourceRaw i) 1 0:ℝ)*j+((gridSourceRaw i) 1 1:ℝ)≠0) :
    ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        original (2*m) f j s-gridSourceSign η i*
          (gridSourceRate i j:ℂ)^(s-(m:ℂ))*
          (∑ n∈Finset.range M, (Complex.I*(gridSourceDerivative i j:ℂ))^n*
            Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
            original (2*m) f (gridSourcePartner i j) (s+(n:ℂ))) = error M s := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  have hw:=grid_words_of_fricke m hf hη hW
  have hF:=grid_source_fourier
    (gridWordSign_unit hη (gridSourceWord i))
    (hw (gridSourceWord i))
  simp only [gridSource_sign] at hF
  have hC : ((gridSourceRaw i) 1 0:ℝ)≠0 := by
    fin_cases i <;> first | exact (hi rfl).elim | norm_num [gridSourceRaw]
  have hd : ((gridSourceRaw i) 0 0:ℝ)*((gridSourceRaw i) 1 1:ℝ)-
      ((gridSourceRaw i) 0 1:ℝ)*((gridSourceRaw i) 1 0:ℝ)=(gridSourceDet i:ℝ) := by
    have hh:=gridSourceRaw_det i
    rw [det_fin_two] at hh
    exact_mod_cast hh
  have hh:=QuantitativeArithmeticTwoSequenceTaylor.matrix_even_rows
    (polynomial_bound hf.zero hg (2*m)) (fullCoefficients_zero hf.zero (2*m)) m
    ((gridSourceRaw i) 0 0) ((gridSourceRaw i) 0 1) ((gridSourceRaw i) 1 0)
    ((gridSourceRaw i) 1 1) j hC (by rw [hd]; exact_mod_cast gridSourceDet_pos i) hj
    (gridSourceSign η i) (by
      intro z hz
      simpa only [hd,Complex.ofReal_natCast,Complex.ofReal_intCast,gridSourceSign] using hF z hz)
  simpa only [hd,gridSourceRate,gridSourceDerivative,gridSourcePartner,original] using hh

/-- Every selected matrix row comes from the original Euler solution;
there is no continuation hypothesis on any additive twist. -/
theorem original_grid_source_taylor (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 28 (2*m) f) :
    ∃ η : ℂ, (η=1 ∨ η= -1) ∧ ∀ i : Fin 10, i≠9 → ∀ j : ℝ,
      ((gridSourceRaw i) 1 0:ℝ)*j+((gridSourceRaw i) 1 1:ℝ)≠0 →
      ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
        AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, bound<s.re →
          original (2*m) f j s-gridSourceSign η i*
            (gridSourceRate i j:ℂ)^(s-(m:ℂ))*
            (∑ n∈Finset.range M, (Complex.I*(gridSourceDerivative i j:ℂ))^n*
              Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
              original (2*m) f (gridSourcePartner i j) (s+(n:ℂ))) = error M s := by
  obtain ⟨η,hη,hW⟩:=original_fricke_sign (by decide : 0<28) m hf
  exact ⟨η,hη,fun i hi j hj => grid_source_taylor_of_fricke m hf hη hW i hi j hj⟩

#print axioms grid_source_taylor_of_fricke
#print axioms original_grid_source_taylor
end SmallLevelTwentyEightGrid
end
end

/-! ## TwentyEightGridGeometry -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightGrid
open Matrix SmallLevelAdditive

def gridGroupSource : Fin 46→Fin 10
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 3
  | 8 => 3
  | 9 => 3
  | 10 => 3
  | 11 => 3
  | 12 => 3
  | 13 => 3
  | 14 => 3
  | 15 => 3
  | 16 => 3
  | 17 => 3
  | 18 => 3
  | 19 => 4
  | 20 => 4
  | 21 => 4
  | 22 => 4
  | 23 => 4
  | 24 => 4
  | 25 => 4
  | 26 => 4
  | 27 => 4
  | 28 => 4
  | 29 => 4
  | 30 => 4
  | 31 => 4
  | 32 => 4
  | 33 => 4
  | 34 => 4
  | 35 => 4
  | 36 => 4
  | 37 => 4
  | 38 => 4
  | 39 => 5
  | 40 => 6
  | 41 => 7
  | 42 => 7
  | 43 => 7
  | 44 => 7
  | _ => 8

def gridGroupIndex : Fin 46→Fin 84
  | 0 => 0
  | 1 => 0
  | 2 => 42
  | 3 => 0
  | 4 => 21
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | 8 => 4
  | 9 => 6
  | 10 => 7
  | 11 => 9
  | 12 => 12
  | 13 => 14
  | 14 => 18
  | 15 => 21
  | 16 => 28
  | 17 => 36
  | 18 => 63
  | 19 => 6
  | 20 => 14
  | 21 => 24
  | 22 => 28
  | 23 => 30
  | 24 => 33
  | 25 => 35
  | 26 => 36
  | 27 => 38
  | 28 => 39
  | 29 => 40
  | 30 => 41
  | 31 => 43
  | 32 => 44
  | 33 => 45
  | 34 => 46
  | 35 => 49
  | 36 => 51
  | 37 => 54
  | 38 => 60
  | 39 => 83
  | 40 => 54
  | 41 => 60
  | 42 => 69
  | 43 => 74
  | 44 => 76
  | _ => 5

def gridGroupPartner : Fin 46→ℤ
  | 0 => -2
  | 1 => -3
  | 2 => -2
  | 3 => -6
  | 4 => -4
  | 5 => -252
  | 6 => -126
  | 7 => -84
  | 8 => -63
  | 9 => -42
  | 10 => -36
  | 11 => -28
  | 12 => -21
  | 13 => -18
  | 14 => -14
  | 15 => -12
  | 16 => -9
  | 17 => -7
  | 18 => -4
  | 19 => 7
  | 20 => 9
  | 21 => 14
  | 22 => 18
  | 23 => 21
  | 24 => 28
  | 25 => 36
  | 26 => 42
  | 27 => 63
  | 28 => 84
  | 29 => 126
  | 30 => 252
  | 31 => -252
  | 32 => -126
  | 33 => -84
  | 34 => -63
  | 35 => -36
  | 36 => -28
  | 37 => -21
  | 38 => -14
  | 39 => 252
  | 40 => -5
  | 41 => 8
  | 42 => 10
  | 43 => 15
  | 44 => 24
  | _ => 30

def gridGroupTarget : Fin 46→Fin 84
  | 0 => 82
  | 1 => 81
  | 2 => 82
  | 3 => 78
  | 4 => 80
  | 5 => 0
  | 6 => 42
  | 7 => 0
  | 8 => 21
  | 9 => 42
  | 10 => 48
  | 11 => 56
  | 12 => 63
  | 13 => 66
  | 14 => 70
  | 15 => 72
  | 16 => 75
  | 17 => 77
  | 18 => 80
  | 19 => 7
  | 20 => 9
  | 21 => 14
  | 22 => 18
  | 23 => 21
  | 24 => 28
  | 25 => 36
  | 26 => 42
  | 27 => 63
  | 28 => 0
  | 29 => 42
  | 30 => 0
  | 31 => 0
  | 32 => 42
  | 33 => 0
  | 34 => 21
  | 35 => 48
  | 36 => 56
  | 37 => 63
  | 38 => 70
  | 39 => 0
  | 40 => 79
  | 41 => 8
  | 42 => 10
  | 43 => 15
  | 44 => 24
  | _ => 30

def gridGroupRate : Fin 46→ℚ
  | 0 => 63
  | 1 => 28
  | 2 => 63
  | 3 => 7
  | 4 => (63/4)
  | 5 => (1/252)
  | 6 => (1/63)
  | 7 => (1/28)
  | 8 => (4/63)
  | 9 => (1/7)
  | 10 => (7/36)
  | 11 => (9/28)
  | 12 => (4/7)
  | 13 => (7/9)
  | 14 => (9/7)
  | 15 => (7/4)
  | 16 => (28/9)
  | 17 => (36/7)
  | 18 => (63/4)
  | 19 => (36/7)
  | 20 => (28/9)
  | 21 => (9/7)
  | 22 => (7/9)
  | 23 => (4/7)
  | 24 => (9/28)
  | 25 => (7/36)
  | 26 => (1/7)
  | 27 => (4/63)
  | 28 => (1/28)
  | 29 => (1/63)
  | 30 => (1/252)
  | 31 => (1/252)
  | 32 => (1/63)
  | 33 => (1/28)
  | 34 => (4/63)
  | 35 => (7/36)
  | 36 => (9/28)
  | 37 => (4/7)
  | 38 => (9/7)
  | 39 => (1/252)
  | 40 => 36
  | 41 => 9
  | 42 => (9/4)
  | 43 => (4/9)
  | 44 => (1/9)
  | _ => (1/36)

def gridGroupDerivative : Fin 46→ℚ
  | 0 => 42
  | 1 => 28
  | 2 => 42
  | 3 => 14
  | 4 => 21
  | 5 => (1/3)
  | 6 => (2/3)
  | 7 => 1
  | 8 => (4/3)
  | 9 => 2
  | 10 => (7/3)
  | 11 => 3
  | 12 => 4
  | 13 => (14/3)
  | 14 => 6
  | 15 => 7
  | 16 => (28/3)
  | 17 => 12
  | 18 => 21
  | 19 => -12
  | 20 => (-28/3)
  | 21 => -6
  | 22 => (-14/3)
  | 23 => -4
  | 24 => -3
  | 25 => (-7/3)
  | 26 => -2
  | 27 => (-4/3)
  | 28 => -1
  | 29 => (-2/3)
  | 30 => (-1/3)
  | 31 => (1/3)
  | 32 => (2/3)
  | 33 => 1
  | 34 => (4/3)
  | 35 => (7/3)
  | 36 => 3
  | 37 => 4
  | 38 => 6
  | 39 => (-1/3)
  | 40 => -84
  | 41 => -42
  | 42 => -21
  | 43 => (-28/3)
  | 44 => (-14/3)
  | _ => (-7/3)

def gridGroupCertificateRow : Fin 46→Fin 86
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 6
  | 6 => 7
  | 7 => 8
  | 8 => 9
  | 9 => 10
  | 10 => 11
  | 11 => 12
  | 12 => 13
  | 13 => 14
  | 14 => 15
  | 15 => 16
  | 16 => 17
  | 17 => 18
  | 18 => 19
  | 19 => 20
  | 20 => 21
  | 21 => 22
  | 22 => 23
  | 23 => 24
  | 24 => 25
  | 25 => 26
  | 26 => 27
  | 27 => 28
  | 28 => 29
  | 29 => 30
  | 30 => 31
  | 31 => 32
  | 32 => 33
  | 33 => 34
  | 34 => 35
  | 35 => 36
  | 36 => 37
  | 37 => 38
  | 38 => 39
  | 39 => 40
  | 40 => 41
  | 41 => 42
  | 42 => 43
  | 43 => 44
  | 44 => 45
  | _ => 46

theorem gridGroup_source_nonaffine (i : Fin 46) : gridGroupSource i≠9 := by
  fin_cases i <;> decide

theorem gridGroup_geometry (i : Fin 46) :
    ((gridSourceRaw (gridGroupSource i)) 1 0:ℝ)*((gridGroupIndex i:ℕ):ℝ)/84+
      ((gridSourceRaw (gridGroupSource i)) 1 1:ℝ)≠0 ∧
    gridSourcePartner (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/84)=
      (gridGroupPartner i:ℝ)/84 ∧
    gridSourceRate (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/84)=(gridGroupRate i:ℝ) ∧
    gridSourceDerivative (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/84)=(gridGroupDerivative i:ℝ) := by
  fin_cases i <;> norm_num [gridGroupSource,gridGroupIndex,gridGroupPartner,
    gridGroupRate,gridGroupDerivative,gridSourcePartner,gridSourceRate,gridSourceDerivative,
    gridSourceRaw,gridSourceDet]

theorem gridGroup_target_mod (i : Fin 46) :
    gridGroupPartner i%84=((gridGroupTarget i:ℕ):ℤ) := by
  fin_cases i <;> decide

theorem gridGroup_rate_pos (i : Fin 46) : 0<gridGroupRate i := by
  fin_cases i <;> norm_num [gridGroupRate]

theorem gridGroup_partner_transform (k : ℕ) (f : ℕ→ℂ) (i : Fin 46) (s : ℂ) :
    original k f (gridSourcePartner (gridGroupSource i) (((gridGroupIndex i:ℕ):ℝ)/84)) s=
      grid k f 84 ((gridGroupTarget i:ℕ):ℤ) s := by
  rw [(gridGroup_geometry i).2.1]
  change grid k f 84 (gridGroupPartner i) s=_
  rw [← grid_mod k f (by decide : 0<84)]
  norm_num only [Nat.cast_ofNat]
  rw [gridGroup_target_mod]

#print axioms gridGroup_geometry
#print axioms gridGroup_partner_transform
end SmallLevelTwentyEightGrid
end
end

/-! ## TwentyEightGridMatrixRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightGrid
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessNormalizedTwistProduct
open SmallLevelAdditive Complex Set
open SmallLevelTwentyEightGenerators (W)
open scoped MatrixGroups ModularForm

def gridMatrixScalar (m : ℕ) (η : ℂ) (i : Fin 46) (n : ℕ) (s : ℂ) : ℂ :=
  gridSourceSign η (gridGroupSource i)*(gridGroupRate i:ℂ)^(s-(m:ℂ))*
    (Complex.I*(gridGroupDerivative i:ℂ))^n*
    Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

/-- The 46 selected matrix rows of the actual closed 84-grid system.
The leading term and every positive shift use the same grid coordinate. -/
theorem grid_matrix_rows_of_fricke (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 28 (2*m) f)
    {η : ℂ} (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (i : Fin 46) :
    ∃ (bound : ℝ) (error : ℕ→ℂ→ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        grid (2*m) f 84 ((gridGroupIndex i:ℕ):ℤ) s-
          gridMatrixScalar m η i 0 s*
            grid (2*m) f 84 ((gridGroupTarget i:ℕ):ℤ) s=
        error M s+∑ n∈Finset.range M,gridMatrixScalar m η i (n+1) s*
          grid (2*m) f 84 ((gridGroupTarget i:ℕ):ℤ) (s+((n:ℂ)+1)) := by
  obtain ⟨B,error,hrows⟩:=grid_source_taylor_of_fricke m hf hη hW
    (gridGroupSource i) (gridGroup_source_nonaffine i) (((gridGroupIndex i:ℕ):ℝ)/84) (by
      simpa only [mul_div_assoc] using (gridGroup_geometry i).1)
  refine ⟨B,fun M => error (M+1),?_⟩
  intro M
  refine ⟨?_,?_⟩
  · simpa only [Nat.cast_add,Nat.cast_one] using (hrows (M+1)).1
  intro s hs
  have hh:=(hrows (M+1)).2 s hs
  simp_rw [gridGroup_partner_transform] at hh
  rw [(gridGroup_geometry i).2.2.1,(gridGroup_geometry i).2.2.2,
    Finset.sum_range_succ'] at hh
  simp only [Complex.ofReal_ratCast,Nat.cast_zero,add_zero,pow_zero,
    Ring.choose_zero_right,one_mul,Nat.cast_add,Nat.cast_one] at hh
  simp only [gridMatrixScalar,Nat.cast_zero,add_zero,pow_zero,
    Ring.choose_zero_right,mul_one,Nat.cast_add,Nat.cast_one]
  rw [mul_add,Finset.mul_sum] at hh
  simp only [← mul_assoc] at hh
  simp only [grid,Int.cast_natCast,Nat.cast_ofNat] at hh ⊢
  linear_combination hh

/-- The chosen 35 matrix rows hold for original solutions, with a single
sign and with no assumptions on any additive continuation. -/
theorem original_grid_matrix_rows (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 28 (2*m) f) :
    ∃ η : ℂ, (η=1 ∨ η= -1) ∧ ∀ i : Fin 46,
    ∃ (bound : ℝ) (error : ℕ→ℂ→ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | bound-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, bound<s.re →
        grid (2*m) f 84 ((gridGroupIndex i:ℕ):ℤ) s-
          gridMatrixScalar m η i 0 s*
            grid (2*m) f 84 ((gridGroupTarget i:ℕ):ℤ) s=
        error M s+∑ n∈Finset.range M,gridMatrixScalar m η i (n+1) s*
          grid (2*m) f 84 ((gridGroupTarget i:ℕ):ℤ) (s+((n:ℂ)+1)) := by
  obtain ⟨η,hη,hW⟩:=original_fricke_sign (by decide : 0<28) m hf
  exact ⟨η,hη,grid_matrix_rows_of_fricke m hf hη hW⟩

#print axioms grid_matrix_rows_of_fricke
#print axioms original_grid_matrix_rows
end SmallLevelTwentyEightGrid
end
end

/-! ## TwentyEightGridCoherentFricke -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightGrid
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
open FinitenessNormalizedTwistProduct FinitenessRamanujanFourier
open SmallLevelAdditive SmallLevelTaylor Complex Set MeasureTheory
open SmallLevelTwentyEightGenerators (W)
open scoped MatrixGroups ModularForm

/-- Literal coherent physical laws, supplied for every original solution. -/
def GridFrickeLaws (k : ℕ) (f : ℕ→ℂ) (ε : ℂ) : Prop :=
  ∀ q : ℕ, 0<q → ∀ z : ℂ, 0<z.im →
    FinitenessAnalyticReconstruction.twist (fourier (fullCoefficients f k)) q z=
      (root 28 f q*ε*Complex.I^k)/(((Real.sqrt (Nat.lcm 28 (q^2)):ℂ)*z)^k)*
        FinitenessAnalyticReconstruction.twist (fourier (fullCoefficients f k)) q
          (-1/((Nat.lcm 28 (q^2):ℕ)*z))

theorem original_grid_fricke_laws {k : ℕ} {f : ℕ→ℂ} (hf : IsSolution 28 k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ GridFrickeLaws k f ε :=
  FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<28) hf

theorem grid_physical_sign (m : ℕ) {ε : ℂ} (hε : ε=1 ∨ ε= -1) :
    ε*Complex.I^(2*m)=1 ∨ ε*Complex.I^(2*m)= -1 := by
  have hi : Complex.I^(2*m)=(-1:ℂ)^m := by rw [pow_mul,Complex.I_sq]
  rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hε with rfl|rfl <;> simp [hi,h]

theorem grid_fricke_of_laws (m : ℕ) {f : ℕ→ℂ} {ε : ℂ}
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      (ε*Complex.I^(2*m)) • SmallLevelOriginal.fourierFunction (2*m) f := by
  have h:=fricke_law 28 (2*m) (by decide)
    (fourier (fullCoefficients f (2*m))) (ε*Complex.I^(2*m)) (by
      intro z hz
      simpa [root,FinitenessAnalyticReconstruction.twist,Finset.sum_range_succ] using hlaw 1 (by decide) z hz)
  change SmallLevelOriginal.fourierFunction (2*m) f=(ε*Complex.I^(2*m)) •
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W) at h
  rcases grid_physical_sign m hε with hc|hc
  · rw [hc] at h ⊢; simpa using h.symm
  · rw [hc] at h ⊢
    simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg h.symm

/-- All-order Ramanujan Taylor rows retain the explicitly supplied coherent
sign, so their sign cannot be chosen independently of the matrix rows. -/
theorem grid_twisted_taylor_of_laws (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 28 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) (q : ℕ) (hq : 0<q) (r : ℝ) (hr : r≠0) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
        (Nat.lcm 28 (q^2)) r (root 28 f q*ε*Complex.I^(2*m)) M))
        {s : ℂ | B-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        transform (fullCoefficients (twisted f q) (2*m)) r s-
          (root 28 f q*ε*Complex.I^(2*m))*
            (((Nat.lcm 28 (q^2):ℝ)*r^2:ℝ):ℂ)^(s-(((2*m:ℕ):ℂ)/2))*
            normalizedTaylorSum (2*m) (fullCoefficients (twisted f q) (2*m))
              (Nat.lcm 28 (q^2)) r M s=
          mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
            (Nat.lcm 28 (q^2)) r (root 28 f q*ε*Complex.I^(2*m)) M) s := by
  obtain ⟨τ,_,hg⟩:=hf.growth
  have hL : 0<Nat.lcm 28 (q^2):=Nat.lcm_pos (by decide) (pow_pos hq _)
  apply normalized_taylor_mellin_rows (by exact_mod_cast hL) hr (2*m) (even_two_mul m)
    (polynomial_bound (twisted_zero hf.zero q) (twisted_growth hg q) (2*m))
    (fullCoefficients_zero (twisted_zero hf.zero q) (2*m)) (root 28 f q*ε*Complex.I^(2*m))
  intro z hz
  have hreflect : 0<(-1/((Nat.lcm 28 (q^2):ℕ)*z)).im := by
    simpa only [Complex.ofReal_natCast] using FinitenessComplexGeometry.reflected_im_pos
      (L := (Nat.lcm 28 (q^2):ℝ)) (by exact_mod_cast hL) hz
  simpa only [Complex.ofReal_natCast,fourier_twisted hf.zero hg q (2*m) hz,
    fourier_twisted hf.zero hg q (2*m) hreflect] using hlaw q hq z hz

theorem grid_ramanujan_taylor_of_laws (m : ℕ) {f : ℕ→ℂ} (hf : IsSolution 28 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) (q : ℕ) (hq : 0<q) (r : ℝ) (hr : r≠0) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
        (Nat.lcm 28 (q^2)) r (root 28 f q*ε*Complex.I^(2*m)) M))
        {s : ℂ | B-(M:ℝ)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        ramanujanAdditive (2*m) f q r s-
          (root 28 f q*ε*Complex.I^(2*m))*
            (((Nat.lcm 28 (q^2):ℝ)*r^2:ℝ):ℂ)^(s-(((2*m:ℕ):ℂ)/2))*
            ramanujanTaylorSum (2*m) f q (Nat.lcm 28 (q^2)) r M s=
          mellin (frickeError (2*m) (fullCoefficients (twisted f q) (2*m))
            (Nat.lcm 28 (q^2)) r (root 28 f q*ε*Complex.I^(2*m)) M) s := by
  obtain ⟨B,hB⟩:=grid_twisted_taylor_of_laws m hf hlaw q hq r hr
  obtain ⟨C,hC⟩:=ramanujan_additive_sum hf q
  refine ⟨max B C,?_⟩
  intro M
  constructor
  · intro s hs
    apply (hB M).1 s
    change max B C-(M:ℝ)<s.re at hs
    change B-(M:ℝ)<s.re
    linarith [le_max_left B C]
  · intro s hs
    have hsB : B<s.re:=lt_of_le_of_lt (le_max_left _ _) hs
    have hsC : C<s.re:=lt_of_le_of_lt (le_max_right _ _) hs
    have hm:=(hB M).2 s hsB
    rw [hC r s hsC] at hm
    have he : normalizedTaylorSum (2*m) (fullCoefficients (twisted f q) (2*m))
        (Nat.lcm 28 (q^2)) r M s=ramanujanTaylorSum (2*m) f q (Nat.lcm 28 (q^2)) r M s := by
      unfold normalizedTaylorSum ramanujanTaylorSum ramanujanAdditive
      apply Finset.sum_congr rfl
      intro n _
      rw [hC _ (s+(n:ℂ)) (by
        simp only [Complex.add_re,Complex.natCast_re]
        exact lt_of_lt_of_le hsC (le_add_of_nonneg_right (Nat.cast_nonneg n)))]
    rw [he] at hm
    exact hm

#print axioms original_grid_fricke_laws
#print axioms grid_fricke_of_laws
#print axioms grid_ramanujan_taylor_of_laws
end SmallLevelTwentyEightGrid
end
end

/-! ## TwentyEightGridRamanujan -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightGrid
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalFourier FinitenessRamanujanFourier FinitenessNormalizedTwistProduct

def gridTaylorSpecs : Fin 10→ℕ×ℤ :=
  ![(3,1),(3,-1),(3,2),(3,-2),(3,4),(3,-4),(7,1),(7,-1),(7,2),(7,3)]
def gridTaylorQ (i : Fin 10) : ℕ := (gridTaylorSpecs i).1
def gridTaylorT (i : Fin 10) : ℤ := (gridTaylorSpecs i).2
def gridTaylorL (i : Fin 10) : ℕ := Nat.lcm 28 ((gridTaylorQ i)^2)
def gridTaylorD (i : Fin 10) : ℤ := (84:ℤ)^2/(gridTaylorL i:ℤ)
def gridTaylorPartner (i : Fin 10) : ℤ := -(gridTaylorD i/gridTaylorT i)

theorem gridTaylorSpecs_valid : ∀ i : Fin 10,
    0<gridTaylorQ i ∧ gridTaylorQ i∣84 ∧ gridTaylorT i≠0 ∧
      (gridTaylorL i:ℤ)*gridTaylorD i=(84:ℤ)^2 ∧ gridTaylorT i∣gridTaylorD i := by decide

def gridTaylorCoefficient (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 10) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar (2*m) (gridTaylorL i) ((gridTaylorT i:ℝ)/84)
    (root 28 f (gridTaylorQ i)*ε*I^(2*m)) n s

def gridTaylorError (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 10) (M : ℕ) (s : ℂ) : ℂ :=
  mellin (frickeError (2*m) (fullCoefficients (twisted f (gridTaylorQ i)) (2*m))
    (gridTaylorL i) ((gridTaylorT i:ℝ)/84) (root 28 f (gridTaylorQ i)*ε*I^(2*m)) (M+1)) s

theorem grid_ramanujan_rows_of_laws (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) (i : Fin 10) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (gridTaylorError m f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridSum (2*m) f 84 (gridTaylorQ i) (gridTaylorT i) s-
          gridTaylorCoefficient m f ε i 0 s*
            gridSum (2*m) f 84 (gridTaylorQ i) (gridTaylorPartner i) s=
        gridTaylorError m f ε i M s+
          ∑ n∈Finset.range M,gridTaylorCoefficient m f ε i (n+1) s*
            gridSum (2*m) f 84 (gridTaylorQ i) (gridTaylorPartner i) (s+((n:ℂ)+1)) := by
  have hv:=gridTaylorSpecs_valid i
  have hr : (gridTaylorT i:ℝ)/84≠0:=div_ne_zero (by exact_mod_cast hv.2.2.1) (by norm_num)
  have hL : 0<gridTaylorL i:=Nat.lcm_pos (by decide) (pow_pos hv.1 _)
  obtain ⟨B,hB⟩:=grid_ramanujan_taylor_of_laws m hf hlaw (gridTaylorQ i) hv.1 _ hr
  refine ⟨B,?_⟩
  intro M
  constructor
  · intro s hs
    unfold gridTaylorError gridTaylorL
    apply (hB (M+1)).1 s
    change B-((M+1:ℕ):ℝ)<s.re
    change B-((M:ℝ)+1)<s.re at hs
    simpa only [Nat.cast_add,Nat.cast_one] using hs
  · intro s hs
    have hm:=(hB (M+1)).2 s hs
    rw [ramanujanTaylorSum_split] at hm
    rw [show Nat.lcm 28 ((gridTaylorQ i)^2)=gridTaylorL i from rfl] at hm
    have htrans:=ramanujanAdditive_grid (2*m) f (by decide : 0<84) hv.1 hv.2.1 (gridTaylorT i) s
    norm_num only [Nat.cast_ofNat] at htrans
    rw [htrans] at hm
    have hp:=fricke_grid_partner (by decide : 0<84) hL hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2
    norm_num only [Nat.cast_ofNat] at hp
    rw [hp] at hm
    have hgrid (t : ℤ) (w : ℂ) :
        ramanujanAdditive (2*m) f (gridTaylorQ i) ((t:ℝ)/84) w=
          ∑ j∈FinitenessRamanujanSum.residues (gridTaylorQ i),
            grid (2*m) f 84 (t+(j:ℤ)*(84/gridTaylorQ i:ℕ)) w := by
      simpa only [Nat.cast_ofNat] using
        ramanujanAdditive_grid (2*m) f (by decide : 0<84) hv.1 hv.2.1 t w
    simp_rw [hgrid] at hm
    simp only [Nat.cast_add,Nat.cast_one] at hm
    unfold gridTaylorCoefficient gridTaylorError gridTaylorPartner gridSum
    linear_combination hm

/-- All ten Ramanujan rows share a half-plane and the specified sign. -/
theorem grid_ramanujan_system_of_laws (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f)
    {ε : ℂ} (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ, ∀ i : Fin 10, ∀ M : ℕ,
      AnalyticOnNhd ℂ (gridTaylorError m f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridSum (2*m) f 84 (gridTaylorQ i) (gridTaylorT i) s-
          gridTaylorCoefficient m f ε i 0 s*
            gridSum (2*m) f 84 (gridTaylorQ i) (gridTaylorPartner i) s=
        gridTaylorError m f ε i M s+
          ∑ n∈Finset.range M,gridTaylorCoefficient m f ε i (n+1) s*
            gridSum (2*m) f 84 (gridTaylorQ i) (gridTaylorPartner i) (s+((n:ℂ)+1)) := by
  choose b hb using grid_ramanujan_rows_of_laws m hf hlaw
  let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbB (i : Fin 10) : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
  refine ⟨B,?_⟩
  intro i M
  constructor
  · intro s hs
    apply (hb i M).1 s
    change B-((M:ℝ)+1)<s.re at hs
    change b i-((M:ℝ)+1)<s.re
    linarith [hbB i]
  · intro s hs
    exact (hb i M).2 s (lt_of_le_of_lt (hbB i) hs)

#print axioms gridTaylorSpecs_valid
#print axioms grid_ramanujan_rows_of_laws
#print axioms grid_ramanujan_system_of_laws
end SmallLevelTwentyEightGrid
end
end

/-! ## TwentyEightParameters -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightParameters
open Complex FinitenessNormalizedTwistProduct SmallLevelTwentyEightGrid

def sigmaSeven (f : ℕ→ℂ) : ℂ := (Real.sqrt 7:ℂ)*f 7
def phase (m : ℕ) (ε : ℂ) : ℂ := ε*I^(2*m)

theorem root_three (f : ℕ→ℂ) : root 28 f 3=1 := by
  norm_num [root,FinitenessNormalizedTwistLocal.sign]

theorem root_seven (f : ℕ→ℂ) : root 28 f 7= -sigmaSeven f := by
  norm_num [root,FinitenessNormalizedTwistLocal.sign,sigmaSeven]
  ring

theorem sigmaSeven_sign {f : ℕ→ℂ} (hf : FinitenessOriginalInput.EulerData 28 f) :
    sigmaSeven f=1 ∨ sigmaSeven f= -1 := by
  have h:=root_unit hf 7
  rw [root_seven] at h
  rcases h with h|h
  · right; linear_combination -h
  · left; linear_combination -h

theorem phase_sign (m : ℕ) {ε : ℂ} (hε : ε=1 ∨ ε= -1) :
    phase m ε=1 ∨ phase m ε= -1 := grid_physical_sign m hε

#print axioms root_three
#print axioms root_seven
#print axioms sigmaSeven_sign
#print axioms phase_sign
end SmallLevelTwentyEightParameters
end
end

/-! ## TwentyEightMode -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightLaurent
open QuantitativeArithmeticSmallLevelTwentyEight

theorem leading_mode (η σ X Y Z a : ℂ) (i : Fin 86) (hi : i≠82) :
    leadingRows η σ X Y Z a oddMode i=0 := by
  fin_cases i <;> first | exact (hi rfl).elim | norm_num [leadingRows,oddMode]

theorem positive_taylor_mode (η σ X Y Z : ℂ) (n : ℕ) (i : Fin 86) :
    positiveTaylorRows η σ X Y Z n oddMode i=0 := by
  fin_cases i <;> norm_num [positiveTaylorRows,oddMode]

#print axioms leading_mode
#print axioms positive_taylor_mode
end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightQuotientRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightLaurent
open QuantitativeArithmeticSmallLevelTwentyEight

theorem leadingRows_sub_smul (η σ X Y Z a c : ℂ) (v w : Fin 84→ℂ) (i : Fin 86) :
    leadingRows η σ X Y Z a (v-c • w) i=
      leadingRows η σ X Y Z a v i-c*leadingRows η σ X Y Z a w i := by
  fin_cases i <;> norm_num [leadingRows,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] <;> ring

theorem positiveTaylorRows_sub_smul (η σ X Y Z c : ℂ) (n : ℕ)
    (v w : Fin 84→ℂ) (i : Fin 86) :
    positiveTaylorRows η σ X Y Z n (v-c • w) i=
      positiveTaylorRows η σ X Y Z n v i-c*positiveTaylorRows η σ X Y Z n w i := by
  fin_cases i <;> norm_num [positiveTaylorRows,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] <;> ring

/-- The selected original leading rows descend to the quotient. The gauge
row is imposed separately and is not an original functional equation. -/
theorem leading_quotient (η σ X Y Z a : ℂ) (v : Fin 84→ℂ)
    (i : Fin 86) (hi : i≠82) :
    leadingRows η σ X Y Z a (quotientVector v) i=leadingRows η σ X Y Z a v i := by
  rw [quotientVector,leadingRows_sub_smul,leading_mode η σ X Y Z a i hi,mul_zero,sub_zero]

theorem positive_taylor_quotient (η σ X Y Z : ℂ) (n : ℕ) (v : Fin 84→ℂ) (i : Fin 86) :
    positiveTaylorRows η σ X Y Z n (quotientVector v) i=
      positiveTaylorRows η σ X Y Z n v i := by
  rw [quotientVector,positiveTaylorRows_sub_smul,positive_taylor_mode,mul_zero,sub_zero]

theorem leading_quotient_gauge (η σ X Y Z a : ℂ) (v : Fin 84→ℂ) :
    leadingRows η σ X Y Z a (quotientVector v) 82=0 := by
  simpa only [leadingRows,one_mul] using quotient_gauge v

#print axioms leading_quotient
#print axioms positive_taylor_quotient
#print axioms leading_quotient_gauge
end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightLaurentLinear -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightLaurent
open Matrix

theorem leadingRows_zero (η σ X Y Z a : ℂ) (i : Fin 86) :
    leadingRows η σ X Y Z a 0 i=0 := by
  simpa using leadingRows_sub_smul η σ X Y Z a 1 0 0 i

def leadingLinear (η σ X Y Z a : ℂ) : (Fin 84→ℂ) →ₗ[ℂ] (Fin 86→ℂ) where
  toFun:=leadingRows η σ X Y Z a
  map_add':=by
    intro v w
    funext i
    simpa using leadingRows_sub_smul η σ X Y Z a (-1) v w i
  map_smul':=by
    intro c w
    funext i
    simpa [leadingRows_zero] using leadingRows_sub_smul η σ X Y Z a (-c) 0 w i

theorem positiveTaylorRows_zero (η σ X Y Z : ℂ) (n : ℕ) (i : Fin 86) :
    positiveTaylorRows η σ X Y Z n 0 i=0 := by
  simpa using positiveTaylorRows_sub_smul η σ X Y Z 1 n 0 0 i

def positiveTaylorLinear (η σ X Y Z : ℂ) (n : ℕ) : (Fin 84→ℂ) →ₗ[ℂ] (Fin 86→ℂ) where
  toFun:=positiveTaylorRows η σ X Y Z n
  map_add':=by
    intro v w
    funext i
    simpa using positiveTaylorRows_sub_smul η σ X Y Z (-1) n v w i
  map_smul':=by
    intro c w
    funext i
    simpa [positiveTaylorRows_zero] using positiveTaylorRows_sub_smul η σ X Y Z (-c) n 0 w i

def leadingMatrix (η σ X Y Z a : ℂ) : Matrix (Fin 86) (Fin 84) ℂ :=
  (leadingLinear η σ X Y Z a).toMatrix'

def positiveTaylorMatrix (η σ X Y Z : ℂ) (n : ℕ) : Matrix (Fin 86) (Fin 84) ℂ :=
  (positiveTaylorLinear η σ X Y Z n).toMatrix'

theorem leadingMatrix_mulVec (η σ X Y Z a : ℂ) (w : Fin 84→ℂ) :
    leadingMatrix η σ X Y Z a *ᵥ w=leadingRows η σ X Y Z a w := LinearMap.toMatrix'_mulVec _ _

theorem positiveTaylorMatrix_mulVec (η σ X Y Z : ℂ) (n : ℕ) (w : Fin 84→ℂ) :
    positiveTaylorMatrix η σ X Y Z n *ᵥ w=positiveTaylorRows η σ X Y Z n w := LinearMap.toMatrix'_mulVec _ _

#print axioms leadingMatrix_mulVec
#print axioms positiveTaylorMatrix_mulVec
end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightAnalyticRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightLaurent
open Complex Matrix SmallLevelPrimeRates

theorem leadingRows_analytic (m : ℕ) (η σ a : ℂ) (w : Fin 84→ℂ)
    (i : Fin 86) (z : ℂ) :
    AnalyticAt ℂ (fun s => leadingRows η σ (parameter 2 m s) (parameter 3 m s)
      (parameter 7 m s) a w i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 7 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 7 m (by decide) z
  fin_cases i <;> norm_num [leadingRows]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem positiveTaylorRows_analytic (m : ℕ) (η σ : ℂ) (n : ℕ)
    (w : Fin 84→ℂ) (i : Fin 86) (z : ℂ) :
    AnalyticAt ℂ (fun s => positiveTaylorRows η σ (parameter 2 m s) (parameter 3 m s)
      (parameter 7 m s) n w i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 7 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 7 m (by decide) z
  fin_cases i <;> norm_num [positiveTaylorRows]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem leadingMatrix_apply (η σ X Y Z a : ℂ) (i : Fin 86) (j : Fin 84) :
    leadingMatrix η σ X Y Z a i j=leadingRows η σ X Y Z a (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _

theorem positiveTaylorMatrix_apply (η σ X Y Z : ℂ) (n : ℕ) (i : Fin 86) (j : Fin 84) :
    positiveTaylorMatrix η σ X Y Z n i j=positiveTaylorRows η σ X Y Z n (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _

theorem leadingMatrix_analytic (m : ℕ) (η σ a : ℂ) (i : Fin 86) (j : Fin 84) (z : ℂ) :
    AnalyticAt ℂ (fun s => leadingMatrix η σ (parameter 2 m s) (parameter 3 m s)
      (parameter 7 m s) a i j) z := by
  simp_rw [leadingMatrix_apply]
  exact leadingRows_analytic m η σ a (Pi.single j 1) i z

theorem positiveTaylorMatrix_analytic (m : ℕ) (η σ : ℂ) (n : ℕ)
    (i : Fin 86) (j : Fin 84) (z : ℂ) :
    AnalyticAt ℂ (fun s => positiveTaylorMatrix η σ (parameter 2 m s) (parameter 3 m s)
      (parameter 7 m s) n i j) z := by
  simp_rw [positiveTaylorMatrix_apply]
  exact positiveTaylorRows_analytic m η σ n (Pi.single j 1) i z

#print axioms leadingMatrix_analytic
#print axioms positiveTaylorMatrix_analytic
end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightKernelCaseBundleV4 -/
section
set_option autoImplicit false
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightLaurent

theorem kernel_case0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    ∀ j,w j=pole0 X Y Z a j*w 66 :=
  SmallLevelTwentyEightTriangular.kernel_case0 X Y Z a hX hY hZ w hw

#print axioms kernel_case0

theorem kernel_case1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    ∀ j,w j=pole1 X Y Z a j*w 66 :=
  SmallLevelTwentyEightTriangular.kernel_case1 X Y Z a hX hY hZ w hw

#print axioms kernel_case1

theorem kernel_case2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    ∀ j,w j=pole2 X Y Z a j*w 66 :=
  SmallLevelTwentyEightTriangular.kernel_case2 X Y Z a hX hY hZ w hw

#print axioms kernel_case2

theorem kernel_case3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    ∀ j,w j=pole3 X Y Z a j*w 66 :=
  SmallLevelTwentyEightTriangular.kernel_case3 X Y Z a hX hY hZ w hw

#print axioms kernel_case3

end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightResidual -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightLaurent
open Complex

def residual (η u X Y Z a : ℂ) : ℂ :=
  ((1)/(2*X^2*Y^2) + ((-1)*Z^2)/(2*X^2*Y^2) + (3)/(X^2) + ((-1)*Y*a)/(X^2) + ((-1)*Y^2)/(X^2)) + η*(((-1)*Z)/(2*X^2*Y^2) + (1*Z*a)/(2*X^2*Y) + (1*Z)/(2*X^2)) + η*u*(((-1))/(2*X^2*Y^2) + (1*a)/(2*X^2*Y) + ((-3))/(2*X^2))

theorem residual_some_point (η u a : ℂ) (hη : η=1 ∨ η= -1) (hu : u=1 ∨ u= -1) :
    residual η u (1/2) (1/3) (1/7) a≠0 ∨ residual η u (1/4) (1/9) (1/49) a≠0 := by
  by_contra h
  push Not at h
  obtain ⟨ha,hb⟩:=h
  rcases hη with rfl|rfl <;> rcases hu with rfl|rfl
  · norm_num [residual] at ha hb
    have he : (1:ℂ)=0 := by
      linear_combination (2287467/4793800)*ha + (-5639949/153401600)*hb
    norm_num at he
  · norm_num [residual] at ha hb
    have he : (1:ℂ)=0 := by
      linear_combination (-18457173/1299544880)*ha + (3306177/2599089760)*hb
    norm_num at he
  · norm_num [residual] at ha hb
    have he : (1:ℂ)=0 := by
      linear_combination (-9603657/910431016)*ha + (8362683/7283448128)*hb
    norm_num at he
  · norm_num [residual] at ha hb
    have he : (1:ℂ)=0 := by
      linear_combination (3509919/19116064)*ha + (-194481/19116064)*hb
    norm_num at he

#print axioms residual_some_point
end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightResidualCaseBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightLaurent
open Complex

theorem residual_case0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    residual (-1) (-1) X Y Z a*w 66=0 := by
  have hk := kernel_case0 X Y Z a hX hY hZ w hw
  have hr := congrFun hw (83:Fin 84)
  change leadingRows (-1) (-1) X Y Z a w (83:Fin 86)=0 at hr
  norm_num [leadingRows] at hr
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 44,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65,hk 67,hk 68,hk 69,hk 70,hk 71,hk 72,hk 73,hk 74,hk 75,hk 76,hk 77,hk 78,hk 79,hk 80,hk 81,hk 82,hk 83] at hr
  norm_num only [pole0] at hr
  unfold residual
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) hr

theorem kernel_zero_case0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hd : residual (-1) (-1) X Y Z a≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) : w=0 := by
  have h66 : w 66=0 := (mul_eq_zero.mp (residual_case0 X Y Z a hX hY hZ w hw)).resolve_left hd
  funext j
  simpa only [h66,mul_zero,Pi.zero_apply] using kernel_case0 X Y Z a hX hY hZ w hw j

#print axioms residual_case0
#print axioms kernel_zero_case0

theorem residual_case1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    residual (-1) (1) X Y Z a*w 66=0 := by
  have hk := kernel_case1 X Y Z a hX hY hZ w hw
  have hr := congrFun hw (83:Fin 84)
  change leadingRows (-1) (1) X Y Z a w (83:Fin 86)=0 at hr
  norm_num [leadingRows] at hr
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 44,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65,hk 67,hk 68,hk 69,hk 70,hk 71,hk 72,hk 73,hk 74,hk 75,hk 76,hk 77,hk 78,hk 79,hk 80,hk 81,hk 82,hk 83] at hr
  norm_num only [pole1] at hr
  unfold residual
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) hr

theorem kernel_zero_case1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hd : residual (-1) (1) X Y Z a≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) : w=0 := by
  have h66 : w 66=0 := (mul_eq_zero.mp (residual_case1 X Y Z a hX hY hZ w hw)).resolve_left hd
  funext j
  simpa only [h66,mul_zero,Pi.zero_apply] using kernel_case1 X Y Z a hX hY hZ w hw j

#print axioms residual_case1
#print axioms kernel_zero_case1

theorem residual_case2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    residual (1) (-1) X Y Z a*w 66=0 := by
  have hk := kernel_case2 X Y Z a hX hY hZ w hw
  have hr := congrFun hw (83:Fin 84)
  change leadingRows (1) (-1) X Y Z a w (83:Fin 86)=0 at hr
  norm_num [leadingRows] at hr
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 44,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65,hk 67,hk 68,hk 69,hk 70,hk 71,hk 72,hk 73,hk 74,hk 75,hk 76,hk 77,hk 78,hk 79,hk 80,hk 81,hk 82,hk 83] at hr
  norm_num only [pole2] at hr
  unfold residual
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) hr

theorem kernel_zero_case2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hd : residual (1) (-1) X Y Z a≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) : w=0 := by
  have h66 : w 66=0 := (mul_eq_zero.mp (residual_case2 X Y Z a hX hY hZ w hw)).resolve_left hd
  funext j
  simpa only [h66,mul_zero,Pi.zero_apply] using kernel_case2 X Y Z a hX hY hZ w hw j

#print axioms residual_case2
#print axioms kernel_zero_case2

theorem residual_case3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    residual (1) (1) X Y Z a*w 66=0 := by
  have hk := kernel_case3 X Y Z a hX hY hZ w hw
  have hr := congrFun hw (83:Fin 84)
  change leadingRows (1) (1) X Y Z a w (83:Fin 86)=0 at hr
  norm_num [leadingRows] at hr
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 44,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65,hk 67,hk 68,hk 69,hk 70,hk 71,hk 72,hk 73,hk 74,hk 75,hk 76,hk 77,hk 78,hk 79,hk 80,hk 81,hk 82,hk 83] at hr
  norm_num only [pole3] at hr
  unfold residual
  linear_combination (norm := (field_simp [hX,hY,hZ]; all_goals ring)) hr

theorem kernel_zero_case3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (hd : residual (1) (1) X Y Z a≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) : w=0 := by
  have h66 : w 66=0 := (mul_eq_zero.mp (residual_case3 X Y Z a hX hY hZ w hw)).resolve_left hd
  funext j
  simpa only [h66,mul_zero,Pi.zero_apply] using kernel_case3 X Y Z a hX hY hZ w hw j

#print axioms residual_case3
#print axioms kernel_zero_case3

end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightKernelCertificates -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightLaurent
open Complex

theorem core_kernel_zero (η σ X Y Z a : ℂ)
    (hη : η=1 ∨ η= -1) (hσ : σ=1 ∨ σ= -1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hd : residual η σ X Y Z a≠0)
    (w : Fin 84→ℂ) (hw : coreRows η σ X Y Z a w=0) : w=0 := by
  rcases hη with rfl|rfl <;> rcases hσ with rfl|rfl
  · exact kernel_zero_case3 X Y Z a hX hY hZ hd w hw
  · exact kernel_zero_case2 X Y Z a hX hY hZ hd w hw
  · exact kernel_zero_case1 X Y Z a hX hY hZ hd w hw
  · exact kernel_zero_case0 X Y Z a hX hY hZ hd w hw

theorem core_kernel_coordinate_ne_zero (η σ X Y Z a : ℂ)
    (hη : η=1 ∨ η= -1) (hσ : σ=1 ∨ σ= -1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows η σ X Y Z a w=0) (hw0 : w≠0) : w 66≠0 := by
  intro h66
  apply hw0
  rcases hη with rfl|rfl <;> rcases hσ with rfl|rfl
  · funext j
    simpa only [h66,mul_zero,Pi.zero_apply] using kernel_case3 X Y Z a hX hY hZ w hw j
  · funext j
    simpa only [h66,mul_zero,Pi.zero_apply] using kernel_case2 X Y Z a hX hY hZ w hw j
  · funext j
    simpa only [h66,mul_zero,Pi.zero_apply] using kernel_case1 X Y Z a hX hY hZ w hw j
  · funext j
    simpa only [h66,mul_zero,Pi.zero_apply] using kernel_case0 X Y Z a hX hY hZ w hw j

theorem core_residual_zero (η σ X Y Z a : ℂ)
    (hη : η=1 ∨ η= -1) (hσ : σ=1 ∨ σ= -1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows η σ X Y Z a w=0) (hw0 : w≠0) :
    residual η σ X Y Z a=0 := by
  by_contra hd
  exact hw0 (core_kernel_zero η σ X Y Z a hη hσ hX hY hZ hd w hw)

#print axioms core_kernel_zero
#print axioms core_kernel_coordinate_ne_zero
#print axioms core_residual_zero
end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightNonsingular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightLaurent
open Complex Matrix SmallLevelPrimeRates

def coreMatrix (η σ X Y Z a : ℂ) : Matrix (Fin 84) (Fin 84) ℂ :=
  fun i j => leadingMatrix η σ X Y Z a ⟨i.val,by omega⟩ j

theorem coreMatrix_mulVec (η σ X Y Z a : ℂ) (w : Fin 84→ℂ) :
    coreMatrix η σ X Y Z a *ᵥ w=coreRows η σ X Y Z a w := by
  funext i
  exact congrFun (leadingMatrix_mulVec η σ X Y Z a w) ⟨i.val,by omega⟩

theorem coreMatrix_det_ne_zero (η σ X Y Z a : ℂ)
    (hη : η=1 ∨ η= -1) (hσ : σ=1 ∨ σ= -1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hd : residual η σ X Y Z a≠0) :
    (coreMatrix η σ X Y Z a).det≠0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro w v hw
  have hn : coreMatrix η σ X Y Z a *ᵥ (w-v)=0 := by
    rw [Matrix.mulVec_sub,hw,sub_self]
  rw [coreMatrix_mulVec] at hn
  exact sub_eq_zero.mp (core_kernel_zero η σ X Y Z a hη hσ hX hY hZ hd (w-v) hn)

theorem parameter_negative_integer (p m n : ℕ) :
    parameter p m ((m:ℂ)-(n:ℂ))=((p:ℂ)⁻¹)^n := by
  unfold parameter
  rw [show (m:ℂ)-(n:ℂ)-(m:ℂ)= -(n:ℂ) by ring,Complex.cpow_neg,
    Complex.cpow_natCast,inv_pow]

/-- The chosen square subsystem has a nonzero determinant somewhere for
all sign choices and every Hecke parameter, including zero. -/
theorem coreMatrix_nonsingular (m : ℕ) (η σ a : ℂ)
    (hη : η=1 ∨ η= -1) (hσ : σ=1 ∨ σ= -1) :
    ∃ s : ℂ, (coreMatrix η σ (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) a).det≠0 := by
  have hd:=residual_some_point η σ a hη hσ
  have hp (s : ℂ) (hs : residual η σ (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) a≠0) :
      (coreMatrix η σ (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) a).det≠0 :=
    coreMatrix_det_ne_zero η σ _ _ _ a hη hσ
      (parameter_ne_zero 2 m (by decide) s) (parameter_ne_zero 3 m (by decide) s)
      (parameter_ne_zero 7 m (by decide) s) hs
  rcases hd with hd|hd
  · refine ⟨(m:ℂ)-1,hp _ ?_⟩
    have h2:=parameter_negative_integer 2 m 1
    have h3:=parameter_negative_integer 3 m 1
    have h7:=parameter_negative_integer 7 m 1
    norm_num at h2 h3 h7
    rw [h2,h3,h7]
    exact hd
  · refine ⟨(m:ℂ)-2,hp _ ?_⟩
    have h2:=parameter_negative_integer 2 m 2
    have h3:=parameter_negative_integer 3 m 2
    have h7:=parameter_negative_integer 7 m 2
    norm_num at h2 h3 h7
    rw [h2,h3,h7]
    exact hd

#print axioms coreMatrix_det_ne_zero
#print axioms coreMatrix_nonsingular
end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightExtendedSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex Matrix SmallLevelPrimeRates SmallLevelTwentyEightParameters
open SmallLevelTwentyEightLaurent

def extendedLeading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : Matrix (Fin 86) (Fin 84) ℂ :=
  leadingMatrix (phase m ε) (sigmaSeven f) (parameter 2 m s) (parameter 3 m s)
    (parameter 7 m s) ((Real.sqrt 3:ℂ)*f 3)

def extendedShift (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin 86) (Fin 84) ℂ :=
  (I^(n+1)*Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1)) •
    positiveTaylorMatrix (phase m ε) (sigmaSeven f)
      (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) n

def coreLeading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) : Matrix (Fin 84) (Fin 84) ℂ :=
  coreMatrix (phase m ε) (sigmaSeven f) (parameter 2 m s) (parameter 3 m s)
    (parameter 7 m s) ((Real.sqrt 3:ℂ)*f 3)

def coreShift (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin 84) (Fin 84) ℂ :=
  fun i j => extendedShift m f ε n s ⟨i.val,by omega⟩ j

theorem extendedLeading_actual (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 84→ℂ) :
    extendedLeading m f ε s *ᵥ w=leadingRows (phase m ε) (sigmaSeven f)
      (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) ((Real.sqrt 3:ℂ)*f 3) w :=
  leadingMatrix_mulVec _ _ _ _ _ _ w

theorem extendedShift_actual (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (w : Fin 84→ℂ) (i : Fin 86) :
    (∑ j,extendedShift m f ε n s i j*w j)=
      (I^(n+1)*Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1))*
      positiveTaylorRows (phase m ε) (sigmaSeven f)
        (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) n w i := by
  change (extendedShift m f ε n s *ᵥ w) i=_
  rw [extendedShift,Matrix.smul_mulVec,positiveTaylorMatrix_mulVec]
  rfl

theorem extendedLeading_analytic (m : ℕ) (f : ℕ→ℂ) (ε x : ℂ) (i : Fin 86) (j : Fin 84) :
    AnalyticAt ℂ (fun s => extendedLeading m f ε s i j) x :=
  leadingMatrix_analytic m _ _ _ i j x

theorem extendedShift_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (x : ℂ)
    (i : Fin 86) (j : Fin 84) :
    AnalyticAt ℂ (fun s => extendedShift m f ε n s i j) x :=
  (analyticAt_const.mul (SmallLevelTaylor.binomial_shift_analytic (2*m) (n+1) x)).mul
    (positiveTaylorMatrix_analytic m _ _ n i j x)

theorem coreLeading_nonsingular {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (ε : ℂ) (hε : ε=1 ∨ ε= -1) :
    ∃ s : ℂ, (coreLeading m f ε s).det≠0 :=
  coreMatrix_nonsingular m _ _ _ (phase_sign m hε) (sigmaSeven_sign hf.toEulerData)

#print axioms extendedLeading_actual
#print axioms extendedShift_actual
#print axioms extendedLeading_analytic
#print axioms extendedShift_analytic
#print axioms coreLeading_nonsingular
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightJetBlockModel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightJetBlock
open Complex Matrix SmallLevelFiniteShift SmallLevelTwentyEightSystem
open SmallLevelTwentyEightParameters SmallLevelPrimeRates SmallLevelTwentyEightLaurent
open SmallLevelTwentyOneKnownWords (jetScale jetScale_binomial)

def scaledJetStack (m : ℕ) (w : Fin 336→ℂ) (b : Fin 4×Fin 84) : ℂ :=
  jetScale (1-(m:ℂ)) b.1*w (finProdFinEquiv b)

theorem parameter_candidate_lower (p m n : ℕ) (hp : p≠0) :
    parameter p m ((m:ℂ)+1-(n:ℂ))=(p:ℂ)/(p:ℂ)^n := by
  unfold parameter
  rw [show (m:ℂ)+1-(n:ℂ)-(m:ℂ)=1-(n:ℂ) by ring,
    Complex.cpow_sub _ _ (by exact_mod_cast hp),Complex.cpow_one,Complex.cpow_natCast]

theorem leading_apply_laurent (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 84→ℂ) (i : Fin 86) :
    (∑ j,extendedLeading m f ε s i j*w j)=
      leadingRows (phase m ε) (sigmaSeven f)
        (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) ((Real.sqrt 3:ℂ)*f 3) w i := by
  simpa only [Matrix.mulVec,dotProduct] using congrFun (extendedLeading_actual m f ε s w) i

theorem shift_apply_laurent (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (w : Fin 84→ℂ) (i : Fin 86) :
    (∑ j,extendedShift m f ε n s i j*w j)=
      (I^(n+1)*Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1))*
      positiveTaylorRows (phase m ε) (sigmaSeven f)
        (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) n w i :=
  extendedShift_actual m f ε n s w i

/-- Exact falling-factorial normalization of the four-point block at the
sole physical first-jet candidate. The identity itself allows every weight. -/
theorem actual_jetBlockRow (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (hη : phase m ε= -1) (hσ : sigmaSeven f= -1) (ha : (Real.sqrt 3:ℂ)*f 3= -10/3)
    (n : Fin 4) (r : Fin 86) (w : Fin 336→ℂ) :
    (∑ b,blockLeading 3 (extendedLeading m f ε) (extendedShift m f ε)
      ((m:ℂ)+1) (n,r) b*scaledJetStack m w b)=
        jetScale (1-(m:ℂ)) n*jetBlockRow n r w := by
  rw [blockLeading_apply]
  simp only [scaledJetStack,leading_apply_laurent,shift_apply_laurent,
    leadingRows_scale,positiveTaylorRows_scale,
    parameter_candidate_lower 2 m n.val (by decide),
    parameter_candidate_lower 3 m n.val (by decide),
    parameter_candidate_lower 7 m n.val (by decide),hη,hσ,ha,Nat.cast_ofNat]
  unfold jetBlockRow jetSlice
  rw [mul_sub,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha'
  have ha'' : a<n.val:=Finset.mem_range.mp ha'
  have he : (m:ℂ)+1-(n.val:ℂ)+((a+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=
      (1-(m:ℂ))-(n.val:ℂ)+((a+1:ℕ):ℂ) := by push_cast; ring
  rw [he,← mul_assoc,jetScale_binomial (1-(m:ℂ)) n a ha'']
  ring

#print axioms actual_jetBlockRow
end SmallLevelTwentyEightJetBlock
end
end

/-! ## TwentyEightActualBlockKernel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightJetBlock
open Complex Matrix SmallLevelFiniteShift SmallLevelTwentyEightSystem SmallLevelTwentyEightParameters
open SmallLevelTwentyOneKnownWords (jetScale jetScale_ne_zero)

/-- The literal four-point Mellin block is injective at the exceptional
parameters, at every even weight at least four. -/
theorem actual_block_kernel_zero (m : ℕ) (hm : 2≤m) (f : ℕ→ℂ) (ε : ℂ)
    (hη : phase m ε= -1) (hσ : sigmaSeven f= -1) (ha : (Real.sqrt 3:ℂ)*f 3= -10/3)
    (w : Fin 4×Fin 84→ℂ)
    (hw : ∀ r, ∑ b,blockLeading 3 (extendedLeading m f ε) (extendedShift m f ε)
      ((m:ℂ)+1) r b*w b=0) : w=0 := by
  let e : (Fin 4×Fin 84)≃Fin 336:=finProdFinEquiv
  let q : Fin 336→ℂ:=fun j => w (e.symm j)/jetScale (1-(m:ℂ)) (e.symm j).1
  have he : scaledJetStack m q=w := by
    funext b
    simp only [scaledJetStack,q,e,Equiv.symm_apply_apply]
    field_simp [jetScale_ne_zero m hm b.1]
  have hq (n : Fin 4) (i : Fin 86) : jetBlockRow n i q=0 := by
    have hh:=hw (n,i)
    rw [←he,actual_jetBlockRow m f ε hη hσ ha] at hh
    exact (mul_eq_zero.mp hh).resolve_left (jetScale_ne_zero m hm n)
  have hq0:=kernel_zero q hq
  rw [←he,hq0]
  funext b
  simp [scaledJetStack]

#print axioms actual_block_kernel_zero
end SmallLevelTwentyEightJetBlock
end
end

/-! ## TwentyEightSyzygyDataCaseBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightLaurent
open Complex

def rawJet0_0 (_X Y Z a : ℂ) : ℂ := ((-7)*Z)/(Y^2) + ((-7)*a)/(Y) + ((-7))/(3)

def jet0_0Indices : Fin 19→Fin 86 := ![0,2,4,5,10,11,12,13,15,16,19,20,21,22,23,27,39,67,84]
def jet0_0Coeff (X Y Z _a : ℂ) : Fin 19→ℂ := ![(((-2))/(Z)),(((-2))/(Z)),((1*X^2)/(Z)),((2)/(Z)),(1),(((-1)*X^2*Y^2)/(Z)),((-1)*X^2),((-1)),((-1)),(((-1)*X^2)/(Z)),((1*X^2)/(Z)),((-1)),(((-1)*Y^2)/(Z)),((-1)),(((-1)*Y^2)/(Z)),((-1)),((-1)),((1*Y^2)/(Z)),(1)]

def rawJet0_1 (_X Y Z a : ℂ) : ℂ := ((-84)*Z)/(Y^4) + ((-84)*a)/(Y^3) + ((-28)*Z)/(Y^2) + (56)/(3)

def jet0_1Indices : Fin 31→Fin 86 := ![9,10,11,12,15,16,19,20,21,22,23,24,26,27,30,33,36,38,39,53,56,60,65,67,70,71,72,73,77,80,85]
def jet0_1Coeff (X Y Z a : ℂ) : Fin 31→ℂ := ![(1),((1)/(Y^2) + 1),(((-1)*X^2)/(Z)),((1*X^2)/(Y^2) + (1*X^2*a)/(Y) + (-1)*X^2),((1)/(Y^2) + (-1)),(((-1)*X^2)/(Y^2*Z)),((1*X^2)/(Y^2*Z)),(((-1))/(Y^2)),((1)/(Z) + (1*Y*a)/(Z) + ((-1)*Y^2)/(Z)),((1*a)/(Y) + (-1)),((1)/(Z) + (1*Y*a)/(Z) + ((-1)*Y^2)/(Z)),(1),(((-1)*X^2)/(Z)),(((-1))/(Y^2) + (-1)),(1),(1),(((-1)*X^2)/(Z)),((1)/(Y^2) + 1),((-1)),(1),(1),(1),(1),(((-1))/(Z) + ((-1)*Y*a)/(Z) + (1*Y^2)/(Z)),((-1)),((-1)),(1),(1),((-1)),((-1)),(1)]

def rawJet1_0 (_X Y Z a : ℂ) : ℂ := (14)/(Y^2) + ((-7)*Z)/(Y^2) + ((-7)*a)/(Y) + ((-7))/(3)

def jet1_0Indices : Fin 19→Fin 86 := ![0,2,4,5,10,11,12,13,15,16,19,20,21,22,23,27,39,67,84]
def jet1_0Coeff (X Y Z _a : ℂ) : Fin 19→ℂ := ![(((-2))/(Z)),(((-2))/(Z)),((1*X^2)/(Z)),((2)/(Z)),(1),(((-1)*X^2*Y^2)/(Z)),((-1)*X^2),((-1)),((-1)),(((-1)*X^2)/(Z)),((1*X^2)/(Z)),((-1)),(((-1)*Y^2)/(Z)),((-1)),(((-1)*Y^2)/(Z)),((-1)),((-1)),((1*Y^2)/(Z)),(1)]

def rawJet1_1 (_X Y Z a : ℂ) : ℂ := (168)/(Y^4) + ((-84)*Z)/(Y^4) + ((-84)*a)/(Y^3) + (56)/(Y^2) + ((-28)*Z)/(Y^2) + (56)/(3)

def jet1_1Indices : Fin 31→Fin 86 := ![9,10,11,12,15,16,19,20,21,22,23,24,26,27,30,33,36,38,39,53,56,60,65,67,70,71,72,73,77,80,85]
def jet1_1Coeff (X Y Z a : ℂ) : Fin 31→ℂ := ![(1),((1)/(Y^2) + 1),(((-1)*X^2)/(Z)),((1*X^2)/(Y^2) + (1*X^2*a)/(Y) + (-1)*X^2),((1)/(Y^2) + (-1)),(((-1)*X^2)/(Y^2*Z)),((1*X^2)/(Y^2*Z)),(((-1))/(Y^2)),((1)/(Z) + (1*Y*a)/(Z) + ((-1)*Y^2)/(Z)),((1*a)/(Y) + (-1)),((1)/(Z) + (1*Y*a)/(Z) + ((-1)*Y^2)/(Z)),(1),(((-1)*X^2)/(Z)),(((-1))/(Y^2) + (-1)),(1),(1),(((-1)*X^2)/(Z)),((1)/(Y^2) + 1),((-1)),(1),(1),(1),(1),(((-1))/(Z) + ((-1)*Y*a)/(Z) + (1*Y^2)/(Z)),((-1)),((-1)),(1),(1),((-1)),((-1)),(1)]

def rawJet2_0 (_X Y Z a : ℂ) : ℂ := (14)/(Y^2) + (7*Z)/(Y^2) + ((-7)*a)/(Y) + ((-7))/(3)

def jet2_0Indices : Fin 19→Fin 86 := ![0,2,4,5,10,11,12,13,15,16,19,20,21,22,23,27,39,67,84]
def jet2_0Coeff (X Y Z _a : ℂ) : Fin 19→ℂ := ![((2)/(Z)),((2)/(Z)),(((-1)*X^2)/(Z)),(((-2))/(Z)),(1),((1*X^2*Y^2)/(Z)),((-1)*X^2),((-1)),((-1)),((1*X^2)/(Z)),(((-1)*X^2)/(Z)),((-1)),((1*Y^2)/(Z)),((-1)),((1*Y^2)/(Z)),((-1)),((-1)),(((-1)*Y^2)/(Z)),(1)]

def rawJet2_1 (_X Y Z a : ℂ) : ℂ := (168)/(Y^4) + (84*Z)/(Y^4) + ((-84)*a)/(Y^3) + (56)/(Y^2) + (28*Z)/(Y^2) + (56)/(3)

def jet2_1Indices : Fin 31→Fin 86 := ![9,10,11,12,15,16,19,20,21,22,23,24,26,27,30,33,36,38,39,53,56,60,65,67,70,71,72,73,77,80,85]
def jet2_1Coeff (X Y Z a : ℂ) : Fin 31→ℂ := ![(1),((1)/(Y^2) + 1),((1*X^2)/(Z)),((1*X^2)/(Y^2) + (1*X^2*a)/(Y) + (-1)*X^2),((1)/(Y^2) + (-1)),((1*X^2)/(Y^2*Z)),(((-1)*X^2)/(Y^2*Z)),(((-1))/(Y^2)),(((-1))/(Z) + ((-1)*Y*a)/(Z) + (1*Y^2)/(Z)),((1*a)/(Y) + (-1)),(((-1))/(Z) + ((-1)*Y*a)/(Z) + (1*Y^2)/(Z)),(1),((1*X^2)/(Z)),(((-1))/(Y^2) + (-1)),(1),(1),((1*X^2)/(Z)),((1)/(Y^2) + 1),((-1)),(1),(1),(1),(1),((1)/(Z) + (1*Y*a)/(Z) + ((-1)*Y^2)/(Z)),((-1)),((-1)),(1),(1),((-1)),((-1)),(1)]

def rawJet3_0 (_X Y Z a : ℂ) : ℂ := (7*Z)/(Y^2) + ((-7)*a)/(Y) + ((-7))/(3)

def jet3_0Indices : Fin 19→Fin 86 := ![0,2,4,5,10,11,12,13,15,16,19,20,21,22,23,27,39,67,84]
def jet3_0Coeff (X Y Z _a : ℂ) : Fin 19→ℂ := ![((2)/(Z)),((2)/(Z)),(((-1)*X^2)/(Z)),(((-2))/(Z)),(1),((1*X^2*Y^2)/(Z)),((-1)*X^2),((-1)),((-1)),((1*X^2)/(Z)),(((-1)*X^2)/(Z)),((-1)),((1*Y^2)/(Z)),((-1)),((1*Y^2)/(Z)),((-1)),((-1)),(((-1)*Y^2)/(Z)),(1)]

def rawJet3_1 (_X Y Z a : ℂ) : ℂ := (84*Z)/(Y^4) + ((-84)*a)/(Y^3) + (28*Z)/(Y^2) + (56)/(3)

def jet3_1Indices : Fin 31→Fin 86 := ![9,10,11,12,15,16,19,20,21,22,23,24,26,27,30,33,36,38,39,53,56,60,65,67,70,71,72,73,77,80,85]
def jet3_1Coeff (X Y Z a : ℂ) : Fin 31→ℂ := ![(1),((1)/(Y^2) + 1),((1*X^2)/(Z)),((1*X^2)/(Y^2) + (1*X^2*a)/(Y) + (-1)*X^2),((1)/(Y^2) + (-1)),((1*X^2)/(Y^2*Z)),(((-1)*X^2)/(Y^2*Z)),(((-1))/(Y^2)),(((-1))/(Z) + ((-1)*Y*a)/(Z) + (1*Y^2)/(Z)),((1*a)/(Y) + (-1)),(((-1))/(Z) + ((-1)*Y*a)/(Z) + (1*Y^2)/(Z)),(1),((1*X^2)/(Z)),(((-1))/(Y^2) + (-1)),(1),(1),((1*X^2)/(Z)),((1)/(Y^2) + 1),((-1)),(1),(1),(1),(1),((1)/(Z) + (1*Y*a)/(Z) + ((-1)*Y^2)/(Z)),((-1)),((-1)),(1),(1),((-1)),((-1)),(1)]

end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightFirstJetScalarCaseBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightLaurent
open Complex

theorem first_of_raw0 (X Y Z a : ℂ)
    (_hX : X≠0) (hY : Y≠0) (_hZ : Z≠0) (h : rawJet0_0 X Y Z a=0) :
    SmallLevelTwentyEightFirstJet.first (-1) (-1) Y Z a=0 := by
  unfold rawJet0_0 at h
  unfold SmallLevelTwentyEightFirstJet.first
  linear_combination (norm := (field_simp [_hX,hY,_hZ]; all_goals ring)) (((-3)*Y^2)/(7))*h

theorem second_of_raw0 (X Y Z a : ℂ)
    (_hX : X≠0) (hY : Y≠0) (_hZ : Z≠0)
    (h1 : rawJet0_0 X Y Z a=0) (h2 : rawJet0_1 X Y Z a=0) :
    SmallLevelTwentyEightFirstJet.second (-1) (-1) Y Z=0 := by
  unfold rawJet0_0 at h1
  unfold rawJet0_1 at h2
  unfold SmallLevelTwentyEightFirstJet.second
  linear_combination (norm := (field_simp [_hX,hY,_hZ]; all_goals ring)) ((3*Y^2)/(28))*h2-((9)/(7))*h1

theorem residual_of_raw0 (X Y Z a : ℂ)
    (_hX : X≠0) (hY : Y≠0) (_hZ : Z≠0) (h : residual (-1) (-1) X Y Z a=0) :
    SmallLevelTwentyEightFirstJet.residual (-1) (-1) Y Z a=0 := by
  norm_num [residual] at h
  unfold SmallLevelTwentyEightFirstJet.residual
  linear_combination (norm := (field_simp [_hX,hY,_hZ]; all_goals ring)) (2*X^2*Y^2)*h

#print axioms first_of_raw0
#print axioms second_of_raw0
#print axioms residual_of_raw0

theorem first_of_raw1 (X Y Z a : ℂ)
    (_hX : X≠0) (hY : Y≠0) (_hZ : Z≠0) (h : rawJet1_0 X Y Z a=0) :
    SmallLevelTwentyEightFirstJet.first (-1) (1) Y Z a=0 := by
  unfold rawJet1_0 at h
  unfold SmallLevelTwentyEightFirstJet.first
  linear_combination (norm := (field_simp [_hX,hY,_hZ]; all_goals ring)) (((-3)*Y^2)/(7))*h

theorem second_of_raw1 (X Y Z a : ℂ)
    (_hX : X≠0) (hY : Y≠0) (_hZ : Z≠0)
    (h1 : rawJet1_0 X Y Z a=0) (h2 : rawJet1_1 X Y Z a=0) :
    SmallLevelTwentyEightFirstJet.second (-1) (1) Y Z=0 := by
  unfold rawJet1_0 at h1
  unfold rawJet1_1 at h2
  unfold SmallLevelTwentyEightFirstJet.second
  linear_combination (norm := (field_simp [_hX,hY,_hZ]; all_goals ring)) ((3*Y^2)/(28))*h2-((9)/(7))*h1

theorem residual_of_raw1 (X Y Z a : ℂ)
    (_hX : X≠0) (hY : Y≠0) (_hZ : Z≠0) (h : residual (-1) (1) X Y Z a=0) :
    SmallLevelTwentyEightFirstJet.residual (-1) (1) Y Z a=0 := by
  norm_num [residual] at h
  unfold SmallLevelTwentyEightFirstJet.residual
  linear_combination (norm := (field_simp [_hX,hY,_hZ]; all_goals ring)) (2*X^2*Y^2)*h

#print axioms first_of_raw1
#print axioms second_of_raw1
#print axioms residual_of_raw1

theorem first_of_raw2 (X Y Z a : ℂ)
    (_hX : X≠0) (hY : Y≠0) (_hZ : Z≠0) (h : rawJet2_0 X Y Z a=0) :
    SmallLevelTwentyEightFirstJet.first (1) (-1) Y Z a=0 := by
  unfold rawJet2_0 at h
  unfold SmallLevelTwentyEightFirstJet.first
  linear_combination (norm := (field_simp [_hX,hY,_hZ]; all_goals ring)) (((-3)*Y^2)/(7))*h

theorem second_of_raw2 (X Y Z a : ℂ)
    (_hX : X≠0) (hY : Y≠0) (_hZ : Z≠0)
    (h1 : rawJet2_0 X Y Z a=0) (h2 : rawJet2_1 X Y Z a=0) :
    SmallLevelTwentyEightFirstJet.second (1) (-1) Y Z=0 := by
  unfold rawJet2_0 at h1
  unfold rawJet2_1 at h2
  unfold SmallLevelTwentyEightFirstJet.second
  linear_combination (norm := (field_simp [_hX,hY,_hZ]; all_goals ring)) ((3*Y^2)/(28))*h2-((9)/(7))*h1

theorem residual_of_raw2 (X Y Z a : ℂ)
    (_hX : X≠0) (hY : Y≠0) (_hZ : Z≠0) (h : residual (1) (-1) X Y Z a=0) :
    SmallLevelTwentyEightFirstJet.residual (1) (-1) Y Z a=0 := by
  norm_num [residual] at h
  unfold SmallLevelTwentyEightFirstJet.residual
  linear_combination (norm := (field_simp [_hX,hY,_hZ]; all_goals ring)) (2*X^2*Y^2)*h

#print axioms first_of_raw2
#print axioms second_of_raw2
#print axioms residual_of_raw2

theorem first_of_raw3 (X Y Z a : ℂ)
    (_hX : X≠0) (hY : Y≠0) (_hZ : Z≠0) (h : rawJet3_0 X Y Z a=0) :
    SmallLevelTwentyEightFirstJet.first (1) (1) Y Z a=0 := by
  unfold rawJet3_0 at h
  unfold SmallLevelTwentyEightFirstJet.first
  linear_combination (norm := (field_simp [_hX,hY,_hZ]; all_goals ring)) (((-3)*Y^2)/(7))*h

theorem second_of_raw3 (X Y Z a : ℂ)
    (_hX : X≠0) (hY : Y≠0) (_hZ : Z≠0)
    (h1 : rawJet3_0 X Y Z a=0) (h2 : rawJet3_1 X Y Z a=0) :
    SmallLevelTwentyEightFirstJet.second (1) (1) Y Z=0 := by
  unfold rawJet3_0 at h1
  unfold rawJet3_1 at h2
  unfold SmallLevelTwentyEightFirstJet.second
  linear_combination (norm := (field_simp [_hX,hY,_hZ]; all_goals ring)) ((3*Y^2)/(28))*h2-((9)/(7))*h1

theorem residual_of_raw3 (X Y Z a : ℂ)
    (_hX : X≠0) (hY : Y≠0) (_hZ : Z≠0) (h : residual (1) (1) X Y Z a=0) :
    SmallLevelTwentyEightFirstJet.residual (1) (1) Y Z a=0 := by
  norm_num [residual] at h
  unfold SmallLevelTwentyEightFirstJet.residual
  linear_combination (norm := (field_simp [_hX,hY,_hZ]; all_goals ring)) (2*X^2*Y^2)*h

#print axioms first_of_raw3
#print axioms second_of_raw3
#print axioms residual_of_raw3

end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightSyzygyCaseIndexBundleSeriesV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightLaurent
open Complex

theorem jet0_0_syzygy (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (w : Fin 84→ℂ) :
    (∑ i, jet0_0Coeff X Y Z a i*leadingRows (-1) (-1) X Y Z a w (jet0_0Indices i))=0 := by
  simp only [jet0_0Coeff,jet0_0Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet0_0_syzygy

theorem jet0_0_projection (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (∑ i, jet0_0Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows (-1) (-1) X Y Z a w (jet0_0Indices i))=rawJet0_0 X Y Z a*w 66 := by
  have hk:=kernel_case0 X Y Z a hX hY hZ w hw
  simp only [jet0_0Coeff,jet0_0Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 44,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65,hk 67,hk 68,hk 69,hk 70,hk 71,hk 72,hk 73,hk 74,hk 75,hk 76,hk 77,hk 78,hk 79,hk 80,hk 81,hk 82,hk 83]
  norm_num only [pole0,rawJet0_0]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet0_0_projection

theorem jet0_1_syzygy (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (w : Fin 84→ℂ) :
    (∑ i, jet0_1Coeff X Y Z a i*leadingRows (-1) (-1) X Y Z a w (jet0_1Indices i))=0 := by
  simp only [jet0_1Coeff,jet0_1Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet0_1_syzygy

theorem jet0_1_projection (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) :
    (∑ i, jet0_1Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows (-1) (-1) X Y Z a w (jet0_1Indices i))=rawJet0_1 X Y Z a*w 66 := by
  have hk:=kernel_case0 X Y Z a hX hY hZ w hw
  simp only [jet0_1Coeff,jet0_1Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 44,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65,hk 67,hk 68,hk 69,hk 70,hk 71,hk 72,hk 73,hk 74,hk 75,hk 76,hk 77,hk 78,hk 79,hk 80,hk 81,hk 82,hk 83]
  norm_num only [pole0,rawJet0_1]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet0_1_projection

end SmallLevelTwentyEightLaurent
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightLaurent
open Complex

theorem jet1_0_syzygy (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (w : Fin 84→ℂ) :
    (∑ i, jet1_0Coeff X Y Z a i*leadingRows (-1) (1) X Y Z a w (jet1_0Indices i))=0 := by
  simp only [jet1_0Coeff,jet1_0Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet1_0_syzygy

theorem jet1_0_projection (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (∑ i, jet1_0Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows (-1) (1) X Y Z a w (jet1_0Indices i))=rawJet1_0 X Y Z a*w 66 := by
  have hk:=kernel_case1 X Y Z a hX hY hZ w hw
  simp only [jet1_0Coeff,jet1_0Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 44,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65,hk 67,hk 68,hk 69,hk 70,hk 71,hk 72,hk 73,hk 74,hk 75,hk 76,hk 77,hk 78,hk 79,hk 80,hk 81,hk 82,hk 83]
  norm_num only [pole1,rawJet1_0]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet1_0_projection

theorem jet1_1_syzygy (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (w : Fin 84→ℂ) :
    (∑ i, jet1_1Coeff X Y Z a i*leadingRows (-1) (1) X Y Z a w (jet1_1Indices i))=0 := by
  simp only [jet1_1Coeff,jet1_1Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet1_1_syzygy

theorem jet1_1_projection (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (1) X Y Z a w=0) :
    (∑ i, jet1_1Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows (-1) (1) X Y Z a w (jet1_1Indices i))=rawJet1_1 X Y Z a*w 66 := by
  have hk:=kernel_case1 X Y Z a hX hY hZ w hw
  simp only [jet1_1Coeff,jet1_1Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 44,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65,hk 67,hk 68,hk 69,hk 70,hk 71,hk 72,hk 73,hk 74,hk 75,hk 76,hk 77,hk 78,hk 79,hk 80,hk 81,hk 82,hk 83]
  norm_num only [pole1,rawJet1_1]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet1_1_projection

end SmallLevelTwentyEightLaurent
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightLaurent
open Complex

theorem jet2_0_syzygy (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (w : Fin 84→ℂ) :
    (∑ i, jet2_0Coeff X Y Z a i*leadingRows (1) (-1) X Y Z a w (jet2_0Indices i))=0 := by
  simp only [jet2_0Coeff,jet2_0Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet2_0_syzygy

theorem jet2_0_projection (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (∑ i, jet2_0Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows (1) (-1) X Y Z a w (jet2_0Indices i))=rawJet2_0 X Y Z a*w 66 := by
  have hk:=kernel_case2 X Y Z a hX hY hZ w hw
  simp only [jet2_0Coeff,jet2_0Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 44,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65,hk 67,hk 68,hk 69,hk 70,hk 71,hk 72,hk 73,hk 74,hk 75,hk 76,hk 77,hk 78,hk 79,hk 80,hk 81,hk 82,hk 83]
  norm_num only [pole2,rawJet2_0]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet2_0_projection

theorem jet2_1_syzygy (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (w : Fin 84→ℂ) :
    (∑ i, jet2_1Coeff X Y Z a i*leadingRows (1) (-1) X Y Z a w (jet2_1Indices i))=0 := by
  simp only [jet2_1Coeff,jet2_1Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet2_1_syzygy

theorem jet2_1_projection (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (-1) X Y Z a w=0) :
    (∑ i, jet2_1Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows (1) (-1) X Y Z a w (jet2_1Indices i))=rawJet2_1 X Y Z a*w 66 := by
  have hk:=kernel_case2 X Y Z a hX hY hZ w hw
  simp only [jet2_1Coeff,jet2_1Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 44,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65,hk 67,hk 68,hk 69,hk 70,hk 71,hk 72,hk 73,hk 74,hk 75,hk 76,hk 77,hk 78,hk 79,hk 80,hk 81,hk 82,hk 83]
  norm_num only [pole2,rawJet2_1]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet2_1_projection

end SmallLevelTwentyEightLaurent
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0

/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightLaurent
open Complex

theorem jet3_0_syzygy (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (w : Fin 84→ℂ) :
    (∑ i, jet3_0Coeff X Y Z a i*leadingRows (1) (1) X Y Z a w (jet3_0Indices i))=0 := by
  simp only [jet3_0Coeff,jet3_0Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet3_0_syzygy

theorem jet3_0_projection (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (∑ i, jet3_0Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows (1) (1) X Y Z a w (jet3_0Indices i))=rawJet3_0 X Y Z a*w 66 := by
  have hk:=kernel_case3 X Y Z a hX hY hZ w hw
  simp only [jet3_0Coeff,jet3_0Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 44,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65,hk 67,hk 68,hk 69,hk 70,hk 71,hk 72,hk 73,hk 74,hk 75,hk 76,hk 77,hk 78,hk 79,hk 80,hk 81,hk 82,hk 83]
  norm_num only [pole3,rawJet3_0]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet3_0_projection

theorem jet3_1_syzygy (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (w : Fin 84→ℂ) :
    (∑ i, jet3_1Coeff X Y Z a i*leadingRows (1) (1) X Y Z a w (jet3_1Indices i))=0 := by
  simp only [jet3_1Coeff,jet3_1Indices,Fin.sum_univ_succ]
  norm_num [leadingRows]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet3_1_syzygy

theorem jet3_1_projection (X Y Z a : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (1) (1) X Y Z a w=0) :
    (∑ i, jet3_1Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows (1) (1) X Y Z a w (jet3_1Indices i))=rawJet3_1 X Y Z a*w 66 := by
  have hk:=kernel_case3 X Y Z a hX hY hZ w hw
  simp only [jet3_1Coeff,jet3_1Indices,Fin.sum_univ_succ]
  norm_num [firstRows]
  simp only [hk 0,hk 1,hk 2,hk 3,hk 4,hk 5,hk 6,hk 7,hk 8,hk 9,hk 10,hk 11,hk 12,hk 13,hk 14,hk 15,hk 16,hk 17,hk 18,hk 19,hk 20,hk 21,hk 22,hk 23,hk 24,hk 25,hk 26,hk 27,hk 28,hk 29,hk 30,hk 31,hk 32,hk 33,hk 34,hk 35,hk 36,hk 37,hk 38,hk 39,hk 40,hk 41,hk 42,hk 43,hk 44,hk 45,hk 46,hk 47,hk 48,hk 49,hk 50,hk 51,hk 52,hk 53,hk 54,hk 55,hk 56,hk 57,hk 58,hk 59,hk 60,hk 61,hk 62,hk 63,hk 64,hk 65,hk 67,hk 68,hk 69,hk 70,hk 71,hk 72,hk 73,hk 74,hk 75,hk 76,hk 77,hk 78,hk 79,hk 80,hk 81,hk 82,hk 83]
  norm_num only [pole3,rawJet3_1]
  field_simp [hX,hY,hZ]
  <;> ring

#print axioms jet3_1_projection

end SmallLevelTwentyEightLaurent
end
end
end

/-! ## TwentyEightSyzygyUseCaseBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelTwentyEightLaurent
open Complex SmallLevelPrimeRates

theorem jet0_0_analytic (m : ℕ) (a z : ℂ) (i : Fin 19) :
    AnalyticAt ℂ (fun s => jet0_0Coeff (parameter 2 m s) (parameter 3 m s)
      (parameter 7 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 7 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 7 m (by decide) z
  fin_cases i <;> norm_num [jet0_0Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem jet0_0_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) (h66 : w 66≠0)
    (hfirst : (∑ i,jet0_0Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows (-1) (-1) X Y Z a w (jet0_0Indices i))=0) :
    rawJet0_0 X Y Z a=0 := by
  have hp:=(jet0_0_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  exact (mul_eq_zero.mp hp).resolve_right h66

#print axioms jet0_0_analytic
#print axioms jet0_0_necessary

theorem jet0_1_analytic (m : ℕ) (a z : ℂ) (i : Fin 31) :
    AnalyticAt ℂ (fun s => jet0_1Coeff (parameter 2 m s) (parameter 3 m s)
      (parameter 7 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 7 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 7 m (by decide) z
  fin_cases i <;> norm_num [jet0_1Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem jet0_1_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) (-1) X Y Z a w=0) (h66 : w 66≠0)
    (hfirst : (∑ i,jet0_1Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows (-1) (-1) X Y Z a w (jet0_1Indices i))=0) :
    rawJet0_1 X Y Z a=0 := by
  have hp:=(jet0_1_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  exact (mul_eq_zero.mp hp).resolve_right h66

#print axioms jet0_1_analytic
#print axioms jet0_1_necessary

theorem jet1_0_analytic (m : ℕ) (a z : ℂ) (i : Fin 19) :
    AnalyticAt ℂ (fun s => jet1_0Coeff (parameter 2 m s) (parameter 3 m s)
      (parameter 7 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 7 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 7 m (by decide) z
  fin_cases i <;> norm_num [jet1_0Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem jet1_0_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) 1 X Y Z a w=0) (h66 : w 66≠0)
    (hfirst : (∑ i,jet1_0Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows (-1) 1 X Y Z a w (jet1_0Indices i))=0) :
    rawJet1_0 X Y Z a=0 := by
  have hp:=(jet1_0_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  exact (mul_eq_zero.mp hp).resolve_right h66

#print axioms jet1_0_analytic
#print axioms jet1_0_necessary

theorem jet1_1_analytic (m : ℕ) (a z : ℂ) (i : Fin 31) :
    AnalyticAt ℂ (fun s => jet1_1Coeff (parameter 2 m s) (parameter 3 m s)
      (parameter 7 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 7 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 7 m (by decide) z
  fin_cases i <;> norm_num [jet1_1Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem jet1_1_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows (-1) 1 X Y Z a w=0) (h66 : w 66≠0)
    (hfirst : (∑ i,jet1_1Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows (-1) 1 X Y Z a w (jet1_1Indices i))=0) :
    rawJet1_1 X Y Z a=0 := by
  have hp:=(jet1_1_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  exact (mul_eq_zero.mp hp).resolve_right h66

#print axioms jet1_1_analytic
#print axioms jet1_1_necessary

theorem jet2_0_analytic (m : ℕ) (a z : ℂ) (i : Fin 19) :
    AnalyticAt ℂ (fun s => jet2_0Coeff (parameter 2 m s) (parameter 3 m s)
      (parameter 7 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 7 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 7 m (by decide) z
  fin_cases i <;> norm_num [jet2_0Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem jet2_0_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows 1 (-1) X Y Z a w=0) (h66 : w 66≠0)
    (hfirst : (∑ i,jet2_0Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows 1 (-1) X Y Z a w (jet2_0Indices i))=0) :
    rawJet2_0 X Y Z a=0 := by
  have hp:=(jet2_0_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  exact (mul_eq_zero.mp hp).resolve_right h66

#print axioms jet2_0_analytic
#print axioms jet2_0_necessary

theorem jet2_1_analytic (m : ℕ) (a z : ℂ) (i : Fin 31) :
    AnalyticAt ℂ (fun s => jet2_1Coeff (parameter 2 m s) (parameter 3 m s)
      (parameter 7 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 7 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 7 m (by decide) z
  fin_cases i <;> norm_num [jet2_1Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem jet2_1_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows 1 (-1) X Y Z a w=0) (h66 : w 66≠0)
    (hfirst : (∑ i,jet2_1Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows 1 (-1) X Y Z a w (jet2_1Indices i))=0) :
    rawJet2_1 X Y Z a=0 := by
  have hp:=(jet2_1_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  exact (mul_eq_zero.mp hp).resolve_right h66

#print axioms jet2_1_analytic
#print axioms jet2_1_necessary

theorem jet3_0_analytic (m : ℕ) (a z : ℂ) (i : Fin 19) :
    AnalyticAt ℂ (fun s => jet3_0Coeff (parameter 2 m s) (parameter 3 m s)
      (parameter 7 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 7 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 7 m (by decide) z
  fin_cases i <;> norm_num [jet3_0Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem jet3_0_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows 1 1 X Y Z a w=0) (h66 : w 66≠0)
    (hfirst : (∑ i,jet3_0Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows 1 1 X Y Z a w (jet3_0Indices i))=0) :
    rawJet3_0 X Y Z a=0 := by
  have hp:=(jet3_0_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  exact (mul_eq_zero.mp hp).resolve_right h66

#print axioms jet3_0_analytic
#print axioms jet3_0_necessary

theorem jet3_1_analytic (m : ℕ) (a z : ℂ) (i : Fin 31) :
    AnalyticAt ℂ (fun s => jet3_1Coeff (parameter 2 m s) (parameter 3 m s)
      (parameter 7 m s) a i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 7 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 7 m (by decide) z
  fin_cases i <;> norm_num [jet3_1Coeff]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem jet3_1_necessary (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) (hw : coreRows 1 1 X Y Z a w=0) (h66 : w 66≠0)
    (hfirst : (∑ i,jet3_1Coeff (X/2) (Y/3) (Z/7) a i*
      firstRows 1 1 X Y Z a w (jet3_1Indices i))=0) :
    rawJet3_1 X Y Z a=0 := by
  have hp:=(jet3_1_projection X Y Z a hX hY hZ w hw).symm.trans hfirst
  exact (mul_eq_zero.mp hp).resolve_right h66

#print axioms jet3_1_analytic
#print axioms jet3_1_necessary

end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightFirstJetPhysical -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightFirstJet
open Complex

/-- The modulus bounds in the opposite-sign case contradict two exact
integer power comparisons; no numerical logarithm bounds are used. -/
theorem exclude_opposite (h : ℂ) (η : ℂ) (hη : η=1 ∨ η= -1)
    (hy : ((3:ℂ)^h)^(2:ℕ)=21) (hz : (7:ℂ)^h= -η*17) : False := by
  have hn3 : ‖(3:ℂ)^h‖=(3:ℝ)^h.re := by
    simpa using Complex.norm_natCast_cpow_of_pos (by decide : 0<3) h
  have hn7 : ‖(7:ℂ)^h‖=(7:ℝ)^h.re := by
    simpa using Complex.norm_natCast_cpow_of_pos (by decide : 0<7) h
  have hyR : (9:ℝ)^h.re=21 := by
    have hh:=congrArg norm hy
    rw [norm_pow,hn3,Real.rpow_pow_comm (by norm_num : (0:ℝ)≤3)] at hh
    norm_num at hh
    exact hh
  have hzR : (7:ℝ)^h.re=17 := by
    rw [← hn7,hz]
    rcases hη with rfl|rfl <;> norm_num
  have hpos : 0<h.re := by
    by_contra! hn
    have hh:=Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤9) hn
    rw [hyR,Real.rpow_zero] at hh
    norm_num at hh
  have hh:=Real.rpow_lt_rpow (by positivity : (0:ℝ)≤7^10)
    (by norm_num : (7:ℝ)^10<9^9) hpos
  rw [← Real.rpow_pow_comm (by norm_num : (0:ℝ)≤7) h.re 10,
    ← Real.rpow_pow_comm (by norm_num : (0:ℝ)≤9) h.re 9,hzR,hyR] at hh
  norm_num at hh

/-- The actual exponential curve meets the three first-jet constraints
only in the stated weight-independent exceptional parameters. -/
theorem physical (h η σ a : ℂ) (hη : η=1 ∨ η= -1) (hσ : σ=1 ∨ σ= -1)
    (h1 : first η σ ((3:ℂ)^h) ((7:ℂ)^h) a=0)
    (h2 : second η σ ((3:ℂ)^h) ((7:ℂ)^h)=0)
    (hr : residual η σ ((3:ℂ)^h) ((7:ℂ)^h) a=0) :
    h=1 ∧ η= -1 ∧ σ= -1 ∧ a= -10/3 := by
  obtain ⟨hy,ha,hz⟩:=constraints η σ ((3:ℂ)^h) ((7:ℂ)^h) a hη hσ
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))) h1 h2 hr
  have hτ : η*σ=1 ∨ η*σ= -1 := by
    rcases hη with rfl|rfl <;> rcases hσ with rfl|rfl <;> norm_num
  rcases hτ with hτ|hτ
  · simp only [mul_assoc,hτ] at hy ha hz
    norm_num at hy ha hz
    have hp3 : ((3:ℂ)^(h-1))^(2:ℕ)=1 := by
      rw [Complex.cpow_sub _ _ (by norm_num : (3:ℂ)≠0),Complex.cpow_one,div_pow,hy]
      norm_num
    have hp7 : ((7:ℂ)^(h-1))^(2:ℕ)=1 := by
      rw [Complex.cpow_sub _ _ (by norm_num : (7:ℂ)≠0),Complex.cpow_one,hz]
      rcases hη with rfl|rfl <;> norm_num
    have hh:=QuantitativeArithmeticPrimePowerTorsion.distinct_primes_cpow_torsion
      (by decide : Nat.Prime 3) (by decide : Nat.Prime 7) (by decide : (3:ℕ)≠7)
      (h-1) 2 2 (by decide) (by decide) hp3 hp7
    have he : h=1:=sub_eq_zero.mp hh
    rw [he,Complex.cpow_one] at hz ha
    have heη : η= -1 := by linear_combination hz/7
    refine ⟨he,heη,?_,?_⟩
    · rw [heη] at hτ
      linear_combination -hτ
    · linear_combination ha/9
  · simp only [mul_assoc,hτ] at hy hz
    norm_num at hy hz
    exact (exclude_opposite h η hη hy (by simpa only [neg_mul] using hz)).elim

#print axioms exclude_opposite
#print axioms physical
end SmallLevelTwentyEightFirstJet
end
end

/-! ## TwentyEightFirstJetUse -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightLaurent
open Complex SmallLevelPrimeRates

/-- Verified selected first-order relations force all three scalar constraints. -/
theorem firstJet_equations (m : ℕ) (η σ a x : ℂ)
    (hη : η=1 ∨ η= -1) (hσ : σ=1 ∨ σ= -1)
    (w : Fin 84→ℂ)
    (hw : coreRows η σ (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) a w=0)
    (hw0 : w≠0)
    (hselected : ∀ (r : ℕ) (rows : Fin r→Fin 86) (coeff : ℂ→ℂ→ℂ→Fin r→ℂ),
      (∀ z i, AnalyticAt ℂ
        (fun s => coeff (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) i) z) →
      (∀ X Y Z : ℂ, X≠0 → Y≠0 → Z≠0 → ∀ q : Fin 84→ℂ,
        ∑ i,coeff X Y Z i*leadingRows η σ X Y Z a q (rows i)=0) →
      ∑ i,coeff (parameter 2 m x/2) (parameter 3 m x/3) (parameter 7 m x/7) i*
        firstRows η σ (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) a w (rows i)=0) :
    SmallLevelTwentyEightFirstJet.first η σ (parameter 3 m x) (parameter 7 m x) a=0 ∧
    SmallLevelTwentyEightFirstJet.second η σ (parameter 3 m x) (parameter 7 m x)=0 ∧
    SmallLevelTwentyEightFirstJet.residual η σ (parameter 3 m x) (parameter 7 m x) a=0 := by
  have hX:=parameter_ne_zero 2 m (by decide) x
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=parameter_ne_zero 7 m (by decide) x
  have h66:=core_kernel_coordinate_ne_zero η σ _ _ _ a hη hσ hX hY hZ w hw hw0
  have hr:=core_residual_zero η σ _ _ _ a hη hσ hX hY hZ w hw hw0
  rcases hη with rfl|rfl <;> rcases hσ with rfl|rfl
  · have hj0 : rawJet3_0 (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) a=0 := by
      apply jet3_0_necessary _ _ _ a hX hY hZ w hw h66
      apply hselected _ jet3_0Indices (fun X Y Z => jet3_0Coeff X Y Z a)
      · exact jet3_0_analytic m a
      · intro X Y Z hX hY hZ q
        exact jet3_0_syzygy X Y Z a hX hY hZ q
    have hj1 : rawJet3_1 (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) a=0 := by
      apply jet3_1_necessary _ _ _ a hX hY hZ w hw h66
      apply hselected _ jet3_1Indices (fun X Y Z => jet3_1Coeff X Y Z a)
      · exact jet3_1_analytic m a
      · intro X Y Z hX hY hZ q
        exact jet3_1_syzygy X Y Z a hX hY hZ q
    exact ⟨first_of_raw3 _ _ _ a hX hY hZ hj0,
      second_of_raw3 _ _ _ a hX hY hZ hj0 hj1,
      residual_of_raw3 _ _ _ a hX hY hZ hr⟩
  · have hj0 : rawJet2_0 (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) a=0 := by
      apply jet2_0_necessary _ _ _ a hX hY hZ w hw h66
      apply hselected _ jet2_0Indices (fun X Y Z => jet2_0Coeff X Y Z a)
      · exact jet2_0_analytic m a
      · intro X Y Z hX hY hZ q
        exact jet2_0_syzygy X Y Z a hX hY hZ q
    have hj1 : rawJet2_1 (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) a=0 := by
      apply jet2_1_necessary _ _ _ a hX hY hZ w hw h66
      apply hselected _ jet2_1Indices (fun X Y Z => jet2_1Coeff X Y Z a)
      · exact jet2_1_analytic m a
      · intro X Y Z hX hY hZ q
        exact jet2_1_syzygy X Y Z a hX hY hZ q
    exact ⟨first_of_raw2 _ _ _ a hX hY hZ hj0,
      second_of_raw2 _ _ _ a hX hY hZ hj0 hj1,
      residual_of_raw2 _ _ _ a hX hY hZ hr⟩
  · have hj0 : rawJet1_0 (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) a=0 := by
      apply jet1_0_necessary _ _ _ a hX hY hZ w hw h66
      apply hselected _ jet1_0Indices (fun X Y Z => jet1_0Coeff X Y Z a)
      · exact jet1_0_analytic m a
      · intro X Y Z hX hY hZ q
        exact jet1_0_syzygy X Y Z a hX hY hZ q
    have hj1 : rawJet1_1 (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) a=0 := by
      apply jet1_1_necessary _ _ _ a hX hY hZ w hw h66
      apply hselected _ jet1_1Indices (fun X Y Z => jet1_1Coeff X Y Z a)
      · exact jet1_1_analytic m a
      · intro X Y Z hX hY hZ q
        exact jet1_1_syzygy X Y Z a hX hY hZ q
    exact ⟨first_of_raw1 _ _ _ a hX hY hZ hj0,
      second_of_raw1 _ _ _ a hX hY hZ hj0 hj1,
      residual_of_raw1 _ _ _ a hX hY hZ hr⟩
  · have hj0 : rawJet0_0 (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) a=0 := by
      apply jet0_0_necessary _ _ _ a hX hY hZ w hw h66
      apply hselected _ jet0_0Indices (fun X Y Z => jet0_0Coeff X Y Z a)
      · exact jet0_0_analytic m a
      · intro X Y Z hX hY hZ q
        exact jet0_0_syzygy X Y Z a hX hY hZ q
    have hj1 : rawJet0_1 (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) a=0 := by
      apply jet0_1_necessary _ _ _ a hX hY hZ w hw h66
      apply hselected _ jet0_1Indices (fun X Y Z => jet0_1Coeff X Y Z a)
      · exact jet0_1_analytic m a
      · intro X Y Z hX hY hZ q
        exact jet0_1_syzygy X Y Z a hX hY hZ q
    exact ⟨first_of_raw0 _ _ _ a hX hY hZ hj0,
      second_of_raw0 _ _ _ a hX hY hZ hj0 hj1,
      residual_of_raw0 _ _ _ a hX hY hZ hr⟩

#print axioms firstJet_equations
end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightPhysicalCandidate -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightLaurent
open Complex SmallLevelPrimeRates

theorem physical_candidate (m : ℕ) (η σ a x : ℂ)
    (hη : η=1 ∨ η= -1) (hσ : σ=1 ∨ σ= -1)
    (h1 : SmallLevelTwentyEightFirstJet.first η σ (parameter 3 m x) (parameter 7 m x) a=0)
    (h2 : SmallLevelTwentyEightFirstJet.second η σ (parameter 3 m x) (parameter 7 m x)=0)
    (hr : SmallLevelTwentyEightFirstJet.residual η σ (parameter 3 m x) (parameter 7 m x) a=0) :
    x=(m:ℂ)+1 ∧ η= -1 ∧ σ= -1 ∧ a= -10/3 := by
  obtain ⟨he,hη',hσ',ha⟩:=SmallLevelTwentyEightFirstJet.physical (x-(m:ℂ)) η σ a hη hσ
    (by simpa only [parameter,Nat.cast_ofNat] using h1)
    (by simpa only [parameter,Nat.cast_ofNat] using h2)
    (by simpa only [parameter,Nat.cast_ofNat] using hr)
  refine ⟨?_,hη',hσ',ha⟩
  linear_combination he

#print axioms physical_candidate
end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightFirstShiftComparison -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex Matrix SmallLevelPrimeRates SmallLevelTwentyEightParameters SmallLevelTwentyEightLaurent

theorem firstRows_positive (η σ X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0)
    (w : Fin 84→ℂ) :
    positiveTaylorRows η σ (X/2) (Y/3) (Z/7) 0 w=firstRows η σ X Y Z a w := by
  funext i
  fin_cases i <;> norm_num [positiveTaylorRows,firstRows] <;> (try field_simp [hX,hY,hZ]) <;> ring <;> simp

theorem firstShift_actual (m : ℕ) (f : ℕ→ℂ) (ε x : ℂ) (w : Fin 84→ℂ) (i : Fin 86) :
    (∑ j,extendedShift m f ε 0 (x-1) i j*w j)=
      (I*(x-((2*m:ℕ):ℂ)))*firstRows (phase m ε) (sigmaSeven f)
        (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) ((Real.sqrt 3:ℂ)*f 3) w i := by
  have h:=extendedShift_actual m f ε 0 (x-1) w i
  have he : x-1+((0+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=x-((2*m:ℕ):ℂ) := by norm_num
  rw [he] at h
  simp only [zero_add,pow_one,Ring.choose_one_right,
    parameter_shift 2 m (by decide),parameter_shift 3 m (by decide),
    parameter_shift 7 m (by decide),Nat.cast_ofNat] at h
  rw [firstRows_positive _ _ _ _ _ ((Real.sqrt 3:ℂ)*f 3)
    (parameter_ne_zero 2 m (by decide) x) (parameter_ne_zero 3 m (by decide) x)
    (parameter_ne_zero 7 m (by decide) x)] at h
  exact h

#print axioms firstRows_positive
#print axioms firstShift_actual
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightSelectedFirstShift -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex Matrix Filter SmallLevelPrimeRates SmallLevelTwentyEightParameters
open SmallLevelTwentyEightLaurent QuantitativeArithmeticUniversalPoleVector
open scoped Topology

/-- Translate an analytic selected left syzygy of the literal Mellin rows
into its polynomial first-shift equation, away from the weight. -/
theorem selected_regular_polynomial_first_shift {ρ : Type*} [Fintype ρ]
    (rows : ρ→Fin 86) (η σ a : ℂ)
    (coeff : ℂ→ℂ→ℂ→ρ→ℂ)
    (hsyz : ∀ X Y Z : ℂ, X≠0 → Y≠0 → Z≠0 → ∀ w : Fin 84→ℂ,
      ∑ i,coeff X Y Z i*leadingRows η σ X Y Z a w (rows i)=0)
    (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (hη : phase m ε=η) (hσ : sigmaSeven f=σ)
    (ha : (Real.sqrt 3:ℂ)*f 3=a)
    (hcoeff : ∀ z i, AnalyticAt ℂ
      (fun s => coeff (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) i) z)
    (B : ℝ) (G : ℂ→Fin 84→ℂ) (H : ℕ→ℂ→Fin 86→ℂ)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun s => H n s i) z)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j,extendedLeading m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ b∈Finset.range n,
          ∑ j,extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j))
    (x : ℂ) (hx : x≠((2*m:ℕ):ℂ)) (w : Fin 84→ℂ) (hw : IsLeadingVector G x w)
    (htail : ∀ b : ℕ, 1≤b → ∀ i j, ∃ R : ℂ→ℂ, AnalyticAt ℂ R (x-1) ∧
      (fun z => extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j)=ᶠ[𝓝[≠] (x-1)] R) :
    ∑ i,coeff (parameter 2 m x/2) (parameter 3 m x/3) (parameter 7 m x/7) i*
      firstRows η σ (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) a w (rows i)=0 := by
  classical
  let K : ℂ→ρ→ℂ:=fun z => coeff (parameter 2 m z) (parameter 3 m z) (parameter 7 m z)
  have hKA (z : ℂ) (w : Fin 84→ℂ) :
      ∑ i,K z i*(∑ j,extendedLeading m f ε z (rows i) j*w j)=0 := by
    have he (i : Fin 86) : (∑ j,extendedLeading m f ε z i j*w j)=
        leadingRows (phase m ε) (sigmaSeven f)
          (parameter 2 m z) (parameter 3 m z) (parameter 7 m z) ((Real.sqrt 3:ℂ)*f 3) w i :=
      congrFun (extendedLeading_actual m f ε z w) i
    simp only [he,hη,hσ,ha,K]
    exact hsyz _ _ _ (parameter_ne_zero 2 m (by decide) z)
      (parameter_ne_zero 3 m (by decide) z) (parameter_ne_zero 7 m (by decide) z) w
  have hh:=SmallLevelFiniteShift.selected_regular_first_shift rows B G
    (extendedLeading m f ε) (extendedShift m f ε) H
    (extendedShift_analytic m f ε) hH hrow x w hw htail K hcoeff hKA
  simp only [firstShift_actual,hη,hσ,ha,K,
    parameter_shift 2 m (by decide),parameter_shift 3 m (by decide),
    parameter_shift 7 m (by decide),Nat.cast_ofNat] at hh
  have he : (∑ i,coeff (parameter 2 m x/2) (parameter 3 m x/3) (parameter 7 m x/7) i*
      ((I*(x-((2*m:ℕ):ℂ)))*firstRows η σ (parameter 2 m x) (parameter 3 m x)
        (parameter 7 m x) a w (rows i)))=
      (I*(x-((2*m:ℕ):ℂ)))*(∑ i,coeff (parameter 2 m x/2) (parameter 3 m x/3)
        (parameter 7 m x/7) i*firstRows η σ (parameter 2 m x) (parameter 3 m x)
          (parameter 7 m x) a w (rows i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hh
  exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero I_ne_zero (sub_ne_zero.mpr hx))

#print axioms selected_regular_polynomial_first_shift
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightCandidateFromRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex Matrix Filter SmallLevelPrimeRates SmallLevelTwentyEightParameters
open SmallLevelTwentyEightLaurent QuantitativeArithmeticUniversalPoleVector
open scoped Topology

theorem candidate_of_regular_tails {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (B : ℝ) (G : ℂ→Fin 84→ℂ) (H : ℕ→ℂ→Fin 86→ℂ)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun s => H n s i) z)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j,extendedLeading m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ b∈Finset.range n,
          ∑ j,extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j))
    (x : ℂ) (hx : x≠((2*m:ℕ):ℂ)) (w : Fin 84→ℂ) (hw : IsLeadingVector G x w)
    (htail : ∀ d b : ℕ, d≤b → ∀ i j, ∃ R : ℂ→ℂ, AnalyticAt ℂ R (x-d) ∧
      (fun z => extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j)=ᶠ[𝓝[≠] (x-d)] R) :
    x=(m:ℂ)+1 ∧ phase m ε= -1 ∧ sigmaSeven f= -1 ∧ (Real.sqrt 3:ℂ)*f 3= -10/3 := by
  have hη:=phase_sign m hε
  have hσ:=sigmaSeven_sign hf.toEulerData
  have hlead:=hw.regular_tail_leading B G (extendedLeading m f ε) (extendedShift m f ε)
    H x w (extendedLeading_analytic m f ε x) hH
    (fun b i j => by simpa only [Nat.cast_zero,sub_zero] using htail 0 b (Nat.zero_le b) i j) hrow
  rw [extendedLeading_actual] at hlead
  have hcore : coreRows (phase m ε) (sigmaSeven f)
      (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) ((Real.sqrt 3:ℂ)*f 3) w=0 := by
    funext i
    exact congrFun hlead ⟨i.val,by omega⟩
  have hjet:=firstJet_equations m (phase m ε) (sigmaSeven f)
    ((Real.sqrt 3:ℂ)*f 3) x hη hσ w hcore hw.1
    (fun r rows coeff hcoeff hsyz => selected_regular_polynomial_first_shift
      rows _ _ _ coeff hsyz m f ε rfl rfl rfl hcoeff B G H hH hrow x hx w hw
      (fun b hb i j => by simpa only [Nat.cast_one] using htail 1 b hb i j))
  exact physical_candidate m _ _ _ x hη hσ hjet.1 hjet.2.1 hjet.2.2

#print axioms candidate_of_regular_tails
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightGridAuxiliary -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightGrid
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive

def gridEntireSpecs : Fin 4→ℕ := ![1,3,21,7]

theorem gridEntireSpecs_valid : ∀ i : Fin 4, 0<gridEntireSpecs i ∧ gridEntireSpecs i∣84 := by decide

theorem original_grid_entire_rows {k : ℕ} (hk : 0<k) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 k f) :
    (∀ i : Fin 4, ∀ s : ℂ, AnalyticAt ℂ (ramanujanEntire 28 k f (gridEntireSpecs i)) s) ∧
      ∃ B : ℝ, ∀ i : Fin 4, ∀ s : ℂ, B<s.re →
        ramanujanEntire 28 k f (gridEntireSpecs i) s=gridSum k f 84 (gridEntireSpecs i) 0 s := by
  have hh (i : Fin 4):=original_ramanujan_entire (by decide : 0<28) hk hf (gridEntireSpecs_valid i).1
  constructor
  · exact fun i => (hh i).1
  · choose b hb using fun i => (hh i).2
    let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
    refine ⟨B,?_⟩
    intro i s hs
    have hbi : b i≤B:=Finset.le_sup' b (Finset.mem_univ i)
    rw [hb i s (lt_of_le_of_lt hbi hs)]
    have hg:=ramanujanAdditive_grid k f (by decide : 0<84)
      (gridEntireSpecs_valid i).1 (gridEntireSpecs_valid i).2 0 s
    simpa only [Int.cast_zero,zero_div,gridSum] using hg

def gridHalf (k : ℕ) (f : ℕ→ℂ) (j : ℤ) (s : ℂ) : ℂ :=
  grid k f 84 j s+grid k f 84 (j+42) s

theorem original_grid_half {k : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 k f) :
    ∃ B : ℝ, ∀ j : ℤ, ∀ s : ℂ, B<s.re → gridHalf k f j s=0 := by
  obtain ⟨B,hB⟩:=original_square_prime_additive hf (by decide : Nat.Prime 2) (by decide : 2^2∣28)
  refine ⟨B,?_⟩
  intro j s hs
  have hh:=hB ((j:ℝ)/84) s hs
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.cast_zero,
    Nat.cast_one,Nat.cast_ofNat,zero_div,add_zero] at hh
  have h1 : (j:ℝ)/84+1/2=((j+42:ℤ):ℝ)/84 := by push_cast; ring
  rw [h1] at hh
  exact hh

def gridHeckeThree (m : ℕ) (f : ℕ→ℂ) (j : ℤ) (s : ℂ) : ℂ :=
  grid (2*m) f 84 j s+grid (2*m) f 84 (j+28) s+grid (2*m) f 84 (j+56) s-
    ((Real.sqrt 3:ℂ)*f 3)*(3:ℂ)^((m:ℂ)-s)*grid (2*m) f 84 (3*j) s+
    ((3:ℂ)^((m:ℂ)-s))^2*grid (2*m) f 84 (9*j) s

theorem original_grid_hecke_three {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) :
    ∃ B : ℝ, ∀ j : ℤ, ∀ s : ℂ, B<s.re → gridHeckeThree m f j s=0 := by
  obtain ⟨B,hB⟩:=normalized_additive_hecke hf (by decide : Nat.Prime 3) (by decide : ¬3∣28)
  refine ⟨B,?_⟩
  intro j s hs
  have hh:=hB ((j:ℝ)/84) s hs
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.cast_zero,
    Nat.cast_one,Nat.cast_ofNat,zero_div,add_zero] at hh
  have h1 : (j:ℝ)/84+1/3=((j+28:ℤ):ℝ)/84 := by push_cast; ring
  have h2 : (j:ℝ)/84+2/3=((j+56:ℤ):ℝ)/84 := by push_cast; ring
  have h3 : 3*((j:ℝ)/84)=((3*j:ℤ):ℝ)/84 := by push_cast; ring
  have h9 : (9:ℝ)*((j:ℝ)/84)=((9*j:ℤ):ℝ)/84 := by push_cast; ring
  rw [h1,h2,h3,h9] at hh
  exact hh

def gridHalfSpecs : Fin 20→ℤ :=
  ![5,8,10,11,13,15,16,17,19,20,22,23,25,26,27,29,31,32,34,37]

def gridHeckeSpecs : Fin 5→ℤ := ![3,5,6,9,8]

#print axioms original_grid_entire_rows
#print axioms original_grid_half
#print axioms original_grid_hecke_three
end SmallLevelTwentyEightGrid
end
end

/-! ## TwentyEightGridAssembly -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightGrid
open Complex Matrix SmallLevelTaylor SmallLevelAdditive FinitenessRamanujanSum

def gridAssemble (G : Fin 46→ℂ) (T : Fin 10→ℂ) (R : Fin 4→ℂ)
    (H : Fin 5→ℂ) (B : Fin 20→ℂ) (J : ℂ) : Fin 86→ℂ
  | 0 => G 0
  | 1 => G 1
  | 2 => G 2
  | 3 => G 3
  | 4 => G 4
  | 5 => R 0
  | 6 => G 5
  | 7 => G 6
  | 8 => G 7
  | 9 => G 8
  | 10 => G 9
  | 11 => G 10
  | 12 => G 11
  | 13 => G 12
  | 14 => G 13
  | 15 => G 14
  | 16 => G 15
  | 17 => G 16
  | 18 => G 17
  | 19 => G 18
  | 20 => G 19
  | 21 => G 20
  | 22 => G 21
  | 23 => G 22
  | 24 => G 23
  | 25 => G 24
  | 26 => G 25
  | 27 => G 26
  | 28 => G 27
  | 29 => G 28
  | 30 => G 29
  | 31 => G 30
  | 32 => G 31
  | 33 => G 32
  | 34 => G 33
  | 35 => G 34
  | 36 => G 35
  | 37 => G 36
  | 38 => G 37
  | 39 => G 38
  | 40 => G 39
  | 41 => G 40
  | 42 => G 41
  | 43 => G 42
  | 44 => G 43
  | 45 => G 44
  | 46 => G 45
  | 47 => B 0
  | 48 => B 1
  | 49 => B 2
  | 50 => B 3
  | 51 => B 4
  | 52 => B 5
  | 53 => B 6
  | 54 => B 7
  | 55 => B 8
  | 56 => B 9
  | 57 => B 10
  | 58 => B 11
  | 59 => B 12
  | 60 => B 13
  | 61 => B 14
  | 62 => B 15
  | 63 => B 16
  | 64 => B 17
  | 65 => B 18
  | 66 => B 19
  | 67 => R 1
  | 68 => T 0
  | 69 => T 1
  | 70 => T 2
  | 71 => T 3
  | 72 => T 4
  | 73 => T 5
  | 74 => T 6
  | 75 => T 7
  | 76 => T 8
  | 77 => R 2
  | 78 => H 0
  | 79 => H 1
  | 80 => H 2
  | 81 => H 3
  | 82 => J
  | 83 => T 9
  | 84 => R 3
  | _ => H 4

def gridIndex (t : ℤ) : Fin 84 :=
  ⟨(t%84).toNat,by have h:=Int.emod_lt_of_pos t (by decide : (0:ℤ)<84); omega⟩

def gridSample (q : ℕ) (t : ℤ) (w : Fin 84→ℂ) : ℂ :=
  ∑ j∈residues q,w (gridIndex (t+(j:ℤ)*(84/q:ℕ)))

def gridVector (k : ℕ) (f : ℕ→ℂ) (s : ℂ) : Fin 84→ℂ :=
  fun j => grid k f 84 (j:ℕ) s

theorem gridVector_index (k : ℕ) (f : ℕ→ℂ) (s : ℂ) (t : ℤ) :
    gridVector k f s (gridIndex t)=grid k f 84 t s := by
  unfold gridVector
  have he : ((gridIndex t).val:ℤ)=t%84:=Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  rw [he]
  simpa only [Nat.cast_ofNat] using grid_mod k f (by decide : 0<84) t s

theorem gridSample_grid (k : ℕ) (f : ℕ→ℂ) (q : ℕ) (t : ℤ) (s : ℂ) :
    gridSample q t (gridVector k f s)=gridSum k f 84 q t s := by
  unfold gridSample gridSum
  simp_rw [gridVector_index]

theorem gridSample_add (q : ℕ) (t : ℤ) (w v : Fin 84→ℂ) :
    gridSample q t (w+v)=gridSample q t w+gridSample q t v := by
  simp [gridSample,Finset.sum_add_distrib]

theorem gridSample_smul (q : ℕ) (t : ℤ) (c : ℂ) (w : Fin 84→ℂ) :
    gridSample q t (c • w)=c*gridSample q t w := by
  simp [gridSample,Finset.mul_sum]

def gridGroupLeading (m : ℕ) (_f : ℕ→ℂ) (ε s : ℂ) (w : Fin 84→ℂ) (i : Fin 46) : ℂ :=
  w (gridGroupIndex i)-gridMatrixScalar m (ε*I^(2*m)) i 0 s*w (gridGroupTarget i)

def gridRamanujanLeading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 84→ℂ) (i : Fin 10) : ℂ :=
  gridSample (gridTaylorQ i) (gridTaylorT i) w-
    gridTaylorCoefficient m f ε i 0 s*gridSample (gridTaylorQ i) (gridTaylorPartner i) w

def gridHalfLeading (w : Fin 84→ℂ) (i : Fin 20) : ℂ :=
  w (gridIndex (gridHalfSpecs i))+w (gridIndex (gridHalfSpecs i+42))

def gridHeckeLeading (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (w : Fin 84→ℂ) (i : Fin 5) : ℂ :=
  let j:=gridHeckeSpecs i
  w (gridIndex j)+w (gridIndex (j+28))+w (gridIndex (j+56))-
    ((Real.sqrt 3:ℂ)*f 3)*(3:ℂ)^((m:ℂ)-s)*w (gridIndex (3*j))+
    ((3:ℂ)^((m:ℂ)-s))^2*w (gridIndex (9*j))

def gridLeadingRows (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 84→ℂ) : Fin 86→ℂ :=
  gridAssemble (gridGroupLeading m f ε s w) (gridRamanujanLeading m f ε s w)
    (fun i => gridSample (gridEntireSpecs i) 0 w) (gridHeckeLeading m f s w)
    (gridHalfLeading w) (w 53)

def gridShiftRows (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (w : Fin 84→ℂ) : Fin 86→ℂ :=
  gridAssemble
    (fun i => gridMatrixScalar m (ε*I^(2*m)) i (n+1) s*w (gridGroupTarget i))
    (fun i => gridTaylorCoefficient m f ε i (n+1) s*gridSample (gridTaylorQ i) (gridTaylorPartner i) w)
    0 0 0 0

end SmallLevelTwentyEightGrid
end
end

/-! ## TwentyEightMatrixSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightGrid
open Complex Set Matrix SmallLevelTaylor SmallLevelAdditive

def errorVector (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (E : Fin 46→ℕ→ℂ→ℂ)
    (M : ℕ) (s : ℂ) : Fin 86→ℂ :=
  gridAssemble (fun i => E i M s) (fun i => gridTaylorError m f ε i M s)
    (fun i => ramanujanEntire 28 (2*m) f (gridEntireSpecs i) s) 0 0 0

theorem hecke_grid (m : ℕ) (f : ℕ→ℂ) (s : ℂ) (i : Fin 5) :
    gridHeckeLeading m f s (gridVector (2*m) f s) i=gridHeckeThree m f (gridHeckeSpecs i) s := by
  simp only [gridHeckeLeading,gridHeckeThree,gridVector_index]

theorem half_grid (k : ℕ) (f : ℕ→ℂ) (s : ℂ) (i : Fin 20) :
    gridHalfLeading (gridVector k f s) i=gridHalf k f (gridHalfSpecs i) s := by
  simp only [gridHalfLeading,gridHalf,gridVector_index]

/-- Every selected original row except the separately imposed quotient gauge
holds on a common initial half-plane, with errors on arbitrarily enlarged
half-planes. The exceptional gauge is deliberately excluded here. -/
theorem coherent_raw_system {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) {ε : ℂ}
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ, ∃ E : Fin 46→ℕ→ℂ→ℂ,
      (∀ i : Fin 84, ∀ s : ℂ, B<s.re → AnalyticAt ℂ (fun z => gridVector (2*m) f z i) s) ∧
      (∀ M : ℕ, ∀ i : Fin 86, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (fun z => errorVector m f ε E M z i) s) ∧
      ∀ M : ℕ, ∀ s : ℂ, B<s.re → ∀ i : Fin 86, i≠82 →
        gridLeadingRows m f ε s (gridVector (2*m) f s) i=
          errorVector m f ε E M s i+
            ∑ n∈Finset.range M, gridShiftRows m f ε n s (gridVector (2*m) f (s+((n:ℂ)+1))) i := by
  choose b E hG using grid_matrix_rows_of_fricke m hf (grid_physical_sign m hε)
    (grid_fricke_of_laws m hε hlaw)
  let BG : ℝ:=Finset.univ.sup' Finset.univ_nonempty b
  have hbG (i : Fin 46) : b i≤BG:=Finset.le_sup' b (Finset.mem_univ i)
  obtain ⟨BT,hT⟩:=grid_ramanujan_system_of_laws m hf hlaw
  obtain ⟨hRE,BR,hR⟩:=original_grid_entire_rows (by omega : 0<2*m) hf
  obtain ⟨BH,hH⟩:=original_grid_hecke_three hf
  obtain ⟨BB,hB⟩:=original_grid_half hf
  obtain ⟨BF,hF⟩:=SmallLevelAdditive.original_common_halfplane hf
  let bounds : Fin 6→ℝ:=![BG,BT,BR,BH,BB,BF]
  let B : ℝ:=Finset.univ.sup' Finset.univ_nonempty bounds
  have hb (i : Fin 6) : bounds i≤B:=Finset.le_sup' bounds (Finset.mem_univ i)
  have hBG : BG≤B:=hb 0
  have hBT : BT≤B:=hb 1
  have hBR : BR≤B:=hb 2
  have hBH : BH≤B:=hb 3
  have hBB : BB≤B:=hb 4
  have hBF : BF≤B:=hb 5
  refine ⟨B,E,?_,?_,?_⟩
  · intro i s hs
    exact (hF (((i:ℕ):ℝ)/84) s (lt_of_le_of_lt hBF hs)).1
  · intro M i s hs
    have hg (j : Fin 46) : AnalyticAt ℂ (E j M) s := by
      apply (hG j M).1 s
      change b j-((M:ℝ)+1)<s.re
      linarith [hbG j]
    have ht (j : Fin 10) : AnalyticAt ℂ (gridTaylorError m f ε j M) s := by
      apply (hT j M).1 s
      change BT-((M:ℝ)+1)<s.re
      linarith
    fin_cases i
    · exact hg 0
    · exact hg 1
    · exact hg 2
    · exact hg 3
    · exact hg 4
    · exact hRE 0 s
    · exact hg 5
    · exact hg 6
    · exact hg 7
    · exact hg 8
    · exact hg 9
    · exact hg 10
    · exact hg 11
    · exact hg 12
    · exact hg 13
    · exact hg 14
    · exact hg 15
    · exact hg 16
    · exact hg 17
    · exact hg 18
    · exact hg 19
    · exact hg 20
    · exact hg 21
    · exact hg 22
    · exact hg 23
    · exact hg 24
    · exact hg 25
    · exact hg 26
    · exact hg 27
    · exact hg 28
    · exact hg 29
    · exact hg 30
    · exact hg 31
    · exact hg 32
    · exact hg 33
    · exact hg 34
    · exact hg 35
    · exact hg 36
    · exact hg 37
    · exact hg 38
    · exact hg 39
    · exact hg 40
    · exact hg 41
    · exact hg 42
    · exact hg 43
    · exact hg 44
    · exact hg 45
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact hRE 1 s
    · exact ht 0
    · exact ht 1
    · exact ht 2
    · exact ht 3
    · exact ht 4
    · exact ht 5
    · exact ht 6
    · exact ht 7
    · exact ht 8
    · exact hRE 2 s
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact analyticAt_const
    · exact ht 9
    · exact hRE 3 s
    · exact analyticAt_const
  · intro M s hs i hi
    have hg (j : Fin 46):=(hG j M).2 s (lt_of_le_of_lt ((hbG j).trans hBG) hs)
    have ht (j : Fin 10):=(hT j M).2 s (lt_of_le_of_lt hBT hs)
    have hr (j : Fin 4):=hR j s (lt_of_le_of_lt hBR hs)
    have hh (j : Fin 5):=hH (gridHeckeSpecs j) s (lt_of_le_of_lt hBH hs)
    have hb' (j : Fin 20):=hB (gridHalfSpecs j) s (lt_of_le_of_lt hBB hs)
    fin_cases i
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 0
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 1
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 2
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 3
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 4
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using (hr 0).symm
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 5
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 6
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 7
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 8
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 9
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 10
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 11
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 12
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 13
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 14
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 15
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 16
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 17
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 18
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 19
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 20
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 21
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 22
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 23
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 24
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 25
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 26
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 27
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 28
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 29
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 30
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 31
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 32
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 33
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 34
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 35
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 36
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 37
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 38
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 39
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 40
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 41
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 42
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 43
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 44
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hg 45
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 0
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 1
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 2
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 3
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 4
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 5
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 6
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 7
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 8
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 9
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 10
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 11
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 12
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 13
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 14
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 15
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 16
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 17
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 18
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hb' 19
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using (hr 1).symm
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using ht 0
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using ht 1
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using ht 2
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using ht 3
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using ht 4
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using ht 5
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using ht 6
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using ht 7
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using ht 8
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using (hr 2).symm
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hh 0
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hh 1
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hh 2
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hh 3
    · exact (hi rfl).elim
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using ht 9
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using (hr 3).symm
    · simpa [gridLeadingRows,gridShiftRows,errorVector,gridAssemble,Fin.isValue,
        gridGroupLeading,gridVector,gridRamanujanLeading,gridSample_grid,
        hecke_grid,half_grid,Pi.zero_apply,Finset.sum_const_zero,add_zero,zero_add] using hh 4

#print axioms coherent_raw_system
end SmallLevelTwentyEightGrid
end
end

/-! ## TwentyEightRates -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightParameters
open Complex SmallLevelPrimeRates SmallLevelTwentyEightGrid

def groupPowers : Fin 46→ℤ×ℤ×ℤ
  | 0 => (0, 2, 1)
  | 1 => (2, 0, 1)
  | 2 => (0, 2, 1)
  | 3 => (0, 0, 1)
  | 4 => (-2, 2, 1)
  | 5 => (-2, -2, -1)
  | 6 => (0, -2, -1)
  | 7 => (-2, 0, -1)
  | 8 => (2, -2, -1)
  | 9 => (0, 0, -1)
  | 10 => (-2, -2, 1)
  | 11 => (-2, 2, -1)
  | 12 => (2, 0, -1)
  | 13 => (0, -2, 1)
  | 14 => (0, 2, -1)
  | 15 => (-2, 0, 1)
  | 16 => (2, -2, 1)
  | 17 => (2, 2, -1)
  | 18 => (-2, 2, 1)
  | 19 => (2, 2, -1)
  | 20 => (2, -2, 1)
  | 21 => (0, 2, -1)
  | 22 => (0, -2, 1)
  | 23 => (2, 0, -1)
  | 24 => (-2, 2, -1)
  | 25 => (-2, -2, 1)
  | 26 => (0, 0, -1)
  | 27 => (2, -2, -1)
  | 28 => (-2, 0, -1)
  | 29 => (0, -2, -1)
  | 30 => (-2, -2, -1)
  | 31 => (-2, -2, -1)
  | 32 => (0, -2, -1)
  | 33 => (-2, 0, -1)
  | 34 => (2, -2, -1)
  | 35 => (-2, -2, 1)
  | 36 => (-2, 2, -1)
  | 37 => (2, 0, -1)
  | 38 => (0, 2, -1)
  | 39 => (-2, -2, -1)
  | 40 => (2, 2, 0)
  | 41 => (0, 2, 0)
  | 42 => (-2, 2, 0)
  | 43 => (2, -2, 0)
  | 44 => (0, -2, 0)
  | _ => (-2, -2, 0)

def taylorPowers : Fin 10→ℤ×ℤ×ℤ
  | 0 => (-2, 0, -1)
  | 1 => (-2, 0, -1)
  | 2 => (0, 0, -1)
  | 3 => (0, 0, -1)
  | 4 => (2, 0, -1)
  | 5 => (2, 0, -1)
  | 6 => (-2, -2, 0)
  | 7 => (-2, -2, 0)
  | 8 => (0, -2, 0)
  | _ => (-2, 0, 0)

def taylorRate (i : Fin 10) : ℚ := (gridTaylorL i:ℚ)*((gridTaylorT i:ℚ)/84)^2

theorem groupRate_factor (i : Fin 46) :
    gridGroupRate i=(2:ℚ)^(groupPowers i).1*(3:ℚ)^(groupPowers i).2.1*(7:ℚ)^(groupPowers i).2.2 := by
  fin_cases i <;> norm_num [gridGroupRate,groupPowers]

theorem taylorRate_factor (i : Fin 10) :
    taylorRate i=(2:ℚ)^(taylorPowers i).1*(3:ℚ)^(taylorPowers i).2.1*(7:ℚ)^(taylorPowers i).2.2 := by
  fin_cases i <;> norm_num [taylorRate,gridTaylorL,gridTaylorQ,gridTaylorT,gridTaylorSpecs,taylorPowers]

theorem groupRate_complex (i : Fin 46) (h : ℂ) :
    (gridGroupRate i:ℂ)^h=monomial (groupPowers i) ((2:ℂ)^h) ((3:ℂ)^h) ((7:ℂ)^h) :=
  rational_power 2 3 7 (by decide) (by decide) (by decide) _ _ (groupRate_factor i) h

theorem taylorRate_complex (i : Fin 10) (h : ℂ) :
    (taylorRate i:ℂ)^h=monomial (taylorPowers i) ((2:ℂ)^h) ((3:ℂ)^h) ((7:ℂ)^h) :=
  rational_power 2 3 7 (by decide) (by decide) (by decide) _ _ (taylorRate_factor i) h

theorem matrixScalar_leading (m : ℕ) (ε s : ℂ) (i : Fin 46) :
    gridMatrixScalar m (phase m ε) i 0 s=
      gridSourceSign (phase m ε) (gridGroupSource i)*
        monomial (groupPowers i) (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) := by
  simp only [gridMatrixScalar,pow_zero,Ring.choose_zero_right,mul_one]
  rw [groupRate_complex]
  rfl

theorem taylorScalar_leading (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i : Fin 10) :
    gridTaylorCoefficient m f ε i 0 s=
      (FinitenessNormalizedTwistProduct.root 28 f (gridTaylorQ i))*phase m ε*
        monomial (taylorPowers i) (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) := by
  have hm : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
  have hb : (((gridTaylorL i:ℝ)*((gridTaylorT i:ℝ)/84)^2:ℝ):ℂ)=(taylorRate i:ℂ) := by
    simp [taylorRate]
  unfold gridTaylorCoefficient SmallLevelTaylor.taylorRowScalar
  simp only [pow_zero,Ring.choose_zero_right,mul_one,hm]
  rw [hb,taylorRate_complex]
  unfold phase parameter
  ring

theorem taylor_root (f : ℕ→ℂ) (i : Fin 10) :
    FinitenessNormalizedTwistProduct.root 28 f (gridTaylorQ i)=
      if i.val<6 then 1 else -sigmaSeven f := by
  fin_cases i <;> norm_num [gridTaylorQ,gridTaylorSpecs,root_three,root_seven]

#print axioms groupRate_complex
#print axioms taylorRate_complex
#print axioms matrixScalar_leading
#print axioms taylorScalar_leading
#print axioms taylor_root
end SmallLevelTwentyEightParameters
end
end

/-! ## TwentyEightLeadingComparison -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
-- A common finite-case normalization list is used for three different row types.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightParameters
open Complex Matrix SmallLevelPrimeRates SmallLevelTwentyEightGrid
open SmallLevelTwentyEightLaurent FinitenessRamanujanSum

theorem negative_parameter (p m : ℕ) (s : ℂ) :
    (p:ℂ)^((m:ℂ)-s)=1/parameter p m s := by
  unfold parameter
  rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg,one_div]

/-- The algebraic system is the literal selected 86-row Mellin system. -/
theorem leadingRows_actual (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (w : Fin 84→ℂ) :
    gridLeadingRows m f ε s w=
      leadingRows (phase m ε) (sigmaSeven f)
        (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) ((Real.sqrt 3:ℂ)*f 3) w := by
  have hX:=parameter_ne_zero 2 m (by decide) s
  have hY:=parameter_ne_zero 3 m (by decide) s
  have hZ:=parameter_ne_zero 7 m (by decide) s
  have he : ε*I^(2*m)=phase m ε:=rfl
  have hn3 := negative_parameter 3 m s
  norm_num only [Nat.cast_ofNat] at hn3
  funext i
  fin_cases i <;>
    norm_num [gridLeadingRows,gridAssemble,gridGroupLeading,gridRamanujanLeading,
      gridHeckeLeading,gridHalfLeading,gridHalfSpecs,leadingRows,he,matrixScalar_leading,taylorScalar_leading,
      hn3,negative_parameter,gridGroupSource,gridGroupIndex,gridGroupTarget,
      gridSourceSign,groupPowers,taylorPowers,monomial,gridSample,gridIndex,
      gridTaylorQ,gridTaylorT,gridTaylorL,gridTaylorD,gridTaylorPartner,gridTaylorSpecs,
      gridHeckeSpecs,gridEntireSpecs,residues,Finset.sum_filter,Finset.sum_range_succ,
      root_three,root_seven] <;>
    (try field_simp [hX,hY,hZ]) <;> (try simp) <;> ring

#print axioms leadingRows_actual
end SmallLevelTwentyEightParameters
end
end

/-! ## TwentyEightTaylorFactors -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightParameters
open Complex SmallLevelPrimeRates SmallLevelTwentyEightGrid

def taylorDerivative (i : Fin 10) : ℚ := (gridTaylorL i:ℚ)*(gridTaylorT i:ℚ)/84

theorem matrixScalar_factor (m : ℕ) (ε : ℂ) (i : Fin 46) (n : ℕ) (s : ℂ) :
    gridMatrixScalar m (phase m ε) i n s=
      (gridSourceSign (phase m ε) (gridGroupSource i)*
        monomial (groupPowers i) (parameter 2 m s) (parameter 3 m s) (parameter 7 m s))*
      I^n*(gridGroupDerivative i:ℂ)^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  rw [gridMatrixScalar,groupRate_complex,mul_pow]
  norm_num only [parameter,Nat.cast_ofNat]
  ring

theorem taylorScalar_factor (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (i : Fin 10) (n : ℕ) (s : ℂ) :
    gridTaylorCoefficient m f ε i n s=
      (FinitenessNormalizedTwistProduct.root 28 f (gridTaylorQ i)*phase m ε*
        monomial (taylorPowers i) (parameter 2 m s) (parameter 3 m s) (parameter 7 m s))*
      I^n*(taylorDerivative i:ℂ)^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
  have hc : gridTaylorCoefficient m f ε i n s=
      gridTaylorCoefficient m f ε i 0 s*
        I^n*(taylorDerivative i:ℂ)^n*Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n := by
    unfold gridTaylorCoefficient SmallLevelTaylor.taylorRowScalar taylorDerivative
    simp only [pow_zero,Ring.choose_zero_right,mul_one,Rat.cast_div,Rat.cast_mul,
      Rat.cast_natCast,Rat.cast_intCast,Rat.cast_ofNat,Complex.ofReal_div,
      Complex.ofReal_intCast,Complex.ofReal_natCast,Complex.ofReal_ofNat,mul_pow,div_pow]
    ring
  rw [hc,taylorScalar_leading]

#print axioms matrixScalar_factor
#print axioms taylorScalar_factor
end SmallLevelTwentyEightParameters
end
end

/-! ## TwentyEightShiftComparison -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightParameters
open Complex Matrix SmallLevelPrimeRates SmallLevelTwentyEightGrid SmallLevelTwentyEightLaurent
open FinitenessRamanujanSum

theorem gridShiftRows_actual (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (w : Fin 84→ℂ) (i : Fin 86) :
    gridShiftRows m f ε n s w i=
      (I^(n+1)*Ring.choose (s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)) (n+1))*
      positiveTaylorRows (phase m ε) (sigmaSeven f)
        (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) n w i := by
  have hX:=parameter_ne_zero 2 m (by decide) s
  have hY:=parameter_ne_zero 3 m (by decide) s
  have hZ:=parameter_ne_zero 7 m (by decide) s
  have he : ε*I^(2*m)=phase m ε:=rfl
  fin_cases i <;>
    norm_num [gridShiftRows,gridAssemble,matrixScalar_factor,taylorScalar_factor,he,
      positiveTaylorRows,gridGroupTarget,gridGroupSource,gridGroupDerivative,
      gridSourceSign,groupPowers,taylorPowers,taylorDerivative,monomial,
      gridTaylorQ,gridTaylorT,gridTaylorL,gridTaylorD,gridTaylorPartner,gridTaylorSpecs,
      gridSample,gridIndex,residues,Finset.sum_filter,Finset.sum_range_succ,
      root_three,root_seven,pow_succ] <;>
    (try field_simp [hX,hY,hZ]) <;> (try simp) <;> ring <;> simp


#print axioms gridShiftRows_actual
end SmallLevelTwentyEightParameters
end
end

/-! ## TwentyEightQuotientSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex Matrix SmallLevelPrimeRates SmallLevelTwentyEightParameters
open SmallLevelTwentyEightLaurent SmallLevelTwentyEightGrid
open QuantitativeArithmeticSmallLevelTwentyEight (quotientVector oddMode)

def quotientGridVector (k : ℕ) (f : ℕ→ℂ) (s : ℂ) : Fin 84→ℂ :=
  quotientVector (gridVector k f s)

theorem shifted_quotient_row (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s t : ℂ) (i : Fin 86) :
    (extendedShift m f ε n s *ᵥ quotientGridVector (2*m) f t) i=
      gridShiftRows m f ε n s (gridVector (2*m) f t) i := by
  change (∑ j,extendedShift m f ε n s i j*quotientGridVector (2*m) f t j)=_
  rw [extendedShift_actual,quotientGridVector,positive_taylor_quotient]
  exact (gridShiftRows_actual m f ε n s (gridVector (2*m) f t) i).symm

/-- The closed quotient system is derived from the original Euler solution.
The gauge is imposed algebraically; no continuation of the subtracted
53-coordinate occurs among the hypotheses or analytic error terms. -/
theorem coherent_quotient_system {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) {ε : ℂ}
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ, ∃ E : Fin 46→ℕ→ℂ→ℂ,
      (∀ i : Fin 84, ∀ s : ℂ, B<s.re → AnalyticAt ℂ (fun z => quotientGridVector (2*m) f z i) s) ∧
      (∀ M : ℕ, ∀ i : Fin 86, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (fun z => errorVector m f ε E M z i) s) ∧
      ∀ M : ℕ, ∀ s : ℂ, B<s.re →
        extendedLeading m f ε s *ᵥ quotientGridVector (2*m) f s=
          errorVector m f ε E M s+
            ∑ n∈Finset.range M, extendedShift m f ε n s *ᵥ
              quotientGridVector (2*m) f (s+((n:ℂ)+1)) := by
  obtain ⟨B,E,hG,hE,hrow⟩:=coherent_raw_system hm hf hε hlaw
  refine ⟨B,E,?_,hE,?_⟩
  · intro i s hs
    change AnalyticAt ℂ (fun z => gridVector (2*m) f z i-gridVector (2*m) f z 53*oddMode i) s
    exact (hG i s hs).sub ((hG 53 s hs).mul analyticAt_const)
  · intro M s hs
    rw [extendedLeading_actual]
    funext i
    simp only [Pi.add_apply,Finset.sum_apply]
    simp_rw [shifted_quotient_row]
    by_cases hi : i=82
    · subst i
      simpa only [quotientGridVector,errorVector,gridShiftRows,gridAssemble,
        Pi.zero_apply,Finset.sum_const_zero,zero_add] using
        leading_quotient_gauge (phase m ε) (sigmaSeven f) (parameter 2 m s)
          (parameter 3 m s) (parameter 7 m s) ((Real.sqrt 3:ℂ)*f 3) (gridVector (2*m) f s)
    · rw [quotientGridVector,leading_quotient _ _ _ _ _ _ _ i hi]
      have h:=hrow M s hs i hi
      rw [leadingRows_actual] at h
      exact h

#print axioms shifted_quotient_row
#print axioms coherent_quotient_system
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightContinuedSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex Matrix Filter Set SmallLevelTwentyEightGrid
open scoped Topology

/-- Meromorphic continuation of the quotient of the original 84-grid.
The subtracted original coordinate is not separately continued. -/
theorem grid_continuation_of_laws {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ, ∃ G : ℂ→Fin 84→ℂ,
      (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      ∀ z, B<z.re → G z=quotientGridVector (2*m) f z := by
  obtain ⟨B,E,hF,hH,hrow⟩:=coherent_quotient_system hm hf hε hlaw
  refine ⟨B,?_⟩
  apply SmallLevelContinuation.closed_system_continuation B (quotientGridVector (2*m) f)
    (coreLeading m f ε) (coreShift m f ε)
    (fun n z (i : Fin 84) => errorVector m f ε E n z ⟨i.val,by omega⟩)
    hF (fun z i j => extendedLeading_analytic m f ε z ⟨i.val,by omega⟩ j)
    (coreLeading_nonsingular hf ε hε)
    (fun n z i j => extendedShift_analytic m f ε n z ⟨i.val,by omega⟩ j)
    (fun n i z hz => hH n ⟨i.val,by omega⟩ z hz)
  intro n z hz i
  simpa only [coreLeading,coreShift,SmallLevelTwentyEightLaurent.coreMatrix,extendedLeading,
    Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply] using
    congrFun (hrow n z hz) ⟨i.val,by omega⟩

theorem continued_extended_system {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ B : ℝ, ∃ G : ℂ→Fin 84→ℂ, ∃ E : Fin 46→ℕ→ℂ→ℂ,
      (∀ i x, MeromorphicNFAt (fun z => G z i) x) ∧
      (∀ z, B<z.re → G z=quotientGridVector (2*m) f z) ∧
      (∀ i z, B<z.re → AnalyticAt ℂ (fun w => G w i) z) ∧
      (∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re →
        AnalyticAt ℂ (fun w => errorVector m f ε E n w i) z) ∧
      ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
        (fun z => ∑ j, extendedLeading m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
          (fun z => errorVector m f ε E n z i+
            ∑ a∈Finset.range n, ∑ j, extendedShift m f ε a z i j*G (z+((a:ℂ)+1)) j) := by
  obtain ⟨B₀,G,hG,heG⟩:=grid_continuation_of_laws hm hf ε hε hlaw
  obtain ⟨B₁,E,hF,hH,hrow⟩:=coherent_quotient_system hm hf hε hlaw
  let B : ℝ:=max B₀ B₁
  have hGF (z : ℂ) (hz : B<z.re) : G z=quotientGridVector (2*m) f z :=
    heG z (lt_of_le_of_lt (le_max_left _ _) hz)
  have hH' (n : ℕ) (i : Fin 86) (z : ℂ) (hz : B-((n:ℝ)+1)<z.re) :
      AnalyticAt ℂ (fun w => errorVector m f ε E n w i) z := by
    apply hH n i z
    have hb : B₁≤B:=le_max_right _ _
    linarith
  refine ⟨B,G,E,hG,hGF,?_,hH',?_⟩
  · intro i z hz
    apply (hF i z (lt_of_le_of_lt (le_max_right _ _) hz)).congr
    have hn : ∀ᶠ w in 𝓝 z, B<w.re:=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    filter_upwards [hn] with w hw
    exact (congrFun (hGF w hw) i).symm
  · apply QuantitativeArithmeticRectangularContinuation.continued_meromorphic_rows
      B (quotientGridVector (2*m) f) G (extendedLeading m f ε) (extendedShift m f ε)
      (errorVector m f ε E) (fun i x => (hG i x).meromorphicAt) hGF
      (extendedLeading_analytic m f ε) (extendedShift_analytic m f ε)
      (fun n i z hz => (hH' n i z hz).meromorphicAt)
    intro n z hz
    exact hrow n z (lt_of_le_of_lt (le_max_right _ _) hz)


#print axioms grid_continuation_of_laws
#print axioms continued_extended_system
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightPoleSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex Matrix Filter SmallLevelTwentyEightGrid
open scoped Topology

/-- The actual continued rectangular Mellin system, including its original
right-half-plane identification. No pole bound is part of this structure. -/
structure PoleSystem (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) where
  B : ℝ
  G : ℂ→Fin 84→ℂ
  H : ℕ→ℂ→Fin 86→ℂ
  meromorphic : ∀ i z, MeromorphicNFAt (fun s => G s i) z
  original : ∀ z, B<z.re → G z=quotientGridVector (2*m) f z
  halfplane : ∀ i z, B<z.re → AnalyticAt ℂ (fun s => G s i) z
  error : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun s => H n s i) z
  rows : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
    (fun z => ∑ j,extendedLeading m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
      (fun z => H n z i+∑ b∈Finset.range n,
        ∑ j,extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j)

theorem exists_poleSystem {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    Nonempty (PoleSystem m f ε) := by
  obtain ⟨B,G,E,hG,hGF,hhalf,hH,hrow⟩:=continued_extended_system hm hf ε hε hlaw
  exact ⟨⟨B,G,errorVector m f ε E,hG,hGF,hhalf,hH,hrow⟩⟩

#print axioms exists_poleSystem
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightRightmostPole -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex Matrix Filter SmallLevelTwentyEightParameters
open SmallLevelFiniteShift QuantitativeArithmeticUniversalPoleVector
open scoped Topology

theorem PoleSystem.regular_tail_pole_at_weight {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) {ε : ℂ} (hε : ε=1 ∨ ε= -1)
    (S : PoleSystem m f ε) (x : ℂ) (w : Fin 84→ℂ) (hw : IsLeadingVector S.G x w)
    (htail : ∀ d b : ℕ, d≤b → ∀ i j, ∃ R : ℂ→ℂ, AnalyticAt ℂ R (x-d) ∧
      (fun z => extendedShift m f ε b z i j*S.G (z+((b:ℂ)+1)) j)=ᶠ[𝓝[≠] (x-d)] R) :
    x=((2*m:ℕ):ℂ) := by
  by_contra hx
  obtain ⟨he,hη,hσ,ha⟩:=candidate_of_regular_tails hf ε hε S.B S.G S.H
    S.error S.rows x hx w hw htail
  have hm2 : 2≤m := by
    have hm1 : m≠1 := by intro h; subst m; norm_num at he; exact hx he
    omega
  obtain ⟨v,hv,hvk⟩:=continued_regular_block_kernel S.B S.G
    (extendedLeading m f ε) (extendedShift m f ε) S.H x 3
    S.meromorphic (extendedLeading_analytic m f ε) (extendedShift_analytic m f ε)
    S.error (fun n b hb i j => htail n.val b hb i j) S.rows
    (hw.exists_pole (fun j => S.meromorphic j x))
  apply hv
  apply SmallLevelTwentyEightJetBlock.actual_block_kernel_zero m hm2 f ε
    hη hσ ha v
  simpa only [he] using hvk

theorem PoleSystem.rightmost_pole_at_weight {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) {ε : ℂ} (hε : ε=1 ∨ ε= -1)
    (S : PoleSystem m f ε) (x : ℂ) (w : Fin 84→ℂ) (hw : IsLeadingVector S.G x w)
    (hshift : ∀ n : ℕ, 0<n → ∀ j,0≤meromorphicOrderAt (fun z => S.G z j) (x+n)) :
    x=((2*m:ℕ):ℂ) :=
  S.regular_tail_pole_at_weight hm hf hε x w hw
    (fun d b hb i j => regular_pole_tail (extendedShift m f ε) (extendedShift_analytic m f ε)
      S.G S.meromorphic x d hshift b hb i j)

#print axioms PoleSystem.regular_tail_pole_at_weight
#print axioms PoleSystem.rightmost_pole_at_weight
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightUpperRegularity -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex QuantitativeArithmeticUniversalPoleVector

theorem PoleSystem.regular_above_weight {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) {ε : ℂ} (hε : ε=1 ∨ ε= -1)
    (S : PoleSystem m f ε) (x : ℂ) (hx : ((2*m:ℕ):ℝ)<x.re) (i : Fin 84) :
    0≤meromorphicOrderAt (fun z => S.G z i) x := by
  by_contra! hi
  obtain ⟨n,hp,hshift⟩:=SmallLevelPoleGrid.rightmost_pole (fun j z => S.G z j)
    (x:=x) ⟨i,hi⟩ S.B S.halfplane
  obtain ⟨w,hw⟩:=exists_leading_vector S.G (x+n)
    (fun j => (S.meromorphic j _).meromorphicAt) hp
  have he:=S.rightmost_pole_at_weight hm hf hε (x+n) w hw hshift
  have hr:=congrArg Complex.re he
  simp only [Complex.add_re,Complex.natCast_re] at hr
  have hn : (0:ℝ)≤n:=Nat.cast_nonneg n
  linarith

#print axioms PoleSystem.regular_above_weight
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightFirstRowsAnalytic -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightLaurent
open Complex SmallLevelPrimeRates

theorem firstRows_analytic (η σ a : ℂ) (m : ℕ) (w : Fin 84→ℂ) (z : ℂ) (i : Fin 86) :
    AnalyticAt ℂ (fun s => firstRows η σ (parameter 2 m s)
      (parameter 3 m s) (parameter 7 m s) a w i) z := by
  have hX:=parameter_ne_zero 2 m (by decide) z
  have hY:=parameter_ne_zero 3 m (by decide) z
  have hZ:=parameter_ne_zero 7 m (by decide) z
  have hXa:=parameter_analytic 2 m (by decide) z
  have hYa:=parameter_analytic 3 m (by decide) z
  have hZa:=parameter_analytic 7 m (by decide) z
  fin_cases i <;> norm_num [firstRows]
  all_goals fun_prop (disch := simp [hX,hY,hZ])

theorem firstRows_basis (η σ X Y Z a : ℂ) (w : Fin 84→ℂ) (i : Fin 86) :
    (∑ j,firstRows η σ X Y Z a (Pi.single j 1) i*w j)=
      firstRows η σ X Y Z a w i := by
  classical
  fin_cases i <;>
    simp [firstRows,Pi.single_apply,div_eq_mul_inv,mul_add,add_mul,sub_mul,
      mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,←mul_assoc]
  all_goals ring

#print axioms firstRows_analytic
#print axioms firstRows_basis
end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightSelectedRegularizedFirstShift -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex Matrix Filter SmallLevelPrimeRates SmallLevelTwentyEightParameters
open SmallLevelTwentyEightLaurent QuantitativeArithmeticUniversalPoleVector
open scoped Topology

theorem selected_regularized_polynomial_first_shift {ρ : Type*} [Fintype ρ]
    (rows : ρ→Fin 86) (η σ a : ℂ)
    (coeff : ℂ→ℂ→ℂ→ρ→ℂ)
    (hsyz : ∀ X Y Z : ℂ, X≠0 → Y≠0 → Z≠0 → ∀ w : Fin 84→ℂ,
      ∑ i,coeff X Y Z i*leadingRows η σ X Y Z a w (rows i)=0)
    (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (hη : phase m ε=η) (hσ : sigmaSeven f=σ)
    (ha : (Real.sqrt 3:ℂ)*f 3=a)
    (hcoeff : ∀ z i, AnalyticAt ℂ
      (fun s => coeff (parameter 2 m s) (parameter 3 m s) (parameter 7 m s) i) z)
    (B : ℝ) (G : ℂ→Fin 84→ℂ) (H : ℕ→ℂ→Fin 86→ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun s => H n s i) z)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j,extendedLeading m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ b∈Finset.range n,
          ∑ j,extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j))
    (x : ℂ) (w : Fin 84→ℂ)
    (hw : IsLeadingVector (fun z j => (z-((2*m:ℕ):ℂ))*G z j) x w)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n)) :
    ∑ i,coeff (parameter 2 m x/2) (parameter 3 m x/3) (parameter 7 m x/7) i*
      firstRows η σ (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) a w (rows i)=0 := by
  classical
  let K : ℂ→ρ→ℂ:=fun z => coeff (parameter 2 m z) (parameter 3 m z) (parameter 7 m z)
  let A : ℂ→Matrix ρ (Fin 84) ℂ:=fun z i => extendedLeading m f ε z (rows i)
  let C : ℕ→ℂ→Matrix ρ (Fin 84) ℂ:=fun n z i => extendedShift m f ε n z (rows i)
  let L : ℂ→Matrix Unit ρ ℂ:=fun z _ i => K z i
  let D : ℂ→Matrix Unit (Fin 84) ℂ:=fun z _ j =>
    I*∑ i,K (z-1) i*firstRows η σ (parameter 2 m z) (parameter 3 m z)
      (parameter 7 m z) a (Pi.single j 1) (rows i)
  have hKA (z : ℂ) (q : Fin 84→ℂ) : ∑ i,K z i*(∑ j,A z i j*q j)=0 := by
    have he (i : Fin 86) : (∑ j,extendedLeading m f ε z i j*q j)=
        leadingRows (phase m ε) (sigmaSeven f)
          (parameter 2 m z) (parameter 3 m z) (parameter 7 m z) ((Real.sqrt 3:ℂ)*f 3) q i :=
      congrFun (extendedLeading_actual m f ε z q) i
    simp only [A,he,hη,hσ,ha,K]
    exact hsyz _ _ _ (parameter_ne_zero 2 m (by decide) z)
      (parameter_ne_zero 3 m (by decide) z) (parameter_ne_zero 7 m (by decide) z) q
  have hLA (z : ℂ) : L z*A z=0 := by
    ext r j
    have hh:=hKA z (Pi.single j 1)
    simpa [Matrix.mul_apply,L,A,Pi.single_apply] using hh
  have hD (r : Unit) (j : Fin 84) : AnalyticAt ℂ (fun z => D z r j) x := by
    apply analyticAt_const.mul
    apply Finset.analyticAt_fun_sum
    intro i _
    exact ((hcoeff (x-1) i).comp (f:=fun z : ℂ => z-1)
      (analyticAt_id.sub analyticAt_const)).mul
      (firstRows_analytic η σ a m (Pi.single j 1) x (rows i))
  have hfactor (z : ℂ) (r : Unit) (j : Fin 84) :
      (L (z-1)*C 0 (z-1)) r j=(z-((2*m:ℕ):ℂ))*D z r j := by
    have he (i : ρ) : extendedShift m f ε 0 (z-1) (rows i) j=
        (I*(z-((2*m:ℕ):ℂ)))*firstRows η σ (parameter 2 m z) (parameter 3 m z)
          (parameter 7 m z) a (Pi.single j 1) (rows i) := by
      simpa only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
        Finset.mem_univ,ite_true,hη,hσ,ha] using
        firstShift_actual m f ε z (Pi.single j 1) (rows i)
    simp only [Matrix.mul_apply,L,C,D,he]
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hh:=IsLeadingVector.factored_first_shift B G A C (fun n z i => H n z (rows i)) L
    hG (fun n z i j => extendedShift_analytic m f ε n z (rows i) j)
    (fun n i z hz => hH n (rows i) z hz) (fun z _ i => hcoeff z i) hLA
    (fun n i z hz => hrow n (rows i) z hz) x hshift
    (fun z => z-((2*m:ℕ):ℂ)) D hD hfactor w hw
  have hh':=congrFun hh ()
  change (∑ j,(I*∑ i,K (x-1) i*firstRows η σ (parameter 2 m x)
    (parameter 3 m x) (parameter 7 m x) a (Pi.single j 1) (rows i))*w j)=0 at hh'
  simp only [mul_assoc,←Finset.mul_sum,Finset.sum_mul] at hh'
  rw [Finset.sum_comm] at hh'
  simp only [←Finset.mul_sum,firstRows_basis,K,
    parameter_shift 2 m (by decide),parameter_shift 3 m (by decide),
    parameter_shift 7 m (by decide),Nat.cast_ofNat] at hh'
  exact (mul_eq_zero.mp hh').resolve_left I_ne_zero

#print axioms selected_regularized_polynomial_first_shift
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightRegularizedCandidate -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex Matrix Filter SmallLevelPrimeRates SmallLevelTwentyEightParameters
open SmallLevelTwentyEightLaurent QuantitativeArithmeticUniversalPoleVector SmallLevelFiniteShift
open scoped Topology

theorem candidate_of_regularized_vector {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (ε : ℂ) (hε : ε=1 ∨ ε= -1)
    (B : ℝ) (G : ℂ→Fin 84→ℂ) (H : ℕ→ℂ→Fin 86→ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hH : ∀ (n : ℕ) i z, B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun s => H n s i) z)
    (hrow : ∀ (n : ℕ) i x, B-((n:ℝ)+1)<x.re →
      (fun z => ∑ j,extendedLeading m f ε z i j*G z j)=ᶠ[𝓝[≠] x]
        (fun z => H n z i+∑ b∈Finset.range n,
          ∑ j,extendedShift m f ε b z i j*G (z+((b:ℂ)+1)) j))
    (x : ℂ) (w : Fin 84→ℂ)
    (hw : IsLeadingVector (fun z j => (z-((2*m:ℕ):ℂ))*G z j) x w)
    (hshift : ∀ n : ℕ, 0<n → ∀ j,0≤meromorphicOrderAt (fun z => G z j) (x+n)) :
    x=(m:ℂ)+1 ∧ phase m ε= -1 ∧ sigmaSeven f= -1 ∧ (Real.sqrt 3:ℂ)*f 3= -10/3 := by
  have hη:=phase_sign m hε
  have hσ:=sigmaSeven_sign hf.toEulerData
  have hwG:=hw.of_analytic_factor (fun z => z-((2*m:ℕ):ℂ))
    (analyticAt_id.sub analyticAt_const)
  have hlead:=hwG.regular_tail_leading B G (extendedLeading m f ε) (extendedShift m f ε)
    H x w (extendedLeading_analytic m f ε x) hH
    (fun b i j => by
      simpa only [Nat.cast_zero,sub_zero] using
        (regular_pole_tail (extendedShift m f ε) (extendedShift_analytic m f ε)
          G hG x 0 hshift b (Nat.zero_le b) i j)) hrow
  rw [extendedLeading_actual] at hlead
  have hcore : coreRows (phase m ε) (sigmaSeven f)
      (parameter 2 m x) (parameter 3 m x) (parameter 7 m x) ((Real.sqrt 3:ℂ)*f 3) w=0 := by
    funext i
    exact congrFun hlead ⟨i.val,by omega⟩
  have hjet:=firstJet_equations m (phase m ε) (sigmaSeven f)
    ((Real.sqrt 3:ℂ)*f 3) x hη hσ w hcore hw.1
    (fun r rows coeff hcoeff hsyz => selected_regularized_polynomial_first_shift
      rows _ _ _ coeff hsyz m f ε rfl rfl rfl hcoeff B G H hG hH hrow x w hw hshift)
  exact physical_candidate m _ _ _ x hη hσ hjet.1 hjet.2.1 hjet.2.2

#print axioms candidate_of_regularized_vector
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightTaylorBasis -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightLaurent

theorem positiveTaylorRows_basis (η σ X Y Z : ℂ) (n : ℕ) (w : Fin 84→ℂ) (i : Fin 86) :
    (∑ j,positiveTaylorRows η σ X Y Z n (Pi.single j 1) i*w j)=
      positiveTaylorRows η σ X Y Z n w i := by
  simpa only [Matrix.mulVec,dotProduct,positiveTaylorMatrix_apply] using
    congrFun (positiveTaylorMatrix_mulVec η σ X Y Z n w) i

#print axioms positiveTaylorRows_basis
end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightRegularizedTaylor -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightJetBlock
open Complex SmallLevelTwentyEightSystem SmallLevelTwentyEightParameters SmallLevelPrimeRates
open SmallLevelTwentyEightLaurent
open SmallLevelTwentyOneKnownWords (weightOneChooseQuot weightOneChoose_factor)

def weightOneTaylorQuot (f : ℕ→ℂ) (ε : ℂ) (n : Fin 4) (z : ℂ) :
    Matrix (Fin 86) (Fin 84) ℂ:=fun i j =>
  (I^n.val*weightOneChooseQuot n z)*positiveTaylorRows (phase 1 ε) (sigmaSeven f)
    (parameter 2 1 (z-n.val)) (parameter 3 1 (z-n.val)) (parameter 7 1 (z-n.val))
    (n.val-1) (Pi.single j 1) i

theorem weightOneTaylorQuot_apply (f : ℕ→ℂ) (ε : ℂ) (n : Fin 4) (z : ℂ)
    (i : Fin 86) (w : Fin 84→ℂ) :
    (∑ j,weightOneTaylorQuot f ε n z i j*w j)=
      (I^n.val*weightOneChooseQuot n z)*positiveTaylorRows (phase 1 ε) (sigmaSeven f)
        (parameter 2 1 (z-n.val)) (parameter 3 1 (z-n.val)) (parameter 7 1 (z-n.val))
        (n.val-1) w i := by
  simp only [weightOneTaylorQuot,mul_assoc,←Finset.mul_sum,positiveTaylorRows_basis]

theorem weightOneTaylorQuot_analytic (f : ℕ→ℂ) (ε : ℂ) (n : Fin 4)
    (z : ℂ) (i : Fin 86) (j : Fin 84) :
    AnalyticAt ℂ (fun s => weightOneTaylorQuot f ε n s i j) z := by
  have hq : AnalyticAt ℂ (fun s => weightOneChooseQuot n s) z := by
    fin_cases n
    · exact analyticAt_const
    · exact analyticAt_const
    · exact (analyticAt_id.sub analyticAt_const).div_const
    · exact ((analyticAt_id.sub analyticAt_const).mul
        (analyticAt_id.sub analyticAt_const)).div_const
  exact (analyticAt_const.mul hq).mul
    ((positiveTaylorRows_analytic 1 (phase 1 ε) (sigmaSeven f) (n.val-1)
      (Pi.single j 1) i (z-n.val)).comp (f:=fun s : ℂ => s-(n.val:ℂ))
        (analyticAt_id.sub analyticAt_const))

theorem weightOneTaylorQuot_factor (f : ℕ→ℂ) (ε : ℂ) (n : Fin 4) (hn : n≠0)
    (z : ℂ) (i : Fin 86) (j : Fin 84) :
    extendedShift 1 f ε (n.val-1) (z-n.val) i j=(z-2)*weightOneTaylorQuot f ε n z i j := by
  have hnpos : 0<n.val:=Fin.pos_iff_ne_zero.mpr hn
  have hnv : n.val-1+1=n.val:=by omega
  have he:=shift_apply_laurent 1 f ε (n.val-1) (z-n.val) (Pi.single j 1) i
  simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true] at he
  rw [he,hnv]
  have hz : z-(n.val:ℂ)+(n.val:ℂ)-((2*1:ℕ):ℂ)=z-2 := by norm_num
  rw [hz,weightOneChoose_factor n hn]
  unfold weightOneTaylorQuot
  ring

#print axioms weightOneTaylorQuot_factor
#print axioms weightOneTaylorQuot_analytic
end SmallLevelTwentyEightJetBlock
end
end

/-! ## TwentyEightRegularizedBlockModel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightJetBlock
open Complex Matrix SmallLevelFiniteShift SmallLevelTwentyEightSystem
open SmallLevelTwentyEightParameters SmallLevelPrimeRates SmallLevelTwentyEightLaurent
open SmallLevelTwentyOneKnownWords (regularizedJetScale weightOneChooseQuot)

def regularizedScaledStack (w : Fin 336→ℂ) (b : Fin 4×Fin 84) : ℂ :=
  regularizedJetScale b.1*w (finProdFinEquiv b)

theorem actual_regularizedBlockRow (f : ℕ→ℂ) (ε : ℂ)
    (hη : phase 1 ε= -1) (hσ : sigmaSeven f= -1) (ha : (Real.sqrt 3:ℂ)*f 3= -10/3)
    (n : Fin 4) (r : Fin 86) (w : Fin 336→ℂ) :
    (∑ b,regularizedBlock 3 (extendedLeading 1 f ε) (extendedShift 1 f ε)
      (weightOneTaylorQuot f ε) 2 (n,r) b*regularizedScaledStack w b)=
        regularizedJetScale n*jetBlockRow n r w := by
  have hp (p t : ℕ) (hp : p≠0) : parameter p 1 (2-(t:ℂ))=(p:ℂ)/(p:ℂ)^t := by
    simpa only [Nat.cast_one,one_add_one_eq_two] using parameter_candidate_lower p 1 t hp
  have hp0 (p : ℕ) (hp' : p≠0) : parameter p 1 2=(p:ℂ) := by
    simpa using hp p 0 hp'
  have hslice (n : Fin 4) : jetSlice w n=(fun j => w (finProdFinEquiv (n,j))) := rfl
  rw [regularizedBlock_apply]
  simp only [regularizedScaledStack,leading_apply_laurent,shift_apply_laurent,
    weightOneTaylorQuot_apply,leadingRows_scale,positiveTaylorRows_scale,
    hp 2 _ (by decide),hp 3 _ (by decide),hp 7 _ (by decide),hη,hσ,ha,Nat.cast_ofNat]
  fin_cases n <;>
    norm_num [jetBlockRow,jetSlice,regularizedJetScale,weightOneChooseQuot,
      Finset.sum_range_succ,lowerIndex,Ring.choose_eq_smul,←Polynomial.aeval_eq_smeval,
      descPochhammer_succ_right,I_sq,pow_succ]
  all_goals try simp only [hslice]
  all_goals norm_num [hp0 2 (by decide),hp0 3 (by decide),hp0 7 (by decide)]
    <;> ring_nf <;> norm_num [I_sq] <;> ring

#print axioms actual_regularizedBlockRow
end SmallLevelTwentyEightJetBlock
end
end

/-! ## TwentyEightWeightPoleOrder -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex Matrix SmallLevelTwentyEightParameters SmallLevelTwentyEightJetBlock
open SmallLevelFiniteShift QuantitativeArithmeticUniversalPoleVector
open SmallLevelTwentyOneKnownWords (regularizedJetScale regularizedJetScale_ne_zero)

theorem PoleSystem.weight_pole_order {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) {ε : ℂ} (hε : ε=1 ∨ ε= -1)
    (S : PoleSystem m f ε) :
    ∀ j,(-1:WithTop ℤ)≤meromorphicOrderAt (fun z => S.G z j) ((2*m:ℕ):ℂ) := by
  have hshift : ∀ n : ℕ, 0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => S.G z j) (((2*m:ℕ):ℂ)+n) := by
    intro n hn j
    apply S.regular_above_weight hm hf hε _ _ j
    simp only [Complex.add_re,Complex.natCast_re]
    have hn' : (0:ℝ)<n:=by exact_mod_cast hn
    linarith
  by_contra h
  push Not at h
  obtain ⟨w,hw⟩:=exists_regularized_leading_vector S.G ((2*m:ℕ):ℂ)
    (fun j => (S.meromorphic j _).meromorphicAt) h
  obtain ⟨hx,hη,hσ,ha⟩:=candidate_of_regularized_vector hf ε hε S.B S.G S.H
    S.meromorphic S.error S.rows _ w hw hshift
  have hm1 : m=1 := by
    have hr:=congrArg Complex.re hx
    norm_num at hr
    exact_mod_cast (show (m:ℝ)=1 by linarith)
  subst m
  have hpole : ∃ j,meromorphicOrderAt (fun z => (z-(2:ℂ))*S.G z j) 2<0 := by
    obtain ⟨j,hj⟩:=h
    norm_num at hj
    refine ⟨j,?_⟩
    have hloc : MeromorphicAt (fun z : ℂ => z-2) 2 :=
      (analyticAt_id.sub analyticAt_const).meromorphicAt
    change meromorphicOrderAt ((fun z : ℂ => z-2)*(fun z => S.G z j)) 2<0
    rw [meromorphicOrderAt_mul hloc (S.meromorphic j 2).meromorphicAt,
      meromorphicOrderAt_id_sub_const]
    lift meromorphicOrderAt (fun z => S.G z j) 2 to ℤ using hj.ne_top with q hq
    have hqlt : q< -1 := by
      change (q:WithTop ℤ)<((-1:ℤ):WithTop ℤ) at hj
      exact WithTop.coe_lt_coe.mp hj
    exact_mod_cast (show 1+q<0 by omega)
  obtain ⟨v,hv0,hvk⟩:=regularized_block_kernel S.B S.G (extendedLeading 1 f ε)
    (extendedShift 1 f ε) S.H 2 3 (weightOneTaylorQuot f ε) S.meromorphic
    (extendedLeading_analytic 1 f ε) (extendedShift_analytic 1 f ε)
    (fun n r j => weightOneTaylorQuot_analytic f ε n 2 r j)
    (weightOneTaylorQuot_factor f ε) S.error (by simpa using hshift) S.rows hpole
  let e : (Fin 4×Fin 84)≃Fin 336:=finProdFinEquiv
  let q : Fin 336→ℂ:=fun j => v (e.symm j)/regularizedJetScale (e.symm j).1
  have he : regularizedScaledStack q=v := by
    funext b
    simp only [regularizedScaledStack,q,e,Equiv.symm_apply_apply]
    field_simp [regularizedJetScale_ne_zero b.1]
  have hq (n : Fin 4) (i : Fin 86) : jetBlockRow n i q=0 := by
    have hh:=hvk (n,i)
    rw [←he,actual_regularizedBlockRow f ε hη hσ ha] at hh
    exact (mul_eq_zero.mp hh).resolve_left (regularizedJetScale_ne_zero n)
  have hq0:=kernel_zero q hq
  apply hv0
  rw [←he,hq0]
  funext b
  simp [regularizedScaledStack]

#print axioms PoleSystem.weight_pole_order
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightShiftCancellation -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex

theorem extendedShift_zero_at_weight (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (hs : s+((n:ℂ)+1)=((2*m:ℕ):ℂ)) (i : Fin 86) (j : Fin 84) :
    extendedShift m f ε n s i j=0 := by
  have he : s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=0 := by
    rw [Nat.cast_add,Nat.cast_one,hs,sub_self]
  simp only [extendedShift,he,Ring.choose_zero_succ,mul_zero,zero_smul,Matrix.zero_apply]

#print axioms extendedShift_zero_at_weight
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightFullPoleBound -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex SmallLevelFiniteShift QuantitativeArithmeticUniversalPoleVector

theorem PoleSystem.regular_off_weight {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) {ε : ℂ} (hε : ε=1 ∨ ε= -1)
    (S : PoleSystem m f ε) (x : ℂ) (hx : x≠((2*m:ℕ):ℂ)) (i : Fin 84) :
    AnalyticAt ℂ (fun z => S.G z i) x := by
  apply (S.meromorphic i x).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hi
  obtain ⟨n,hne,hp,hshift⟩:=SmallLevelPoleGrid.rightmost_pole_away
    (fun j z => S.G z j) (x:=x) ((2*m:ℕ):ℂ) hx ⟨i,hi⟩ S.B S.halfplane
  obtain ⟨w,hw⟩:=exists_leading_vector S.G (x+n)
    (fun j => (S.meromorphic j _).meromorphicAt) hp
  apply hne
  apply S.regular_tail_pole_at_weight hm hf hε (x+n) w hw
  intro d b hb r j
  exact allowed_simple_pole_tail (extendedShift m f ε) ((2*m:ℕ):ℂ)
    (extendedShift_analytic m f ε) (extendedShift_zero_at_weight m f ε)
    S.G S.meromorphic (x+n) d hshift (S.weight_pole_order hm hf hε) b hb r j

#print axioms PoleSystem.regular_off_weight
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightQuarterKernel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightLaurent
open Complex

def quarterConstraint (η σ Y Z a : ℂ) : ℂ :=
  Z-η*(a*Y)+η*Y^2+η*(1-η*σ)

theorem residual_normalized (η σ X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) :
    (2*X^2*Y^2)*residual η σ X Y Z a=SmallLevelTwentyEightFirstJet.residual η σ Y Z a := by
  unfold residual SmallLevelTwentyEightFirstJet.residual
  field_simp [hX,hY]
  ring

/-- The quarter coordinate cannot vanish in a residual kernel unless Y²=1.
This identity avoids a separate leading-ideal calculation at every weight. -/
theorem quarterConstraint_incompatible (η σ Y Z a : ℂ)
    (hη : η=1 ∨ η= -1) (hσ : σ=1 ∨ σ= -1) (hY : Y≠0) (hY1 : Y^2≠1)
    (hr : SmallLevelTwentyEightFirstJet.residual η σ Y Z a=0)
    (hq : quarterConstraint η σ Y Z a=0) : False := by
  have hb : a*Y=Y^2+η*Z+1-η*σ := by
    unfold quarterConstraint at hq
    rcases hη with rfl|rfl
    · linear_combination -hq
    · linear_combination hq
  unfold SmallLevelTwentyEightFirstJet.residual at hr
  rw [hb] at hr
  have hh : Y^2*(Y^2-1)=0 := by
    rcases hη with rfl|rfl <;> rcases hσ with rfl|rfl
    all_goals linear_combination -(1/4:ℂ)*hr
  exact hY1 (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 hY)))

theorem pole_quarter_case0 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) :
    pole0 X Y Z a 21=(Z/(2*X^2*Y^2))*quarterConstraint (-1) (-1) Y Z a := by
  norm_num [pole0,quarterConstraint]
  field_simp [hX,hY]

theorem pole_quarter_case1 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) :
    pole1 X Y Z a 21=(Z/(2*X^2*Y^2))*quarterConstraint (-1) 1 Y Z a := by
  norm_num [pole1,quarterConstraint]
  field_simp [hX,hY]
  ring

theorem pole_quarter_case2 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) :
    pole2 X Y Z a 21=(Z/(2*X^2*Y^2))*quarterConstraint 1 (-1) Y Z a := by
  norm_num [pole2,quarterConstraint]
  field_simp [hX,hY]
  ring

theorem pole_quarter_case3 (X Y Z a : ℂ) (hX : X≠0) (hY : Y≠0) :
    pole3 X Y Z a 21=(Z/(2*X^2*Y^2))*quarterConstraint 1 1 Y Z a := by
  norm_num [pole3,quarterConstraint]
  field_simp [hX,hY]
  ring

theorem core_quarter_ne_zero (η σ X Y Z a : ℂ)
    (hη : η=1 ∨ η= -1) (hσ : σ=1 ∨ σ= -1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hY1 : Y^2≠1)
    (w : Fin 84→ℂ) (hw : coreRows η σ X Y Z a w=0) (hw0 : w≠0) : w 21≠0 := by
  have h66:=core_kernel_coordinate_ne_zero η σ X Y Z a hη hσ hX hY hZ w hw hw0
  have hr : SmallLevelTwentyEightFirstJet.residual η σ Y Z a=0 := by
    rw [←residual_normalized η σ X Y Z a hX hY,
      core_residual_zero η σ X Y Z a hη hσ hX hY hZ w hw hw0,mul_zero]
  have he : w 21=((Z/(2*X^2*Y^2))*quarterConstraint η σ Y Z a)*w 66 := by
    rcases hη with rfl|rfl <;> rcases hσ with rfl|rfl
    · simpa only [pole_quarter_case3 X Y Z a hX hY] using kernel_case3 X Y Z a hX hY hZ w hw 21
    · simpa only [pole_quarter_case2 X Y Z a hX hY] using kernel_case2 X Y Z a hX hY hZ w hw 21
    · simpa only [pole_quarter_case1 X Y Z a hX hY] using kernel_case1 X Y Z a hX hY hZ w hw 21
    · simpa only [pole_quarter_case0 X Y Z a hX hY] using kernel_case0 X Y Z a hX hY hZ w hw 21
  intro h21
  have hprod:=he.symm.trans h21
  have hc : Z/(2*X^2*Y^2)≠0 :=
    div_ne_zero hZ (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hX)) (pow_ne_zero 2 hY))
  have hq : quarterConstraint η σ Y Z a=0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right h66)).resolve_left hc
  exact quarterConstraint_incompatible η σ Y Z a hη hσ hY hY1 hr hq

#print axioms residual_normalized
#print axioms quarterConstraint_incompatible
#print axioms core_quarter_ne_zero
end SmallLevelTwentyEightLaurent
end
end

/-! ## TwentyEightQuarterPole -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex Matrix Filter SmallLevelPrimeRates SmallLevelTwentyEightParameters
open SmallLevelTwentyEightLaurent QuantitativeArithmeticUniversalPoleVector SmallLevelFiniteShift
open scoped Topology

theorem weight_parameter (p m : ℕ) : parameter p m ((2*m:ℕ):ℂ)=(p:ℂ)^m := by
  unfold parameter
  rw [show ((2*m:ℕ):ℂ)-(m:ℂ)=(m:ℂ) by push_cast; ring,Complex.cpow_natCast]

theorem weight_three_square_ne_one {m : ℕ} (hm : 0<m) :
    (parameter 3 m ((2*m:ℕ):ℂ))^2≠1 := by
  rw [weight_parameter]
  have hp : (1:ℝ)<(3:ℝ)^m := one_lt_pow₀ (by norm_num) (by omega)
  have hsq : ((3:ℝ)^m)^2≠1 := by nlinarith
  exact_mod_cast hsq

/-- The quarter coordinate detects every possible weight pole, uniformly
in the positive weight, both signs, and the good Hecke eigenvalue. -/
theorem PoleSystem.entire_of_quarter_regular {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) {ε : ℂ} (hε : ε=1 ∨ ε= -1)
    (S : PoleSystem m f ε)
    (hq : AnalyticAt ℂ (fun z => S.G z 21) ((2*m:ℕ):ℂ)) :
    ∀ j x, AnalyticAt ℂ (fun z => S.G z j) x := by
  classical
  intro j x
  by_cases hx : x=((2*m:ℕ):ℂ)
  · subst x
    apply (S.meromorphic j _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_contra! hp
    obtain ⟨w,hw⟩:=exists_leading_vector S.G ((2*m:ℕ):ℂ)
      (fun i => (S.meromorphic i _).meromorphicAt) ⟨j,hp⟩
    have hshift : ∀ n : ℕ, 0<n → ∀ i,
        0≤meromorphicOrderAt (fun z => S.G z i) (((2*m:ℕ):ℂ)+n) := by
      intro n hn i
      apply S.regular_above_weight hm hf hε _ _ i
      simp only [Complex.add_re,Complex.natCast_re]
      have hn' : (0:ℝ)<n:=by exact_mod_cast hn
      linarith
    have hlead : extendedLeading m f ε ((2*m:ℕ):ℂ)*ᵥw=0 := by
      funext r
      exact hw.taylor S.meromorphic hshift S.B
        (fun z i => extendedLeading m f ε z r i)
        (fun n z i => extendedShift m f ε n z r i) (fun n z => S.H n z r)
        (fun i => extendedLeading_analytic m f ε _ r i)
        (fun n i => extendedShift_analytic m f ε n _ r i)
        (fun n z hz => S.error n r z hz) (fun n hn => S.rows n r _ hn)
    rw [extendedLeading_actual] at hlead
    have hcore : coreRows (phase m ε) (sigmaSeven f)
        (parameter 2 m ((2*m:ℕ):ℂ)) (parameter 3 m ((2*m:ℕ):ℂ))
        (parameter 7 m ((2*m:ℕ):ℂ)) ((Real.sqrt 3:ℂ)*f 3) w=0 := by
      funext i
      exact congrFun hlead ⟨i.val,by omega⟩
    have hn:=core_quarter_ne_zero _ _ _ _ _ _ (phase_sign m hε)
      (sigmaSeven_sign hf.toEulerData) (parameter_ne_zero 2 m (by decide) _)
      (parameter_ne_zero 3 m (by decide) _) (parameter_ne_zero 7 m (by decide) _)
      (weight_three_square_ne_one hm) w hcore hw.1
    apply hn
    have hh:=hw.2 (fun _ i => if i=21 then (1:ℂ) else 0) (fun z => S.G z 21)
      (fun _ => analyticAt_const) hq (Filter.Eventually.of_forall (by intro z; simp))
    simpa using hh
  · exact S.regular_off_weight hm hf hε x hx j

#print axioms weight_three_square_ne_one
#print axioms PoleSystem.entire_of_quarter_regular
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightTwelfthMellin -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightTwelfth
open Matrix UpperHalfPlane SmallLevelNormalized QuantitativeArithmeticTranslatedFricke
  FinitenessPolynomialSeries FinitenessFourierConstruction SmallLevelAdditive Complex MeasureTheory
open scoped MatrixGroups ModularForm

def twelfthMellin (m : ℕ) (f : ℕ→ℂ) : ℂ→ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1008
    (twelfthCoefficients (FinitenessOriginalFourier.fullCoefficients f (2*m))))

def twelfthEntire (m : ℕ) (f : ℕ→ℂ) : ℂ→ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1
    (twelfthCoefficients (FinitenessOriginalFourier.fullCoefficients f (2*m))))

/-- The twelfth difference has an entire finite-order Mellin transform and
its conductor-1008 functional equation, directly from original input. -/
theorem original_twelfth_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f)
    (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SmallLevelTwentyEightGenerators.W=
      η • SmallLevelOriginal.fourierFunction (2*m) f) :
      Differentiable ℂ (twelfthMellin m f) ∧
      FinitenessFiniteOrder.Bound (twelfthMellin m f) ∧
      ∀ s : ℂ, twelfthMellin m f s=
        ((-η)/(Complex.I^(2*m)))*twelfthMellin m f ((2*m:ℕ)-s) := by
  obtain ⟨hn,hp⟩:=original_twelfth_fricke m hf η hη hW
  have hχ : -η=1 ∨ -η= -1 := by rcases hη with rfl|rfl <;> norm_num
  obtain ⟨τ,_,hg⟩:=hf.growth
  let a:=FinitenessOriginalFourier.fullCoefficients f (2*m)
  have ha : PolynomialBound a:=FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m)
  have ha0 : a 0=0:=FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)
  have hB0 : twelfthCoefficients a 0=0 := by simp [twelfthCoefficients,coefficients_zero ha0]
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ:=((2*m:ℕ):ℤ)
  have hfourier : (fun z : ℍ => fourier (twelfthCoefficients a) z)=
      (F ∣[k] translation (1/12))-(F ∣[k] translation (-1/12)) := by
    funext z
    rw [twelfth_fourier ha z z.im_pos]
    simp only [Pi.sub_apply,translation_slash]
    change fourier a _-fourier a _=fourier a ((translation (1/12) • z:ℍ):ℂ)-
      fourier a ((translation (-1/12) • z:ℍ):ℂ)
    rw [translation_point,translation_point]
  have hslash : (fun z : ℍ => fourier (twelfthCoefficients a) z) ∣[k] fricke 1008 (by decide)=
      (-η) • (fun z : ℍ => fourier (twelfthCoefficients a) z) := by
    rw [hfourier,sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash,hp,hn]
    simp only [_root_.neg_smul,smul_add,smul_neg]
    abel
  have hl:=formula_of_slash 1008 (2*m) (by decide) (fourier (twelfthCoefficients a)) (-η) hχ hslash
  have hχ0 : -η≠0 := by rcases hη with rfl|rfl <;> norm_num
  apply FinitenessAllLevelMellinPair.mellin_entire (by decide : 0<1008) (by omega : 0<2*m)
    (twelfthCoefficients a) (twelfth_polynomial ha) hB0 ((-η)/(Complex.I^(2*m)))
    (div_ne_zero hχ0 (pow_ne_zero _ Complex.I_ne_zero))
  simpa only [div_mul_cancel₀ _ (pow_ne_zero (2*m) Complex.I_ne_zero)] using hl

/-- The entire unscaled even-twelfth continuation agrees with the literal
difference of the two additive Dirichlet series in an initial half-plane. -/
theorem original_twelfth_continuation (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f)
    (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SmallLevelTwentyEightGenerators.W=
      η • SmallLevelOriginal.fourierFunction (2*m) f) :
    Differentiable ℂ (twelfthEntire m f) ∧
    ∃ B : ℝ, ∀ s : ℂ, B<s.re → twelfthEntire m f s=
      original (2*m) f (1/12) s-original (2*m) f (-1/12) s := by
  obtain ⟨he,_,_⟩:=original_twelfth_entire m hm hf η hη hW
  refine ⟨QuantitativeArithmeticMellinScale.entire_at_one (by decide : 0<1008) _ he,?_⟩
  obtain ⟨τ,_,hg⟩:=hf.growth
  let a:=FinitenessOriginalFourier.fullCoefficients f (2*m)
  have ha : PolynomialBound a:=FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m)
  have ha0 : a 0=0:=FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)
  have hB0 : twelfthCoefficients a 0=0 := by simp [twelfthCoefficients,coefficients_zero ha0]
  obtain ⟨B,hB⟩:=common_halfplane (twelfth_polynomial ha) hB0
  obtain ⟨d,hd⟩:=FinitenessAllLevelMellinDirichlet.polynomial_growth ha
  refine ⟨max B ((d:ℝ)+1),fun s hs => ?_⟩
  have hsB : B<s.re := (le_max_left _ _).trans_lt hs
  have hsd : (d:ℝ)+1<s.re := (le_max_right _ _).trans_lt hs
  have hh:=(hB 0 s hsB).2
  have hc0 : coefficients (twelfthCoefficients a) 0=twelfthCoefficients a := by
    funext n
    simp [coefficients,phase]
  have hL : LSeries (twelfthCoefficients a) s=
      LSeries (coefficients a (1/12)) s-LSeries (coefficients a (-1/12)) s :=
    LSeries_sub (summable_at hd _ hsd) (summable_at hd _ hsd)
  change twelfthEntire m f s=transform a (1/12) s-transform a (-1/12) s
  have hmain : twelfthEntire m f s=transform (twelfthCoefficients a) 0 s := by
    have haxis : FinitenessAllLevelAxisDecay.axis 1 (twelfthCoefficients a)=
        (fun t : ℝ => fourier (twelfthCoefficients a) ((t:ℂ)*Complex.I)) := by
      funext t
      simp [FinitenessAllLevelAxisDecay.axis]
    change mellin (FinitenessAllLevelAxisDecay.axis 1 (twelfthCoefficients a)) s=_
    rw [haxis]
    simpa only [Complex.ofReal_zero,zero_add] using hh
  rw [hmain,transform,hc0,hL,transform,transform]
  ring

#print axioms original_twelfth_entire
#print axioms original_twelfth_continuation
end SmallLevelTwentyEightTwelfth
end
end

/-! ## TwentyEightQuarterHecke -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightQuarter
open Complex SmallLevelAdditive SmallLevelTaylor SmallLevelTwentyEightGrid
open SmallLevelTwentyEightTwelfth
open scoped MatrixGroups ModularForm

def denominator (m : ℕ) (f : ℕ→ℂ) (s : ℂ) : ℂ :=
  1+((Real.sqrt 3:ℂ)*f 3)*(3:ℂ)^((m:ℂ)-s)+((3:ℂ)^((m:ℂ)-s))^2

theorem denominator_entire (m : ℕ) (f : ℕ→ℂ) : Differentiable ℂ (denominator m f) := by
  unfold denominator
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]
  fun_prop

/-- The original Hecke-three and half-period rows give the exact quadratic
factor relating the quarter twist to the twelfth difference. -/
theorem original_quarter_hecke {m : ℕ} {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re →
      denominator m f s*original (2*m) f (1/4) s=
        original (2*m) f (1/12) s-original (2*m) f (-1/12) s := by
  obtain ⟨BH,hH⟩:=original_grid_hecke_three hf
  obtain ⟨BB,hB⟩:=original_grid_half hf
  refine ⟨max BH BB,?_⟩
  intro s hs
  have hh:=hH 7 s ((le_max_left _ _).trans_lt hs)
  have hp:=hB 21 s ((le_max_right _ _).trans_lt hs)
  have hn:=hB (-7) s ((le_max_right _ _).trans_lt hs)
  norm_num [gridHeckeThree,gridHalf,grid] at hh hp hn
  unfold denominator
  rw [neg_div]
  linear_combination -hh+(1+((3:ℂ)^((m:ℂ)-s))^2)*hp+hn

theorem original_product {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SmallLevelTwentyEightGenerators.W=
      η • SmallLevelOriginal.fourierFunction (2*m) f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re →
      denominator m f s*original (2*m) f (1/4) s=twelfthEntire m f s := by
  obtain ⟨BH,hH⟩:=original_quarter_hecke hf
  obtain ⟨_,BT,hT⟩:=original_twelfth_continuation m hm hf η hη hW
  refine ⟨max BH BT,fun s hs => ?_⟩
  rw [hH s ((le_max_left _ _).trans_lt hs),hT s ((le_max_right _ _).trans_lt hs)]

#print axioms original_quarter_hecke
#print axioms original_product
end SmallLevelTwentyEightQuarter
end
end

/-! ## TwentyEightQuarterContinuation -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightQuarter
open Complex SmallLevelAdditive SmallLevelTwentyEightTwelfth Filter Set
open scoped Topology MatrixGroups ModularForm

theorem denominator_nonzero (m : ℕ) (f : ℕ→ℂ) : ∃ s : ℂ,denominator m f s≠0 := by
  by_contra h
  push Not at h
  have h0:=h (m:ℂ)
  have h1:=h ((m:ℂ)+1)
  norm_num [denominator,show (m:ℂ)-((m:ℂ)+1)= -1 by ring,Complex.cpow_neg] at h0 h1
  have hbad : (1:ℂ)=0 := by linear_combination -(3/4:ℂ)*(h0-3*h1)
  norm_num at hbad

/-- Independent scalar normal-form continuation, retaining the exact
Hecke denominator. Its possible poles are not removed in this theorem. -/
theorem quarter_continuation {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (η : ℂ) (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SmallLevelTwentyEightGenerators.W=
      η • SmallLevelOriginal.fourierFunction (2*m) f) :
    ∃ (bound : ℝ) (G : ℂ→ℂ), (∀ s,MeromorphicNFAt G s) ∧
      (∀ s,bound<s.re → G s=original (2*m) f (1/4) s) ∧
      (∀ s,denominator m f s≠0 → AnalyticAt ℂ G s) ∧
      (∀ x,G=ᶠ[𝓝[≠] x] (fun s => twelfthEntire m f s/denominator m f s)) := by
  obtain ⟨B,hB⟩:=original_common_halfplane hf
  obtain ⟨C,hC⟩:=original_product hm hf η hη hW
  have hN:=(original_twelfth_continuation m hm hf η hη hW).1
  obtain ⟨G,hG,hagree,hpole,hgerm⟩:=QuantitativeArithmeticEntireQuotient.continuation
    (twelfthEntire m f) (denominator m f) (original (2*m) f (1/4)) (max B C)
    (fun z => hN.analyticAt z) (fun z => (denominator_entire m f).analyticAt z)
    (denominator_nonzero m f)
    (fun z hz => (hB (1/4) z ((le_max_left _ _).trans_lt hz)).1)
    (fun z hz => (hC z ((le_max_right _ _).trans_lt hz)).symm)
  exact ⟨max B C,G,hG,hagree,hpole,hgerm⟩

#print axioms denominator_nonzero
#print axioms quarter_continuation
end SmallLevelTwentyEightQuarter
end
end

/-! ## TwentyEightQuarterReflection -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightQuarter
open Complex SmallLevelAdditive SmallLevelTwentyEightTwelfth SmallLevelTwentyEightGrid
open SmallLevelTwentyEightParameters SmallLevelPrimeRates Filter Set
open scoped Topology MatrixGroups ModularForm

def reflectionMultiplier (m : ℕ) (ε s : ℂ) : ℂ := -ε*(112:ℂ)^((m:ℂ)-s)

theorem reflectionMultiplier_entire (m : ℕ) (ε : ℂ) : Differentiable ℂ (reflectionMultiplier m ε) := by
  unfold reflectionMultiplier
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (112:ℂ)≠0)]
  fun_prop

theorem reflectionMultiplier_ne_zero (m : ℕ) {ε : ℂ} (hε : ε≠0) (s : ℂ) :
    reflectionMultiplier m ε s≠0 :=
  mul_ne_zero (neg_ne_zero.mpr hε) (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))

theorem denominator_reflection (m : ℕ) (f : ℕ→ℂ) (s : ℂ) :
    denominator m f s=((3:ℂ)^((m:ℂ)-s))^2*denominator m f (((2*m:ℕ):ℂ)-s) := by
  have he : (m:ℂ)-(((2*m:ℕ):ℂ)-s)= -((m:ℂ)-s) := by push_cast; ring
  have hn : (3:ℂ)^((m:ℂ)-s)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  simp only [denominator,he,Complex.cpow_neg]
  field_simp [hn]
  ring

theorem numerator_reflection {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) (s : ℂ) :
    twelfthEntire m f s=((3:ℂ)^((m:ℂ)-s))^2*reflectionMultiplier m ε s*
      twelfthEntire m f (((2*m:ℕ):ℂ)-s) := by
  have he:=(original_twelfth_entire m hm hf (phase m ε) (phase_sign m hε)
    (grid_fricke_of_laws m hε hlaw)).2.2
  have hsign : -(phase m ε)/I^(2*m)= -ε := by
    unfold SmallLevelTwentyEightParameters.phase
    rw [neg_div,mul_div_cancel_right₀ _ (pow_ne_zero _ I_ne_zero)]
  simp only [hsign] at he
  have hr:=SmallLevelMellinUnscale.reflection_pair (by decide : 0<1008)
    (twelfthCoefficients (FinitenessOriginalFourier.fullCoefficients f (2*m)))
    (twelfthCoefficients (FinitenessOriginalFourier.fullCoefficients f (2*m))) (-ε) he s
  change twelfthEntire m f s= -ε*(Real.sqrt 1008:ℂ)^(((2*m:ℕ):ℂ)-2*s)*
    twelfthEntire m f (((2*m:ℕ):ℂ)-s) at hr
  have hsqrt:=QuantitativeArithmeticSmallLevelTwentyTwo.sqrt_cpow_even 1008 m (by decide) s
  norm_num only [Nat.cast_ofNat] at hsqrt
  rw [hsqrt] at hr
  have hp : (1008:ℂ)^((m:ℂ)-s)=((3:ℂ)^((m:ℂ)-s))^2*(112:ℂ)^((m:ℂ)-s) := by
    have h:=rational_power 3 3 112 (by decide) (by decide) (by decide)
      1008 (1,1,1) (by norm_num) ((m:ℂ)-s)
    simpa [monomial,pow_two] using h
  rw [hp] at hr
  unfold reflectionMultiplier
  linear_combination hr

theorem raw_quotient_reflection {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) (s : ℂ) :
    twelfthEntire m f s/denominator m f s=reflectionMultiplier m ε s*
      (twelfthEntire m f (((2*m:ℕ):ℂ)-s)/denominator m f (((2*m:ℕ):ℂ)-s)) := by
  have hn : ((3:ℂ)^((m:ℂ)-s))^2≠0 :=
    pow_ne_zero _ (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
  rw [numerator_reflection hm hf ε hε hlaw s,denominator_reflection,mul_assoc,
    mul_div_mul_left _ _ hn]
  ring

theorem quarter_functional_equation {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) :
    ∃ (B : ℝ) (Q : ℂ→ℂ), (∀ s,MeromorphicNFAt Q s) ∧
      (∀ s,B<s.re → Q s=original (2*m) f (1/4) s) ∧
      (∀ s,Q s=reflectionMultiplier m ε s*Q (((2*m:ℕ):ℂ)-s)) ∧
      (∀ s,denominator m f s≠0 → AnalyticAt ℂ Q s) := by
  obtain ⟨B,Q,hQ,hQF,hQD,hgerm⟩:=quarter_continuation hm hf (phase m ε)
    (phase_sign m hε) (grid_fricke_of_laws m hε hlaw)
  have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
  refine ⟨B,Q,hQ,hQF,?_,hQD⟩
  exact QuantitativeArithmeticQuadraticTwistReflection.normal_form_reflection
    (fun s => twelfthEntire m f s/denominator m f s) Q
    (reflectionMultiplier m ε) ((2*m:ℕ):ℂ) hQ
    (fun s => (reflectionMultiplier_entire m ε).analyticAt s)
    (reflectionMultiplier_ne_zero m hε0) hgerm (raw_quotient_reflection hm hf ε hε hlaw)

#print axioms numerator_reflection
#print axioms quarter_functional_equation
end SmallLevelTwentyEightQuarter
end
end

/-! ## TwentyEightEntireGrid -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightSystem
open Complex Filter SmallLevelTwentyEightGrid SmallLevelTwentyEightQuarter
open SmallLevelAdditive SmallLevelTaylor
open QuantitativeArithmeticSmallLevelTwentyEight (quotientVector oddMode)
open scoped Topology

theorem quotientGrid_quarter (k : ℕ) (f : ℕ→ℂ) (s : ℂ) :
    quotientGridVector k f s 21=SmallLevelAdditive.original k f (1/4) s := by
  norm_num [quotientGridVector,quotientVector,oddMode,gridVector,grid]

theorem PoleSystem.quarter_matches {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (B : ℝ) (Q : ℂ→ℂ)
    (hQ : ∀ s,MeromorphicNFAt Q s)
    (hQF : ∀ s,B<s.re → Q s=SmallLevelAdditive.original (2*m) f (1/4) s) :
    ∀ x,Q x=S.G x 21 := by
  intro x
  have he : Q=ᶠ[𝓝[≠] x] (fun z => S.G z 21) := by
    apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) (max B S.B)
    · exact fun z _ => (hQ z).meromorphicAt
    · exact fun z _ => (S.meromorphic 21 z).meromorphicAt
    · intro z hz
      dsimp only
      rw [hQF z ((le_max_left _ _).trans_lt hz),S.original z ((le_max_right _ _).trans_lt hz),
        quotientGrid_quarter]
    · linarith
  exact (((hQ x).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (S.meromorphic 21 x)).mp he).eq_of_nhds

/-- Quarter reflection removes the possible weight pole, then the checked
uniform kernel calculation removes every residue in the quotient grid. -/
theorem PoleSystem.entire {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) {ε : ℂ}
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) (S : PoleSystem m f ε) :
    ∀ j x,AnalyticAt ℂ (fun z => S.G z j) x := by
  obtain ⟨B,Q,hQ,hQF,hFE,_⟩:=quarter_functional_equation hm hf ε hε hlaw
  have heq:=S.quarter_matches B Q hQ hQF
  have he : (fun z => S.G z 21)=(fun z => reflectionMultiplier m ε z*S.G (((2*m:ℕ):ℂ)-z) 21) := by
    funext z
    rw [←heq z,←heq (((2*m:ℕ):ℂ)-z)]
    exact hFE z
  have h0 : AnalyticAt ℂ (fun z => S.G z 21) 0 :=
    S.regular_off_weight hm hf hε 0 (by norm_num; omega) 21
  have hc : AnalyticAt ℂ (fun z => S.G (((2*m:ℕ):ℂ)-z) 21) ((2*m:ℕ):ℂ) := by
    have h0' : AnalyticAt ℂ (fun z => S.G z 21) (((2*m:ℕ):ℂ)-((2*m:ℕ):ℂ)) := by
      simpa only [sub_self] using h0
    exact h0'.comp (f:=fun z : ℂ => ((2*m:ℕ):ℂ)-z)
      (analyticAt_const.sub analyticAt_id)
  apply S.entire_of_quarter_regular hm hf hε
  rw [he]
  exact ((reflectionMultiplier_entire m ε).analyticAt _).mul hc

#print axioms quotientGrid_quarter
#print axioms PoleSystem.quarter_matches
#print axioms PoleSystem.entire
end SmallLevelTwentyEightSystem
end
end

/-! ## TwentyEightQuarterOrder -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightQuarter
open Complex Filter SmallLevelTwentyEightGrid SmallLevelTwentyEightParameters
open SmallLevelTwentyEightTwelfth SmallLevelAdditive
open scoped Topology

theorem uniform_product {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε)
    {Q : ℂ→ℂ} (hQ : Differentiable ℂ Q) (B : ℝ)
    (hQF : ∀ s,B<s.re → Q s=original (2*m) f (1/4) s) :
    ∀ s,denominator m f s*Q s=twelfthEntire m f s := by
  have hW:=grid_fricke_of_laws m hε hlaw
  obtain ⟨C,hC⟩:=original_product hm hf (phase m ε) (phase_sign m hε) hW
  have hN:=(original_twelfth_continuation m hm hf (phase m ε) (phase_sign m hε) hW).1
  have hleft:=(denominator_entire m f).mul hQ
  intro s
  have he : (fun z => denominator m f z*Q z)=ᶠ[𝓝[≠] s] twelfthEntire m f := by
    apply SmallLevelContinuation.halfplane_germ_identity (s.re-1) (max B C)
    · exact fun z _ => (hleft.analyticAt z).meromorphicAt
    · exact fun z _ => (hN.analyticAt z).meromorphicAt
    · intro z hz
      dsimp only
      rw [hQF z ((le_max_left _ _).trans_lt hz)]
      exact hC z ((le_max_right _ _).trans_lt hz)
    · linarith
  exact (((hleft.analyticAt s).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hN.analyticAt s).meromorphicNFAt).mp he).eq_of_nhds

theorem quarter_finiteOrder {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε)
    {Q : ℂ→ℂ} (hQ : Differentiable ℂ Q) (B : ℝ)
    (hQF : ∀ s,B<s.re → Q s=original (2*m) f (1/4) s) :
    FinitenessOriginalInput.FiniteOrder Q := by
  have hW:=grid_fricke_of_laws m hε hlaw
  have he:=original_twelfth_entire m hm hf (phase m ε) (phase_sign m hε) hW
  have hN:=(original_twelfth_continuation m hm hf (phase m ε) (phase_sign m hε) hW).1
  have hb:=SmallLevelMellinUnscale.finite_order_at_one (by decide : 0<1008) _ he.2.1
  exact SmallLevelQuadraticExponential.finiteOrder_of_quadratic_base 3 (by decide)
    ((Real.sqrt 3:ℂ)*f 3) (m:ℂ) hN.continuous
    (FinitenessInputBounds.bound_finiteOrder hb) hQ (uniform_product hm hf ε hε hlaw hQ B hQF)

#print axioms uniform_product
#print axioms quarter_finiteOrder
end SmallLevelTwentyEightQuarter
end
end

/-! ## TwentyEightQuarterBridge -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightQuarter
open Complex Matrix UpperHalfPlane SmallLevelNormalized SmallLevelSixEigen
open SmallLevelTwentyEightGenerators (W)
open SmallLevelTwentyEightGrid SmallLevelEvenScale
open FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticSmallLevelTwentyEight (QuarterTransformation quarter_matrix)
open scoped MatrixGroups ModularForm

def quarterMatrix : GL (Fin 2) ℝ:=matrix 2 (-1/2) (-14) 4 (by norm_num)
def quarterInverse : GL (Fin 2) ℝ:=matrix 4 (1/2) 14 2 (by norm_num)

theorem quarterMatrix_det : (GeneralLinearGroup.det quarterMatrix:ℝ)=1 := matrix_det _ _ _ _ _
theorem quarterInverse_det : (GeneralLinearGroup.det quarterInverse:ℝ)=1 := matrix_det _ _ _ _ _

theorem quarter_inverse : quarterInverse=quarterMatrix⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).mpr
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quarterMatrix,quarterInverse,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem quarter_branch : quarterInverse=
    translation (1/4)*fricke 112 (by decide)*translation (-1/4)*W⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  have hs : (Real.sqrt 28)^2=28:=Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 28≠0:=(Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs112 : Real.sqrt 112=2*Real.sqrt 28 := by
    rw [show (112:ℝ)=4*28 by norm_num,Real.sqrt_mul (by norm_num)]
    norm_num
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quarterInverse,W,fricke,translation,hs112,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two] <;> field_simp [hn] <;> nlinarith

def scaledQuarterMatrix : SL(2,ℤ):=⟨!![2,-1;-7,4],by decide⟩

theorem scaled_quarter (k : ℕ) (f : ℕ→ℂ)
    (h : SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] quarterMatrix=
      -SmallLevelOriginal.fourierFunction k f) : QuarterTransformation k f := by
  unfold QuarterTransformation
  rw [quarter_matrix]
  change scaledFunction k f ∣[(k:ℤ)] scaledQuarterMatrix= -scaledFunction k f
  funext z
  let t : ℍ:=⟨(z:ℂ)/2,by simpa using div_pos z.im_pos (by norm_num : (0:ℝ)<2)⟩
  have he:=congrFun h t
  rw [det_one_slash _ quarterMatrix_det] at he
  rw [ModularForm.SL_slash_apply]
  have hd : denom scaledQuarterMatrix z=denom quarterMatrix t := by
    norm_num [denom,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      scaledQuarterMatrix,quarterMatrix,matrix,GeneralLinearGroup.mkOfDetNeZero,t]
    ring
  have hpoint : ((scaledQuarterMatrix • z : ℍ):ℂ)/2=
      ((quarterMatrix • t : ℍ):ℂ) := by
    rw [coe_specialLinearGroup_apply,coe_smul_of_det_pos (by rw [quarterMatrix_det]; norm_num)]
    norm_num [num,denom,SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      scaledQuarterMatrix,quarterMatrix,matrix,GeneralLinearGroup.mkOfDetNeZero,t]
    ring
  rw [hd]
  simpa only [scaledFunction,scaledFourier,SmallLevelOriginal.fourierFunction,
    Pi.neg_apply,hpoint] using he

/-- The quarter-twist Fricke law and the original Fricke law give exactly
the missing signed generator in the level-28 modularity criterion. -/
theorem transformation_of_quarter_fricke (m : ℕ) {f : ℕ→ℂ} (η : ℂ)
    (hη : η=1 ∨ η= -1)
    (hW : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] W=
      η • SmallLevelOriginal.fourierFunction (2*m) f)
    (hq : ∀ z : ℂ,0<z.im → fourier (fullCoefficients f (2*m)) (z+(1/4:ℝ))=
      (-η)/(((Real.sqrt 112:ℂ)*z)^(2*m))*
        fourier (fullCoefficients f (2*m)) (-1/((112:ℂ)*z)+(1/4:ℝ))) :
    QuarterTransformation (2*m) f := by
  let F:=SmallLevelOriginal.fourierFunction (2*m) f
  let k:ℤ:=((2*m:ℕ):ℤ)
  have hq' : (F ∣[k] translation (1/4)) ∣[k] fricke 112 (by decide)=
      (-η) • (F ∣[k] translation (1/4)) := by
    have hh:=fricke_law 112 (2*m) (by decide)
      (fun z => fourier (fullCoefficients f (2*m)) (z+(1/4:ℝ))) (-η) hq
    have he : (fun z : ℍ => fourier (fullCoefficients f (2*m)) ((z:ℂ)+(1/4:ℝ)))=
        F ∣[k] translation (1/4) := by
      funext z
      rw [translation_slash]
      change _=fourier (fullCoefficients f (2*m)) ((translation (1/4) • z:ℍ):ℂ)
      rw [translation_point]
    rw [he] at hh
    rcases hη with rfl|rfl
    · simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg hh.symm
    · simpa only [neg_neg,one_smul] using hh.symm
  have hWdet : (GeneralLinearGroup.det W:ℝ)=1:=fricke_det 28 (by decide)
  have hWi : F ∣[k] W⁻¹=η • F:=eigen_inverse F k W hWdet η hη hW
  have ht0 : translation ((1/4:ℝ)+(-1/4))=(1:GL (Fin 2) ℝ) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]
  have hinv : F ∣[k] quarterInverse=(-1:ℂ) • F := by
    rw [quarter_branch,SlashAction.slash_mul,SlashAction.slash_mul,
      SlashAction.slash_mul,hq',det_one_smul _ (translation_det _),
      ←SlashAction.slash_mul,translation_mul,ht0,SlashAction.slash_one,
      det_one_smul _ (det_one_inv W hWdet),hWi]
    rcases hη with rfl|rfl <;> simp
  have hmain:=eigen_inverse F k quarterInverse quarterInverse_det (-1) (Or.inr rfl) hinv
  rw [quarter_inverse,inv_inv] at hmain
  apply scaled_quarter
  simpa only [neg_one_smul] using hmain

#print axioms quarter_branch
#print axioms scaled_quarter
#print axioms transformation_of_quarter_fricke
end SmallLevelTwentyEightQuarter
end
end

/-! ## TwentyEightModular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelTwentyEightQuarter
open Complex SmallLevelAdditive SmallLevelTwentyEightGrid SmallLevelTwentyEightSystem
open SmallLevelTwentyEightParameters
open QuantitativeArithmeticSmallLevelTwentyEight

theorem quarter_from_system {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (hlaw : GridFrickeLaws (2*m) f ε) (S : PoleSystem m f ε) :
    QuarterTransformation (2*m) f := by
  let Q : ℂ→ℂ:=fun z => S.G z 21
  have hQ : Differentiable ℂ Q:=fun z => (S.entire hm hf hε hlaw 21 z).differentiableAt
  have hQF : ∀ s,S.B<s.re → Q s=original (2*m) f (1/4) s := by
    intro s hs
    dsimp only [Q]
    rw [S.original s hs,quotientGrid_quarter]
  have hfinite:=quarter_finiteOrder hm hf ε hε hlaw hQ S.B hQF
  obtain ⟨B,R,hR,hRF,hFE,_⟩:=quarter_functional_equation hm hf ε hε hlaw
  have heq:=S.quarter_matches B R hR hRF
  have hQFE : ∀ s,Q s=(-ε)*(112:ℂ)^(((2*m:ℕ):ℂ)/2-s)*Q (((2*m:ℕ):ℂ)-s) := by
    intro s
    have h:=hFE s
    rw [heq s,heq (((2*m:ℕ):ℂ)-s)] at h
    have he : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
    simpa only [he,reflectionMultiplier] using h
  obtain ⟨τ,_,hgrowth⟩:=hf.growth
  have hphys:=single_translate_fricke (by decide : 0<112) hf.zero hgrowth (1/4) Q
    hQ hfinite hQF (by rcases hε with rfl|rfl <;> norm_num : ‖-ε‖=1) hQFE
  apply transformation_of_quarter_fricke m (phase m ε) (phase_sign m hε)
    (grid_fricke_of_laws m hε hlaw)
  simpa only [SmallLevelTwentyEightParameters.phase,neg_mul,Nat.cast_ofNat] using hphys

#print axioms quarter_from_system
end SmallLevelTwentyEightQuarter

namespace SmallLevelOriginal
open SmallLevelTwentyEightGrid SmallLevelTwentyEightSystem SmallLevelTwentyEightQuarter

/-- The original level-28 converse, at every positive even weight, with
no extra continuation, pole, generator, or growth-exponent premise. -/
theorem level_twenty_eight {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 28 k f) : IsModular 28 k f := by
  obtain ⟨m,hm⟩:=heven
  have hk2 : k=2*m := by omega
  rw [hk2] at hk hf ⊢
  have hmpos : 0<m:=by omega
  obtain ⟨ε,hε,hlaw⟩:=original_grid_fricke_laws hf
  obtain ⟨S⟩:=exists_poleSystem hmpos hf ε hε hlaw
  exact QuantitativeArithmeticSmallLevelTwentyEight.modular_of_quarter (even_two_mul m) hf
    (quarter_from_system hmpos hf ε hε hlaw S)

#print axioms level_twenty_eight
end SmallLevelOriginal
end
end
