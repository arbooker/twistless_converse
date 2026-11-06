module
public import QuantitativeArithmeticPrimitiveResiduePairV4

public import FinitenessFiniteOrderClosureV1
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Tactic
public import Mathlib.Tactic.Group
public import QuantitativeArithmeticCompact34MMMRecurrenceV1
public import QuantitativeArithmeticCompact34MMPRecurrenceV1
public import QuantitativeArithmeticEntireQuotientV1
public import QuantitativeArithmeticMellinScaleV1
public import QuantitativeArithmeticQuadraticTwistInversionTheoryV4
public import QuantitativeArithmeticQuadraticTwistQuotientOrderV1
public import QuantitativeArithmeticQuadraticTwistReflectionTheoryV4
public import QuantitativeArithmeticRationalRecurrenceInterfaceV1
public import QuantitativeArithmeticCoherentTaylorTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujanTheoryV4
public import QuantitativeArithmeticTranslatedFrickeTheoryV4
public import QuantitativeArithmeticUniversalPoleVectorV1
public import SmallLevelActivePoleVectorV1
public import SmallLevelTaylorTheoryV4
public import SmallLevelContinuedRegularShiftedV1
public import SmallLevelContinuationTheoryV4
public import SmallLevelCrossedFrickeV1
public import SmallLevelLinearSourcePoleKernelV1
public import SmallLevelMellinUnscaleV1
public import SmallLevelModularCriterionV1
public import SmallLevelNormalizedEvenFrickeV1
public import SmallLevelPrimeRatesTheoryV4
public import SmallLevelAnalyticRigidityTheoryV4
public import SmallLevelRegularOrSimplePoleTailV1
public import SmallLevelSimplePoleTaylorTheoryV4
public import SmallLevelSixRootsV1
public import SmallLevelThirtyFourTheoryV4
public import SmallLevelThirtyFourGridTheoryV4
public import SmallLevelThirtyFourGridSlopeFromLeadingV1
public import SmallLevelThirtyFourGroupOriginalEV1
public import SmallLevelThirtyFourJetOperatorMMMTheoryV4
public import SmallLevelThirtyFourJetOperatorMMPTheoryV4
public import SmallLevelThirtyFourJetSourceMMMBundleV4
public import SmallLevelThirtyFourJetSourceMMPFamilyV4
public import SmallLevelThirtyFourPrimeFiveTheoryV4
public import SmallLevelThirtyFourPrimeFiveOriginalDefectV1
public import SmallLevelThirtyFourUnitMMMTheoryV4
public import SmallLevelThirtyFourUnitMMMInhomogeneousTheoryV4
public import SmallLevelThirtyFourUnitMMMResidualPart00V1
public import SmallLevelThirtyFourUnitMMMResidualSingleBundleV4
public import SmallLevelThirtyFourUnitMMPTheoryV4
public import SmallLevelThirtyFourUnitMMPInhomogeneousTheoryV4
public import SmallLevelThreePairV1
public import SmallLevelTransversalV1
public meta import QuantitativeArithmeticCompact34ExportsV1

/-! Consolidated converse argument. Large exact certificates remain
in their own modules; declarations and proof bodies are preserved. -/

/-! ## ThirtyFourPositiveShift -/
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFour

def shiftD (u : ℝ) : ℝ := 748*u^6-1126*u^5+540*u^4-1168*u^3+176*u^2-288*u

def shiftN (u : ℝ) : ℝ :=
  1122*u^7-6054*u^6+27603*u^5-44208*u^4+17676*u^3-14688*u^2+1632*u-1344

theorem shift_D_positive (u : ℝ) (hu : 2≤u) : 0<shiftD u := by
  have he : shiftD u=748*(u-2)^6+7850*(u-2)^5+34160*(u-2)^4+
      77792*(u-2)^3+95568*(u-2)^2+57216*(u-2)+11264 := by unfold shiftD; ring
  rw [he]
  have hv : 0≤u-2 := by linarith
  positivity

theorem shift_bounds (u : ℝ) (hu : 2≤u) :
    -(9*u/2)*shiftD u<shiftN u ∧ shiftN u<(9*u/2)*shiftD u := by
  have hv : 0≤u-2 := by linarith
  have he1 : 9*u*shiftD u-2*shiftN u=
      4488*(u-2)^7+64806*(u-2)^6+350334*(u-2)^5+949524*(u-2)^4+
      1404744*(u-2)^3+1155888*(u-2)^2+553536*(u-2)+169344 := by unfold shiftD shiftN; ring
  have he2 : 9*u*shiftD u+2*shiftN u=
      8976*(u-2)^7+103422*(u-2)^6+547146*(u-2)^5+1680492*(u-2)^4+
      3115992*(u-2)^3+3314448*(u-2)^2+1708992*(u-2)+236160 := by unfold shiftD shiftN; ring
  have hp1 : 0<9*u*shiftD u-2*shiftN u := by rw [he1]; positivity
  have hp2 : 0<9*u*shiftD u+2*shiftN u := by rw [he2]; positivity
  constructor <;> nlinarith

/-- The positive-shift scalar constraints have no physical solution. -/
theorem positive_shift_impossible (u : ℝ) (hu : 2≤u) (Y : ℂ)
    (hY : 9*u/2≤‖Y‖) (he : (shiftD u:ℂ)*Y=(shiftN u:ℂ)) : False := by
  have hd := shift_D_positive u hu
  have hb := shift_bounds u hu
  have ha : |shiftN u|<(9*u/2)*shiftD u := abs_lt.mpr ⟨by nlinarith [hb.1],hb.2⟩
  have hn := congrArg norm he
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd] at hn
  have hh := mul_le_mul_of_nonneg_left hY hd.le
  nlinarith

theorem powers_gap (n : ℕ) (hn : 1≤n) : (9/2:ℝ)*2^n≤9^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n=0
    · subst n; norm_num
    · have hh := ih (by omega)
      rw [pow_succ,pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤9) n]
#print axioms positive_shift_impossible
#print axioms powers_gap
end QuantitativeArithmeticSmallLevelThirtyFour
end
end

/-! ## ThirtyFourCenters -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourCenters
open SmallLevelNormalized SmallLevelThirtyFour SmallLevelOriginal
  QuantitativeArithmeticTranslatedFricke Complex Filter Set MeasureTheory
  FinitenessPolynomialSeries FinitenessFourierConstruction Matrix UpperHalfPlane
open scoped Topology MatrixGroups ModularForm

def center (positive : Bool) : ℝ := if positive then 1/6 else -(1/6)

/-- The original level34 input supplies both individual denominator-six
Fricke laws, with one common sign, via the proved modulus-six invariance. -/
theorem original_centers (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ positive : Bool,
      (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center positive))
        ∣[((2*m:ℕ):ℤ)] fricke 612 (by decide)=
      χ • (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center positive)) := by
  obtain ⟨χ,hχ,hF⟩ := original_fricke_sign (by decide : 0<34) m hf
  let δ := FinitenessNormalizedTwistProduct.root 34 f 2
  have hδ : δ=1 ∨ δ= -1 := FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2
  have hχδ : χ*δ=1 ∨ χ*δ= -1 := by
    rcases hχ with h|h <;> rcases hδ with hd|hd <;> simp [h,hd]
  refine ⟨χ*δ,hχδ,?_⟩
  intro positive
  cases positive
  · exact translated_slash_eigen 34 612 (2*m) (by decide) (by decide) _ χ δ _ A A_det
      hF (SmallLevelSixEigen.thirty_four_A (by omega) hf) fricke_branch_neg
  · exact translated_slash_eigen 34 612 (2*m) (by decide) (by decide) _ χ δ _ B B_det
      hF (SmallLevelSixEigen.thirty_four_B (by omega) hf) fricke_branch_pos

def centeredMellin (m : ℕ) (f : ℕ → ℂ) (positive : Bool) : ℂ → ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 612
    (SmallLevelAdditive.coefficients (FinitenessOriginalFourier.fullCoefficients f (2*m)) (center positive)))

/-- Actual entire finite-order continuations and functional equations for
both denominator-six additive twists, obtained from original input alone. -/
theorem original_centers_entire (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ positive : Bool,
      Differentiable ℂ (centeredMellin m f positive) ∧
      FinitenessFiniteOrder.Bound (centeredMellin m f positive) ∧
      ∀ s : ℂ, centeredMellin m f positive s=
        (χ/(Complex.I^(2*m)))*centeredMellin m f positive ((2*m:ℕ)-s) := by
  obtain ⟨χ,hχ,hF⟩ := original_centers m hm hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  refine ⟨χ,hχ,fun positive => ?_⟩
  exact translated_mellin_entire 612 (2*m) (by decide) (by omega) _
    (FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m))
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)) (center positive) χ hχ
    (hF positive)

#print axioms original_centers
#print axioms original_centers_entire
end SmallLevelThirtyFourCenters
end
end

/-! ## ThirtyFourGridContinuation -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGrid
open Complex

/-- Global additive continuation on the common 414-coordinate support,
from the original level34 solution hypotheses, with all eight signs covered. -/
theorem original_grid_continuation (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) :
    ∃ B : ℝ,∃ G : ℂ→Fin 414→ℂ,
      (∀ i x,MeromorphicNFAt (fun z => G z i) x) ∧
      ∀ z,B<z.re → G z=SmallLevelThirtyFourUnitMMM.actualGrid m f z := by
  obtain ⟨ε,hε,hlaw⟩:=original_grid_fricke_laws hf
  have hη : phase m ε=1 ∨ phase m ε= -1 := grid_physical_sign m hε
  have h₂:=badParameter_two_sign hf.toEulerData
  have h₁₇:=badParameter_seventeen_sign hf.toEulerData
  rcases hη with hη|hη <;> rcases h₂ with h₂|h₂ <;> rcases h₁₇ with h₁₇|h₁₇
  · exact SmallLevelThirtyFourUnitMMP.original_grid_continuation_scaled m hm hf hε hlaw
      (-1) (1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact SmallLevelThirtyFourUnitMMM.original_grid_continuation_scaled m hm hf hε hlaw
      (-1) (1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact SmallLevelThirtyFourUnitMMM.original_grid_continuation_scaled m hm hf hε hlaw
      (1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact SmallLevelThirtyFourUnitMMP.original_grid_continuation_scaled m hm hf hε hlaw
      (1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact SmallLevelThirtyFourUnitMMM.original_grid_continuation_scaled m hm hf hε hlaw
      (-1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact SmallLevelThirtyFourUnitMMP.original_grid_continuation_scaled m hm hf hε hlaw
      (-1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact SmallLevelThirtyFourUnitMMP.original_grid_continuation_scaled m hm hf hε hlaw
      (1) (1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact SmallLevelThirtyFourUnitMMM.original_grid_continuation_scaled m hm hf hε hlaw
      (1) (1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)

#print axioms original_grid_continuation
end SmallLevelThirtyFourGrid
end
end

/-! ## ThirtyFourGridLeadingRestriction -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGrid
open Complex SmallLevelPrimeRates SmallLevelFiniteGridSupport

/-- Restriction to the closed414-coordinate support for every physical sign. -/
theorem original_leading_restrict (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.EulerData 34 f) {ε : ℂ}
    (hε : ε=1 ∨ ε= -1) (s : ℂ) (w : Fin 510→ℂ) (i : Fin 546) :
    gridLeadingRows m f ε s (extension supportIndex (fun j => w (supportIndex j)))
      (selectedSource i)=gridLeadingRows m f ε s w (selectedSource i) := by
  have hmm (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
      (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
      (h₁₇ : badParameter f 17= -v) :
      gridLeadingRows m f ε s (extension supportIndex (fun j => w (supportIndex j)))
        (selectedSource i)=gridLeadingRows m f ε s w (selectedSource i) := by
    rw [←SmallLevelThirtyFourUnitMMM.scaled_sourceRows_actual m f ε u v s hu hv hη h₂ h₁₇,
      ←SmallLevelThirtyFourUnitMMM.scaled_sourceRows_actual m f ε u v s hu hv hη h₂ h₁₇]
    exact congrFun (SmallLevelThirtyFourUnitMMM.sourceRows_restrict _ _ _ _ _ _ w) i
  have hmp (u v : ℂ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
      (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
      (h₁₇ : badParameter f 17= v) :
      gridLeadingRows m f ε s (extension supportIndex (fun j => w (supportIndex j)))
        (selectedSource i)=gridLeadingRows m f ε s w (selectedSource i) := by
    rw [←SmallLevelThirtyFourUnitMMP.scaled_sourceRows_actual m f ε u v s hu hv hη h₂ h₁₇,
      ←SmallLevelThirtyFourUnitMMP.scaled_sourceRows_actual m f ε u v s hu hv hη h₂ h₁₇]
    exact congrFun (SmallLevelThirtyFourUnitMMP.sourceRows_restrict _ _ _ _ _ _ w) i
  have hη : phase m ε=1 ∨ phase m ε= -1 := grid_physical_sign m hε
  have h₂:=badParameter_two_sign hf
  have h₁₇:=badParameter_seventeen_sign hf
  rcases hη with hη|hη <;> rcases h₂ with h₂|h₂ <;> rcases h₁₇ with h₁₇|h₁₇
  · exact hmp (-1) 1 (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact hmm (-1) 1 (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact hmm 1 (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact hmp 1 (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact hmm (-1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact hmp (-1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact hmp 1 1 (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)
  · exact hmm 1 1 (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇)

#print axioms original_leading_restrict
end SmallLevelThirtyFourGrid
end
end

/-! ## ThirtyFourGridPoleSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGrid
open Complex Matrix Filter SmallLevelThirtyFourUnitMMM
open scoped Topology

/-- Meromorphic continuation together with every selected original Taylor row.
The structure makes no assertion that poles have been removed. -/
structure PoleSystem (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) where
  B : ℝ
  G : ℂ→Fin 414→ℂ
  E : ℕ→ℂ→Fin 546→ℂ
  meromorphic : ∀ i x,MeromorphicNFAt (fun z => G z i) x
  agreement : ∀ z,B<z.re → G z=actualGrid m f z
  error : ∀ (n : ℕ) (i : Fin 546) (z : ℂ),B-((n:ℝ)+1)<z.re → AnalyticAt ℂ (fun w => E n w i) z
  rows : ∀ n z,B<z.re →
    leadingMatrix m f ε z *ᵥ actualGrid m f z=E n z+
      ∑ j∈Finset.range n,restrictedShiftMatrix selectedSource supportIndex m f ε j z *ᵥ
        actualGrid m f (z+((j:ℂ)+1))

/-- Both continuation and the source equations follow from the original solution. -/
theorem original_pole_system (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) :
    ∃ ε : ℂ,(ε=1 ∨ ε= -1) ∧ Nonempty (PoleSystem m f ε) := by
  obtain ⟨ε,hε,hlaw⟩:=original_grid_fricke_laws hf
  obtain ⟨B,E,_hF,hE,hrow⟩:=initial_system_of_laws m hm hf hε hlaw
  obtain ⟨BG,G,hG,hGF⟩:=original_grid_continuation m hm hf
  refine ⟨ε,hε,⟨{
    B := max B BG
    G := G
    E := fun n s i => E (selectedSource i) n s
    meromorphic := hG
    agreement := ?_
    error := ?_
    rows := ?_
  }⟩⟩
  · intro z hz
    exact hGF z (lt_of_le_of_lt (le_max_right B BG) hz)
  · intro n i z hz
    apply hE n (selectedSource i) z
    linarith [le_max_left B BG]
  · intro n s hs
    have hb : B<s.re:=lt_of_le_of_lt (le_max_left B BG) hs
    funext i
    simp only [Pi.add_apply,Finset.sum_apply]
    change (restrictedLeadingMatrix selectedSource supportIndex m f ε s *ᵥ
      (fun j => gridVector (2*m) f s (supportIndex j))) i =
        E (selectedSource i) n s + ∑ c∈Finset.range n,
          (restrictedShiftMatrix selectedSource supportIndex m f ε c s *ᵥ
            (fun j => gridVector (2*m) f (s+((c:ℂ)+1)) (supportIndex j))) i
    rw [restrictedLeadingMatrix_mulVec,original_leading_restrict m hf.toEulerData hε]
    simp_rw [restrictedShiftMatrix_mulVec,shiftRows_restrict]
    exact hrow n s hb (selectedSource i)

/-- The original Taylor rows persist as punctured meromorphic identities. -/
theorem PoleSystem.continued_rows {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (n : ℕ) (i : Fin 546) (x : ℂ)
    (hx : S.B-((n:ℝ)+1)<x.re) :
    (fun z => ∑ j,leadingMatrix m f ε z i j*S.G z j)=ᶠ[𝓝[≠] x]
      (fun z => S.E n z i+∑ a∈Finset.range n,
        ∑ j,restrictedShiftMatrix selectedSource supportIndex m f ε a z i j*
          S.G (z+((a:ℂ)+1)) j) :=
  SmallLevelContinuation.rectangular_continued_rows S.B (actualGrid m f) S.G
    (leadingMatrix m f ε) (restrictedShiftMatrix selectedSource supportIndex m f ε) S.E
    (fun i z => (S.meromorphic i z).meromorphicAt) S.agreement
    (fun z i j => restrictedLeadingMatrix_analytic selectedSource supportIndex m f ε i j z)
    (fun n z i j => restrictedShiftMatrix_analytic selectedSource supportIndex m f ε n i j z)
    S.error S.rows n i x hx

#print axioms original_pole_system
#print axioms PoleSystem.continued_rows
end SmallLevelThirtyFourGrid
end
end

/-! ## ThirtyFourGridShiftCancellation -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGrid
open Complex SmallLevelFiniteGridSupport

/-- Every positive Taylor coefficient vanishes when its shifted argument
is the weight. This retains the permitted simple pole at that point. -/
theorem shiftRows_zero_at_weight (m : ℕ) (f : ℕ→ℂ) (ε : ℂ)
    (n : ℕ) (s : ℂ) (hs : s+((n:ℂ)+1)=((2*m:ℕ):ℂ))
    (v : Fin 510→ℂ) (i : GridSource) : gridShiftRows m f ε n s v i=0 := by
  have he : s+((n+1:ℕ):ℂ)-((2*m:ℕ):ℂ)=0 := by
    apply sub_eq_zero.mpr
    simpa only [Nat.cast_add,Nat.cast_one] using hs
  rw [shiftRows_factor,he,Ring.choose_zero_pos ℂ (Nat.succ_pos n),mul_zero,zero_mul]

theorem restrictedShiftMatrix_zero_at_weight {r d : ℕ}
    (J : Fin r→GridSource) (u : Fin d→Fin 510)
    (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ)
    (hs : s+((n:ℂ)+1)=((2*m:ℕ):ℂ)) (i : Fin r) (j : Fin d) :
    restrictedShiftMatrix J u m f ε n s i j=0 := by
  simp only [restrictedShiftMatrix,LinearMap.toMatrix'_apply,LinearMap.comp_apply]
  exact shiftRows_zero_at_weight m f ε n s hs (extension u (Pi.single j 1)) (J i)

#print axioms shiftRows_zero_at_weight
#print axioms restrictedShiftMatrix_zero_at_weight
end SmallLevelThirtyFourGrid
end
end

/-! ## ThirtyFourGridActivePoleSources -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGrid
open Complex Matrix Filter SmallLevelFiniteShift SmallLevelThirtyFourUnitMMM
open QuantitativeArithmeticUniversalPoleVector
open scoped Topology

/-- Lower Taylor equations retain their lower-variable terms exactly.
Positive shifts may include a simple pole at the weight; the center may
itself equal the weight and have higher pole order. -/
theorem PoleSystem.shifted_source_remainder {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ) (d : ℕ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => S.G z j) (x+n) ∨
      (x+n=((2*m:ℕ):ℂ) ∧ (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => S.G z j) (x+n))) :
    ∃ R : ℂ→Fin 546→ℂ,(∀ i,AnalyticAt ℂ (fun z => R z i) x) ∧
      ∀ i,(fun z => (∑ j,leadingMatrix m f ε (z-d) i j*S.G (z-d) j)-
        ∑ a∈Finset.range d,∑ j,
          restrictedShiftMatrix selectedSource supportIndex m f ε a (z-d) i j*
            S.G (z-((d-1-a:ℕ):ℂ)) j)=ᶠ[𝓝[≠] x] (fun z => R z i) := by
  apply continued_regular_shifted_source S.B S.G (leadingMatrix m f ε)
    (restrictedShiftMatrix selectedSource supportIndex m f ε) S.E x d S.error
  · intro a ha i j
    exact regular_or_simple_pole_tail
      (restrictedShiftMatrix selectedSource supportIndex m f ε) ((2*m:ℕ):ℂ)
      (fun n z i j => restrictedShiftMatrix_analytic selectedSource supportIndex m f ε n i j z)
      (restrictedShiftMatrix_zero_at_weight selectedSource supportIndex m f ε)
      S.G S.meromorphic x d hshift a ha i j
  · exact fun n i y hy => S.continued_rows n i y hy

theorem PoleSystem.active_leading_kernel {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ) (v : Fin 414→ℂ)
    (hv : IsLeadingVector S.G x v)
    (hshift : ∀ n : ℕ,0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => S.G z j) (x+n) ∨
      (x+n=((2*m:ℕ):ℂ) ∧ (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => S.G z j) (x+n))) :
    leadingMatrix m f ε x *ᵥ v=0 := by
  obtain ⟨R,hR,he⟩:=S.shifted_source_remainder x 0 hshift
  funext i
  apply hv.2 (fun z j => leadingMatrix m f ε z i j) (fun z => R z i)
    (fun j => restrictedLeadingMatrix_analytic selectedSource supportIndex m f ε i j x) (hR i)
  simpa only [Nat.cast_zero,sub_zero,Finset.range_zero,Finset.sum_empty] using he i

#print axioms PoleSystem.shifted_source_remainder
#print axioms PoleSystem.active_leading_kernel

/-- At the first lower point the only nonanalytic source is the first
Taylor coefficient applied to the vector at the center. -/
theorem PoleSystem.first_source_remainder {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ)
    (hshift : ∀ n : ℕ,0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => S.G z j) (x+n) ∨
      (x+n=((2*m:ℕ):ℂ) ∧ (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => S.G z j) (x+n))) :
    ∃ R : ℂ→Fin 546→ℂ,(∀ i,AnalyticAt ℂ (fun z => R z i) x) ∧
      ∀ᶠ z in 𝓝[≠] x,∀ i,
        (leadingMatrix m f ε (z-1) *ᵥ S.G (z-1)) i=
          (∑ j,restrictedShiftMatrix selectedSource supportIndex m f ε 0 (z-1) i j*S.G z j)+R z i := by
  obtain ⟨R,hR,he⟩:=S.shifted_source_remainder x 1 hshift
  refine ⟨R,hR,?_⟩
  have hall := (Filter.eventually_all).mpr he
  filter_upwards [hall] with z hz
  intro i
  have hi:=hz i
  simp only [Nat.cast_one,Finset.sum_range_one,Nat.sub_self,Nat.cast_zero,sub_zero] at hi
  change (∑ j,leadingMatrix m f ε (z-1) i j*S.G (z-1) j)=_
  linear_combination hi

#print axioms PoleSystem.first_source_remainder

/-- The common pole vector is taken after multiplying by `s-2m`.
This retains ordinary poles away from the weight and higher poles at the
weight, while allowing the eventual simple pole at the weight. -/
theorem PoleSystem.active_weighted_leading_kernel {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x : ℂ) (v : Fin 414→ℂ)
    (hv : IsLeadingVector (fun z j => (z-((2*m:ℕ):ℂ))*S.G z j) x v)
    (hshift : ∀ n : ℕ,0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => S.G z j) (x+n) ∨
      (x+n=((2*m:ℕ):ℂ) ∧ (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => S.G z j) (x+n))) :
    leadingMatrix m f ε x *ᵥ v=0 := by
  obtain ⟨R,hR,he⟩:=S.shifted_source_remainder x 0 hshift
  funext i
  apply hv.2 (fun z j => leadingMatrix m f ε z i j)
    (fun z => (z-((2*m:ℕ):ℂ))*R z i)
    (fun j => restrictedLeadingMatrix_analytic selectedSource supportIndex m f ε i j x)
    ((analyticAt_id.sub analyticAt_const).mul (hR i))
  filter_upwards [he i] with z hz
  simp only [Nat.cast_zero,sub_zero,Finset.range_zero,Finset.sum_empty] at hz
  calc
    _ = (z-((2*m:ℕ):ℂ))*(∑ j,leadingMatrix m f ε z i j*S.G z j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := congrArg (fun a : ℂ => (z-((2*m:ℕ):ℂ))*a) hz

#print axioms PoleSystem.active_weighted_leading_kernel
end SmallLevelThirtyFourGrid
end
end

/-! ## ThirtyFourUnitMMMInhomogeneousFirstSourceGerm -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMMInhomogeneous
open Complex Matrix Filter SmallLevelThirtyFourGrid SmallLevelPrimeRates SmallLevelFiniteGridSupport
open SmallLevelThirtyFourUnitMMM
open scoped Topology

def zeroRows (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : Fin 14→ℂ :=
  ![rhsZero0 X Y Z W a b r, rhsZero1 X Y Z W a b r, rhsZero2 X Y Z W a b r, rhsZero3 X Y Z W a b r, rhsZero4 X Y Z W a b r, rhsZero5 X Y Z W a b r, rhsZero6 X Y Z W a b r, rhsZero7 X Y Z W a b r, rhsZero8 X Y Z W a b r, rhsZero9 X Y Z W a b r, rhsZero10 X Y Z W a b r, rhsZero11 X Y Z W a b r, rhsZero12 X Y Z W a b r, rhsZero13 X Y Z W a b r]

theorem zeroRows_of_source (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (w : Fin 510→ℂ) (r : Fin 546→ℂ) (hw : ∀ i,sourceRows X Y Z W a b w i=r i) :
    zeroRows X Y Z W a b r=0 := by
  funext i
  fin_cases i
  · exact zero_row_0 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_1 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_2 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_3 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_4 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_5 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_6 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_7 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_8 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_9 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_10 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_11 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_12 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_13 X Y Z W a b hX hY hZ hW w r hw

/-- The fourteen eliminated first-Taylor equations follow from the continued
original source system, with the analytic remainder retained exactly. -/
theorem first_source_zero_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= -v)
    (hshift : ∀ n : ℕ,0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => S.G z j) (x+n) ∨
      (x+n=((2*m:ℕ):ℂ) ∧ (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => S.G z j) (x+n))) :
    ∃ R : ℂ→Fin 546→ℂ,(∀ i,AnalyticAt ℂ (fun z => R z i) x) ∧
      ∀ᶠ z in 𝓝[≠] x,
        zeroRows (u*parameter 2 m (z-1)) (parameter 3 m (z-1))
          (v*parameter 17 m (z-1)) (parameter 5 m (z-1))
          (badParameter f 3) (badParameter f 5)
          (fun i => (∑ j,restrictedShiftMatrix selectedSource supportIndex m f ε 0 (z-1) i j*S.G z j)+R z i)=0 := by
  obtain ⟨R,hR,he⟩:=S.first_source_remainder x hshift
  refine ⟨R,hR,?_⟩
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  filter_upwards [he] with z hz
  apply zeroRows_of_source _ _ _ _ _ _
    (mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) (z-1)))
    (parameter_ne_zero 3 m (by decide) (z-1))
    (mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) (z-1)))
    (parameter_ne_zero 5 m (by decide) (z-1))
    (extension supportIndex (S.G (z-1)))
  intro i
  rw [scaled_sourceRows_actual m f ε u v (z-1) hu hv hη h₂ h₁₇]
  rw [←restrictedLeadingMatrix_mulVec]
  exact hz i

#print axioms zeroRows_of_source
#print axioms first_source_zero_germ
end SmallLevelThirtyFourUnitMMMInhomogeneous
end
end

/-! ## ThirtyFourUnitMMMInhomogeneousRhsPropertiesFamilyV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false

open QuantitativeArithmeticRationalRecurrence

namespace QuantitativeArithmeticCompact34MMPRecurrence
def certificate : Certificate 546 411 where
  instructions := instructions
  «row» v := rows (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
  before i hi t ht :=
    of_decide_eq_true (List.all_eq_true.mp (before ⟨i, hi⟩) t ht)
  recurrence v r i hi := by
    have hv : ![v 0, v 1, v 2, v 3, v 4, v 5] = v := by
      funext j
      fin_cases j <;> rfl
    simpa only [hv] using recurrence (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) r ⟨i, hi⟩
end QuantitativeArithmeticCompact34MMPRecurrence

namespace SmallLevelThirtyFourUnitMMPInhomogeneous
def rhsMap (i : Fin 411) (X Y Z W a b : ℂ) : (Fin 546 → ℂ) →ₗ[ℂ] ℂ :=
  QuantitativeArithmeticCompact34MMPRecurrence.certificate.rowMap ![X,Y,Z,W,a,b] i

theorem rhsMap_apply (i : Fin 411) (X Y Z W a b : ℂ) (r : Fin 546 → ℂ) :
    rhsMap i X Y Z W a b r = QuantitativeArithmeticCompact34MMPRecurrence.rows X Y Z W a b i.val r := rfl

theorem rhs_add (i : Fin 411) (X Y Z W a b : ℂ) (r t : Fin 546 → ℂ) :
    QuantitativeArithmeticCompact34MMPRecurrence.rows X Y Z W a b i.val (r+t) =
    QuantitativeArithmeticCompact34MMPRecurrence.rows X Y Z W a b i.val r + QuantitativeArithmeticCompact34MMPRecurrence.rows X Y Z W a b i.val t :=
  (rhsMap i X Y Z W a b).map_add r t

theorem rhs_smul (i : Fin 411) (X Y Z W a b c : ℂ) (r : Fin 546 → ℂ) :
    QuantitativeArithmeticCompact34MMPRecurrence.rows X Y Z W a b i.val (c • r) =
    c * QuantitativeArithmeticCompact34MMPRecurrence.rows X Y Z W a b i.val r := by
  exact (rhsMap i X Y Z W a b).map_smul c r

theorem rhs_analytic (i : Fin 411) (X Y Z W a b : ℂ → ℂ) (r : ℂ → Fin 546 → ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ j, AnalyticAt ℂ (fun t => r t j) x) :
    AnalyticAt ℂ (fun t => QuantitativeArithmeticCompact34MMPRecurrence.rows (X t) (Y t) (Z t) (W t) (a t) (b t) i.val (r t)) x := by
  apply QuantitativeArithmeticCompact34MMPRecurrence.certificate.analytic (fun t => ![X t,Y t,Z t,W t,a t,b t]) r x ?_ ?_ hr i
  · intro j
    fin_cases j
    · exact hX
    · exact hY
    · exact hZ
    · exact hW
    · exact ha
    · exact hb
  · intro j
    fin_cases j
    · exact hX0
    · exact hY0
    · exact hZ0
    · exact hW0

#print axioms rhsMap
#print axioms rhs_add
#print axioms rhs_smul
#print axioms rhs_analytic
export_rhs_interfaces
#print axioms rhsPivot410Map
#print axioms rhsPivot410_analytic
end SmallLevelThirtyFourUnitMMPInhomogeneous

namespace QuantitativeArithmeticCompact34MMMRecurrence
def certificate : Certificate 546 411 where
  instructions := instructions
  «row» v := rows (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
  before i hi t ht :=
    of_decide_eq_true (List.all_eq_true.mp (before ⟨i, hi⟩) t ht)
  recurrence v r i hi := by
    have hv : ![v 0, v 1, v 2, v 3, v 4, v 5] = v := by
      funext j
      fin_cases j <;> rfl
    simpa only [hv] using recurrence (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) r ⟨i, hi⟩
end QuantitativeArithmeticCompact34MMMRecurrence

namespace SmallLevelThirtyFourUnitMMMInhomogeneous
def rhsMap (i : Fin 411) (X Y Z W a b : ℂ) : (Fin 546 → ℂ) →ₗ[ℂ] ℂ :=
  QuantitativeArithmeticCompact34MMMRecurrence.certificate.rowMap ![X,Y,Z,W,a,b] i

theorem rhsMap_apply (i : Fin 411) (X Y Z W a b : ℂ) (r : Fin 546 → ℂ) :
    rhsMap i X Y Z W a b r = QuantitativeArithmeticCompact34MMMRecurrence.rows X Y Z W a b i.val r := rfl

theorem rhs_add (i : Fin 411) (X Y Z W a b : ℂ) (r t : Fin 546 → ℂ) :
    QuantitativeArithmeticCompact34MMMRecurrence.rows X Y Z W a b i.val (r+t) =
    QuantitativeArithmeticCompact34MMMRecurrence.rows X Y Z W a b i.val r + QuantitativeArithmeticCompact34MMMRecurrence.rows X Y Z W a b i.val t :=
  (rhsMap i X Y Z W a b).map_add r t

theorem rhs_smul (i : Fin 411) (X Y Z W a b c : ℂ) (r : Fin 546 → ℂ) :
    QuantitativeArithmeticCompact34MMMRecurrence.rows X Y Z W a b i.val (c • r) =
    c * QuantitativeArithmeticCompact34MMMRecurrence.rows X Y Z W a b i.val r := by
  exact (rhsMap i X Y Z W a b).map_smul c r

theorem rhs_analytic (i : Fin 411) (X Y Z W a b : ℂ → ℂ) (r : ℂ → Fin 546 → ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ j, AnalyticAt ℂ (fun t => r t j) x) :
    AnalyticAt ℂ (fun t => QuantitativeArithmeticCompact34MMMRecurrence.rows (X t) (Y t) (Z t) (W t) (a t) (b t) i.val (r t)) x := by
  apply QuantitativeArithmeticCompact34MMMRecurrence.certificate.analytic (fun t => ![X t,Y t,Z t,W t,a t,b t]) r x ?_ ?_ hr i
  · intro j
    fin_cases j
    · exact hX
    · exact hY
    · exact hZ
    · exact hW
    · exact ha
    · exact hb
  · intro j
    fin_cases j
    · exact hX0
    · exact hY0
    · exact hZ0
    · exact hW0

#print axioms rhsMap
#print axioms rhs_add
#print axioms rhs_smul
#print axioms rhs_analytic
export_rhs_interfaces
#print axioms rhsPivot410Map
#print axioms rhsPivot410_analytic
end SmallLevelThirtyFourUnitMMMInhomogeneous
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SmallLevelThirtyFourUnitMMMInhomogeneous
open Complex

theorem rhsZero0_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero0 X Y Z W a b (r+t)=rhsZero0 X Y Z W a b r+rhsZero0 X Y Z W a b t := by
  simp only [rhsZero0, Pi.add_apply, rhsPivot70_add, rhsPivot110_add, rhsPivot126_add, rhsPivot235_add, rhsPivot236_add, rhsPivot256_add]
  ring

theorem rhsZero0_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero0 X Y Z W a b (c • r)=c*rhsZero0 X Y Z W a b r := by
  simp only [rhsZero0, Pi.smul_apply, smul_eq_mul, rhsPivot70_smul, rhsPivot110_smul, rhsPivot126_smul, rhsPivot235_smul, rhsPivot236_smul, rhsPivot256_smul]
  ring

def rhsZero0Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero0 X Y Z W a b
  map_add' := rhsZero0_add X Y Z W a b
  map_smul' c r := rhsZero0_smul X Y Z W a b c r

theorem rhsZero0_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero0 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot70:=rhsPivot70_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot110:=rhsPivot110_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot126:=rhsPivot126_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot236:=rhsPivot236_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero0
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero1_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero1 X Y Z W a b (r+t)=rhsZero1 X Y Z W a b r+rhsZero1 X Y Z W a b t := by
  simp only [rhsZero1, Pi.add_apply, rhsPivot77_add, rhsPivot235_add, rhsPivot236_add, rhsPivot256_add]
  ring

theorem rhsZero1_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero1 X Y Z W a b (c • r)=c*rhsZero1 X Y Z W a b r := by
  simp only [rhsZero1, Pi.smul_apply, smul_eq_mul, rhsPivot77_smul, rhsPivot235_smul, rhsPivot236_smul, rhsPivot256_smul]
  ring

def rhsZero1Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero1 X Y Z W a b
  map_add' := rhsZero1_add X Y Z W a b
  map_smul' c r := rhsZero1_smul X Y Z W a b c r

theorem rhsZero1_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero1 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot77:=rhsPivot77_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot236:=rhsPivot236_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero1
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero2_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero2 X Y Z W a b (r+t)=rhsZero2 X Y Z W a b r+rhsZero2 X Y Z W a b t := by
  simp only [rhsZero2, Pi.add_apply, rhsPivot164_add, rhsPivot239_add, rhsPivot252_add, rhsPivot255_add, rhsPivot256_add]
  ring

theorem rhsZero2_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero2 X Y Z W a b (c • r)=c*rhsZero2 X Y Z W a b r := by
  simp only [rhsZero2, Pi.smul_apply, smul_eq_mul, rhsPivot164_smul, rhsPivot239_smul, rhsPivot252_smul, rhsPivot255_smul, rhsPivot256_smul]
  ring

def rhsZero2Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero2 X Y Z W a b
  map_add' := rhsZero2_add X Y Z W a b
  map_smul' c r := rhsZero2_smul X Y Z W a b c r

theorem rhsZero2_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero2 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot164:=rhsPivot164_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot239:=rhsPivot239_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot252:=rhsPivot252_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot255:=rhsPivot255_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero2
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero3_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero3 X Y Z W a b (r+t)=rhsZero3 X Y Z W a b r+rhsZero3 X Y Z W a b t := by
  simp only [rhsZero3, Pi.add_apply, rhsPivot60_add, rhsPivot93_add, rhsPivot126_add, rhsPivot141_add, rhsPivot235_add, rhsPivot236_add, rhsPivot256_add]
  ring

theorem rhsZero3_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero3 X Y Z W a b (c • r)=c*rhsZero3 X Y Z W a b r := by
  simp only [rhsZero3, Pi.smul_apply, smul_eq_mul, rhsPivot60_smul, rhsPivot93_smul, rhsPivot126_smul, rhsPivot141_smul, rhsPivot235_smul, rhsPivot236_smul, rhsPivot256_smul]
  ring

def rhsZero3Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero3 X Y Z W a b
  map_add' := rhsZero3_add X Y Z W a b
  map_smul' c r := rhsZero3_smul X Y Z W a b c r

theorem rhsZero3_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero3 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot60:=rhsPivot60_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot93:=rhsPivot93_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot126:=rhsPivot126_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot141:=rhsPivot141_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot236:=rhsPivot236_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero3
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero4_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero4 X Y Z W a b (r+t)=rhsZero4 X Y Z W a b r+rhsZero4 X Y Z W a b t := by
  simp only [rhsZero4, Pi.add_apply, rhsPivot86_add, rhsPivot141_add, rhsPivot184_add, rhsPivot186_add, rhsPivot235_add, rhsPivot236_add, rhsPivot256_add]
  ring

theorem rhsZero4_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero4 X Y Z W a b (c • r)=c*rhsZero4 X Y Z W a b r := by
  simp only [rhsZero4, Pi.smul_apply, smul_eq_mul, rhsPivot86_smul, rhsPivot141_smul, rhsPivot184_smul, rhsPivot186_smul, rhsPivot235_smul, rhsPivot236_smul, rhsPivot256_smul]
  ring

def rhsZero4Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero4 X Y Z W a b
  map_add' := rhsZero4_add X Y Z W a b
  map_smul' c r := rhsZero4_smul X Y Z W a b c r

theorem rhsZero4_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero4 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot86:=rhsPivot86_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot141:=rhsPivot141_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot184:=rhsPivot184_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot186:=rhsPivot186_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot236:=rhsPivot236_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero4
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero5_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero5 X Y Z W a b (r+t)=rhsZero5 X Y Z W a b r+rhsZero5 X Y Z W a b t := by
  simp only [rhsZero5, Pi.add_apply, rhsPivot102_add, rhsPivot150_add, rhsPivot189_add, rhsPivot233_add, rhsPivot235_add, rhsPivot257_add]
  ring

theorem rhsZero5_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero5 X Y Z W a b (c • r)=c*rhsZero5 X Y Z W a b r := by
  simp only [rhsZero5, Pi.smul_apply, smul_eq_mul, rhsPivot102_smul, rhsPivot150_smul, rhsPivot189_smul, rhsPivot233_smul, rhsPivot235_smul, rhsPivot257_smul]
  ring

def rhsZero5Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero5 X Y Z W a b
  map_add' := rhsZero5_add X Y Z W a b
  map_smul' c r := rhsZero5_smul X Y Z W a b c r

theorem rhsZero5_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero5 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot102:=rhsPivot102_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot150:=rhsPivot150_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot189:=rhsPivot189_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot233:=rhsPivot233_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot257:=rhsPivot257_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero5
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero6_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero6 X Y Z W a b (r+t)=rhsZero6 X Y Z W a b r+rhsZero6 X Y Z W a b t := by
  simp only [rhsZero6, Pi.add_apply, rhsPivot177_add, rhsPivot178_add, rhsPivot179_add, rhsPivot189_add, rhsPivot233_add, rhsPivot235_add, rhsPivot257_add]
  ring

theorem rhsZero6_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero6 X Y Z W a b (c • r)=c*rhsZero6 X Y Z W a b r := by
  simp only [rhsZero6, Pi.smul_apply, smul_eq_mul, rhsPivot177_smul, rhsPivot178_smul, rhsPivot179_smul, rhsPivot189_smul, rhsPivot233_smul, rhsPivot235_smul, rhsPivot257_smul]
  ring

def rhsZero6Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero6 X Y Z W a b
  map_add' := rhsZero6_add X Y Z W a b
  map_smul' c r := rhsZero6_smul X Y Z W a b c r

theorem rhsZero6_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero6 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot177:=rhsPivot177_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot178:=rhsPivot178_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot179:=rhsPivot179_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot189:=rhsPivot189_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot233:=rhsPivot233_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot257:=rhsPivot257_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero6
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero7_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero7 X Y Z W a b (r+t)=rhsZero7 X Y Z W a b r+rhsZero7 X Y Z W a b t := by
  simp only [rhsZero7, Pi.add_apply, rhsPivot121_add, rhsPivot232_add, rhsPivot235_add, rhsPivot256_add, rhsPivot257_add, rhsPivot319_add, rhsPivot335_add]
  ring

theorem rhsZero7_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero7 X Y Z W a b (c • r)=c*rhsZero7 X Y Z W a b r := by
  simp only [rhsZero7, Pi.smul_apply, smul_eq_mul, rhsPivot121_smul, rhsPivot232_smul, rhsPivot235_smul, rhsPivot256_smul, rhsPivot257_smul, rhsPivot319_smul, rhsPivot335_smul]
  ring

def rhsZero7Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero7 X Y Z W a b
  map_add' := rhsZero7_add X Y Z W a b
  map_smul' c r := rhsZero7_smul X Y Z W a b c r

theorem rhsZero7_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero7 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot121:=rhsPivot121_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot232:=rhsPivot232_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot257:=rhsPivot257_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot319:=rhsPivot319_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot335:=rhsPivot335_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero7
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero8_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero8 X Y Z W a b (r+t)=rhsZero8 X Y Z W a b r+rhsZero8 X Y Z W a b t := by
  simp only [rhsZero8, Pi.add_apply, rhsPivot89_add, rhsPivot102_add, rhsPivot131_add, rhsPivot141_add, rhsPivot194_add, rhsPivot235_add, rhsPivot256_add, rhsPivot331_add, rhsPivot335_add]
  ring

theorem rhsZero8_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero8 X Y Z W a b (c • r)=c*rhsZero8 X Y Z W a b r := by
  simp only [rhsZero8, Pi.smul_apply, smul_eq_mul, rhsPivot89_smul, rhsPivot102_smul, rhsPivot131_smul, rhsPivot141_smul, rhsPivot194_smul, rhsPivot235_smul, rhsPivot256_smul, rhsPivot331_smul, rhsPivot335_smul]
  ring

def rhsZero8Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero8 X Y Z W a b
  map_add' := rhsZero8_add X Y Z W a b
  map_smul' c r := rhsZero8_smul X Y Z W a b c r

theorem rhsZero8_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero8 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot89:=rhsPivot89_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot102:=rhsPivot102_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot131:=rhsPivot131_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot141:=rhsPivot141_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot194:=rhsPivot194_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot331:=rhsPivot331_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot335:=rhsPivot335_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero8
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero9_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero9 X Y Z W a b (r+t)=rhsZero9 X Y Z W a b r+rhsZero9 X Y Z W a b t := by
  simp only [rhsZero9, Pi.add_apply, rhsPivot66_add, rhsPivot107_add, rhsPivot126_add, rhsPivot161_add, rhsPivot186_add, rhsPivot233_add, rhsPivot236_add, rhsPivot256_add, rhsPivot329_add, rhsPivot331_add, rhsPivot335_add]
  ring

theorem rhsZero9_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero9 X Y Z W a b (c • r)=c*rhsZero9 X Y Z W a b r := by
  simp only [rhsZero9, Pi.smul_apply, smul_eq_mul, rhsPivot66_smul, rhsPivot107_smul, rhsPivot126_smul, rhsPivot161_smul, rhsPivot186_smul, rhsPivot233_smul, rhsPivot236_smul, rhsPivot256_smul, rhsPivot329_smul, rhsPivot331_smul, rhsPivot335_smul]
  ring

def rhsZero9Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero9 X Y Z W a b
  map_add' := rhsZero9_add X Y Z W a b
  map_smul' c r := rhsZero9_smul X Y Z W a b c r

theorem rhsZero9_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero9 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot66:=rhsPivot66_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot107:=rhsPivot107_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot126:=rhsPivot126_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot161:=rhsPivot161_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot186:=rhsPivot186_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot233:=rhsPivot233_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot236:=rhsPivot236_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot329:=rhsPivot329_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot331:=rhsPivot331_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot335:=rhsPivot335_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero9
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero10_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero10 X Y Z W a b (r+t)=rhsZero10 X Y Z W a b r+rhsZero10 X Y Z W a b t := by
  simp only [rhsZero10, Pi.add_apply, rhsPivot79_add, rhsPivot87_add, rhsPivot110_add, rhsPivot174_add, rhsPivot232_add, rhsPivot235_add, rhsPivot256_add, rhsPivot265_add, rhsPivot335_add]
  ring

theorem rhsZero10_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero10 X Y Z W a b (c • r)=c*rhsZero10 X Y Z W a b r := by
  simp only [rhsZero10, Pi.smul_apply, smul_eq_mul, rhsPivot79_smul, rhsPivot87_smul, rhsPivot110_smul, rhsPivot174_smul, rhsPivot232_smul, rhsPivot235_smul, rhsPivot256_smul, rhsPivot265_smul, rhsPivot335_smul]
  ring

def rhsZero10Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero10 X Y Z W a b
  map_add' := rhsZero10_add X Y Z W a b
  map_smul' c r := rhsZero10_smul X Y Z W a b c r

theorem rhsZero10_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero10 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot79:=rhsPivot79_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot87:=rhsPivot87_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot110:=rhsPivot110_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot174:=rhsPivot174_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot232:=rhsPivot232_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot265:=rhsPivot265_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot335:=rhsPivot335_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero10
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero11_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero11 X Y Z W a b (r+t)=rhsZero11 X Y Z W a b r+rhsZero11 X Y Z W a b t := by
  simp only [rhsZero11, Pi.add_apply, rhsPivot93_add, rhsPivot126_add, rhsPivot150_add, rhsPivot189_add, rhsPivot233_add, rhsPivot236_add, rhsPivot256_add, rhsPivot257_add, rhsPivot277_add, rhsPivot331_add, rhsPivot335_add]
  ring

theorem rhsZero11_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero11 X Y Z W a b (c • r)=c*rhsZero11 X Y Z W a b r := by
  simp only [rhsZero11, Pi.smul_apply, smul_eq_mul, rhsPivot93_smul, rhsPivot126_smul, rhsPivot150_smul, rhsPivot189_smul, rhsPivot233_smul, rhsPivot236_smul, rhsPivot256_smul, rhsPivot257_smul, rhsPivot277_smul, rhsPivot331_smul, rhsPivot335_smul]
  ring

def rhsZero11Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero11 X Y Z W a b
  map_add' := rhsZero11_add X Y Z W a b
  map_smul' c r := rhsZero11_smul X Y Z W a b c r

theorem rhsZero11_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero11 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot93:=rhsPivot93_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot126:=rhsPivot126_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot150:=rhsPivot150_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot189:=rhsPivot189_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot233:=rhsPivot233_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot236:=rhsPivot236_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot257:=rhsPivot257_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot277:=rhsPivot277_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot331:=rhsPivot331_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot335:=rhsPivot335_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero11
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero12_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero12 X Y Z W a b (r+t)=rhsZero12 X Y Z W a b r+rhsZero12 X Y Z W a b t := by
  simp only [rhsZero12, Pi.add_apply, rhsPivot86_add, rhsPivot115_add, rhsPivot141_add, rhsPivot235_add, rhsPivot256_add, rhsPivot307_add, rhsPivot310_add, rhsPivot331_add, rhsPivot335_add]
  ring

theorem rhsZero12_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero12 X Y Z W a b (c • r)=c*rhsZero12 X Y Z W a b r := by
  simp only [rhsZero12, Pi.smul_apply, smul_eq_mul, rhsPivot86_smul, rhsPivot115_smul, rhsPivot141_smul, rhsPivot235_smul, rhsPivot256_smul, rhsPivot307_smul, rhsPivot310_smul, rhsPivot331_smul, rhsPivot335_smul]
  ring

def rhsZero12Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero12 X Y Z W a b
  map_add' := rhsZero12_add X Y Z W a b
  map_smul' c r := rhsZero12_smul X Y Z W a b c r

theorem rhsZero12_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero12 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot86:=rhsPivot86_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot115:=rhsPivot115_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot141:=rhsPivot141_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot307:=rhsPivot307_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot310:=rhsPivot310_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot331:=rhsPivot331_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot335:=rhsPivot335_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero12
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero13_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero13 X Y Z W a b (r+t)=rhsZero13 X Y Z W a b r+rhsZero13 X Y Z W a b t := by
  simp only [rhsZero13, Pi.add_apply, rhsPivot25_add, rhsPivot220_add, rhsPivot268_add, rhsPivot355_add, rhsPivot356_add, rhsPivot358_add, rhsPivot383_add]
  ring

theorem rhsZero13_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero13 X Y Z W a b (c • r)=c*rhsZero13 X Y Z W a b r := by
  simp only [rhsZero13, Pi.smul_apply, smul_eq_mul, rhsPivot25_smul, rhsPivot220_smul, rhsPivot268_smul, rhsPivot355_smul, rhsPivot356_smul, rhsPivot358_smul, rhsPivot383_smul]
  ring

def rhsZero13Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero13 X Y Z W a b
  map_add' := rhsZero13_add X Y Z W a b
  map_smul' c r := rhsZero13_smul X Y Z W a b c r

theorem rhsZero13_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero13 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot25:=rhsPivot25_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot220:=rhsPivot220_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot268:=rhsPivot268_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot355:=rhsPivot355_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot356:=rhsPivot356_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot358:=rhsPivot358_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot383:=rhsPivot383_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero13
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

#print axioms rhsZero13_analytic
#print axioms rhsZero13Map
end SmallLevelThirtyFourUnitMMMInhomogeneous
end
end
end

/-! ## ThirtyFourUnitMMMInhomogeneousFirstJetPole -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMMInhomogeneous
open Complex Matrix Filter SmallLevelThirtyFourGrid SmallLevelPrimeRates
open QuantitativeArithmeticUniversalPoleVector SmallLevelLinearSourcePoleKernel
open scoped Topology

def zeroMap (X Y Z W a b : ℂ) (l : Fin 14) : (Fin 546→ℂ)→ₗ[ℂ]ℂ :=
  ![rhsZero0Map X Y Z W a b, rhsZero1Map X Y Z W a b, rhsZero2Map X Y Z W a b, rhsZero3Map X Y Z W a b, rhsZero4Map X Y Z W a b, rhsZero5Map X Y Z W a b, rhsZero6Map X Y Z W a b, rhsZero7Map X Y Z W a b, rhsZero8Map X Y Z W a b, rhsZero9Map X Y Z W a b, rhsZero10Map X Y Z W a b, rhsZero11Map X Y Z W a b, rhsZero12Map X Y Z W a b, rhsZero13Map X Y Z W a b] l

theorem zeroMap_apply (X Y Z W a b : ℂ) (l : Fin 14) (r : Fin 546→ℂ) :
    zeroMap X Y Z W a b l r=zeroRows X Y Z W a b r l := by
  fin_cases l <;> rfl

theorem zeroMap_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) (l : Fin 14) :
    AnalyticAt ℂ (fun z => zeroMap (X z) (Y z) (Z z) (W z) (a z) (b z) l (r z)) x := by
  fin_cases l
  · exact rhsZero0_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero1_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero2_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero3_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero4_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero5_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero6_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero7_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero8_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero9_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero10_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero11_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero12_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero13_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr

def physicalZeroMap (m : ℕ) (f : ℕ→ℂ) (u v z : ℂ) (l : Fin 14) : (Fin 546→ℂ)→ₗ[ℂ]ℂ :=
  zeroMap (u*parameter 2 m (z-1)) (parameter 3 m (z-1))
    (v*parameter 17 m (z-1)) (parameter 5 m (z-1)) (badParameter f 3) (badParameter f 5) l

theorem physicalZeroMap_analytic (m : ℕ) (f : ℕ→ℂ) (u v x : ℂ)
    (hu : u≠0) (hv : v≠0) (r : ℂ→Fin 546→ℂ)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) (l : Fin 14) :
    AnalyticAt ℂ (fun z => physicalZeroMap m f u v z l (r z)) x := by
  have hp (p : ℕ) (hp : p≠0) : AnalyticAt ℂ (fun z => parameter p m (z-1)) x :=
    (parameter_analytic p m hp (x-1)).comp (f:=fun z : ℂ => z-1) (analyticAt_id.sub analyticAt_const)
  exact zeroMap_analytic _ _ _ _ _ _ r x
    (analyticAt_const.mul (hp 2 (by decide))) (hp 3 (by decide))
    (analyticAt_const.mul (hp 17 (by decide))) (hp 5 (by decide))
    analyticAt_const analyticAt_const
    (mul_ne_zero hu (parameter_ne_zero 2 m (by decide) (x-1)))
    (parameter_ne_zero 3 m (by decide) (x-1))
    (mul_ne_zero hv (parameter_ne_zero 17 m (by decide) (x-1)))
    (parameter_ne_zero 5 m (by decide) (x-1)) hr l

def firstJetMatrix (m : ℕ) (f : ℕ→ℂ) (ε u v z : ℂ) : Matrix (Fin 14) (Fin 414) ℂ :=
  fun l j => physicalZeroMap m f u v z l
    (fun i => restrictedSlopeMatrix selectedSource supportIndex m f ε (z-1) i j)

/-- All fourteen first-Taylor rows annihilate the SAME weighted pole vector
as the leading rows. This includes higher poles at the weight. -/
theorem active_first_jet_kernel {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= -v)
    (w : Fin 414→ℂ)
    (hw : IsLeadingVector (fun z j => (z-((2*m:ℕ):ℂ))*S.G z j) x w)
    (hshift : ∀ n : ℕ,0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => S.G z j) (x+n) ∨
      (x+n=((2*m:ℕ):ℂ) ∧ (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => S.G z j) (x+n))) :
    firstJetMatrix m f ε u v x *ᵥ w=0 := by
  obtain ⟨R,hR,he⟩:=first_source_zero_germ S x u v hu hv hη h₂ h₁₇ hshift
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  funext l
  apply eliminated_first_source_kernel _ x w hw
    (fun z => physicalZeroMap m f u v z l)
    (fun z i j => restrictedSlopeMatrix selectedSource supportIndex m f ε (z-1) i j) R
    (fun r hr => physicalZeroMap_analytic m f u v x hu0 hv0 r hr l)
    (fun i j => (restrictedSlopeMatrix_analytic selectedSource supportIndex m f ε i j (x-1)).comp (f:=fun z : ℂ => z-1)
      (analyticAt_id.sub analyticAt_const)) hR
  filter_upwards [he] with z hz
  change zeroMap _ _ _ _ _ _ l _=0
  rw [zeroMap_apply]
  simpa only [first_source_weighted,Pi.zero_apply] using congrFun hz l

#print axioms physicalZeroMap_analytic
#print axioms active_first_jet_kernel
end SmallLevelThirtyFourUnitMMMInhomogeneous
end
end

/-! ## ThirtyFourGridSlopeLinear -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGrid
open Complex Matrix SmallLevelFiniteGridSupport

def slopeLinearMap (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) :
    (Fin 510→ℂ)→ₗ[ℂ](GridSource→ℂ) where
  toFun := slopeRows m f ε 1 s
  map_add' v w := by
    funext i
    cases i <;> simp [slopeRows,gridSample_add,mul_add]
  map_smul' c v := by
    funext i
    cases i <;> simp [slopeRows,gridSample_smul,mul_left_comm]

def selectedSlopeLinearMap {r : ℕ} (J : Fin r→GridSource)
    (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) :
    (Fin 510→ℂ)→ₗ[ℂ](Fin r→ℂ) where
  toFun v i := slopeRows m f ε 1 s v (J i)
  map_add' v w := by
    funext i
    exact congrFun ((slopeLinearMap m f ε s).map_add v w) (J i)
  map_smul' c v := by
    funext i
    exact congrFun ((slopeLinearMap m f ε s).map_smul c v) (J i)

theorem restrictedSlopeMatrix_mulVec {r d : ℕ} (J : Fin r→GridSource) (u : Fin d→Fin 510)
    (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (v : Fin d→ℂ) (i : Fin r) :
    (restrictedSlopeMatrix J u m f ε s *ᵥ v) i=
      slopeRows m f ε 1 s (extension u v) (J i) := by
  have he : restrictedSlopeMatrix J u m f ε s=
      ((selectedSlopeLinearMap J m f ε s).comp (extension u)).toMatrix' := by
    ext i j
    rfl
  rw [he,LinearMap.toMatrix'_mulVec,LinearMap.comp_apply]
  rfl

#print axioms restrictedSlopeMatrix_mulVec
end SmallLevelThirtyFourGrid
end
end

/-! ## ThirtyFourUnitMMMInhomogeneousFirstJetSource -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMMInhomogeneous
open Complex Matrix SmallLevelThirtyFourGrid SmallLevelPrimeRates SmallLevelFiniteGridSupport
open SmallLevelThirtyFourUnitMMM SmallLevelLinearSourcePoleKernel

theorem firstJetMatrix_source_apply (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= -v) (w : Fin 414→ℂ) (l : Fin 14) :
    (firstJetMatrix m f ε u v x *ᵥ w) l=
      zeroRows (u*parameter 2 m (x-1)) (parameter 3 m (x-1))
        (v*parameter 17 m (x-1)) (parameter 5 m (x-1)) (badParameter f 3) (badParameter f 5)
        (sourceSlopeRows (u*parameter 2 m (x-1)) (parameter 3 m (x-1))
          (v*parameter 17 m (x-1)) (parameter 5 m (x-1)) (badParameter f 3) (badParameter f 5)
          (extension supportIndex w)) l := by
  change (∑ j,physicalZeroMap m f u v x l
    (fun i => restrictedSlopeMatrix selectedSource supportIndex m f ε (x-1) i j)*w j)=_
  rw [←apply_matrix]
  have he : (fun i => ∑ j,restrictedSlopeMatrix selectedSource supportIndex m f ε (x-1) i j*w j)=
      (fun i => slopeRows m f ε 1 (x-1) (extension supportIndex w) (selectedSource i)) := by
    funext i
    exact restrictedSlopeMatrix_mulVec selectedSource supportIndex m f ε (x-1) w i
  rw [he]
  have hs := funext (scaled_sourceSlopeRows_actual m f ε u v (x-1) hu hv hη h₂ h₁₇
    (extension supportIndex w))
  rw [←hs]
  exact zeroMap_apply _ _ _ _ _ _ l _

#print axioms firstJetMatrix_source_apply
end SmallLevelThirtyFourUnitMMMInhomogeneous
end
end

/-! ## ThirtyFourFiniteJetMMMDataBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourFiniteJetMMM
open Complex

def row0 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 0 + (((1)/(X)) + ((2)/(W^2)) + (((-1)*X)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-2)*X^2)/(W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 2
def row1 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2*Z)/(X*W^2)) + (((-1)*Y^2*Z)/(W^2)))*v 0 + (((1*Z)/(X)) + ((2*Z)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X^2*Y^2*Z)/(W^2)))*v 1 + ((((-1)*Z)/(2*W^2)) + (((-1)*Y*Z*a)/(2*W^2)) + (((-1)*Y^2*Z)/(2*W^2)) + (((-2)*X^2*Z)/(W^2)) + ((1*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + (((-3)*X^3*Y^2*Z)/(2*W^2)) + ((1*X^4*Z)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2*Z*a^2)/(2*W^2)) + ((1*X^4*Y^3*Z*a)/(2*W^2)))*v 2
def row2 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-2))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + ((2)/(Y^2)) + (((-1)*Z)/(Y^2)))*v 1 + (((2*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + (((-1)*X^2)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + ((1*X^2*a)/(Y)) + (((-1)*X^2*Z*a)/(2*Y)) + (1*X^2) + (((-1)*X^2*Z)/(2)) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-1)*X^3*a)/(Y)) + ((1*X^3*Z*a)/(2*Y)) + ((-1)*X^3) + ((1*X^3*Z)/(2)))*v 2
def row3 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 0 + (((1)/(X^2)) + ((4)/(X*W^2)) + ((1)/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((4*Y^2)/(X*W^2)) + ((5)/(W^2)) + (((-1)*b)/(W)) + ((-2)) + (((-1)*Z)/(W^2)) + (((-2)*Y*a)/(W^2)) + ((3*Y^2)/(W^2)) + ((1*Y^4)/(W^2)) + (((-1)*X)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + (((-1)*Y^4)/(2*X*W^2)) + (((-3))/(2*W^2)) + (((-3)*Y*a)/(2*W^2)) + ((4*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + (((-3)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + (((-8)*X)/(W^2)) + (((-1)*X*b)/(W)) + ((1*X)/(2)) + ((1*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((2*X*Y^2)/(W^2)) + (((-2)*X*Y^2*a^2)/(W^2)) + ((1*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-2)*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(W^2)) + (((-10)*X^2)/(W^2)) + ((3*X^2)/(2)) + ((3*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-11)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-2)*X^2*Y^3*a)/(W^2)) + (((-3)*X^2*Y^4)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3)/(2)) + ((1*X^3*Z)/(2*W^2)) + (((-2)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-9)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + ((2*X^4)/(W^2)) + ((1*X^4*Y*a)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + ((1*X^4*Y^3*a)/(W^2)))*v 2
def row4 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-2)*Y^2)/(X*W^2)) + (((-2)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 0 + ((((-1))/(X^2)) + ((1)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1))/(W^2)) + ((1*b)/(W)) + (2) + ((1*Y*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((3*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((3*X*Y^2)/(W^2)) + ((3*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((4*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 1 + (((1)/(2*X*W^2)) + ((1*Y*a)/(2*X*W^2)) + ((1*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + (((-1))/(2*W^2)) + (((-7)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + ((1*X*b)/(W)) + (((-1)*X)/(2)) + ((1*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y*Z*a)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(W^2)) + (((-1)*X*Y^2)/(2)) + ((1*X*Y^2*Z)/(2*W^2)) + (((-2)*X*Y^4)/(W^2)) + (((-1)*X^2)/(2*W^2)) + (((-3)*X^2)/(2)) + (((-2)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + ((9*X^2*Y^2)/(2*W^2)) + (((-3)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + (((-7)*X^3)/(W^2)) + (((-1)*X^3)/(2)) + ((1*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a)/(2)) + ((3*X^3*Y^2)/(W^2)) + (((-3)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-5)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(W^2)) + (((-17)*X^4)/(2*W^2)) + ((3*X^4*Z)/(2*W^2)) + (((-2)*X^4*Y*a)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-3)*X^4*Y^2)/(2*W^2)) + (((-3)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-5)*X^4*Y^3*a)/(2*W^2)) + (((-1)*X^4*Y^4)/(W^2)) + (((-2)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-3)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-3)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 2
def row5 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^3*W^2)) + ((1*X*Y^2)/(W^2)))*v 0 + (((1)/(X^4)) + ((4)/(X^3*W^2)) + ((2)/(X^3)) + (((-1)*Z)/(X^3*W^2)) + (((-1)*Y*a)/(X^3*W^2)) + ((4*Y^2)/(X^3*W^2)) + ((2)/(X^2*W^2)) + (((-2)*b)/(X^2*W)) + (((-4))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-2)*Y*a)/(X^2*W^2)) + ((1*Y^2)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + (((-1))/(X*W^2)) + ((2*b)/(X*W)) + ((1*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-2))/(W^2)) + (((-1)*b)/(W)) + (((-1)*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-5)*X)/(W^2)) + ((2*X*Z)/(W^2)) + ((2*X*Y*a)/(W^2)) + (((-3)*X*Y^2)/(W^2)) + ((2*X^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X^3*W^2)) + (((-1)*Y*a)/(2*X^3*W^2)) + (((-1)*Y^3*a)/(2*X^3*W^2)) + (((-1)*Y^4)/(2*X^3*W^2)) + (((-2))/(X^2*W^2)) + (((-2)*Y*a)/(X^2*W^2)) + ((4*Y^2)/(X^2*W^2)) + (((-1)*Y^2*a^2)/(X^2*W^2)) + (((-2)*Y^3*a)/(X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-15))/(2*X*W^2)) + (((-1)*b)/(X*W)) + ((1)/(2*X)) + ((1*Z)/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + ((1*Y*a)/(2*X)) + (((-1)*Y*Z*a)/(2*X*W^2)) + (((-2)*Y^2*a^2)/(X*W^2)) + ((1*Y^2)/(2*X)) + (((-1)*Y^2*Z)/(2*X*W^2)) + (((-3)*Y^3*a)/(2*X*W^2)) + ((3*Y^4)/(2*X*W^2)) + (((-13))/(2*W^2)) + ((2*b)/(W)) + (2) + ((2*Z)/(W^2)) + ((1*Y*Z*a)/(W^2)) + (((-5)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^2*Z)/(W^2)) + (((-2)*Y^3*a)/(W^2)) + (((-3)*Y^4)/(W^2)) + (((-1)*Y^4*a^2)/(2*W^2)) + (((-1)*Y^5*a)/(2*W^2)) + (((-5)*X)/(2*W^2)) + (((-1)*X*b)/(W)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + (1*X*Y*a) + (((-3)*X*Y^2*a^2)/(2*W^2)) + (1*X*Y^2) + (((-1)*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((3*X^2)/(2*W^2)) + ((-1)*X^2) + ((1*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-7)*X^2*Y^2)/(2*W^2)) + ((5*X^2*Y^2*a^2)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((15*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-3)*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + ((1*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((4*X^4)/(W^2)) + (((-1)*X^4*Z)/(W^2)) + ((3*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*Z*a)/(W^2)) + ((3*X^4*Y^2)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^2*Z)/(W^2)) + ((2*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(W^2)))*v 2
def row6 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^3*W^2)) + (((-1)*Y^2)/(X^2*W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 0 + ((((-1))/(X^4)) + ((1)/(X^3*W^2)) + (((-1))/(X^3)) + (((-2)*Y^2)/(X^3*W^2)) + (((-3))/(X^2*W^2)) + ((1*b)/(X^2*W)) + ((1)/(X^2)) + ((1*Y*a)/(X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-5))/(X*W^2)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-3)*Y^2)/(X*W^2)) + ((1*b)/(W)) + (1) + ((1*Z)/(W^2)) + ((2*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-1)*X)/(W^2)))*v 1 + (((1)/(2*X^3*W^2)) + ((1*Y*a)/(2*X^3*W^2)) + ((1*Y^3*a)/(2*X^3*W^2)) + ((1*Y^4)/(2*X^3*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + (((-3)*Y^2)/(X^2*W^2)) + ((1*Y^2*a^2)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1)/(2*X*W^2)) + ((1*b)/(X*W)) + (((-1))/(2*X)) + ((1*Z)/(2*X*W^2)) + ((1*Y*a)/(2*X*W^2)) + (((-1)*Y*a)/(2*X)) + ((1*Y*Z*a)/(2*X*W^2)) + (((-1)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(X*W^2)) + (((-1)*Y^2)/(2*X)) + ((1*Y^2*Z)/(2*X*W^2)) + ((1*Y^3*a)/(2*X*W^2)) + (((-3)*Y^4)/(2*X*W^2)) + ((7)/(2*W^2)) + (((-3))/(2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + (((-3)*Y^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((3*Y^3*a)/(2*W^2)) + ((1*Y^4)/(W^2)) + ((1*Y^4*a^2)/(2*W^2)) + ((1*Y^5*a)/(2*W^2)) + ((17*X)/(2*W^2)) + ((1*X*b)/(W)) + ((-2)*X) + (((-1)*X*Z)/(2*W^2)) + ((2*X*Y*a)/(W^2)) + ((-1)*X*Y*a) + ((1*X*Y*Z*a)/(2*W^2)) + ((3*X*Y^2)/(2*W^2)) + ((3*X*Y^2*a^2)/(2*W^2)) + ((-1)*X*Y^2) + ((1*X*Y^2*Z)/(2*W^2)) + ((3*X*Y^3*a)/(2*W^2)) + (((-1)*X*Y^4)/(W^2)) + ((7*X^2)/(2*W^2)) + ((-1)*X^2) + (((-3)*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((6*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((1*X^2*Y^3*a)/(W^2)) + ((3*X^2*Y^4)/(2*W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((3*X^3)/(2*W^2)) + (((-1)*X^3*Z)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((1*X^3*Y^3*a)/(2*W^2)) + ((1*X^3*Y^4)/(2*W^2)))*v 2
def row7 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 0 + ((((-1))/(X^3)) + (((-4))/(X^2*W^2)) + (((-1))/(X^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-4)*Y^2)/(X^2*W^2)) + (((-5))/(X*W^2)) + ((1*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-3)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-1))/(W^2)) + ((1*Z)/(W^2)) + ((2*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + ((2*X*Y^2)/(W^2)))*v 1 + (((1)/(2*X^2*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(2*X^2*W^2)) + ((3)/(2*X*W^2)) + ((3*Y*a)/(2*X*W^2)) + (((-4)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(X*W^2)) + ((3*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((8)/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + (((-1)*Z)/(2*W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((2*Y^2*a^2)/(W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((2*Y^3*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((10*X)/(W^2)) + (((-3)*X)/(2)) + (((-3)*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((11*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((2*X*Y^3*a)/(W^2)) + ((3*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((3*X^2)/(W^2)) + (((-1)*X^2)/(2)) + (((-3)*X^2*Z)/(2*W^2)) + ((2*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((9*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)) + (((-3)*X^3)/(W^2)) + ((1*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2)/(W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + (((-1)*X^4)/(W^2)) + ((1*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2)/(W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)))*v 2

def row8 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 0 + (((1)/(X^3)) + (((-1))/(X^2*W^2)) + ((1)/(X^2)) + ((2*Y^2)/(X^2*W^2)) + ((3)/(X*W^2)) + (((-1)*b)/(X*W)) + (((-2))/(X)) + (((-1)*Y*a)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-4))/(W^2)) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-3)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-5)*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + ((3*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + (((-1)*b)/(W)) + ((1)/(2)) + (((-1)*Z)/(2*W^2)) + ((1*Y*a)/(2)) + (((-1)*Y*Z*a)/(2*W^2)) + ((1*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + ((1*Y^2)/(2)) + (((-1)*Y^2*Z)/(2*W^2)) + ((2*Y^4)/(W^2)) + (((-3)*X)/(2*W^2)) + ((3*X)/(2)) + ((2*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + (((-9)*X*Y^2)/(2*W^2)) + ((3*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^2)/(2)) + ((1*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + ((15*X^2)/(2*W^2)) + ((1*X^2)/(2)) + (((-1)*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(2)) + (((-9)*X^2*Y^2)/(2*W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((19*X^3)/(2*W^2)) + (((-3)*X^3*Z)/(2*W^2)) + ((5*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + ((2*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((3*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 2
def row9 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1)/(X^3)) + ((1)/(X^2)) + ((1)/(X)) + (1))*v 0 + (((1*W^2)/(X^4*Y^2)) + (((-1))/(X^3*Y^2)) + ((1*W^2)/(X^3*Y^2)) + ((2)/(X^3)) + ((3)/(X^2*Y^2)) + (((-1)*W*b)/(X^2*Y^2)) + (((-2)*W^2)/(X^2*Y^2)) + (((-1)*a)/(X^2*Y)) + ((1*Y^2)/(X^2)) + (((-4))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + ((1*a)/(X*Y)) + (((-3))/(X)) + (((-3))/(Y^2)) + ((1*Z)/(Y^2)) + ((1*a)/(Y)) + ((-5)) + ((1*X)/(Y^2)) + ((-1)*X))*v 1 + ((((-1))/(2*X^3*Y^2)) + (((-1)*a)/(2*X^3*Y)) + (((-1)*Y*a)/(2*X^3)) + (((-1)*Y^2)/(2*X^3)) + (((-1)*a)/(2*X^2*Y)) + ((3)/(X^2)) + (((-1)*a^2)/(2*X^2)) + (((-1)*Y*a)/(2*X^2)) + (((-1)*W*b)/(X*Y^2)) + ((1*W^2)/(2*X*Y^2)) + (((-1)*Z)/(2*X*Y^2)) + ((1*W^2*a)/(2*X*Y)) + (((-1)*Z*a)/(2*X*Y)) + ((1)/(X)) + (((-1)*a^2)/(X)) + ((1*W^2)/(2*X)) + (((-1)*Z)/(2*X)) + ((2*Y^2)/(X)) + (((-3))/(2*Y^2)) + ((3*W^2)/(2*Y^2)) + ((2*a)/(Y)) + ((1*W^2*a)/(2*Y)) + (((-9))/(2)) + ((3*a^2)/(2)) + ((1*W^2)/(2)) + (1*Y*a) + (((-1)*Y^2*a^2)/(2)) + (((-1)*Y^3*a)/(2)) + ((15*X)/(2*Y^2)) + ((1*X*W^2)/(2*Y^2)) + (((-1)*X*Z)/(Y^2)) + ((1*X*W^2*a)/(2*Y)) + (((-9)*X)/(2)) + ((3*X*a^2)/(2)) + ((1*X*W^2)/(2)) + ((5*X*Y*a)/(2)) + (1*X*Y^2) + ((19*X^2)/(2*Y^2)) + (((-3)*X^2*Z)/(2*Y^2)) + ((5*X^2*a)/(2*Y)) + (((-1)*X^2*Z*a)/(2*Y)) + ((3*X^2)/(2)) + (2*X^2*a^2) + (((-1)*X^2*Z)/(2)) + (3*X^2*Y*a) + (1*X^2*Y^2) + ((2*X^3)/(Y^2)) + (((-1)*X^3*Z)/(2*Y^2)) + ((3*X^3*a)/(2*Y)) + (((-1)*X^3*Z*a)/(2*Y)) + ((3*X^3)/(2)) + ((1*X^3*a^2)/(2)) + (((-1)*X^3*Z)/(2)) + (1*X^3*Y*a) + ((1*X^3*Y^2)/(2)))*v 2
def row10 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1)/(X^3)) + ((1)/(X^2)) + ((1)/(X)) + (1))*v 0 + ((((-1)*W^2)/(X^4*Y^2)) + (((-4))/(X^3*Y^2)) + (((-1)*W^2)/(X^3*Y^2)) + ((1*Z)/(X^3*Y^2)) + ((1*a)/(X^3*Y)) + (((-4))/(X^3)) + (((-5))/(X^2*Y^2)) + ((1*W*b)/(X^2*Y^2)) + ((2*W^2)/(X^2*Y^2)) + ((1*Z)/(X^2*Y^2)) + ((2*a)/(X^2*Y)) + (((-3))/(X^2)) + (((-1)*Y^2)/(X^2)) + (((-1))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + ((2)/(Y^2)) + (((-1)*Z)/(Y^2)) + (2))*v 1 + (((1)/(2*X^3*Y^2)) + ((1*a)/(2*X^3*Y)) + ((1*Y*a)/(2*X^3)) + ((1*Y^2)/(2*X^3)) + ((3)/(2*X^2*Y^2)) + ((3*a)/(2*X^2*Y)) + (((-4))/(X^2)) + ((1*a^2)/(X^2)) + ((3*Y*a)/(2*X^2)) + ((1*Y^2)/(2*X^2)) + ((8)/(X*Y^2)) + ((1*W*b)/(X*Y^2)) + (((-1)*W^2)/(2*X*Y^2)) + (((-1)*Z)/(2*X*Y^2)) + ((1*a)/(X*Y)) + (((-1)*W^2*a)/(2*X*Y)) + ((1*Z*a)/(2*X*Y)) + (((-2))/(X)) + ((2*a^2)/(X)) + (((-1)*W^2)/(2*X)) + ((1*Z)/(2*X)) + ((2*Y*a)/(X)) + (((-1)*Y^2)/(X)) + ((10)/(Y^2)) + (((-3)*W^2)/(2*Y^2)) + (((-3)*Z)/(2*Y^2)) + ((1*a)/(Y)) + (((-1)*W^2*a)/(2*Y)) + (((-1)*Z*a)/(2*Y)) + ((11)/(2)) + (((-1)*W^2)/(2)) + (((-1)*Z)/(2)) + (2*Y*a) + ((3*Y^2)/(2)) + ((1*Y^2*a^2)/(2)) + ((1*Y^3*a)/(2)) + ((3*X)/(Y^2)) + (((-1)*X*W^2)/(2*Y^2)) + (((-3)*X*Z)/(2*Y^2)) + ((2*X*a)/(Y)) + (((-1)*X*W^2*a)/(2*Y)) + (((-1)*X*Z*a)/(2*Y)) + ((9*X)/(2)) + (((-1)*X*W^2)/(2)) + (((-1)*X*Z)/(2)) + ((1*X*Y*a)/(2)) + ((1*X*Y^2)/(2)) + (((-3)*X^2)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + (((-1)*X^2*Z*a)/(2*Y)) + (1*X^2) + ((-1)*X^2*a^2) + (((-1)*X^2*Z)/(2)) + ((-1)*X^2*Y*a) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-1)*X^3*a)/(Y)) + ((1*X^3*Z*a)/(2*Y)) + ((-1)*X^3) + ((1*X^3*Z)/(2)))*v 2
def row11 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1))/(X^2)) + (((-1))/(X)) + (1*X^2) + (1*X^3))*v 0 + ((((-1)*W^2)/(X^3*Y^2)) + ((1)/(X^2*Y^2)) + (((-1)*W^2)/(X^2*Y^2)) + (((-2))/(X^2)) + (((-3))/(X*Y^2)) + ((1*W*b)/(X*Y^2)) + ((1*W^2)/(X*Y^2)) + ((1*a)/(X*Y)) + (((-1)*Y^2)/(X)) + (((-5))/(Y^2)) + ((2*W^2)/(Y^2)) + ((1*Z)/(Y^2)) + ((1*a)/(Y)) + ((-3)) + ((1*X*W*b)/(Y^2)) + ((1*X*W^2)/(Y^2)) + ((1*X*Z)/(Y^2)) + ((2*X*a)/(Y)) + ((-1)*X) + ((-1)*X*Y^2) + (((-1)*X^2)/(Y^2)))*v 1 + (((1)/(2*X^2*Y^2)) + ((1*a)/(2*X^2*Y)) + ((1*Y*a)/(2*X^2)) + ((1*Y^2)/(2*X^2)) + ((1*a)/(2*X*Y)) + (((-3))/(X)) + ((1*a^2)/(2*X)) + ((1*Y*a)/(2*X)) + ((1)/(2*Y^2)) + ((1*W*b)/(Y^2)) + (((-1)*W^2)/(2*Y^2)) + ((1*Z)/(2*Y^2)) + ((1*a)/(2*Y)) + (((-1)*W^2*a)/(2*Y)) + ((1*Z*a)/(2*Y)) + ((-1)) + (1*a^2) + (((-1)*W^2)/(2)) + ((1*Z)/(2)) + ((1*Y*a)/(2)) + (((-3)*Y^2)/(2)) + ((7*X)/(2*Y^2)) + (((-3)*X*W^2)/(2*Y^2)) + (((-1)*X*a)/(2*Y)) + (((-1)*X*W^2*a)/(2*Y)) + (((-3)*X)/(2)) + (((-1)*X*W^2)/(2)) + ((3*X*Y*a)/(2)) + (1*X*Y^2) + ((1*X*Y^2*a^2)/(2)) + ((1*X*Y^3*a)/(2)) + ((17*X^2)/(2*Y^2)) + ((1*X^2*W*b)/(Y^2)) + (((-2)*X^2*W^2)/(Y^2)) + (((-1)*X^2*Z)/(2*Y^2)) + ((2*X^2*a)/(Y)) + (((-1)*X^2*W^2*a)/(Y)) + ((1*X^2*Z*a)/(2*Y)) + ((3*X^2)/(2)) + ((3*X^2*a^2)/(2)) + ((-1)*X^2*W^2) + ((1*X^2*Z)/(2)) + ((3*X^2*Y*a)/(2)) + ((-1)*X^2*Y^2) + ((7*X^3)/(2*Y^2)) + (((-1)*X^3*W^2)/(Y^2)) + (((-3)*X^3*Z)/(2*Y^2)) + ((1*X^3*a)/(2*Y)) + (((-1)*X^3*W^2*a)/(Y)) + (((-1)*X^3*Z*a)/(2*Y)) + (6*X^3) + ((-1)*X^3*a^2) + ((-1)*X^3*W^2) + (((-1)*X^3*Z)/(2)) + (1*X^3*Y*a) + ((3*X^3*Y^2)/(2)) + ((1*X^3*Y^2*a^2)/(2)) + ((1*X^3*Y^3*a)/(2)) + ((3*X^4)/(2*Y^2)) + (((-1)*X^4*Z)/(2*Y^2)) + ((1*X^4*a)/(2*Y)) + (((-1)*X^4*Z*a)/(2*Y)) + (1*X^4) + (((-1)*X^4*Z)/(2)) + ((1*X^4*Y*a)/(2)) + ((1*X^4*Y^2)/(2)))*v 2
def row12 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1))/(X^2)) + (1*X^2))*v 0 + (((1*W^2)/(X^3*Y^2)) + ((4)/(X^2*Y^2)) + ((2*W^2)/(X^2*Y^2)) + (((-1)*Z)/(X^2*Y^2)) + (((-1)*a)/(X^2*Y)) + ((4)/(X^2)) + ((2)/(X*Y^2)) + (((-2)*W*b)/(X*Y^2)) + (((-4)*W^2)/(X*Y^2)) + (((-1)*Z)/(X*Y^2)) + (((-2)*a)/(X*Y)) + ((1)/(X)) + ((1*Y^2)/(X)) + (((-1))/(Y^2)) + ((2*W*b)/(Y^2)) + ((1*a)/(Y)) + (2) + ((-1)*Y^2) + (((-2)*X)/(Y^2)) + (((-1)*X*W*b)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + ((1*X*a)/(Y)) + ((-3)*X) + (((-5)*X^2)/(Y^2)) + ((2*X^2*Z)/(Y^2)) + ((2*X^2*a)/(Y)) + ((-3)*X^2) + ((2*X^3)/(Y^2)) + ((-2)*X^3))*v 1 + ((((-1))/(2*X^2*Y^2)) + (((-1)*a)/(2*X^2*Y)) + (((-1)*Y*a)/(2*X^2)) + (((-1)*Y^2)/(2*X^2)) + (((-2))/(X*Y^2)) + (((-2)*a)/(X*Y)) + ((4)/(X)) + (((-1)*a^2)/(X)) + (((-2)*Y*a)/(X)) + (((-1)*Y^2)/(X)) + (((-15))/(2*Y^2)) + (((-1)*W*b)/(Y^2)) + ((1*W^2)/(2*Y^2)) + ((1*Z)/(2*Y^2)) + (((-1)*a)/(2*Y)) + ((1*W^2*a)/(2*Y)) + (((-1)*Z*a)/(2*Y)) + ((-2)*a^2) + ((1*W^2)/(2)) + (((-1)*Z)/(2)) + (((-3)*Y*a)/(2)) + ((3*Y^2)/(2)) + (((-13)*X)/(2*Y^2)) + ((2*X*W*b)/(Y^2)) + ((2*X*W^2)/(Y^2)) + ((2*X*Z)/(Y^2)) + ((1*X*Z*a)/(Y)) + (((-5)*X)/(2)) + ((1*X*a^2)/(2)) + (1*X*Z) + ((-2)*X*Y*a) + ((-3)*X*Y^2) + (((-1)*X*Y^2*a^2)/(2)) + (((-1)*X*Y^3*a)/(2)) + (((-5)*X^2)/(2*Y^2)) + (((-1)*X^2*W*b)/(Y^2)) + (((-1)*X^2*Z)/(Y^2)) + (((-1)*X^2*a)/(Y)) + ((1*X^2*W^2*a)/(Y)) + (((-3)*X^2*a^2)/(2)) + (1*X^2*W^2) + (((-1)*X^2*Y*a)/(2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*a^2)/(2)) + ((1*X^2*Y^3*a)/(2)) + ((3*X^3)/(2*Y^2)) + (((-1)*X^3*W^2)/(Y^2)) + ((1*X^3*Z)/(Y^2)) + ((1*X^3*a)/(Y)) + (((-7)*X^3)/(2)) + ((5*X^3*a^2)/(2)) + ((5*X^3*Y*a)/(2)) + ((15*X^4)/(2*Y^2)) + (((-1)*X^4*W^2)/(2*Y^2)) + (((-3)*X^4*Z)/(2*Y^2)) + (((-1)*X^4*a)/(Y)) + (((-1)*X^4*W^2*a)/(2*Y)) + ((1*X^4*Z*a)/(2*Y)) + ((-1)*X^4) + ((1*X^4*a^2)/(2)) + (((-1)*X^4*W^2)/(2)) + ((1*X^4*Z)/(2)) + (1*X^4*Y*a) + ((1*X^4*Y^2)/(2)) + ((4*X^5)/(Y^2)) + (((-1)*X^5*Z)/(Y^2)) + ((3*X^5*a)/(Y)) + (((-1)*X^5*Z*a)/(Y)) + (3*X^5) + (1*X^5*a^2) + ((-1)*X^5*Z) + (2*X^5*Y*a) + (1*X^5*Y^2))*v 2
def row13 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-2)*Y^2)/(X^2)) + (((-2)*Y^2)/(X)) + ((-1)*Y^2) + ((-1)*X*Y^2))*v 0 + ((((-1)*W^2)/(X^3)) + ((1)/(X^2)) + (((-2)*Y^2)/(X^2)) + (((-1))/(X)) + ((1*W*b)/(X)) + ((2*W^2)/(X)) + ((1*Y*a)/(X)) + (((-1)*Y^4)/(X)) + (3) + ((-1)*Z) + ((-1)*Y*a) + (3*Y^2) + (3*X) + ((-1)*X*Z) + ((-1)*X*Y*a) + (4*X*Y^2) + ((-1)*X^2) + (1*X^2*Y^2))*v 1 + (((1)/(2*X^2)) + ((1*Y*a)/(2*X^2)) + ((1*Y^3*a)/(2*X^2)) + ((1*Y^4)/(2*X^2)) + (((-1))/(2*X)) + (((-7)*Y^2)/(2*X)) + ((1*Y^2*a^2)/(2*X)) + ((1*Y^3*a)/(2*X)) + (1*W*b) + (((-1)*W^2)/(2)) + ((1*Z)/(2)) + (((-1)*Y*W^2*a)/(2)) + ((1*Y*Z*a)/(2)) + ((-1)*Y^2) + (1*Y^2*a^2) + (((-1)*Y^2*W^2)/(2)) + ((1*Y^2*Z)/(2)) + ((-2)*Y^4) + (((-1)*X)/(2)) + (((-3)*X*W^2)/(2)) + ((-2)*X*Y*a) + (((-1)*X*Y*W^2*a)/(2)) + ((9*X*Y^2)/(2)) + (((-3)*X*Y^2*a^2)/(2)) + (((-1)*X*Y^2*W^2)/(2)) + ((-1)*X*Y^3*a) + ((1*X*Y^4*a^2)/(2)) + ((1*X*Y^5*a)/(2)) + ((-7)*X^2) + (((-1)*X^2*W^2)/(2)) + (1*X^2*Z) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*W^2*a)/(2)) + (3*X^2*Y^2) + (((-3)*X^2*Y^2*a^2)/(2)) + (((-1)*X^2*Y^2*W^2)/(2)) + (((-5)*X^2*Y^3*a)/(2)) + ((-1)*X^2*Y^4) + (((-17)*X^3)/(2)) + ((3*X^3*Z)/(2)) + ((-2)*X^3*Y*a) + ((1*X^3*Y*Z*a)/(2)) + (((-3)*X^3*Y^2)/(2)) + (((-3)*X^3*Y^2*a^2)/(2)) + ((1*X^3*Y^2*Z)/(2)) + (((-5)*X^3*Y^3*a)/(2)) + ((-1)*X^3*Y^4) + ((-2)*X^4) + ((1*X^4*Z)/(2)) + (((-3)*X^4*Y*a)/(2)) + ((1*X^4*Y*Z*a)/(2)) + (((-3)*X^4*Y^2)/(2)) + (((-1)*X^4*Y^2*a^2)/(2)) + ((1*X^4*Y^2*Z)/(2)) + ((-1)*X^4*Y^3*a) + (((-1)*X^4*Y^4)/(2)))*v 2
def row14 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^2)) + (((-1)*Y^2)/(X)) + ((-1)*Y^2) + ((-1)*X*Y^2))*v 0 + (((1*W^2)/(X^3)) + ((4)/(X^2)) + ((1*W^2)/(X^2)) + (((-1)*Z)/(X^2)) + (((-1)*Y*a)/(X^2)) + ((4*Y^2)/(X^2)) + ((5)/(X)) + (((-1)*W*b)/(X)) + (((-2)*W^2)/(X)) + (((-1)*Z)/(X)) + (((-2)*Y*a)/(X)) + ((3*Y^2)/(X)) + ((1*Y^4)/(X)) + ((-1)) + ((-2)*X*Y^2))*v 1 + ((((-1))/(2*X^2)) + (((-1)*Y*a)/(2*X^2)) + (((-1)*Y^3*a)/(2*X^2)) + (((-1)*Y^4)/(2*X^2)) + (((-3))/(2*X)) + (((-3)*Y*a)/(2*X)) + ((4*Y^2)/(X)) + (((-1)*Y^2*a^2)/(X)) + (((-3)*Y^3*a)/(2*X)) + (((-1)*Y^4)/(2*X)) + ((-8)) + ((-1)*W*b) + ((1*W^2)/(2)) + ((1*Z)/(2)) + ((-1)*Y*a) + ((1*Y*W^2*a)/(2)) + (((-1)*Y*Z*a)/(2)) + (2*Y^2) + ((-2)*Y^2*a^2) + ((1*Y^2*W^2)/(2)) + (((-1)*Y^2*Z)/(2)) + ((-2)*Y^3*a) + (1*Y^4) + ((-10)*X) + ((3*X*W^2)/(2)) + ((3*X*Z)/(2)) + ((-1)*X*Y*a) + ((1*X*Y*W^2*a)/(2)) + ((1*X*Y*Z*a)/(2)) + (((-11)*X*Y^2)/(2)) + ((1*X*Y^2*W^2)/(2)) + ((1*X*Y^2*Z)/(2)) + ((-2)*X*Y^3*a) + (((-3)*X*Y^4)/(2)) + (((-1)*X*Y^4*a^2)/(2)) + (((-1)*X*Y^5*a)/(2)) + ((-1)*X^2) + ((1*X^2*W^2)/(2)) + ((1*X^2*Z)/(2)) + ((-2)*X^2*Y*a) + ((1*X^2*Y*W^2*a)/(2)) + ((1*X^2*Y*Z*a)/(2)) + (((-9)*X^2*Y^2)/(2)) + ((1*X^2*Y^2*W^2)/(2)) + ((1*X^2*Y^2*Z)/(2)) + (((-1)*X^2*Y^3*a)/(2)) + (((-1)*X^2*Y^4)/(2)) + (2*X^3) + (1*X^3*Y*a) + (1*X^3*Y^2*a^2) + (1*X^3*Y^3*a))*v 2
def row15 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((-2)) + (1*Z) + (2*X) + ((-1)*X*Z))*v 1 + ((2*X^2) + ((-1)*X^2*Z) + ((-1)*X^3) + ((1*X^3*Z)/(2)) + (1*X^3*Y*a) + (((-1)*X^3*Y*Z*a)/(2)) + (1*X^3*Y^2) + (((-1)*X^3*Y^2*Z)/(2)) + ((-1)*X^4) + ((1*X^4*Z)/(2)) + ((-1)*X^4*Y*a) + ((1*X^4*Y*Z*a)/(2)) + ((-1)*X^4*Y^2) + ((1*X^4*Y^2*Z)/(2)))*v 2

def row16 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 0 + ((((-1))/(X^3)) + (((-4))/(X^2*W^2)) + (((-1))/(X^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-4)*Y^2)/(X^2*W^2)) + (((-5))/(X*W^2)) + ((1*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-3)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + ((1)/(W^2)) + ((2*X*Y^2)/(W^2)))*v 1 + (((1)/(2*X^2*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(2*X^2*W^2)) + ((3)/(2*X*W^2)) + ((3*Y*a)/(2*X*W^2)) + (((-4)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(X*W^2)) + ((3*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((8)/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + (((-1)*Z)/(2*W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((2*Y^2*a^2)/(W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((2*Y^3*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((10*X)/(W^2)) + (((-3)*X)/(2)) + (((-3)*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((11*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((2*X*Y^3*a)/(W^2)) + ((3*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Z)/(2*W^2)) + ((2*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((9*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)) + (((-2)*X^3)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^3*a)/(W^2)))*v 2
def row17 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1))/(X)) + ((-1)) + ((-1)*X) + ((-1)*X^2))*v 0 + (((1*W^2)/(X^2*Y^2)) + ((4)/(X*Y^2)) + ((1*W^2)/(X*Y^2)) + (((-1)*Z)/(X*Y^2)) + (((-1)*a)/(X*Y)) + ((4)/(X)) + ((5)/(Y^2)) + (((-1)*W*b)/(Y^2)) + (((-2)*W^2)/(Y^2)) + (((-1)*Z)/(Y^2)) + (((-2)*a)/(Y)) + (3) + (1*Y^2) + (((-1)*X)/(Y^2)) + ((-2)*X^2))*v 1 + ((((-1))/(2*X*Y^2)) + (((-1)*a)/(2*X*Y)) + (((-1)*Y*a)/(2*X)) + (((-1)*Y^2)/(2*X)) + (((-3))/(2*Y^2)) + (((-3)*a)/(2*Y)) + (4) + ((-1)*a^2) + (((-3)*Y*a)/(2)) + (((-1)*Y^2)/(2)) + (((-8)*X)/(Y^2)) + (((-1)*X*W*b)/(Y^2)) + ((1*X*W^2)/(2*Y^2)) + ((1*X*Z)/(2*Y^2)) + (((-1)*X*a)/(Y)) + ((1*X*W^2*a)/(2*Y)) + (((-1)*X*Z*a)/(2*Y)) + (2*X) + ((-2)*X*a^2) + ((1*X*W^2)/(2)) + (((-1)*X*Z)/(2)) + ((-2)*X*Y*a) + (1*X*Y^2) + (((-10)*X^2)/(Y^2)) + ((3*X^2*W^2)/(2*Y^2)) + ((3*X^2*Z)/(2*Y^2)) + (((-1)*X^2*a)/(Y)) + ((1*X^2*W^2*a)/(2*Y)) + ((1*X^2*Z*a)/(2*Y)) + (((-11)*X^2)/(2)) + ((1*X^2*W^2)/(2)) + ((1*X^2*Z)/(2)) + ((-2)*X^2*Y*a) + (((-3)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*a^2)/(2)) + (((-1)*X^2*Y^3*a)/(2)) + (((-1)*X^3)/(Y^2)) + ((1*X^3*W^2)/(2*Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-2)*X^3*a)/(Y)) + ((1*X^3*W^2*a)/(2*Y)) + ((1*X^3*Z*a)/(2*Y)) + (((-9)*X^3)/(2)) + ((1*X^3*W^2)/(2)) + ((1*X^3*Z)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)) + ((2*X^4)/(Y^2)) + ((1*X^4*a)/(Y)) + (1*X^4*a^2) + (1*X^4*Y*a))*v 2
def row18 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-2))/(X)) + ((-2)) + ((-1)*X) + ((-1)*X^2))*v 0 + ((((-1)*W^2)/(X^2*Y^2)) + ((1)/(X*Y^2)) + (((-2))/(X)) + (((-1))/(Y^2)) + ((1*W*b)/(Y^2)) + ((2*W^2)/(Y^2)) + ((1*a)/(Y)) + ((-1)*Y^2) + ((3*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + (((-1)*X*a)/(Y)) + (3*X) + ((3*X^2)/(Y^2)) + (((-1)*X^2*Z)/(Y^2)) + (((-1)*X^2*a)/(Y)) + (4*X^2) + (((-1)*X^3)/(Y^2)) + (1*X^3))*v 1 + (((1)/(2*X*Y^2)) + ((1*a)/(2*X*Y)) + ((1*Y*a)/(2*X)) + ((1*Y^2)/(2*X)) + (((-1))/(2*Y^2)) + (((-7))/(2)) + ((1*a^2)/(2)) + ((1*Y*a)/(2)) + ((1*X*W*b)/(Y^2)) + (((-1)*X*W^2)/(2*Y^2)) + ((1*X*Z)/(2*Y^2)) + (((-1)*X*W^2*a)/(2*Y)) + ((1*X*Z*a)/(2*Y)) + ((-1)*X) + (1*X*a^2) + (((-1)*X*W^2)/(2)) + ((1*X*Z)/(2)) + ((-2)*X*Y^2) + (((-1)*X^2)/(2*Y^2)) + (((-3)*X^2*W^2)/(2*Y^2)) + (((-2)*X^2*a)/(Y)) + (((-1)*X^2*W^2*a)/(2*Y)) + ((9*X^2)/(2)) + (((-3)*X^2*a^2)/(2)) + (((-1)*X^2*W^2)/(2)) + ((-1)*X^2*Y*a) + ((1*X^2*Y^2*a^2)/(2)) + ((1*X^2*Y^3*a)/(2)) + (((-7)*X^3)/(Y^2)) + (((-1)*X^3*W^2)/(2*Y^2)) + ((1*X^3*Z)/(Y^2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3*W^2*a)/(2*Y)) + (3*X^3) + (((-3)*X^3*a^2)/(2)) + (((-1)*X^3*W^2)/(2)) + (((-5)*X^3*Y*a)/(2)) + ((-1)*X^3*Y^2) + (((-17)*X^4)/(2*Y^2)) + ((3*X^4*Z)/(2*Y^2)) + (((-2)*X^4*a)/(Y)) + ((1*X^4*Z*a)/(2*Y)) + (((-3)*X^4)/(2)) + (((-3)*X^4*a^2)/(2)) + ((1*X^4*Z)/(2)) + (((-5)*X^4*Y*a)/(2)) + ((-1)*X^4*Y^2) + (((-2)*X^5)/(Y^2)) + ((1*X^5*Z)/(2*Y^2)) + (((-3)*X^5*a)/(2*Y)) + ((1*X^5*Z*a)/(2*Y)) + (((-3)*X^5)/(2)) + (((-1)*X^5*a^2)/(2)) + ((1*X^5*Z)/(2)) + ((-1)*X^5*Y*a) + (((-1)*X^5*Y^2)/(2)))*v 2
def row19 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2)) + ((1*Y^2)/(X)) + (1*Y^2) + (1*X*Y^2))*v 0 + (((1*W^2)/(X^3)) + (((-1))/(X^2)) + ((1*W^2)/(X^2)) + ((2*Y^2)/(X^2)) + ((3)/(X)) + (((-1)*W*b)/(X)) + (((-2)*W^2)/(X)) + (((-1)*Y*a)/(X)) + ((1*Y^4)/(X)) + ((-4)) + (1*Z) + (1*Y*a) + ((-3)*Y^2) + ((-3)*X) + (1*X*Z) + (1*X*Y*a) + ((-5)*X*Y^2) + (1*X^2) + ((-1)*X^2*Y^2))*v 1 + ((((-1))/(2*X^2)) + (((-1)*Y*a)/(2*X^2)) + (((-1)*Y^3*a)/(2*X^2)) + (((-1)*Y^4)/(2*X^2)) + (((-1)*Y*a)/(2*X)) + ((3*Y^2)/(X)) + (((-1)*Y^2*a^2)/(2*X)) + (((-1)*Y^3*a)/(2*X)) + ((-1)*W*b) + ((1*W^2)/(2)) + (((-1)*Z)/(2)) + ((1*Y*W^2*a)/(2)) + (((-1)*Y*Z*a)/(2)) + (1*Y^2) + ((-1)*Y^2*a^2) + ((1*Y^2*W^2)/(2)) + (((-1)*Y^2*Z)/(2)) + (2*Y^4) + (((-3)*X)/(2)) + ((3*X*W^2)/(2)) + (2*X*Y*a) + ((1*X*Y*W^2*a)/(2)) + (((-9)*X*Y^2)/(2)) + ((3*X*Y^2*a^2)/(2)) + ((1*X*Y^2*W^2)/(2)) + (1*X*Y^3*a) + (((-1)*X*Y^4*a^2)/(2)) + (((-1)*X*Y^5*a)/(2)) + ((15*X^2)/(2)) + ((1*X^2*W^2)/(2)) + ((-1)*X^2*Z) + ((1*X^2*Y*W^2*a)/(2)) + (((-9)*X^2*Y^2)/(2)) + ((3*X^2*Y^2*a^2)/(2)) + ((1*X^2*Y^2*W^2)/(2)) + ((5*X^2*Y^3*a)/(2)) + (1*X^2*Y^4) + ((19*X^3)/(2)) + (((-3)*X^3*Z)/(2)) + ((5*X^3*Y*a)/(2)) + (((-1)*X^3*Y*Z*a)/(2)) + ((3*X^3*Y^2)/(2)) + (2*X^3*Y^2*a^2) + (((-1)*X^3*Y^2*Z)/(2)) + (3*X^3*Y^3*a) + (1*X^3*Y^4) + (2*X^4) + (((-1)*X^4*Z)/(2)) + ((3*X^4*Y*a)/(2)) + (((-1)*X^4*Y*Z*a)/(2)) + ((3*X^4*Y^2)/(2)) + ((1*X^4*Y^2*a^2)/(2)) + (((-1)*X^4*Y^2*Z)/(2)) + (1*X^4*Y^3*a) + ((1*X^4*Y^4)/(2)))*v 2
def row20 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2)) + ((1*Y^2)/(X)) + (1*Y^2) + (1*X*Y^2))*v 0 + ((((-1)*W^2)/(X^3)) + (((-4))/(X^2)) + (((-1)*W^2)/(X^2)) + ((1*Z)/(X^2)) + ((1*Y*a)/(X^2)) + (((-4)*Y^2)/(X^2)) + (((-5))/(X)) + ((1*W*b)/(X)) + ((2*W^2)/(X)) + ((1*Z)/(X)) + ((2*Y*a)/(X)) + (((-3)*Y^2)/(X)) + (((-1)*Y^4)/(X)) + (1) + (2*X*Y^2))*v 1 + (((1)/(2*X^2)) + ((1*Y*a)/(2*X^2)) + ((1*Y^3*a)/(2*X^2)) + ((1*Y^4)/(2*X^2)) + ((3)/(2*X)) + ((3*Y*a)/(2*X)) + (((-4)*Y^2)/(X)) + ((1*Y^2*a^2)/(X)) + ((3*Y^3*a)/(2*X)) + ((1*Y^4)/(2*X)) + (8) + (1*W*b) + (((-1)*W^2)/(2)) + (((-1)*Z)/(2)) + (1*Y*a) + (((-1)*Y*W^2*a)/(2)) + ((1*Y*Z*a)/(2)) + ((-2)*Y^2) + (2*Y^2*a^2) + (((-1)*Y^2*W^2)/(2)) + ((1*Y^2*Z)/(2)) + (2*Y^3*a) + ((-1)*Y^4) + (10*X) + (((-3)*X*W^2)/(2)) + (((-3)*X*Z)/(2)) + (1*X*Y*a) + (((-1)*X*Y*W^2*a)/(2)) + (((-1)*X*Y*Z*a)/(2)) + ((11*X*Y^2)/(2)) + (((-1)*X*Y^2*W^2)/(2)) + (((-1)*X*Y^2*Z)/(2)) + (2*X*Y^3*a) + ((3*X*Y^4)/(2)) + ((1*X*Y^4*a^2)/(2)) + ((1*X*Y^5*a)/(2)) + (1*X^2) + (((-1)*X^2*W^2)/(2)) + (((-1)*X^2*Z)/(2)) + (2*X^2*Y*a) + (((-1)*X^2*Y*W^2*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2)) + ((9*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*W^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2)) + ((1*X^2*Y^3*a)/(2)) + ((1*X^2*Y^4)/(2)) + ((-2)*X^3) + ((-1)*X^3*Y*a) + ((-1)*X^3*Y^2*a^2) + ((-1)*X^3*Y^3*a))*v 2
def row21 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-2))/(Y^2)) + ((1*Z)/(Y^2)) + ((2*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)))*v 1 + (((2*X^2)/(Y^2)) + (((-1)*X^2*Z)/(Y^2)) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + ((1*X^3*a)/(Y)) + (((-1)*X^3*Z*a)/(2*Y)) + (1*X^3) + (((-1)*X^3*Z)/(2)) + (((-1)*X^4)/(Y^2)) + ((1*X^4*Z)/(2*Y^2)) + (((-1)*X^4*a)/(Y)) + ((1*X^4*Z*a)/(2*Y)) + ((-1)*X^4) + ((1*X^4*Z)/(2)))*v 2
def row22 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((2*Y^2)/(X^2*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 0 + ((((-5))/(X^2*W^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-2)*Y^2)/(X^2*W^2)) + ((3)/(X*W^2)) + ((1)/(X)) + (((-1)*Y^2)/(X*W^2)) + ((1)/(W^2)) + (((-1)*X)/(W^2)) + ((4*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 1 + (((3)/(2*X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(2*X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((6)/(W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(W^2)) + ((1*Y^4)/(2*W^2)) + ((1*X)/(2*W^2)) + (((-1)*X*Z)/(2*W^2)) + ((2*X*Y*a)/(W^2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((2*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((1*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-2)*X^2)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + (((-9)*X^4)/(2*W^2)) + ((1*X^4*Z)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)) + (((-1)*X^4*Y^4)/(2*W^2)) + (((-2)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-3)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-3)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 2
def row23 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 0 + (((2)/(X^3)) + ((1)/(X^2*W^2)) + (((-1)*b)/(X^2*W)) + (((-2))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + ((2*Y^2)/(X^2*W^2)) + (((-4))/(X*W^2)) + ((1*b)/(X*W)) + ((1*Z)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-6))/(W^2)) + (1) + ((1*Z)/(W^2)) + ((4*Y*a)/(W^2)) + (((-7)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-5)*X)/(W^2)) + ((2*X*Z)/(W^2)) + ((2*X*Y*a)/(W^2)) + (((-6)*X*Y^2)/(W^2)) + ((2*X^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + (((-1)*Y^3*a)/(X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-1))/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + (((-5))/(2*W^2)) + ((1*b)/(W)) + (1) + ((1*Z)/(W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y^2)/(W^2)) + ((1*Y^3*a)/(2*W^2)) + ((1*Y^4)/(2*W^2)) + ((9*X)/(2*W^2)) + (((-1)*X)/(2)) + (((-3)*X*Z)/(2*W^2)) + ((2*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + ((1*X*Y*Z*a)/(2*W^2)) + (((-4)*X*Y^2)/(W^2)) + ((3*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^2)/(2)) + ((1*X*Y^2*Z)/(2*W^2)) + ((2*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((23*X^2)/(2*W^2)) + (((-3)*X^2)/(2)) + (((-3)*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + ((5*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((5*X^2*Y^3*a)/(W^2)) + ((2*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((13*X^3)/(W^2)) + (((-1)*X^3)/(2)) + (((-5)*X^3*Z)/(2*W^2)) + ((2*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + ((2*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((7*X^3*Y^3*a)/(2*W^2)) + ((3*X^3*Y^4)/(2*W^2)) + ((4*X^4)/(W^2)) + (((-1)*X^4*Z)/(W^2)) + ((3*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*Z*a)/(W^2)) + ((3*X^4*Y^2)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^2*Z)/(W^2)) + ((2*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(W^2)))*v 2

def row24 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^2*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 0 + ((((-2))/(X^2*W^2)) + (((-1)*b)/(X^2*W)) + (((-3))/(X^2)) + (((-4)*Y^2)/(X^2*W^2)) + (((-10))/(X*W^2)) + ((3*b)/(X*W)) + ((4)/(X)) + ((2*Z)/(X*W^2)) + ((4*Y*a)/(X*W^2)) + (((-4)*Y^2)/(X*W^2)) + (((-2)*Y^4)/(X*W^2)) + (((-2))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-2)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 1 + (((1)/(2*X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-11)*Y^2)/(2*X*W^2)) + ((1*Y^2*a^2)/(2*X*W^2)) + ((3*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(X*W^2)) + ((11)/(2*W^2)) + ((3*b)/(W)) + ((1*Z)/(W^2)) + ((5*Y*a)/(2*W^2)) + ((-1)*Y*a) + ((1*Y*Z*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + ((3*Y^2*a^2)/(W^2)) + ((-1)*Y^2) + ((1*Y^2*Z)/(W^2)) + ((5*Y^3*a)/(2*W^2)) + (((-5)*Y^4)/(2*W^2)) + ((14*X)/(W^2)) + (((-7)*X)/(2)) + (((-3)*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a)/(2)) + ((6*X*Y^2)/(W^2)) + (((-1)*X*Y^2)/(2)) + ((3*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(W^2)) + ((1*X*Y^4*a^2)/(W^2)) + ((1*X*Y^5*a)/(W^2)) + ((11*X^2)/(2*W^2)) + (((-5)*X^2)/(2)) + (((-1)*X^2*Z)/(W^2)) + ((5*X^2*Y*a)/(2*W^2)) + (((-3)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(W^2)) + ((7*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + (((-3)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(W^2)) + ((3*X^2*Y^3*a)/(W^2)) + ((3*X^2*Y^4)/(2*W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((5*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^4)/(2*W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 2
def row25 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X*W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 0 + ((((-2))/(X*W^2)) + (((-1)*b)/(X*W)) + (((-3))/(X)) + (((-4)*Y^2)/(X*W^2)) + (((-10))/(W^2)) + ((3*b)/(W)) + (4) + ((2*Z)/(W^2)) + ((4*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-2)*Y^4)/(W^2)) + (((-2)*X)/(W^2)) + (1*X) + ((3*X*Y*a)/(W^2)) + (((-4)*X*Y^2)/(W^2)) + (((-1)*X*Y^4)/(W^2)) + (((-2)*X^2)/(W^2)) + ((1*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + ((1*X^3)/(W^2)) + (((-1)*X^3*Y^2)/(W^2)))*v 1 + (((1)/(2*W^2)) + ((1*Y*a)/(W^2)) + (((-11)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((3*Y^3*a)/(2*W^2)) + ((1*Y^4)/(W^2)) + ((11*X)/(2*W^2)) + ((3*X*b)/(W)) + ((1*X*Z)/(W^2)) + ((5*X*Y*a)/(2*W^2)) + ((-1)*X*Y*a) + ((1*X*Y*Z*a)/(W^2)) + (((-4)*X*Y^2)/(W^2)) + ((3*X*Y^2*a^2)/(W^2)) + ((-1)*X*Y^2) + ((1*X*Y^2*Z)/(W^2)) + ((5*X*Y^3*a)/(2*W^2)) + (((-5)*X*Y^4)/(2*W^2)) + ((14*X^2)/(W^2)) + (((-7)*X^2)/(2)) + (((-3)*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + ((6*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(2)) + ((3*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(W^2)) + ((1*X^2*Y^5*a)/(W^2)) + ((11*X^3)/(2*W^2)) + (((-5)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + ((5*X^3*Y*a)/(2*W^2)) + (((-3)*X^3*Y*a)/(2)) + (((-1)*X^3*Y*Z*a)/(W^2)) + ((7*X^3*Y^2)/(W^2)) + ((1*X^3*Y^2*a^2)/(W^2)) + (((-3)*X^3*Y^2)/(2)) + (((-1)*X^3*Y^2*Z)/(W^2)) + ((3*X^3*Y^3*a)/(W^2)) + ((3*X^3*Y^4)/(2*W^2)) + ((1*X^3*Y^4*a^2)/(2*W^2)) + ((1*X^3*Y^5*a)/(2*W^2)) + ((5*X^4)/(2*W^2)) + (((-1)*X^4)/(2)) + (((-1)*X^4*Z)/(W^2)) + (((-1)*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*a)/(2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2)/(2)) + ((1*X^4*Y^4)/(2*W^2)) + ((2*X^5)/(W^2)) + (((-1)*X^5*Z)/(2*W^2)) + ((3*X^5*Y*a)/(2*W^2)) + (((-1)*X^5*Y*Z*a)/(2*W^2)) + ((3*X^5*Y^2)/(2*W^2)) + ((1*X^5*Y^2*a^2)/(2*W^2)) + (((-1)*X^5*Y^2*Z)/(2*W^2)) + ((1*X^5*Y^3*a)/(W^2)) + ((1*X^5*Y^4)/(2*W^2)))*v 2
def row26 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 0 + (((2)/(X^2)) + ((1)/(X*W^2)) + (((-1)*b)/(X*W)) + (((-2))/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-4))/(W^2)) + ((1*b)/(W)) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)) + (((-6)*X)/(W^2)) + (1*X) + ((1*X*Z)/(W^2)) + ((4*X*Y*a)/(W^2)) + (((-7)*X*Y^2)/(W^2)) + (((-1)*X*Y^4)/(W^2)) + (((-5)*X^2)/(W^2)) + ((2*X^2*Z)/(W^2)) + ((2*X^2*Y*a)/(W^2)) + (((-6)*X^2*Y^2)/(W^2)) + ((2*X^3)/(W^2)) + (((-2)*X^3*Y^2)/(W^2)))*v 1 + ((((-1))/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + (((-1)*Y^3*a)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + ((2*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + (((-1)*Y^3*a)/(2*W^2)) + ((1*Y^4)/(2*W^2)) + (((-5)*X)/(2*W^2)) + ((1*X*b)/(W)) + (1*X) + ((1*X*Z)/(W^2)) + ((3*X*Y*a)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + ((9*X^2)/(2*W^2)) + (((-1)*X^2)/(2)) + (((-3)*X^2*Z)/(2*W^2)) + ((2*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-4)*X^2*Y^2)/(W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + ((2*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + ((23*X^3)/(2*W^2)) + (((-3)*X^3)/(2)) + (((-3)*X^3*Z)/(2*W^2)) + ((1*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)) + ((5*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((5*X^3*Y^3*a)/(W^2)) + ((2*X^3*Y^4)/(W^2)) + ((1*X^3*Y^4*a^2)/(2*W^2)) + ((1*X^3*Y^5*a)/(2*W^2)) + ((13*X^4)/(W^2)) + (((-1)*X^4)/(2)) + (((-5)*X^4*Z)/(2*W^2)) + ((2*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*a)/(2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + ((2*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^2)/(2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((7*X^4*Y^3*a)/(2*W^2)) + ((3*X^4*Y^4)/(2*W^2)) + ((4*X^5)/(W^2)) + (((-1)*X^5*Z)/(W^2)) + ((3*X^5*Y*a)/(W^2)) + (((-1)*X^5*Y*Z*a)/(W^2)) + ((3*X^5*Y^2)/(W^2)) + ((1*X^5*Y^2*a^2)/(W^2)) + (((-1)*X^5*Y^2*Z)/(W^2)) + ((2*X^5*Y^3*a)/(W^2)) + ((1*X^5*Y^4)/(W^2)))*v 2
def row27 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-2)*Y^2)/(X^3*W^2)) + (((-1)*Y^2)/(X^2*W^2)) + ((2*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 0 + (((5)/(X^3*W^2)) + ((1)/(X^3)) + (((-1)*Z)/(X^3*W^2)) + (((-1)*Y*a)/(X^3*W^2)) + ((2*Y^2)/(X^3*W^2)) + (((-1))/(X^2*W^2)) + (((-1)*b)/(X^2*W)) + (((-3))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + ((1*Y^2)/(X^2*W^2)) + (((-6))/(X*W^2)) + ((2*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-2))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-6)*X)/(W^2)) + ((2*X*Z)/(W^2)) + ((2*X*Y*a)/(W^2)) + (((-3)*X*Y^2)/(W^2)) + ((2*X^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 1 + ((((-2))/(X^2*W^2)) + (((-3)*Y*a)/(2*X^2*W^2)) + ((1*Y^2)/(X^2*W^2)) + (((-1)*Y^2*a^2)/(2*X^2*W^2)) + (((-3)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-7))/(X*W^2)) + ((1*Z)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + (((-1)*Y^3*a)/(X*W^2)) + (((-3))/(W^2)) + ((2*b)/(W)) + ((1)/(2)) + ((2*Z)/(W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + ((1*Y^2*a^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(W^2)) + (((-1)*Y^3*a)/(2*W^2)) + (((-2)*Y^4)/(W^2)) + ((6*X)/(W^2)) + ((-2)*X) + (((-3)*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + ((1*X*Y*Z*a)/(2*W^2)) + ((3*X*Y^2)/(2*W^2)) + ((1*X*Y^2*Z)/(2*W^2)) + ((1*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((5*X^2)/(W^2)) + ((-2)*X^2) + (((-1)*X^2*Z)/(2*W^2)) + ((3*X^2*Y*a)/(2*W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((5*X^2*Y^2)/(2*W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((7*X^2*Y^3*a)/(2*W^2)) + ((3*X^2*Y^4)/(2*W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((9*X^3)/(W^2)) + (((-1)*X^3)/(2)) + (((-2)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((3*X^3*Y^3*a)/(2*W^2)) + ((1*X^3*Y^4)/(W^2)) + ((4*X^4)/(W^2)) + (((-1)*X^4*Z)/(W^2)) + ((3*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*Z*a)/(W^2)) + ((3*X^4*Y^2)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^2*Z)/(W^2)) + ((2*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(W^2)))*v 2
def row28 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((2*Y^2)/(X^2*W^2)) + (((-3)*Y^2)/(X*W^2)) + (((-3)*Y^2)/(W^2)) + (((-2)*X*Y^2)/(W^2)) + (((-4)*X^2*Y^2)/(W^2)))*v 0 + ((((-5))/(X^2*W^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-2)*Y^2)/(X^2*W^2)) + ((8)/(X*W^2)) + ((1)/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((1*Y^2)/(X*W^2)) + ((3)/(W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((3*Y^2)/(W^2)) + ((2*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((3*X*Y^2)/(W^2)) + ((7*X^2)/(W^2)) + (((-2)*X^2*Z)/(W^2)) + (((-2)*X^2*Y*a)/(W^2)) + ((4*X^2*Y^2)/(W^2)) + (((-2)*X^3)/(W^2)) + ((2*X^3*Y^2)/(W^2)))*v 1 + (((3)/(2*X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(2*X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((9)/(2*W^2)) + (((-1)*Z)/(W^2)) + (((-3)*Y*a)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-15)*X)/(2*W^2)) + ((1*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((3*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-21)*X^2)/(2*W^2)) + ((3*X^2*Z)/(2*W^2)) + (((-4)*X^2*Y*a)/(W^2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-2)*X^2*Y^2)/(W^2)) + (((-3)*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-3)*X^2*Y^3*a)/(W^2)) + (((-3)*X^2*Y^4)/(2*W^2)) + (((-9)*X^3)/(W^2)) + ((3*X^3*Z)/(2*W^2)) + (((-3)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-2)*X^3*Y^2*a^2)/(W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-4)*X^3*Y^3*a)/(W^2)) + (((-2)*X^3*Y^4)/(W^2)) + (((-12)*X^4)/(W^2)) + ((5*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-3)*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-5)*X^4*Y^3*a)/(2*W^2)) + (((-3)*X^4*Y^4)/(2*W^2)) + (((-4)*X^5)/(W^2)) + ((1*X^5*Z)/(W^2)) + (((-3)*X^5*Y*a)/(W^2)) + ((1*X^5*Y*Z*a)/(W^2)) + (((-3)*X^5*Y^2)/(W^2)) + (((-1)*X^5*Y^2*a^2)/(W^2)) + ((1*X^5*Y^2*Z)/(W^2)) + (((-2)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(W^2)))*v 2
def row29 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*W^2)) + (((-1))/(W^2)))*v 1 + ((((-1)*X)/(W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + ((1*X^3)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)))*v 2
def row30 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*Y^2*W^2)) + (((-1))/(Y^2*W^2)))*v 1 + ((((-1)*X)/(Y^2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(2*W^2)) + ((1*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3)/(2*W^2)))*v 2
def row31 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X)) + (1))*v 1 + ((1*X) + (((-1)*X^2)/(2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y^2)/(2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)))*v 2

def row32 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 0 + (((4)/(X*W^2)) + (((-1))/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + ((1)/(W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((3*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(W^2)) + (((-1)*Y*a)/(2*W^2)) + ((3*Y^2)/(2*W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + (((-1)*Y^3*a)/(W^2)) + (((-1)*Y^4)/(2*W^2)) + (((-7)*X)/(W^2)) + ((1*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(W^2)) + (((-2)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(W^2)) + (((-11)*X^2)/(2*W^2)) + ((3*X^2*Z)/(2*W^2)) + (((-3)*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-3)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-2)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(W^2)) + (((-5)*X^3)/(2*W^2)) + ((1*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + (((-1)*X^4)/(W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 2
def row33 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X*Y^2)) + ((1)/(Y^2)))*v 1 + (((1*X)/(Y^2)) + (((-1)*X^2)/(2*Y^2)) + ((1*X^2*a)/(2*Y)) + ((1*X^2)/(2)) + (((-1)*X^3)/(2*Y^2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3)/(2)))*v 2
def row34 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1)*Z)/(X*Y^2)) + ((1*Z)/(Y^2)))*v 1 + (((1*X*Z)/(Y^2)) + (((-1)*X^2*Z)/(2*Y^2)) + ((1*X^2*Z*a)/(2*Y)) + ((1*X^2*Z)/(2)) + (((-1)*X^3*Z)/(2*Y^2)) + (((-1)*X^3*Z*a)/(2*Y)) + (((-1)*X^3*Z)/(2)))*v 2
def row35 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X*Y^2*W^2)) + ((1)/(Y^2*W^2)))*v 1 + (((1*X)/(Y^2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + ((1*X^2*a)/(2*Y*W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(2*Y*W^2)) + (((-1)*X^3)/(2*W^2)))*v 2
def row36 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X)) + ((-1)))*v 1 + (((-1)*X) + ((1*X^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2)))*v 2
def row37 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)))*v 0 + ((((-4))/(X*W^2)) + ((1)/(X)) + ((1*Z)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1))/(W^2)) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 1 + (((1)/(W^2)) + ((1*Y*a)/(2*W^2)) + (((-3)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(W^2)) + ((1*Y^4)/(2*W^2)) + ((7*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(W^2)) + ((2*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(W^2)) + ((11*X^2)/(2*W^2)) + (((-3)*X^2*Z)/(2*W^2)) + ((3*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((3*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((2*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4)/(W^2)) + ((5*X^3)/(2*W^2)) + (((-1)*X^3*Z)/(2*W^2)) + ((1*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((1*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 2
def row38 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1*Z)/(X*Y^2)) + (((-1)*Z)/(Y^2)))*v 1 + ((((-1)*X*Z)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + (((-1)*X^2*Z*a)/(2*Y)) + (((-1)*X^2*Z)/(2)) + ((1*X^3*Z)/(2*Y^2)) + ((1*X^3*Z*a)/(2*Y)) + ((1*X^3*Z)/(2)))*v 2
def row39 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*Y^2)) + (((-1))/(Y^2)))*v 1 + ((((-1)*X)/(Y^2)) + ((1*X^2)/(2*Y^2)) + (((-1)*X^2*a)/(2*Y)) + (((-1)*X^2)/(2)) + ((1*X^3)/(2*Y^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3)/(2)))*v 2

def row40 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^2*W^2)) + (((-1)*Y^2)/(X*W^2)))*v 0 + (((1)/(X^2)) + ((2)/(X*W^2)) + (((-1))/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + (((-1)*Y^2)/(2*X*W^2)) + (((-2)*X)/(W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-3)*X^2*Y^2)/(2*W^2)) + ((1*X^3)/(W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^3*a)/(2*W^2)))*v 2
def row41 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2*W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 0 + (((1)/(X^3)) + (((-3))/(X^2*W^2)) + (((-1)*b)/(X^2*W)) + (((-3))/(X^2)) + (((-2)*Y^2)/(X^2*W^2)) + (((-4))/(X*W^2)) + ((2*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-3))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-2)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((5*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + ((1)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + ((4)/(W^2)) + ((2*b)/(W)) + ((1)/(2)) + ((1*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((3*Y^2*a^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((3*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(W^2)) + ((13*X)/(2*W^2)) + ((-2)*X) + (((-2)*X*Z)/(W^2)) + ((2*X*Y*a)/(W^2)) + ((5*X*Y^2)/(2*W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + ((2*X*Y^3*a)/(W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((4*X^2)/(W^2)) + ((-2)*X^2) + (((-1)*X^2*Z)/(2*W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((3*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((5*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-7)*X^4)/(2*W^2)) + ((1*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + (((-2)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-3)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-3)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 2
def row42 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X*W^2)) + ((1)/(W^2)))*v 1 + (((1*X)/(W^2)) + (((-1)*X^2)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y^2)/(2*W^2)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)))*v 2
def row43 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1)*a)/(Y*W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X^2)/(Y^2*W^2)) + ((1*X^2)/(W^2)))*v 1 + (((1*X^2)/(Y^2*W^2)) + ((1*X^2*a)/(Y*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3)/(W^2)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + (((-1)*X^4)/(Y^2*W^2)) + (((-1)*X^4*a)/(2*Y*W^2)) + (((-1)*X^4*a^2)/(2*W^2)) + (((-1)*X^4*Y*a)/(2*W^2)))*v 2
def row44 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1*a)/(X*Y)) + (((-1))/(Y^2)) + (((-1)*X)/(Y^2)) + ((-1)*X))*v 1 + ((((-1)*X)/(Y^2)) + (((-1)*X*a)/(Y)) + (((-1)*X^2*a)/(2*Y)) + ((-1)*X^2) + (((-1)*X^2*a^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + ((1*X^3)/(Y^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3*a^2)/(2)) + ((1*X^3*Y*a)/(2)))*v 2
def row45 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*Y^2)) + (((-1)*a)/(X*Y)) + ((1)/(Y^2)) + (1))*v 1 + (((1)/(Y^2)) + ((1*X*a)/(Y)) + (1*X) + (((-1)*X^2)/(Y^2)))*v 2
def row46 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1))/(X^2*W^2)) + (((-1))/(X*W^2)))*v 0 + (((1)/(X^2*Y^2)) + ((2)/(X*Y^2*W^2)) + ((1*a)/(X*Y)) + (((-1))/(Y^2*W^2)) + (((-1)*a)/(Y)) + (((-1)*X)/(W^2)))*v 1 + ((((-1))/(2*X*Y^2*W^2)) + (((-1)*a)/(2*X*Y*W^2)) + (((-1))/(2*X*W^2)) + (((-2)*X)/(Y^2*W^2)) + (((-1)*X*a)/(Y)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + ((1*X^2*a)/(2*Y)) + (((-3)*X^2)/(2*W^2)) + (((-1)*X^2*a^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*a^2)/(2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a)/(2)))*v 2
def row47 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y*a)/(X^2*W^2)) + (((-1))/(W^2)) + (((-1)*X)/(W^2)) + ((1*X^2*Y*a)/(W^2)))*v 0 + ((((-1)*a)/(X^3*Y)) + ((1)/(X^2*Y^2*W^2)) + ((2*a)/(X^2*Y*W^2)) + ((1*a*b)/(X^2*Y*W)) + ((3*a)/(X^2*Y)) + ((2*Y*a)/(X^2*W^2)) + ((1)/(X*Y^2*W^2)) + ((4*a)/(X*Y*W^2)) + (((-2)*a*b)/(X*Y*W)) + (((-2)*a)/(X*Y)) + (((-1)*Z*a)/(X*Y*W^2)) + ((1)/(X*W^2)) + (((-2)*a^2)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((4)/(Y^2*W^2)) + (((-1))/(Y^2)) + (((-1)*Z)/(Y^2*W^2)) + ((2*a)/(Y*W^2)) + (((-1)*a)/(Y)) + ((2)/(W^2)) + (((-3)*a^2)/(W^2)) + ((4*Y*a)/(W^2)) + ((1*Y^3*a)/(W^2)) + ((1*X)/(Y^2*W^2)) + (((-1)*X*Z)/(Y^2*W^2)) + ((1*X*a)/(Y*W^2)) + (((-1)*X*Z*a)/(Y*W^2)) + ((3*X)/(W^2)) + (((-1)*X*a^2)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-5)*X^2*a)/(Y*W^2)) + ((1*X^2*Z*a)/(Y*W^2)) + ((1*X^2)/(W^2)) + ((1*X^2*a^2)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^3*a)/(Y*W^2)) + ((1*X^3)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)))*v 1 + (((1*a)/(2*X^2*Y*W^2)) + ((1*a^2)/(2*X^2*W^2)) + ((1*Y^2*a^2)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1)/(X*Y^2*W^2)) + (((-1)*a)/(X*Y*W^2)) + (((-1)*a^2)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + (((-1)*Y^3*a)/(X*W^2)) + (((-3)*a)/(Y*W^2)) + (((-2)*a*b)/(Y*W)) + (((-1)*a)/(2*Y)) + (((-1)*Z*a)/(2*Y*W^2)) + ((1)/(W^2)) + (((-3)*a^2)/(2*W^2)) + ((1*a^2)/(2)) + (((-1)*Z*a^2)/(2*W^2)) + ((2*Y*a)/(W^2)) + (((-3)*Y*a^3)/(2*W^2)) + ((1*Y*a)/(2)) + (((-1)*Y*Z*a)/(2*W^2)) + (((-3)*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(W^2)) + (((-2)*X)/(Y^2*W^2)) + (((-7)*X*a)/(Y*W^2)) + ((2*X*a)/(Y)) + ((2*X*Z*a)/(Y*W^2)) + ((3*X)/(2*W^2)) + (((-5)*X*a^2)/(2*W^2)) + (((-7)*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y^2)/(2*W^2)) + (((-2)*X*Y^2*a^2)/(W^2)) + (((-1)*X*Y^3*a^3)/(2*W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-7)*X^2)/(Y^2*W^2)) + ((1*X^2*Z)/(Y^2*W^2)) + (((-5)*X^2*a)/(Y*W^2)) + ((2*X^2*a)/(Y)) + ((1*X^2*Z*a)/(2*Y*W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*a^2)/(W^2)) + (1*X^2*a^2) + ((1*X^2*Z*a^2)/(2*W^2)) + (((-5)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a^3)/(W^2)) + (1*X^2*Y*a) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-5)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^3*a^3)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-11)*X^3)/(2*Y^2*W^2)) + ((3*X^3*Z)/(2*Y^2*W^2)) + (((-4)*X^3*a)/(Y*W^2)) + ((1*X^3*a)/(2*Y)) + ((3*X^3*Z*a)/(2*Y*W^2)) + (((-3)*X^3)/(2*W^2)) + ((1*X^3*a^2)/(2)) + ((1*X^3*Z)/(2*W^2)) + (((-7)*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a^3)/(2*W^2)) + ((1*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-5)*X^4)/(2*Y^2*W^2)) + ((1*X^4*Z)/(2*Y^2*W^2)) + ((5*X^4*a)/(2*Y*W^2)) + (((-2)*X^4*a^2)/(W^2)) + ((1*X^4*Z)/(2*W^2)) + ((1*X^4*Z*a^2)/(2*W^2)) + (((-5)*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2)/(2*W^2)) + (((-1)*X^5)/(Y^2*W^2)) + ((3*X^5*a)/(2*Y*W^2)) + (((-1)*X^5*Z*a)/(2*Y*W^2)) + ((1*X^5*a^2)/(W^2)) + (((-1)*X^5*Z*a^2)/(2*W^2)) + ((1*X^5*Y*a)/(W^2)) + ((1*X^5*Y*a^3)/(2*W^2)) + (((-1)*X^5*Y*Z*a)/(2*W^2)) + ((1*X^5*Y^2*a^2)/(W^2)) + ((1*X^5*Y^3*a)/(2*W^2)))*v 2

def row48 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(Y^2)) + ((1*a)/(Y)) + (((-1)*X)/(Y^2)) + ((-1)*X))*v 1 + ((((-1)*X)/(Y^2)) + (((-1)*X^2*a)/(Y)) + ((-1)*X^2) + ((1*X^3)/(Y^2)))*v 2
def row49 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1))/(X*W^2)) + (((-1))/(W^2)))*v 0 + (((1)/(X*Y^2)) + ((2)/(Y^2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X^2)/(W^2)))*v 1 + ((((-1))/(2*Y^2*W^2)) + (((-1)*a)/(2*Y*W^2)) + (((-1))/(2*W^2)) + (((-2)*X^2)/(Y^2*W^2)) + ((1*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(2*Y*W^2)) + (((-3)*X^3)/(2*W^2)) + ((1*X^4)/(Y^2*W^2)) + ((1*X^4*a)/(2*Y*W^2)) + ((1*X^4*a^2)/(2*W^2)) + ((1*X^4*Y*a)/(2*W^2)))*v 2
def row50 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(Y^2*W^2)) + (((-1)*a)/(Y*W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X)/(W^2)))*v 1 + (((1*X)/(Y^2*W^2)) + ((1*X^2*a)/(Y*W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^3)/(Y^2*W^2)))*v 2
def row51 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(Y^2*W^2)) + ((1*a)/(Y*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X)/(W^2)))*v 1 + ((((-1)*X)/(Y^2*W^2)) + (((-1)*X^2*a)/(Y*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^3)/(Y^2*W^2)))*v 2
def row52 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1))/(X*W^2)) + (((-1))/(W^2)))*v 0 + (((4)/(X*Y^2*W^2)) + (((-1))/(X*Y^2)) + (((-1)*Z)/(X*Y^2*W^2)) + (((-1)*a)/(X*Y*W^2)) + ((2)/(X*W^2)) + ((1)/(Y^2*W^2)) + (((-1)*Z)/(Y^2*W^2)) + ((3)/(W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X)/(W^2)) + (((-1)*X^2)/(Y^2*W^2)))*v 1 + ((((-1))/(Y^2*W^2)) + (((-1)*a)/(2*Y*W^2)) + ((3)/(2*W^2)) + (((-1)*a^2)/(2*W^2)) + (((-1)*Y*a)/(W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-7)*X)/(Y^2*W^2)) + ((1*X*Z)/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + ((1*X)/(W^2)) + (((-1)*X*a^2)/(W^2)) + (((-2)*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-13)*X^2)/(2*Y^2*W^2)) + ((3*X^2*Z)/(2*Y^2*W^2)) + (((-5)*X^2*a)/(2*Y*W^2)) + ((1*X^2*Z*a)/(2*Y*W^2)) + (((-3)*X^2)/(2*W^2)) + (((-1)*X^2*a^2)/(W^2)) + ((1*X^2*Z)/(2*W^2)) + (((-2)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-5)*X^3)/(2*Y^2*W^2)) + ((1*X^3*Z)/(2*Y^2*W^2)) + (((-3)*X^3*a)/(2*Y*W^2)) + ((1*X^3*Z*a)/(2*Y*W^2)) + (((-1)*X^3)/(W^2)) + (((-1)*X^3*a^2)/(W^2)) + ((1*X^3*Z)/(2*W^2)) + (((-3)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)))*v 2
def row53 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)))*v 0 + (((1)/(X*Y^2*W^2)) + (((-1))/(X)) + (((-1))/(Y^2*W^2)) + (((-2))/(W^2)) + ((1*X)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 1 + (((1)/(2*W^2)) + ((1*Y*a)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + ((3*X^2)/(2*W^2)) + ((1*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^4)/(W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 2
def row54 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(Y^2)) + (((-1)*a)/(Y)) + ((1*X)/(Y^2)) + (1*X))*v 1 + (((1*X)/(Y^2)) + ((1*X^2*a)/(Y)) + (1*X^2) + (((-1)*X^3)/(Y^2)))*v 2
def row55 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 0 + (((4)/(W^2)) + ((-1)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((2*Y^2)/(W^2)) + ((1*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((3*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 1 + ((((-1)*X)/(W^2)) + (((-1)*X*Y*a)/(2*W^2)) + ((3*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-7)*X^2)/(W^2)) + ((1*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + (((-2)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(W^2)) + (((-11)*X^3)/(2*W^2)) + ((3*X^3*Z)/(2*W^2)) + (((-3)*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-3)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-2)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(W^2)) + (((-5)*X^4)/(2*W^2)) + ((1*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(W^2)) + (((-1)*X^4*Y^4)/(2*W^2)) + (((-1)*X^5)/(W^2)) + (((-1)*X^5*Y*a)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(2*W^2)))*v 2

def row56 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1)*a)/(X*Y)) + ((1*a)/(Y)))*v 1 + (((1*X*a)/(Y)) + (((-1)*X^2*a)/(2*Y)) + ((1*X^2*a^2)/(2)) + ((1*X^2*Y*a)/(2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3*a^2)/(2)) + (((-1)*X^3*Y*a)/(2)))*v 2
def row57 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X*Y^2*W^2)) + ((1*a)/(X*Y*W^2)) + (((-1))/(Y^2*W^2)) + (((-1))/(W^2)))*v 1 + ((((-1))/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + (((-1)*X)/(W^2)) + ((1*X^2)/(Y^2*W^2)))*v 2
def row58 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*Y^2*W^2)) + (((-1)*a)/(X*Y*W^2)) + ((1)/(Y^2*W^2)) + ((1)/(W^2)))*v 1 + (((1)/(Y^2*W^2)) + ((1*X*a)/(Y*W^2)) + ((1*X)/(W^2)) + (((-1)*X^2)/(Y^2*W^2)))*v 2
def row59 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X*Y^2)) + ((1*a)/(X*Y)) + (((-1))/(Y^2)) + ((-1)))*v 1 + ((((-1))/(Y^2)) + (((-1)*X*a)/(Y)) + ((-1)*X) + ((1*X^2)/(Y^2)))*v 2
def row60 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(Y^2)) + (((-1)*X)/(Y^2)))*v 1 + ((((-1)*X^2)/(Y^2)) + ((1*X^3)/(2*Y^2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3)/(2)) + ((1*X^4)/(2*Y^2)) + ((1*X^4*a)/(2*Y)) + ((1*X^4)/(2)))*v 2
def row61 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 0 + ((((-1))/(Y^2*W^2)) + (((-4))/(W^2)) + (1) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-2)*Y^2)/(W^2)) + ((1*X)/(Y^2*W^2)) + (((-1)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-3)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-1)*X^3*Y^2)/(W^2)))*v 1 + (((1*X)/(W^2)) + ((1*X*Y*a)/(2*W^2)) + (((-3)*X*Y^2)/(2*W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(2*W^2)) + ((1*X^2)/(Y^2*W^2)) + ((7*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((2*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4)/(W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((6*X^3)/(W^2)) + (((-3)*X^3*Z)/(2*W^2)) + ((3*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((2*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(W^2)) + (((-1)*X^4)/(2*Y^2*W^2)) + (((-1)*X^4*a)/(2*Y*W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)) + ((1*X^5)/(W^2)) + ((1*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^3*a)/(2*W^2)))*v 2
def row62 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1)/(W^2)) + ((1*X)/(W^2)))*v 0 + ((((-4))/(Y^2*W^2)) + ((1)/(Y^2)) + ((1*Z)/(Y^2*W^2)) + ((1*a)/(Y*W^2)) + (((-2))/(W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X*Z)/(Y^2*W^2)) + ((1*X*a)/(Y*W^2)) + (((-3)*X)/(W^2)) + (((-1)*X^2)/(W^2)) + (((-1)*X^3)/(W^2)))*v 1 + (((1*X)/(Y^2*W^2)) + ((1*X*a)/(2*Y*W^2)) + (((-3)*X)/(2*W^2)) + ((1*X*a^2)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + ((1*X*Y^2)/(2*W^2)) + ((7*X^2)/(Y^2*W^2)) + (((-1)*X^2*Z)/(Y^2*W^2)) + ((1*X^2*a)/(Y*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*a^2)/(W^2)) + ((2*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + ((11*X^3)/(2*Y^2*W^2)) + (((-3)*X^3*Z)/(2*Y^2*W^2)) + ((3*X^3*a)/(2*Y*W^2)) + (((-1)*X^3*Z*a)/(2*Y*W^2)) + ((3*X^3)/(2*W^2)) + ((1*X^3*a^2)/(W^2)) + (((-1)*X^3*Z)/(2*W^2)) + ((2*X^3*Y*a)/(W^2)) + ((1*X^3*Y^2)/(W^2)) + ((5*X^4)/(2*Y^2*W^2)) + (((-1)*X^4*Z)/(2*Y^2*W^2)) + ((1*X^4*a)/(Y*W^2)) + (((-1)*X^4*Z*a)/(2*Y*W^2)) + ((1*X^4*a^2)/(2*W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(W^2)) + ((1*X^4*Y^2)/(2*W^2)) + ((1*X^5)/(Y^2*W^2)) + ((1*X^5*a)/(2*Y*W^2)) + ((1*X^5*a^2)/(2*W^2)) + ((1*X^5*Y*a)/(2*W^2)))*v 2
def row63 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-2))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + (((-1)*a)/(X*Y)) + ((3)/(Y^2)) + (((-1)*Z)/(Y^2)) + ((1*X)/(Y^2)) + (1*X))*v 1 + (((3*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + ((1*X*a)/(Y)) + (((-1)*X^2)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + ((3*X^2*a)/(2*Y)) + (((-1)*X^2*Z*a)/(2*Y)) + (2*X^2) + ((1*X^2*a^2)/(2)) + (((-1)*X^2*Z)/(2)) + ((1*X^2*Y*a)/(2)) + (((-2)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-3)*X^3*a)/(2*Y)) + ((1*X^3*Z*a)/(2*Y)) + ((-1)*X^3) + (((-1)*X^3*a^2)/(2)) + ((1*X^3*Z)/(2)) + (((-1)*X^3*Y*a)/(2)))*v 2

def row64 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1*a)/(X*Y*W^2)) + (((-1))/(Y^2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X)/(W^2)))*v 1 + ((((-1)*X)/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(W^2)) + (((-1)*X^2*a^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)))*v 2
def row65 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*W^2)) + ((1*b)/(X*W)) + ((1)/(X)))*v 1 + (((1)/(2*W^2)) + ((1*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + ((1*Y^4)/(2*W^2)) + (((-1)*X)/(W^2)) + (((-1)*X*b)/(W)) + ((-1)*X) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*b)/(2*W)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a*b)/(2*W)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*b)/(2*W)) + (((-1)*X^2*Y^2)/(2)))*v 2
def row66 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^2*W^2)) + ((1*X^2*Y^2)/(W^2)))*v 0 + (((1)/(X^3)) + ((3)/(X^2*W^2)) + (((-2))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + (((-7))/(X*W^2)) + ((1*b)/(X*W)) + ((1)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-3))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-2)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-4))/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + ((3*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-3)*Y^2)/(W^2)) + ((3*Y^2*a^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + (((-2)*Y^4)/(W^2)) + ((11*X)/(2*W^2)) + ((1*X*b)/(2*W)) + (((-3)*X)/(2)) + (((-3)*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a*b)/(2*W)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y*Z*a)/(2*W^2)) + (((-1)*X*Y^2*b)/(2*W)) + (((-1)*X*Y^2)/(2)) + ((1*X*Y^2*Z)/(2*W^2)) + ((1*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((5*X^2)/(W^2)) + ((1*X^2*b)/(2*W)) + (((-3)*X^2)/(2)) + (((-1)*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a*b)/(2*W)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((4*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((1*X^2*Y^2*b)/(2*W)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((4*X^3)/(W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^3*a)/(2*W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 2
def row67 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (0)*v 1 + ((((-1)*Z)/(2*Y^2*W^2)) + (((-1)*Z)/(W^2)) + ((1*Z*a^2)/(2*W^2)) + (((-1)*Y^2*Z)/(2*W^2)) + ((1*X*Z)/(2*Y^2*W^2)) + ((1*X*Z)/(W^2)) + (((-1)*X*Z*a^2)/(2*W^2)) + ((1*X*Y^2*Z)/(2*W^2)))*v 2
def row68 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (0)*v 1 + ((((-1)*X)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((1*X^2)/(2*W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)))*v 2
def row69 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)))*v 0 + ((((-1)*a)/(X*Y)) + (((-1))/(X)) + (((-1))/(Y^2*W^2)) + (((-1)*b)/(Y^2*W)) + (((-2))/(W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X*b)/(W)) + ((1*X^2*Y^2)/(W^2)))*v 1 + ((((-1)*a)/(2*Y*W^2)) + ((1)/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + ((1*Y*a^3)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + ((1*X*a)/(Y)) + ((1*X^2*a)/(2*Y)) + ((1*X^2)/(W^2)) + (((-1)*X^2*b)/(W)) + ((1*X^2*a^2)/(2)) + ((1*X^2*Y*a)/(2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3*b)/(Y^2*W)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a*b)/(2*Y*W)) + (((-1)*X^3)/(2*W^2)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*a^2*b)/(2*W)) + ((1*X^3*Y*a)/(W^2)) + ((1*X^3*Y*a*b)/(2*W)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^4)/(W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 2
def row70 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^3*W^2)) + ((1*X*Y^2)/(W^2)))*v 0 + (((1)/(X^4)) + ((3)/(X^3*W^2)) + (((-2))/(X^3)) + (((-1)*Z)/(X^3*W^2)) + (((-1)*Y*a)/(X^3*W^2)) + (((-7))/(X^2*W^2)) + ((1*b)/(X^2*W)) + ((1)/(X^2)) + ((1*Z)/(X^2*W^2)) + ((2*Y*a)/(X^2*W^2)) + (((-1)*Y^2)/(X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-3))/(X*W^2)) + ((1)/(X)) + ((3*Y*a)/(X*W^2)) + (((-4)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-2))/(W^2)) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y^2)/(W^2)) + ((1*X)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X^3*W^2)) + (((-1)*Y*a)/(2*X^3*W^2)) + (((-1)*Y^3*a)/(2*X^3*W^2)) + (((-1)*Y^4)/(2*X^3*W^2)) + (((-1)*Y^2*a^2)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + (((-4))/(X*W^2)) + ((1*b)/(X*W)) + (((-1))/(2*X)) + ((3*Z)/(2*X*W^2)) + ((3*Y*a)/(2*X*W^2)) + (((-1)*Y*a)/(2*X)) + ((1*Y*Z*a)/(2*X*W^2)) + (((-3)*Y^2)/(X*W^2)) + ((3*Y^2*a^2)/(2*X*W^2)) + (((-1)*Y^2)/(2*X)) + ((1*Y^2*Z)/(2*X*W^2)) + ((1*Y^3*a)/(2*X*W^2)) + (((-2)*Y^4)/(X*W^2)) + ((11)/(2*W^2)) + ((1*b)/(2*W)) + (((-3))/(2)) + (((-3)*Z)/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y*a*b)/(2*W)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-1)*Y^2*b)/(2*W)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((1*Y^3*a)/(W^2)) + (((-1)*Y^4)/(2*W^2)) + ((1*Y^4*a^2)/(2*W^2)) + ((1*Y^5*a)/(2*W^2)) + ((9*X)/(2*W^2)) + ((1*X*b)/(2*W)) + (((-3)*X)/(2)) + (((-1)*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + ((1*X*Y*a*b)/(2*W)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((3*X*Y^2)/(W^2)) + ((3*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^2*b)/(2*W)) + (((-1)*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((5*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((9*X^2)/(2*W^2)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + ((3*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((2*X^3)/(W^2)) + (((-1)*X^3*Z)/(2*W^2)) + ((3*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((1*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(2*W^2)))*v 2
def row71 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1*Z)/(Y^2*W^2)) + ((1*Z*b)/(Y^2*W)) + ((1*Z)/(Y^2)))*v 1 + (((1*X*Z)/(2*Y^2*W^2)) + ((1*X*Z)/(W^2)) + (((-1)*X*Z*a^2)/(2*W^2)) + ((1*X*Y^2*Z)/(2*W^2)) + (((-1)*X^2*Z)/(Y^2*W^2)) + (((-1)*X^2*Z*b)/(Y^2*W)) + (((-1)*X^2*Z)/(Y^2)) + (((-1)*X^3*Z)/(2*Y^2*W^2)) + (((-1)*X^3*Z*b)/(2*Y^2*W)) + (((-1)*X^3*Z)/(2*Y^2)) + (((-1)*X^3*Z*a)/(2*Y*W^2)) + (((-1)*X^3*Z*a*b)/(2*Y*W)) + (((-1)*X^3*Z*a)/(2*Y)) + (((-1)*X^3*Z)/(2*W^2)) + (((-1)*X^3*Z*b)/(2*W)) + (((-1)*X^3*Z)/(2)))*v 2

def row72 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2*W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 0 + (((1)/(X^3)) + (((-2))/(X^2*W^2)) + (((-2))/(X^2)) + (((-2)*Y^2)/(X^2*W^2)) + (((-4))/(X*W^2)) + ((2*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-3))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + (((-2)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((5*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + ((3)/(2*X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(2*X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((3*Y^4)/(2*X*W^2)) + ((3)/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + ((1*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((3*Y^2*a^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((3*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(W^2)) + ((6*X)/(W^2)) + (((-1)*X*b)/(2*W)) + (((-5)*X)/(2)) + (((-2)*X*Z)/(W^2)) + ((3*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a*b)/(2*W)) + (((-1)*X*Y*a)/(2)) + ((2*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^2*b)/(2*W)) + (((-1)*X*Y^2)/(2)) + ((2*X*Y^3*a)/(W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((4*X^2)/(W^2)) + ((-2)*X^2) + (((-1)*X^2*Z)/(2*W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((3*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((5*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-7)*X^4)/(2*W^2)) + ((1*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + (((-2)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-3)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-3)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 2
def row73 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1)*a)/(Y*W^2)) + (((-1)*a)/(Y)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X^2*b)/(Y^2*W)) + (((-1)*X^2*b)/(W)))*v 1 + ((((-1)*X*a)/(2*Y*W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + (((-1)*X^2*b)/(Y^2*W)) + ((1*X^2*a)/(Y*W^2)) + ((1*X^2*a)/(Y)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3*a^2)/(2*W^2)) + (((-1)*X^3*b)/(W)) + ((1*X^3*a^2)/(2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a)/(2)) + ((1*X^4*b)/(Y^2*W)) + ((1*X^4*a*b)/(2*Y*W)) + ((1*X^4*a^2*b)/(2*W)) + ((1*X^4*Y*a*b)/(2*W)))*v 2
def row74 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(W^2)) + ((1*b)/(W)) + (1))*v 1 + (((1*X)/(2*W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(W^2)) + (((-1)*X^2*b)/(W)) + ((-1)*X^2) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*b)/(2*W)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a*b)/(2*W)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*b)/(2*W)) + (((-1)*X^3*Y^2)/(2)))*v 2
def row75 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X^2*W^2)) + ((1)/(X*W^2)) + (((-1))/(X)) + (1))*v 1 + (((1)/(W^2)) + (((-1)*X)/(2*W^2)) + (1*X) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)))*v 2
def row76 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(W^2)) + (((-1)*b)/(W)) + ((-1)))*v 1 + ((((-1)*X)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((1*X^2)/(W^2)) + ((1*X^2*b)/(W)) + (1*X^2) + ((1*X^3)/(2*W^2)) + ((1*X^3*b)/(2*W)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a*b)/(2*W)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*b)/(2*W)) + ((1*X^3*Y^2)/(2)))*v 2
def row77 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1)/(X*W^2)) + ((1)/(W^2)))*v 0 + ((((-1))/(X*Y^2)) + (((-2))/(Y^2*W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X^2)/(W^2)))*v 1 + (((1)/(2*Y^2*W^2)) + ((1*a)/(2*Y*W^2)) + ((1)/(2*W^2)) + ((1*X*a)/(2*Y*W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + ((1*X*Y^3*a)/(2*W^2)) + ((2*X^2)/(Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a^3)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((3*X^3)/(2*W^2)) + (((-1)*X^4)/(Y^2*W^2)) + (((-1)*X^4*a)/(2*Y*W^2)) + (((-1)*X^4*a^2)/(2*W^2)) + (((-1)*X^4*Y*a)/(2*W^2)))*v 2
def row78 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*Y^2*W^2)) + ((2*b)/(X*Y^2*W)) + (((-1)*Z*b)/(X*Y^2*W)) + (((-1))/(Y^2*W^2)) + (((-2)*b)/(Y^2*W)) + ((1*Z*b)/(Y^2*W)))*v 1 + ((((-1)*X)/(Y^2*W^2)) + (((-2)*X*b)/(Y^2*W)) + ((1*X*Z*b)/(Y^2*W)) + ((1*X^2)/(2*Y^2*W^2)) + ((1*X^2*b)/(Y^2*W)) + (((-1)*X^2*Z*b)/(2*Y^2*W)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a*b)/(Y*W)) + ((1*X^2*Z*a*b)/(2*Y*W)) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*b)/(W)) + ((1*X^2*Z*b)/(2*W)) + ((1*X^3)/(2*Y^2*W^2)) + ((1*X^3*b)/(Y^2*W)) + (((-1)*X^3*Z*b)/(2*Y^2*W)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a*b)/(Y*W)) + (((-1)*X^3*Z*a*b)/(2*Y*W)) + ((1*X^3)/(2*W^2)) + ((1*X^3*b)/(W)) + (((-1)*X^3*Z*b)/(2*W)))*v 2
def row79 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2*W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 0 + ((((-1))/(X^3)) + (((-3))/(X^2*W^2)) + ((2)/(X^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + ((7)/(X*W^2)) + (((-1)*b)/(X*W)) + (((-1))/(X)) + (((-1)*Z)/(X*W^2)) + (((-2)*Y*a)/(X*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + ((3)/(W^2)) + ((-1)) + (((-3)*Y*a)/(W^2)) + ((4*Y^2)/(W^2)) + ((1*Y^4)/(W^2)) + ((2*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 1 + (((1)/(2*X^2*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(2*X^2*W^2)) + ((1*Y^2*a^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + ((4)/(W^2)) + (((-1)*b)/(W)) + ((1)/(2)) + (((-3)*Z)/(2*W^2)) + (((-3)*Y*a)/(2*W^2)) + ((1*Y*a)/(2)) + (((-1)*Y*Z*a)/(2*W^2)) + ((3*Y^2)/(W^2)) + (((-3)*Y^2*a^2)/(2*W^2)) + ((1*Y^2)/(2)) + (((-1)*Y^2*Z)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + ((2*Y^4)/(W^2)) + (((-11)*X)/(2*W^2)) + (((-1)*X*b)/(2*W)) + ((3*X)/(2)) + ((3*X*Z)/(2*W^2)) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y*a*b)/(2*W)) + ((1*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((1*X*Y^2*b)/(2*W)) + ((1*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + (((-5)*X^2)/(W^2)) + (((-1)*X^2*b)/(2*W)) + ((3*X^2)/(2)) + ((1*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a*b)/(2*W)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-4)*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + (((-1)*X^2*Y^2*b)/(2*W)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-5)*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^2*Y^4)/(W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-4)*X^3)/(W^2)) + ((1*X^3)/(2)) + ((1*X^3*Z)/(W^2)) + ((1*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2)/(2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + (((-2)*X^4)/(W^2)) + ((1*X^4*Z)/(2*W^2)) + (((-3)*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-3)*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(W^2)) + (((-1)*X^4*Y^4)/(2*W^2)))*v 2

def row80 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1)*Z)/(Y^2*W^2)) + (((-1)*Z*b)/(Y^2*W)) + (((-1)*Z)/(Y^2)))*v 1 + ((((-1)*X*Z)/(2*Y^2*W^2)) + (((-1)*X*Z)/(W^2)) + ((1*X*Z*a^2)/(2*W^2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((1*X^2*Z)/(Y^2*W^2)) + ((1*X^2*Z*b)/(Y^2*W)) + ((1*X^2*Z)/(Y^2)) + ((1*X^3*Z)/(2*Y^2*W^2)) + ((1*X^3*Z*b)/(2*Y^2*W)) + ((1*X^3*Z)/(2*Y^2)) + ((1*X^3*Z*a)/(2*Y*W^2)) + ((1*X^3*Z*a*b)/(2*Y*W)) + ((1*X^3*Z*a)/(2*Y)) + ((1*X^3*Z)/(2*W^2)) + ((1*X^3*Z*b)/(2*W)) + ((1*X^3*Z)/(2)))*v 2
def row81 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^3*W^2)) + ((1*X*Y^2)/(W^2)))*v 0 + ((((-1))/(X^4)) + ((2)/(X^3*W^2)) + ((2)/(X^3)) + ((2*Y^2)/(X^3*W^2)) + ((4)/(X^2*W^2)) + (((-2)*b)/(X^2*W)) + (((-2))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-2)*Y*a)/(X^2*W^2)) + ((2*Y^2)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + ((3)/(X*W^2)) + (((-1))/(X)) + (((-3)*Y*a)/(X*W^2)) + ((4*Y^2)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + ((2)/(W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((1*Y^2)/(W^2)) + (((-5)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 1 + (((1)/(2*X^3*W^2)) + ((1*Y*a)/(2*X^3*W^2)) + ((1*Y^3*a)/(2*X^3*W^2)) + ((1*Y^4)/(2*X^3*W^2)) + (((-3))/(2*X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + ((1*Y^2)/(X^2*W^2)) + ((1*Y^2*a^2)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(X^2*W^2)) + (((-3)*Y^4)/(2*X^2*W^2)) + (((-3))/(X*W^2)) + (((-1)*b)/(X*W)) + ((1)/(2*X)) + (((-1)*Z)/(2*X*W^2)) + (((-3)*Y*a)/(2*X*W^2)) + ((1*Y*a)/(2*X)) + (((-1)*Y*Z*a)/(2*X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-3)*Y^2*a^2)/(2*X*W^2)) + ((1*Y^2)/(2*X)) + (((-1)*Y^2*Z)/(2*X*W^2)) + (((-3)*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-6))/(W^2)) + ((1*b)/(2*W)) + ((5)/(2)) + ((2*Z)/(W^2)) + (((-3)*Y*a)/(2*W^2)) + ((1*Y*a*b)/(2*W)) + ((1*Y*a)/(2)) + (((-2)*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + ((1*Y^2*b)/(2*W)) + ((1*Y^2)/(2)) + (((-2)*Y^3*a)/(W^2)) + (((-1)*Y^4*a^2)/(2*W^2)) + (((-1)*Y^5*a)/(2*W^2)) + (((-7)*X)/(2*W^2)) + (2*X) + ((1*X*Z)/(2*W^2)) + (1*X*Y*a) + ((1*X*Y*Z*a)/(2*W^2)) + (((-2)*X*Y^2)/(W^2)) + (((-3)*X*Y^2*a^2)/(2*W^2)) + (1*X*Y^2) + ((1*X*Y^2*Z)/(2*W^2)) + (((-5)*X*Y^3*a)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + (((-3)*X^2)/(W^2)) + ((1*X^2)/(2)) + ((1*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a)/(2)) + (((-5)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + ((7*X^3)/(2*W^2)) + (((-1)*X^3*Z)/(2*W^2)) + (((-3)*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 2
def row82 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1*a)/(X*Y*W^2)) + ((1*a)/(X*Y)) + ((1*b)/(Y^2*W)) + ((1*X*b)/(Y^2*W)) + ((1*X*b)/(W)))*v 1 + (((1*a)/(2*Y*W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y*a^3)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + ((1*X*b)/(Y^2*W)) + (((-1)*X*a)/(Y*W^2)) + (((-1)*X*a)/(Y)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a)/(2*Y)) + (((-1)*X^2*a^2)/(2*W^2)) + ((1*X^2*b)/(W)) + (((-1)*X^2*a^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^3*b)/(Y^2*W)) + (((-1)*X^3*a*b)/(2*Y*W)) + (((-1)*X^3*a^2*b)/(2*W)) + (((-1)*X^3*Y*a*b)/(2*W)))*v 2
def row83 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X*W^2)) + (((-1)*b)/(X*W)) + (((-1))/(X)))*v 1 + ((((-1))/(2*W^2)) + (((-1)*Y^2)/(W^2)) + ((1*Y^2*a^2)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + ((1*X)/(W^2)) + ((1*X*b)/(W)) + (1*X) + ((1*X^2)/(2*W^2)) + ((1*X^2*b)/(2*W)) + ((1*X^2)/(2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*a*b)/(2*W)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*b)/(2*W)) + ((1*X^2*Y^2)/(2)))*v 2
def row84 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(Y^2*W^2)) + ((1*a)/(Y)) + ((2*X)/(Y^2*W^2)) + ((1*X*b)/(Y^2*W)) + ((1*X^2)/(Y^2*W^2)) + ((1*X^2*b)/(Y^2*W)) + ((1*X^2)/(W^2)) + ((1*X^2*b)/(W)))*v 1 + (((2*X^2)/(Y^2*W^2)) + ((1*X^2*b)/(Y^2*W)) + ((1*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a)/(Y)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a^3)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + (((-1)*X^3*a)/(2*Y)) + ((3*X^3)/(2*W^2)) + ((1*X^3*b)/(W)) + (((-1)*X^3*a^2)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-3)*X^4)/(2*Y^2*W^2)) + (((-1)*X^4*b)/(Y^2*W)) + (((-1)*X^4*a)/(Y*W^2)) + (((-1)*X^4*a*b)/(2*Y*W)) + (((-1)*X^4)/(2*W^2)) + (((-1)*X^4*a^2)/(2*W^2)) + (((-1)*X^4*a^2*b)/(2*W)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*a*b)/(2*W)))*v 2
def row85 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*Y^2*W^2)) + ((1*b)/(X*Y^2*W)) + ((1)/(X*Y^2)) + (((-1))/(W^2)) + (((-1)*b)/(W)) + ((-1)))*v 1 + (((1)/(2*Y^2*W^2)) + ((1)/(W^2)) + (((-1)*a^2)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X)/(Y^2)) + (((-1)*X)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*b)/(2*Y^2*W)) + (((-1)*X^2)/(2*Y^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a*b)/(2*Y*W)) + (((-1)*X^2*a)/(2*Y)) + ((1*X^2)/(2*W^2)) + ((1*X^2*b)/(2*W)) + ((1*X^2)/(2)) + ((1*X^3)/(2*W^2)) + ((1*X^3*b)/(2*W)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a*b)/(2*W)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*b)/(2*W)) + ((1*X^3*Y^2)/(2)))*v 2
def row86 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1))/(X^2*W^2)) + (((-1))/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 0 + (((1)/(X^2*Y^2)) + ((2)/(X*Y^2*W^2)) + ((1*a)/(X*Y)) + ((1)/(X)) + ((1*b)/(Y^2*W)) + ((2)/(W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X*b)/(Y^2*W)) + (((-1)*X)/(W^2)) + ((1*X*b)/(W)) + (((-1)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X*Y^2*W^2)) + (((-1)*a)/(2*X*Y*W^2)) + (((-1))/(2*X*W^2)) + (((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X*b)/(Y^2*W)) + ((1*X*a)/(2*Y*W^2)) + (((-1)*X*a)/(Y)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + ((1*X*Y^3*a)/(2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a)/(2*Y)) + (((-5)*X^2)/(2*W^2)) + ((1*X^2*b)/(W)) + (((-1)*X^2*a^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^3*b)/(Y^2*W)) + (((-1)*X^3*a*b)/(2*Y*W)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*a^2*b)/(2*W)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a*b)/(2*W)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 2
def row87 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (0)*v 1 + (((1*X)/(2*W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^4)/(2*W^2)))*v 2

def row88 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (0)*v 1 + (((1*Z)/(2*Y^2*W^2)) + ((1*Z)/(W^2)) + (((-1)*Z*a^2)/(2*W^2)) + ((1*Y^2*Z)/(2*W^2)) + (((-1)*X*Z)/(2*Y^2*W^2)) + (((-1)*X*Z)/(W^2)) + ((1*X*Z*a^2)/(2*W^2)) + (((-1)*X*Y^2*Z)/(2*W^2)))*v 2
def row89 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1)*a)/(X*Y)) + (((-1))/(Y^2*W^2)) + (((-1)*b)/(Y^2*W)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X)/(W^2)) + (((-1)*X*b)/(W)))*v 1 + ((((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X*a)/(2*Y*W^2)) + ((1*X*a)/(Y)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + ((1*X^2*a)/(2*Y)) + (((-1)*X^2)/(W^2)) + (((-1)*X^2*b)/(W)) + ((1*X^2*a^2)/(2)) + ((1*X^2*Y*a)/(2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3*b)/(Y^2*W)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a*b)/(2*Y*W)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*a^2*b)/(2*W)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a*b)/(2*W)))*v 2
def row90 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((3400)/(3*X*W^2)) + ((1700)/(3*W^2)))*v 1 + (((4930)/(W^2)) + ((340*Y*a)/(W^2)) + ((340*Y^2)/(W^2)) + (((-6970)*X)/(3*W^2)) + (((-170)*X*Y*a)/(W^2)) + (((-170)*X*Y^2)/(W^2)) + ((3145*X^2)/(6*W^2)) + ((1105*X^2*Y*a)/(3*W^2)) + ((1105*X^2*Y^2)/(3*W^2)) + (((-850)*X^3)/(3*W^2)) + (((-850)*X^3*Y*a)/(3*W^2)) + (((-850)*X^3*Y^2)/(3*W^2)))*v 2
def row91 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((136)/(3*X)) + ((68)/(3)))*v 1 + (((986)/(5)) + ((68*Y*a)/(5)) + ((68*Y^2)/(5)) + (((-1394)*X)/(15)) + (((-34)*X*Y*a)/(5)) + (((-34)*X*Y^2)/(5)) + ((629*X^2)/(30)) + ((221*X^2*Y*a)/(15)) + ((221*X^2*Y^2)/(15)) + (((-34)*X^3)/(3)) + (((-34)*X^3*Y*a)/(3)) + (((-34)*X^3*Y^2)/(3)))*v 2
def row92 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-136))/(3*X)) + (((-68))/(3)))*v 1 + ((((-986))/(5)) + (((-68)*Y*a)/(5)) + (((-68)*Y^2)/(5)) + ((1394*X)/(15)) + ((34*X*Y*a)/(5)) + ((34*X*Y^2)/(5)) + (((-629)*X^2)/(30)) + (((-221)*X^2*Y*a)/(15)) + (((-221)*X^2*Y^2)/(15)) + ((34*X^3)/(3)) + ((34*X^3*Y*a)/(3)) + ((34*X^3*Y^2)/(3)))*v 2
def row93 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((408)/(X*Y^2)) + ((204)/(Y^2)))*v 1 + (((8874)/(5*Y^2)) + ((612*a)/(5*Y)) + ((612)/(5)) + (((-4182)*X)/(5*Y^2)) + (((-306)*X*a)/(5*Y)) + (((-306)*X)/(5)) + ((1887*X^2)/(10*Y^2)) + ((663*X^2*a)/(5*Y)) + ((663*X^2)/(5)) + (((-102)*X^3)/(Y^2)) + (((-102)*X^3*a)/(Y)) + ((-102)*X^3))*v 2
def row94 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((10200)/(X*Y^2*W^2)) + ((5100)/(Y^2*W^2)))*v 1 + (((44370)/(Y^2*W^2)) + ((3060*a)/(Y*W^2)) + ((3060)/(W^2)) + (((-20910)*X)/(Y^2*W^2)) + (((-1530)*X*a)/(Y*W^2)) + (((-1530)*X)/(W^2)) + ((9435*X^2)/(2*Y^2*W^2)) + ((3315*X^2*a)/(Y*W^2)) + ((3315*X^2)/(W^2)) + (((-2550)*X^3)/(Y^2*W^2)) + (((-2550)*X^3*a)/(Y*W^2)) + (((-2550)*X^3)/(W^2)))*v 2
def row95 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-68))/(X)))*v 1 + ((((-986))/(5)) + (((-68)*Y*a)/(5)) + (((-68)*Y^2)/(5)) + ((578*X)/(5)) + ((34*X*Y*a)/(5)) + ((34*X*Y^2)/(5)) + (((-323)*X^2)/(10)) + (((-17)*X^2*Y*a)/(5)) + (((-17)*X^2*Y^2)/(5)))*v 2

def row96 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-15300))/(X*Y^2*W^2)))*v 1 + ((((-44370))/(Y^2*W^2)) + (((-3060)*a)/(Y*W^2)) + (((-3060))/(W^2)) + ((26010*X)/(Y^2*W^2)) + ((1530*X*a)/(Y*W^2)) + ((1530*X)/(W^2)) + (((-14535)*X^2)/(2*Y^2*W^2)) + (((-765)*X^2*a)/(Y*W^2)) + (((-765)*X^2)/(W^2)))*v 2
def row97 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-68)*a)/(Y)) + (((-34)*X*a)/(Y)))*v 1 + ((((-1479)*X*a)/(5*Y)) + (((-102)*X*a^2)/(5)) + (((-102)*X*Y*a)/(5)) + ((697*X^2*a)/(5*Y)) + ((51*X^2*a^2)/(5)) + ((51*X^2*Y*a)/(5)) + (((-629)*X^3*a)/(20*Y)) + (((-221)*X^3*a^2)/(10)) + (((-221)*X^3*Y*a)/(10)) + ((17*X^4*a)/(Y)) + (17*X^4*a^2) + (17*X^4*Y*a))*v 2
def row98 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((816)/(X*Y^2)) + (((-68))/(X)) + (((-204))/(Y^2)) + (((-68)*a)/(Y)) + ((68)/(3)))*v 1 + ((((-714))/(Y^2)) + (((-2958)*a)/(5*Y)) + (((-986))/(5)) + (((-204)*a^2)/(5)) + (((-272)*Y*a)/(5)) + (((-68)*Y^2)/(5)) + ((1122*X)/(5*Y^2)) + ((204*X*a)/(Y)) + ((1156*X)/(5)) + ((102*X*a^2)/(5)) + ((102*X*Y*a)/(5)) + ((357*X^2)/(2*Y^2)) + (((-136)*X^2*a)/(Y)) + (((-374)*X^2)/(3)) + ((-102)*X^2*a^2) + ((-102)*X^2*Y*a) + ((34*X^3*a)/(Y)) + (((-34)*X^3)/(3)) + (34*X^3*a^2) + ((68*X^3*Y*a)/(3)) + (((-34)*X^3*Y^2)/(3)))*v 2
def row99 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-10200))/(X*Y^2*W^2)) + ((8500)/(3*X*W^2)) + ((10200)/(Y^2*W^2)) + ((1700*a)/(Y*W^2)))*v 1 + (((62220)/(Y^2*W^2)) + ((17850*a)/(Y*W^2)) + ((12920)/(W^2)) + ((1020*a^2)/(W^2)) + ((1700*Y*a)/(W^2)) + ((680*Y^2)/(W^2)) + (((-26520)*X)/(Y^2*W^2)) + (((-6630)*X*a)/(Y*W^2)) + (((-28900)*X)/(3*W^2)) + (((-510)*X*a^2)/(W^2)) + (((-680)*X*Y*a)/(W^2)) + (((-170)*X*Y^2)/(W^2)) + ((255*X^2)/(Y^2*W^2)) + ((6715*X^2*a)/(Y*W^2)) + ((41735*X^2)/(6*W^2)) + ((2550*X^2*a^2)/(W^2)) + ((8755*X^2*Y*a)/(3*W^2)) + ((1105*X^2*Y^2)/(3*W^2)) + (((-2550)*X^3)/(Y^2*W^2)) + (((-3400)*X^3*a)/(Y*W^2)) + (((-2550)*X^3)/(W^2)) + (((-850)*X^3*a^2)/(W^2)) + (((-850)*X^3*Y*a)/(W^2)))*v 2
def row100 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-3400)*a)/(X*Y*W^2)) + (((-1700)*a)/(Y*W^2)))*v 1 + ((((-14790)*a)/(Y*W^2)) + (((-1020)*a^2)/(W^2)) + (((-1020)*Y*a)/(W^2)) + ((6970*X*a)/(Y*W^2)) + ((510*X*a^2)/(W^2)) + ((510*X*Y*a)/(W^2)) + (((-3145)*X^2*a)/(2*Y*W^2)) + (((-1105)*X^2*a^2)/(W^2)) + (((-1105)*X^2*Y*a)/(W^2)) + ((850*X^3*a)/(Y*W^2)) + ((850*X^3*a^2)/(W^2)) + ((850*X^3*Y*a)/(W^2)))*v 2
def row101 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-204))/(Y^2)) + ((204*X)/(Y^2)) + ((34*X*a)/(Y)) + (((-34)*X)/(3)))*v 1 + (((6222*X)/(5*Y^2)) + ((357*X*a)/(Y)) + ((306*X)/(5)) + ((102*X*a^2)/(5)) + ((102*X*Y*a)/(5)) + (((-2652)*X^2)/(5*Y^2)) + (((-663)*X^2*a)/(5*Y)) + (((-442)*X^2)/(5)) + (((-51)*X^2*a^2)/(5)) + (((-34)*X^2*Y*a)/(5)) + ((17*X^2*Y^2)/(5)) + ((51*X^3)/(10*Y^2)) + ((1343*X^3*a)/(10*Y)) + ((6749*X^3)/(60)) + (51*X^3*a^2) + ((493*X^3*Y*a)/(10)) + (((-17)*X^3*Y^2)/(10)) + (((-51)*X^4)/(Y^2)) + (((-68)*X^4*a)/(Y)) + (((-136)*X^4)/(3)) + ((-17)*X^4*a^2) + (((-34)*X^4*Y*a)/(3)) + ((17*X^4*Y^2)/(3)))*v 2
def row102 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((10200)/(Y^2*W^2)) + (((-4250))/(3*W^2)) + (((-2550)*X)/(Y^2*W^2)) + (((-850)*X*a)/(Y*W^2)))*v 1 + ((((-8925)*X)/(Y^2*W^2)) + (((-7395)*X*a)/(Y*W^2)) + (((-4930)*X)/(W^2)) + (((-510)*X*a^2)/(W^2)) + (((-850)*X*Y*a)/(W^2)) + (((-340)*X*Y^2)/(W^2)) + ((2805*X^2)/(Y^2*W^2)) + ((2550*X^2*a)/(Y*W^2)) + ((12155*X^2)/(3*W^2)) + ((255*X^2*a^2)/(W^2)) + ((340*X^2*Y*a)/(W^2)) + ((85*X^2*Y^2)/(W^2)) + ((8925*X^3)/(4*Y^2*W^2)) + (((-1700)*X^3*a)/(Y*W^2)) + (((-21845)*X^3)/(12*W^2)) + (((-1275)*X^3*a^2)/(W^2)) + (((-8755)*X^3*Y*a)/(6*W^2)) + (((-1105)*X^3*Y^2)/(6*W^2)) + ((425*X^4*a)/(Y*W^2)) + ((425*X^4*a^2)/(W^2)) + ((425*X^4*Y*a)/(W^2)))*v 2
def row103 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-5100)*X)/(Y^2*W^2)) + ((2125*X)/(3*W^2)) + ((1275*X^2)/(Y^2*W^2)) + ((425*X^2*a)/(Y*W^2)))*v 1 + (((8925*X^2)/(2*Y^2*W^2)) + ((7395*X^2*a)/(2*Y*W^2)) + ((2465*X^2)/(W^2)) + ((255*X^2*a^2)/(W^2)) + ((425*X^2*Y*a)/(W^2)) + ((170*X^2*Y^2)/(W^2)) + (((-2805)*X^3)/(2*Y^2*W^2)) + (((-1275)*X^3*a)/(Y*W^2)) + (((-12155)*X^3)/(6*W^2)) + (((-255)*X^3*a^2)/(2*W^2)) + (((-170)*X^3*Y*a)/(W^2)) + (((-85)*X^3*Y^2)/(2*W^2)) + (((-8925)*X^4)/(8*Y^2*W^2)) + ((850*X^4*a)/(Y*W^2)) + ((21845*X^4)/(24*W^2)) + ((1275*X^4*a^2)/(2*W^2)) + ((8755*X^4*Y*a)/(12*W^2)) + ((1105*X^4*Y^2)/(12*W^2)) + (((-425)*X^5*a)/(2*Y*W^2)) + (((-425)*X^5*a^2)/(2*W^2)) + (((-425)*X^5*Y*a)/(2*W^2)))*v 2

end SmallLevelThirtyFourFiniteJetMMM
end
end

/-! ## ThirtyFourFiniteJetMMMData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourFiniteJetMMM
open Complex
def rows (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : Fin 104→ℂ
  | 0 => row0 X Y Z W a b v
  | 1 => row1 X Y Z W a b v
  | 2 => row2 X Y Z W a b v
  | 3 => row3 X Y Z W a b v
  | 4 => row4 X Y Z W a b v
  | 5 => row5 X Y Z W a b v
  | 6 => row6 X Y Z W a b v
  | 7 => row7 X Y Z W a b v
  | 8 => row8 X Y Z W a b v
  | 9 => row9 X Y Z W a b v
  | 10 => row10 X Y Z W a b v
  | 11 => row11 X Y Z W a b v
  | 12 => row12 X Y Z W a b v
  | 13 => row13 X Y Z W a b v
  | 14 => row14 X Y Z W a b v
  | 15 => row15 X Y Z W a b v
  | 16 => row16 X Y Z W a b v
  | 17 => row17 X Y Z W a b v
  | 18 => row18 X Y Z W a b v
  | 19 => row19 X Y Z W a b v
  | 20 => row20 X Y Z W a b v
  | 21 => row21 X Y Z W a b v
  | 22 => row22 X Y Z W a b v
  | 23 => row23 X Y Z W a b v
  | 24 => row24 X Y Z W a b v
  | 25 => row25 X Y Z W a b v
  | 26 => row26 X Y Z W a b v
  | 27 => row27 X Y Z W a b v
  | 28 => row28 X Y Z W a b v
  | 29 => row29 X Y Z W a b v
  | 30 => row30 X Y Z W a b v
  | 31 => row31 X Y Z W a b v
  | 32 => row32 X Y Z W a b v
  | 33 => row33 X Y Z W a b v
  | 34 => row34 X Y Z W a b v
  | 35 => row35 X Y Z W a b v
  | 36 => row36 X Y Z W a b v
  | 37 => row37 X Y Z W a b v
  | 38 => row38 X Y Z W a b v
  | 39 => row39 X Y Z W a b v
  | 40 => row40 X Y Z W a b v
  | 41 => row41 X Y Z W a b v
  | 42 => row42 X Y Z W a b v
  | 43 => row43 X Y Z W a b v
  | 44 => row44 X Y Z W a b v
  | 45 => row45 X Y Z W a b v
  | 46 => row46 X Y Z W a b v
  | 47 => row47 X Y Z W a b v
  | 48 => row48 X Y Z W a b v
  | 49 => row49 X Y Z W a b v
  | 50 => row50 X Y Z W a b v
  | 51 => row51 X Y Z W a b v
  | 52 => row52 X Y Z W a b v
  | 53 => row53 X Y Z W a b v
  | 54 => row54 X Y Z W a b v
  | 55 => row55 X Y Z W a b v
  | 56 => row56 X Y Z W a b v
  | 57 => row57 X Y Z W a b v
  | 58 => row58 X Y Z W a b v
  | 59 => row59 X Y Z W a b v
  | 60 => row60 X Y Z W a b v
  | 61 => row61 X Y Z W a b v
  | 62 => row62 X Y Z W a b v
  | 63 => row63 X Y Z W a b v
  | 64 => row64 X Y Z W a b v
  | 65 => row65 X Y Z W a b v
  | 66 => row66 X Y Z W a b v
  | 67 => row67 X Y Z W a b v
  | 68 => row68 X Y Z W a b v
  | 69 => row69 X Y Z W a b v
  | 70 => row70 X Y Z W a b v
  | 71 => row71 X Y Z W a b v
  | 72 => row72 X Y Z W a b v
  | 73 => row73 X Y Z W a b v
  | 74 => row74 X Y Z W a b v
  | 75 => row75 X Y Z W a b v
  | 76 => row76 X Y Z W a b v
  | 77 => row77 X Y Z W a b v
  | 78 => row78 X Y Z W a b v
  | 79 => row79 X Y Z W a b v
  | 80 => row80 X Y Z W a b v
  | 81 => row81 X Y Z W a b v
  | 82 => row82 X Y Z W a b v
  | 83 => row83 X Y Z W a b v
  | 84 => row84 X Y Z W a b v
  | 85 => row85 X Y Z W a b v
  | 86 => row86 X Y Z W a b v
  | 87 => row87 X Y Z W a b v
  | 88 => row88 X Y Z W a b v
  | 89 => row89 X Y Z W a b v
  | 90 => row90 X Y Z W a b v
  | 91 => row91 X Y Z W a b v
  | 92 => row92 X Y Z W a b v
  | 93 => row93 X Y Z W a b v
  | 94 => row94 X Y Z W a b v
  | 95 => row95 X Y Z W a b v
  | 96 => row96 X Y Z W a b v
  | 97 => row97 X Y Z W a b v
  | 98 => row98 X Y Z W a b v
  | 99 => row99 X Y Z W a b v
  | 100 => row100 X Y Z W a b v
  | 101 => row101 X Y Z W a b v
  | 102 => row102 X Y Z W a b v
  | _ => row103 X Y Z W a b v

end SmallLevelThirtyFourFiniteJetMMM
end
end

/-! ## ThirtyFourFiniteJetMMMLeadingBindingBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourFiniteJetMMM
open Complex SmallLevelThirtyFourUnitMMM

theorem leading_binding_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row0 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_0 X Y Z W a b hX hY hZ hW v hv
  simpa only [row0,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_0
theorem leading_binding_1 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row1 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_1 X Y Z W a b hX hY hZ hW v hv
  simpa only [row1,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_1
theorem leading_binding_2 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row2 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_2 X Y Z W a b hX hY hZ hW v hv
  simpa only [row2,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_2
theorem leading_binding_3 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row3 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_3 X Y Z W a b hX hY hZ hW v hv
  simpa only [row3,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_3
theorem leading_binding_4 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row4 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_4 X Y Z W a b hX hY hZ hW v hv
  simpa only [row4,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_4
theorem leading_binding_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row5 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_5 X Y Z W a b hX hY hZ hW v hv
  simpa only [row5,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_5
theorem leading_binding_6 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row6 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_6 X Y Z W a b hX hY hZ hW v hv
  simpa only [row6,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_6
theorem leading_binding_7 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row7 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_7 X Y Z W a b hX hY hZ hW v hv
  simpa only [row7,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_7

theorem leading_binding_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row8 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_8 X Y Z W a b hX hY hZ hW v hv
  simpa only [row8,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_8
theorem leading_binding_9 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row9 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_9 X Y Z W a b hX hY hZ hW v hv
  simpa only [row9,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_9
theorem leading_binding_10 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row10 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_10 X Y Z W a b hX hY hZ hW v hv
  simpa only [row10,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_10
theorem leading_binding_11 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row11 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_11 X Y Z W a b hX hY hZ hW v hv
  simpa only [row11,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_11
theorem leading_binding_12 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row12 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_12 X Y Z W a b hX hY hZ hW v hv
  simpa only [row12,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_12
theorem leading_binding_13 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row13 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_13 X Y Z W a b hX hY hZ hW v hv
  simpa only [row13,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_13
theorem leading_binding_14 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row14 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_14 X Y Z W a b hX hY hZ hW v hv
  simpa only [row14,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_14
theorem leading_binding_15 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row15 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_15 X Y Z W a b hX hY hZ hW v hv
  simpa only [row15,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_15

theorem leading_binding_16 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row16 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_16 X Y Z W a b hX hY hZ hW v hv
  simpa only [row16,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_16
theorem leading_binding_17 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row17 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_20 X Y Z W a b hX hY hZ hW v hv
  simpa only [row17,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_17
theorem leading_binding_18 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row18 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_21 X Y Z W a b hX hY hZ hW v hv
  simpa only [row18,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_18
theorem leading_binding_19 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row19 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_22 X Y Z W a b hX hY hZ hW v hv
  simpa only [row19,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_19
theorem leading_binding_20 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row20 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_23 X Y Z W a b hX hY hZ hW v hv
  simpa only [row20,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_20
theorem leading_binding_21 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row21 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_25 X Y Z W a b hX hY hZ hW v hv
  simpa only [row21,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_21
theorem leading_binding_22 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row22 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_26 X Y Z W a b hX hY hZ hW v hv
  simpa only [row22,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_22
theorem leading_binding_23 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row23 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_27 X Y Z W a b hX hY hZ hW v hv
  simpa only [row23,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_23

theorem leading_binding_24 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row24 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_28 X Y Z W a b hX hY hZ hW v hv
  simpa only [row24,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_24
theorem leading_binding_25 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row25 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_29 X Y Z W a b hX hY hZ hW v hv
  simpa only [row25,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_25
theorem leading_binding_26 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row26 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_30 X Y Z W a b hX hY hZ hW v hv
  simpa only [row26,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_26
theorem leading_binding_27 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row27 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_32 X Y Z W a b hX hY hZ hW v hv
  simpa only [row27,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_27
theorem leading_binding_28 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row28 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_33 X Y Z W a b hX hY hZ hW v hv
  simpa only [row28,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_28
theorem leading_binding_29 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row29 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_35 X Y Z W a b hX hY hZ hW v hv
  simpa only [row29,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_29
theorem leading_binding_30 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row30 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_36 X Y Z W a b hX hY hZ hW v hv
  simpa only [row30,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_30
theorem leading_binding_31 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row31 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_37 X Y Z W a b hX hY hZ hW v hv
  simpa only [row31,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_31

theorem leading_binding_32 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row32 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_38 X Y Z W a b hX hY hZ hW v hv
  simpa only [row32,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_32
theorem leading_binding_33 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row33 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_40 X Y Z W a b hX hY hZ hW v hv
  simpa only [row33,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_33
theorem leading_binding_34 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row34 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_41 X Y Z W a b hX hY hZ hW v hv
  simpa only [row34,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_34
theorem leading_binding_35 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row35 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_42 X Y Z W a b hX hY hZ hW v hv
  simpa only [row35,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_35
theorem leading_binding_36 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row36 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_43 X Y Z W a b hX hY hZ hW v hv
  simpa only [row36,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_36
theorem leading_binding_37 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row37 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_45 X Y Z W a b hX hY hZ hW v hv
  simpa only [row37,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_37
theorem leading_binding_38 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row38 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_47 X Y Z W a b hX hY hZ hW v hv
  simpa only [row38,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_38
theorem leading_binding_39 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row39 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_48 X Y Z W a b hX hY hZ hW v hv
  simpa only [row39,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_39

theorem leading_binding_40 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row40 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_49 X Y Z W a b hX hY hZ hW v hv
  simpa only [row40,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_40
theorem leading_binding_41 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row41 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_50 X Y Z W a b hX hY hZ hW v hv
  simpa only [row41,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_41
theorem leading_binding_42 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row42 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_54 X Y Z W a b hX hY hZ hW v hv
  simpa only [row42,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_42
theorem leading_binding_43 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row43 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_55 X Y Z W a b hX hY hZ hW v hv
  simpa only [row43,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_43
theorem leading_binding_44 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row44 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_57 X Y Z W a b hX hY hZ hW v hv
  simpa only [row44,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_44
theorem leading_binding_45 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row45 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_58 X Y Z W a b hX hY hZ hW v hv
  simpa only [row45,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_45
theorem leading_binding_46 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row46 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_60 X Y Z W a b hX hY hZ hW v hv
  simpa only [row46,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_46
theorem leading_binding_47 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row47 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_61 X Y Z W a b hX hY hZ hW v hv
  simpa only [row47,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_47

theorem leading_binding_48 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row48 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_62 X Y Z W a b hX hY hZ hW v hv
  simpa only [row48,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_48
theorem leading_binding_49 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row49 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_63 X Y Z W a b hX hY hZ hW v hv
  simpa only [row49,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_49
theorem leading_binding_50 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row50 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_64 X Y Z W a b hX hY hZ hW v hv
  simpa only [row50,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_50
theorem leading_binding_51 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row51 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_65 X Y Z W a b hX hY hZ hW v hv
  simpa only [row51,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_51
theorem leading_binding_52 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row52 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_66 X Y Z W a b hX hY hZ hW v hv
  simpa only [row52,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_52
theorem leading_binding_53 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row53 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_67 X Y Z W a b hX hY hZ hW v hv
  simpa only [row53,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_53
theorem leading_binding_54 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row54 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_68 X Y Z W a b hX hY hZ hW v hv
  simpa only [row54,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_54
theorem leading_binding_55 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row55 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_70 X Y Z W a b hX hY hZ hW v hv
  simpa only [row55,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_55

theorem leading_binding_56 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row56 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_72 X Y Z W a b hX hY hZ hW v hv
  simpa only [row56,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_56
theorem leading_binding_57 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row57 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_74 X Y Z W a b hX hY hZ hW v hv
  simpa only [row57,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_57
theorem leading_binding_58 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row58 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_75 X Y Z W a b hX hY hZ hW v hv
  simpa only [row58,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_58
theorem leading_binding_59 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row59 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_76 X Y Z W a b hX hY hZ hW v hv
  simpa only [row59,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_59
theorem leading_binding_60 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row60 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_77 X Y Z W a b hX hY hZ hW v hv
  simpa only [row60,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_60
theorem leading_binding_61 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row61 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_78 X Y Z W a b hX hY hZ hW v hv
  simpa only [row61,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_61
theorem leading_binding_62 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row62 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_79 X Y Z W a b hX hY hZ hW v hv
  simpa only [row62,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_62
theorem leading_binding_63 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row63 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_80 X Y Z W a b hX hY hZ hW v hv
  simpa only [row63,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_63

theorem leading_binding_64 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row64 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_81 X Y Z W a b hX hY hZ hW v hv
  simpa only [row64,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_64
theorem leading_binding_65 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row65 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_82 X Y Z W a b hX hY hZ hW v hv
  simpa only [row65,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_65
theorem leading_binding_66 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row66 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_83 X Y Z W a b hX hY hZ hW v hv
  simpa only [row66,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_66
theorem leading_binding_67 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row67 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_84 X Y Z W a b hX hY hZ hW v hv
  simpa only [row67,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_67
theorem leading_binding_68 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row68 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_85 X Y Z W a b hX hY hZ hW v hv
  simpa only [row68,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_68
theorem leading_binding_69 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row69 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_86 X Y Z W a b hX hY hZ hW v hv
  simpa only [row69,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_69
theorem leading_binding_70 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row70 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_87 X Y Z W a b hX hY hZ hW v hv
  simpa only [row70,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_70
theorem leading_binding_71 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row71 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_88 X Y Z W a b hX hY hZ hW v hv
  simpa only [row71,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_71

theorem leading_binding_72 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row72 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_89 X Y Z W a b hX hY hZ hW v hv
  simpa only [row72,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_72
theorem leading_binding_73 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row73 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_90 X Y Z W a b hX hY hZ hW v hv
  simpa only [row73,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_73
theorem leading_binding_74 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row74 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_91 X Y Z W a b hX hY hZ hW v hv
  simpa only [row74,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_74
theorem leading_binding_75 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row75 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_92 X Y Z W a b hX hY hZ hW v hv
  simpa only [row75,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_75
theorem leading_binding_76 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row76 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_95 X Y Z W a b hX hY hZ hW v hv
  simpa only [row76,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_76
theorem leading_binding_77 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row77 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_96 X Y Z W a b hX hY hZ hW v hv
  simpa only [row77,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_77
theorem leading_binding_78 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row78 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_98 X Y Z W a b hX hY hZ hW v hv
  simpa only [row78,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_78
theorem leading_binding_79 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row79 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_99 X Y Z W a b hX hY hZ hW v hv
  simpa only [row79,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_79

theorem leading_binding_80 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row80 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_100 X Y Z W a b hX hY hZ hW v hv
  simpa only [row80,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_80
theorem leading_binding_81 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row81 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_101 X Y Z W a b hX hY hZ hW v hv
  simpa only [row81,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_81
theorem leading_binding_82 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row82 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_102 X Y Z W a b hX hY hZ hW v hv
  simpa only [row82,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_82
theorem leading_binding_83 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row83 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_103 X Y Z W a b hX hY hZ hW v hv
  simpa only [row83,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_83
theorem leading_binding_84 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row84 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_104 X Y Z W a b hX hY hZ hW v hv
  simpa only [row84,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_84
theorem leading_binding_85 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row85 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_105 X Y Z W a b hX hY hZ hW v hv
  simpa only [row85,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_85
theorem leading_binding_86 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row86 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_107 X Y Z W a b hX hY hZ hW v hv
  simpa only [row86,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_86
theorem leading_binding_87 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row87 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_108 X Y Z W a b hX hY hZ hW v hv
  simpa only [row87,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_87

theorem leading_binding_88 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row88 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_109 X Y Z W a b hX hY hZ hW v hv
  simpa only [row88,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_88
theorem leading_binding_89 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row89 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_110 X Y Z W a b hX hY hZ hW v hv
  simpa only [row89,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_89

end SmallLevelThirtyFourFiniteJetMMM
end
end

/-! ## ThirtyFourFiniteJetMMMLeadingBindings -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourFiniteJetMMM
open Complex SmallLevelThirtyFourUnitMMM
theorem leading_rows_of_source (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    ∀ i : Fin 90,rows X Y Z W a b ![v 370,v 390,v 435] ⟨i.val,by omega⟩=0 := by
  intro i
  fin_cases i
  · exact leading_binding_0 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_1 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_2 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_3 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_4 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_5 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_6 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_7 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_8 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_9 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_10 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_11 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_12 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_13 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_14 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_15 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_16 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_17 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_18 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_19 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_20 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_21 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_22 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_23 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_24 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_25 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_26 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_27 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_28 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_29 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_30 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_31 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_32 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_33 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_34 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_35 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_36 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_37 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_38 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_39 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_40 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_41 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_42 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_43 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_44 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_45 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_46 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_47 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_48 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_49 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_50 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_51 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_52 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_53 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_54 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_55 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_56 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_57 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_58 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_59 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_60 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_61 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_62 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_63 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_64 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_65 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_66 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_67 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_68 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_69 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_70 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_71 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_72 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_73 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_74 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_75 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_76 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_77 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_78 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_79 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_80 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_81 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_82 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_83 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_84 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_85 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_86 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_87 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_88 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_89 X Y Z W a b hX hY hZ hW v hv

#print axioms leading_rows_of_source

end SmallLevelThirtyFourFiniteJetMMM
end
end

/-! ## ThirtyFourJetOperatorMMM -/
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourJetOperatorMMM
open Complex SmallLevelThirtyFourUnitMMMInhomogeneous

theorem jet_value_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsZero0 (X/2) (Y/3) (Z/17) (W/5) a b r=
      SmallLevelThirtyFourFiniteJetMMM.row90 X Y Z W a b v := by
  have hs:=hr 265 (by decide)
  change r 265=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsZero0,hs]
  rw [pivot_value_70 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_110 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_126 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_235 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_236 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_256 X Y Z W a b hX hY hZ hW v r hr]
  unfold SmallLevelThirtyFourFiniteJetMMM.row90
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms jet_value_0

theorem jet_value_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsZero5 (X/2) (Y/3) (Z/17) (W/5) a b r=
      SmallLevelThirtyFourFiniteJetMMM.row95 X Y Z W a b v := by
  have hs:=hr 354 (by decide)
  change r 354=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsZero5,hs]
  rw [pivot_value_102 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_150 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_189 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_233 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_235 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_257 X Y Z W a b hX hY hZ hW v r hr]
  unfold SmallLevelThirtyFourFiniteJetMMM.row95
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms jet_value_5

theorem jet_value_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : SourceValues X Y Z W a b v r) :
    rhsZero8 (X/2) (Y/3) (Z/17) (W/5) a b r=
      SmallLevelThirtyFourFiniteJetMMM.row98 X Y Z W a b v := by
  have hs:=hr 447 (by decide)
  change r 447=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsZero8,hs]
  rw [pivot_value_89 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_102 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_131 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_141 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_194 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_235 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_256 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_331 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_335 X Y Z W a b hX hY hZ hW v r hr]
  unfold SmallLevelThirtyFourFiniteJetMMM.row98
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms jet_value_8

end SmallLevelThirtyFourJetOperatorMMM
end
end

/-! ## ThirtyFourJetSourceMMM -/
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourJetSourceMMM
open Complex SmallLevelThirtyFourUnitMMM SmallLevelThirtyFourJetOperatorMMM SmallLevelThirtyFourSlopeLiteralMMM
theorem actual_source_values (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    SourceValues X Y Z W a b ![v 370,v 390,v 435]
      (sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v) := by
  intro i hi
  simp only [requiredSources,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact source_value_1 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_3 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_4 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_6 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_7 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_8 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_9 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_10 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_12 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_20 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_21 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_22 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_24 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_25 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_28 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_29 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_30 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_31 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_32 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_34 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_35 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_37 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_38 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_42 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_43 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_61 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_62 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_63 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_64 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_66 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_67 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_68 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_69 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_71 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_73 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_77 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_78 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_79 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_81 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_82 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_83 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_84 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_85 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_86 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_94 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_95 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_98 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_99 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_102 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_105 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_106 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_107 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_108 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_142 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_144 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_148 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_152 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_157 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_170 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_172 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_173 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_174 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_176 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_183 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_189 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_199 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_201 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_202 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_225 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_246 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_260 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_263 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_266 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_275 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_277 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_279 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_285 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_286 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_288 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_290 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_296 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_297 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_305 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_319 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_326 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_328 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_331 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_344 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_352 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_355 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_379 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_384 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_393 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_399 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_401 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_404 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_411 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_485 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_636 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_675 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_1177 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_1585 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2331 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2334 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2338 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2339 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2340 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2341 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2356 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2386 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2395 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2396 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2407 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2425 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2441 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2459 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2461 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2464 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2465 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2469 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2475 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2480 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2485 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2486 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2498 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2504 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2512 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2523 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2525 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2526 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2530 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2546 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2547 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2559 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2568 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2575 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2586 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2588 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2599 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2601 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2619 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2620 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2656 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2664 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2672 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2675 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2686 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2692 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2699 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2746 X Y Z W a b hX hY hZ hW v hv

#print axioms actual_source_values

theorem actual_jet_value_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    SmallLevelThirtyFourUnitMMMInhomogeneous.rhsZero0 (X/2) (Y/3) (Z/17) (W/5) a b
      (sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v)=
      SmallLevelThirtyFourFiniteJetMMM.row90 X Y Z W a b ![v 370,v 390,v 435] :=
  jet_value_0 X Y Z W a b hX hY hZ hW _ _ (actual_source_values X Y Z W a b hX hY hZ hW v hv)

#print axioms actual_jet_value_0

theorem actual_jet_value_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    SmallLevelThirtyFourUnitMMMInhomogeneous.rhsZero5 (X/2) (Y/3) (Z/17) (W/5) a b
      (sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v)=
      SmallLevelThirtyFourFiniteJetMMM.row95 X Y Z W a b ![v 370,v 390,v 435] :=
  jet_value_5 X Y Z W a b hX hY hZ hW _ _ (actual_source_values X Y Z W a b hX hY hZ hW v hv)

#print axioms actual_jet_value_5

theorem actual_jet_value_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    SmallLevelThirtyFourUnitMMMInhomogeneous.rhsZero8 (X/2) (Y/3) (Z/17) (W/5) a b
      (sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v)=
      SmallLevelThirtyFourFiniteJetMMM.row98 X Y Z W a b ![v 370,v 390,v 435] :=
  jet_value_8 X Y Z W a b hX hY hZ hW _ _ (actual_source_values X Y Z W a b hX hY hZ hW v hv)

#print axioms actual_jet_value_8

end SmallLevelThirtyFourJetSourceMMM
end
end

/-! ## ThirtyFourPhysicalFiniteMMM -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourPhysicalFiniteMMM
open Complex Matrix SmallLevelThirtyFourGrid SmallLevelPrimeRates SmallLevelFiniteGridSupport
open SmallLevelThirtyFourUnitMMM SmallLevelThirtyFourUnitMMMInhomogeneous
theorem source_kernel (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= -v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0) :
    ∀ i,sourceRows (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) (extension supportIndex w) i=0 := by
  intro i
  rw [scaled_sourceRows_actual m f ε u v x hu hv hη h₂ h₁₇]
  have h:=congrFun hlead i
  simpa only [SmallLevelThirtyFourUnitMMM.leadingMatrix,restrictedLeadingMatrix_mulVec,
    Pi.zero_apply] using h

theorem finite_leading_rows (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= -v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0) :
    ∀ i : Fin 90,SmallLevelThirtyFourFiniteJetMMM.rows (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435] ⟨i.val,by omega⟩=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) x)
  have hW:=parameter_ne_zero 5 m (by decide) x
  have hs:=source_kernel m f ε u v x hu hv hη h₂ h₁₇ w hlead
  exact SmallLevelThirtyFourFiniteJetMMM.leading_rows_of_source (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW (extension supportIndex w) hs

theorem finite_jet_row_0 (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= -v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0)
    (hjet : firstJetMatrix m f ε u v x *ᵥ w=0) :
    SmallLevelThirtyFourFiniteJetMMM.row90 (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435]=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) x)
  have hW:=parameter_ne_zero 5 m (by decide) x
  have hs:=source_kernel m f ε u v x hu hv hη h₂ h₁₇ w hlead
  rw [←SmallLevelThirtyFourJetSourceMMM.actual_jet_value_0 (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW (extension supportIndex w) hs]
  have hj:=congrFun hjet (0:Fin 14)
  rw [firstJetMatrix_source_apply m f ε u v x hu hv hη h₂ h₁₇] at hj
  change rhsZero0 _ _ _ _ _ _ _=0 at hj
  simpa only [parameter_shift 2 m (by decide),parameter_shift 3 m (by decide),
    parameter_shift 17 m (by decide),parameter_shift 5 m (by decide),←mul_div_assoc,Nat.cast_ofNat] using hj

#print axioms finite_jet_row_0

theorem finite_jet_row_5 (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= -v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0)
    (hjet : firstJetMatrix m f ε u v x *ᵥ w=0) :
    SmallLevelThirtyFourFiniteJetMMM.row95 (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435]=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) x)
  have hW:=parameter_ne_zero 5 m (by decide) x
  have hs:=source_kernel m f ε u v x hu hv hη h₂ h₁₇ w hlead
  rw [←SmallLevelThirtyFourJetSourceMMM.actual_jet_value_5 (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW (extension supportIndex w) hs]
  have hj:=congrFun hjet (5:Fin 14)
  rw [firstJetMatrix_source_apply m f ε u v x hu hv hη h₂ h₁₇] at hj
  change rhsZero5 _ _ _ _ _ _ _=0 at hj
  simpa only [parameter_shift 2 m (by decide),parameter_shift 3 m (by decide),
    parameter_shift 17 m (by decide),parameter_shift 5 m (by decide),←mul_div_assoc,Nat.cast_ofNat] using hj

#print axioms finite_jet_row_5

theorem finite_jet_row_8 (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= -v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0)
    (hjet : firstJetMatrix m f ε u v x *ᵥ w=0) :
    SmallLevelThirtyFourFiniteJetMMM.row98 (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435]=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) x)
  have hW:=parameter_ne_zero 5 m (by decide) x
  have hs:=source_kernel m f ε u v x hu hv hη h₂ h₁₇ w hlead
  rw [←SmallLevelThirtyFourJetSourceMMM.actual_jet_value_8 (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW (extension supportIndex w) hs]
  have hj:=congrFun hjet (8:Fin 14)
  rw [firstJetMatrix_source_apply m f ε u v x hu hv hη h₂ h₁₇] at hj
  change rhsZero8 _ _ _ _ _ _ _=0 at hj
  simpa only [parameter_shift 2 m (by decide),parameter_shift 3 m (by decide),
    parameter_shift 17 m (by decide),parameter_shift 5 m (by decide),←mul_div_assoc,Nat.cast_ofNat] using hj

#print axioms finite_jet_row_8

#print axioms finite_leading_rows
end SmallLevelThirtyFourPhysicalFiniteMMM
end
end

/-! ## ThirtyFourCriticalMMMData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourCriticalMMM
def critical_mmm_row (b w z A Y : ℂ) (i : Fin 18) : ℂ :=
  match i.val with
  | 0 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (9/2:ℂ)*b*w + (12:ℂ)*w^2*A + (12:ℂ)*w^2*Y + (39:ℂ)*w^2 + (16/3:ℂ)*z*A + (16/3:ℂ)*z*Y + (39:ℂ)*z + (-10/3:ℂ)*A^2*Y + (-17:ℂ)*A^2 + (-13/3:ℂ)*A*Y^2 + (-142/3:ℂ)*A*Y + (5/6:ℂ)*A + (-1:ℂ)*Y^3 + (-63/2:ℂ)*Y^2 + (-505/6:ℂ)*Y + (-541/3:ℂ)
  | 1 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (9/2:ℂ)*b*w + (8:ℂ)*w^2*A + (8:ℂ)*w^2*Y + (-17/3:ℂ)*w^2 + (-12:ℂ)*z*A + (-12:ℂ)*z*Y + (-137/3:ℂ)*z + (-10/3:ℂ)*A^2*Y + (97/3:ℂ)*A^2 + (-13/3:ℂ)*A*Y^2 + (58:ℂ)*A*Y + (35/2:ℂ)*A + (-1:ℂ)*Y^3 + (49/2:ℂ)*Y^2 + (125/2:ℂ)*Y + (367/3:ℂ)
  | 2 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (67/6:ℂ)*b*w + (23/3:ℂ)*w^2*A + (23/3:ℂ)*w^2*Y + (107/6:ℂ)*w^2 + (1:ℂ)*z*A + (1:ℂ)*z*Y + (67/6:ℂ)*z + (-1:ℂ)*A^2 + (-20/3:ℂ)*A*Y + (-107/6:ℂ)*A + (-17/3:ℂ)*Y^2 + (67/6:ℂ)*Y + (-40:ℂ)
  | 3 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (9/2:ℂ)*b*w + (11:ℂ)*w^2*A + (11:ℂ)*w^2*Y + (167/6:ℂ)*w^2 + (1:ℂ)*z*A + (1:ℂ)*z*Y + (107/6:ℂ)*z + (-10/3:ℂ)*A^2*Y + (-14/3:ℂ)*A^2 + (-13/3:ℂ)*A*Y^2 + (-21:ℂ)*A*Y + (5:ℂ)*A + (-1:ℂ)*Y^3 + (-35/2:ℂ)*Y^2 + (-95/2:ℂ)*Y + (-314/3:ℂ)
  | 4 => (1:ℂ)*b*w + (-19/20:ℂ)*w^2*A + (-19/20:ℂ)*w^2*Y + (-261/40:ℂ)*w^2 + (-39/20:ℂ)*z*A + (-39/20:ℂ)*z*Y + (-421/40:ℂ)*z + (1/2:ℂ)*A^2*Y + (61/10:ℂ)*A^2 + (13/20:ℂ)*A*Y^2 + (14:ℂ)*A*Y + (-31/20:ℂ)*A + (3/20:ℂ)*Y^3 + (323/40:ℂ)*Y^2 + (253/10:ℂ)*Y + (175/4:ℂ)
  | 5 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (7/6:ℂ)*b*w + (79/6:ℂ)*w^2*A + (79/6:ℂ)*w^2*Y + (461/12:ℂ)*w^2 + (19/6:ℂ)*z*A + (19/6:ℂ)*z*Y + (127/4:ℂ)*z + (-5:ℂ)*A^2*Y + (-38/3:ℂ)*A^2 + (-13/2:ℂ)*A*Y^2 + (-124/3:ℂ)*A*Y + (43/3:ℂ)*A + (-3/2:ℂ)*Y^3 + (-365/12:ℂ)*Y^2 + (-571/6:ℂ)*Y + (-1049/6:ℂ)
  | 6 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (-13/6:ℂ)*b*w + (43/3:ℂ)*w^2*A + (43/3:ℂ)*w^2*Y + (227/6:ℂ)*w^2 + (1:ℂ)*z*A + (1:ℂ)*z*Y + (49/2:ℂ)*z + (-20/3:ℂ)*A^2*Y + (-25/3:ℂ)*A^2 + (-26/3:ℂ)*A*Y^2 + (-106/3:ℂ)*A*Y + (167/6:ℂ)*A + (-2:ℂ)*Y^3 + (-88/3:ℂ)*Y^2 + (-637/6:ℂ)*Y + (-508/3:ℂ)
  | 7 => (1:ℂ)*w^2*A + (1:ℂ)*w^2*Y + (67/6:ℂ)*w^2 + (13/3:ℂ)*z*A + (13/3:ℂ)*z*Y + (127/6:ℂ)*z + (-37/3:ℂ)*A^2 + (-79/3:ℂ)*A*Y + (-25/6:ℂ)*A + (-14:ℂ)*Y^2 + (-110/3:ℂ)*Y + (-227/3:ℂ)
  | 8 => (1:ℂ)*A^2 + (95/6:ℂ)*A + (-1:ℂ)*Y^2 + (-13/2:ℂ)*Y + (-67/3:ℂ)
  | 9 => (1:ℂ)*b*w*A^2 + (1:ℂ)*b*w*A*Y + (-13/6:ℂ)*b*w*A + (43/3:ℂ)*w^2*A^2 + (43/3:ℂ)*w^2*A*Y + (239/6:ℂ)*w^2*A + (2:ℂ)*w^2*Y + (67/3:ℂ)*w^2 + (1:ℂ)*z*A^2 + (1:ℂ)*z*A*Y + (199/6:ℂ)*z*A + (26/3:ℂ)*z*Y + (127/3:ℂ)*z + (-20/3:ℂ)*A^3*Y + (-25/3:ℂ)*A^3 + (-26/3:ℂ)*A^2*Y^2 + (-106/3:ℂ)*A^2*Y + (25/6:ℂ)*A^2 + (-2:ℂ)*A*Y^3 + (-88/3:ℂ)*A*Y^2 + (-953/6:ℂ)*A*Y + (-971/6:ℂ)*A + (-29:ℂ)*Y^2 + (-479/6:ℂ)*Y + (-521/3:ℂ)
  | 10 => (1:ℂ)*w^2*A + (1:ℂ)*w^2*Y + (67/6:ℂ)*w^2 + (13/3:ℂ)*z*A + (13/3:ℂ)*z*Y + (127/6:ℂ)*z + (-77/6:ℂ)*A^2 + (-79/3:ℂ)*A*Y + (-145/12:ℂ)*A + (-27/2:ℂ)*Y^2 + (-401/12:ℂ)*Y + (-129/2:ℂ)
  | 11 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (127/26:ℂ)*b*w + (1:ℂ)*w^2*A + (1:ℂ)*w^2*Y + (127/26:ℂ)*w^2 + (10/13:ℂ)*A^2 + (1:ℂ)*A + (-10/13:ℂ)*Y^2 + (-7/13:ℂ)*Y + (107/26:ℂ)
  | 12 => (1:ℂ)*b*w*A^2 + (13/10:ℂ)*b*w*A*Y + (8/5:ℂ)*b*w*A + (3/10:ℂ)*b*w*Y^2 + (39/20:ℂ)*b*w*Y + (67/10:ℂ)*b*w + (13/10:ℂ)*w^2*A^2 + (13/10:ℂ)*w^2*A*Y + (127/20:ℂ)*w^2*A + (1:ℂ)*A^3 + (1:ℂ)*A^2 + (-1:ℂ)*A*Y^2 + (-7/10:ℂ)*A*Y + (3/5:ℂ)*A + (3/10:ℂ)*Y^2 + (39/20:ℂ)*Y + (67/10:ℂ)
  | 13 => (1:ℂ)*b*w*z*A + (1:ℂ)*b*w*z*Y + (127/26:ℂ)*b*w*z + (1:ℂ)*w^2*z*A + (1:ℂ)*w^2*z*Y + (127/26:ℂ)*w^2*z + (10/13:ℂ)*z*A^2 + (1:ℂ)*z*A + (-10/13:ℂ)*z*Y^2 + (-7/13:ℂ)*z*Y + (107/26:ℂ)*z
  | 14 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (57/16:ℂ)*b*w + (7/2:ℂ)*w^2*A + (7/2:ℂ)*w^2*Y + (177/16:ℂ)*w^2 + (3/16:ℂ)*z*A + (3/16:ℂ)*z*Y + (147/32:ℂ)*z + (-5/4:ℂ)*A^2*Y + (-15/16:ℂ)*A^2 + (-13/8:ℂ)*A*Y^2 + (-53/8:ℂ)*A*Y + (193/32:ℂ)*A + (-3/8:ℂ)*Y^3 + (-49/8:ℂ)*Y^2 + (-651/32:ℂ)*Y + (-909/32:ℂ)
  | 15 => (1:ℂ)*b*w*A^2 + (13/10:ℂ)*b*w*A*Y + (8/5:ℂ)*b*w*A + (3/10:ℂ)*b*w*Y^2 + (39/20:ℂ)*b*w*Y + (67/10:ℂ)*b*w + (13/10:ℂ)*w^2*A^2 + (13/10:ℂ)*w^2*A*Y + (127/20:ℂ)*w^2*A + (1:ℂ)*A^3 + (13/10:ℂ)*A^2 + (-1:ℂ)*A*Y^2 + (-7/10:ℂ)*A*Y + (107/20:ℂ)*A
  | 16 => (1:ℂ)*b*w*A*Y + (-1:ℂ)*b*w*A + (1:ℂ)*b*w*Y^2 + (101/26:ℂ)*b*w*Y + (-127/26:ℂ)*b*w + (1:ℂ)*w^2*A*Y + (-1:ℂ)*w^2*A + (1:ℂ)*w^2*Y^2 + (101/26:ℂ)*w^2*Y + (-127/26:ℂ)*w^2 + (10/13:ℂ)*A^2*Y + (-10/13:ℂ)*A^2 + (1:ℂ)*A*Y + (-1:ℂ)*A + (-10/13:ℂ)*Y^3 + (3/13:ℂ)*Y^2 + (121/26:ℂ)*Y + (-107/26:ℂ)
  | _ => (1:ℂ)*A^2 + (85/69:ℂ)*A*Y + (275/46:ℂ)*A + (16/69:ℂ)*Y^2 + (104/69:ℂ)*Y + (393/23:ℂ)
/-- Explicit rational Nullstellensatz identity, checked by Lean's ring
normalizer. No external polynomial-system solver is trusted. -/

def remainder0 (b w z A Y : ℂ) : ℂ := ((396517998815621857445641994115836121960:ℂ))

def remainder1 (b w z A Y : ℂ) : ℂ := ((2662851286082254481913426211754637232710:ℂ)) + ((1792675881003011969446086342255433986915:ℂ)*Y) + ((738880390367955746707637585893136196975:ℂ)*Y^2) + ((140939698350016886886664111530068115330:ℂ)*Y^3) + ((4075308919142049580863300277842352320:ℂ)*Y^4) + ((-1810861446560905282213688685178219594575:ℂ)*A) + ((-248828223606319721256304794820098507600:ℂ)*A*Y) + ((-67128635821156003049827098103448111670:ℂ)*A*Y^2) + ((7676001611063280715008884062413150120:ℂ)*A*Y^3) + ((221966671059624193856047111511220273750:ℂ)*A^2) + ((-361388587987029178124853130717564445460:ℂ)*A^2*Y) + ((-29678208547697438206072473353997124200:ℂ)*A^2*Y^2) + ((-169722396322055213635112091406696402200:ℂ)*A^3) + ((-33278901239618669340218057138567922000:ℂ)*A^3*Y) + ((-490131228484650678489335958343326672750:ℂ)*z) + ((-225963540630765667464176192318699832480:ℂ)*z*Y) + ((-21734980902090931097937601481825879040:ℂ)*z*Y^2) + ((322336651719312697470043787038396595400:ℂ)*z*A) + ((31511261081298939846411289939882796160:ℂ)*z*A*Y) + ((53246241983389870944348891421708675200:ℂ)*z*A^2) + ((-490131228484650678489335958343326672750:ℂ)*w^2) + ((-309746656611047834727310544172259947480:ℂ)*w^2*Y) + ((-48903707029704594970359603334108227840:ℂ)*w^2*Y^2) + ((238553535739030530206909435184836480400:ℂ)*w^2*A) + ((70900337432922614654425402364736291360:ℂ)*w^2*A*Y) + ((119804044462627209624785005698844519200:ℂ)*w^2*A^2) + ((-56553603286690462902615687501153077625:ℂ)*b*w) + ((-30906357533181548203355004028324602690:ℂ)*b*w*Y) + ((-4075308919142049580863300277842352320:ℂ)*b*w*Y^2) + ((32359049276442878519824224359032677450:ℂ)*b*w*A) + ((5908361452743551221202116863728024280:ℂ)*b*w*A*Y) + ((9983670371885600802065417141570376600:ℂ)*b*w*A^2)

def remainder2 (b w z A Y : ℂ) : ℂ := ((4699038382352323607753601999050975357400:ℂ)) + ((3389795724542559292523583813919284408900:ℂ)*Y) + ((1431158419447223260008110798413511971620:ℂ)*Y^2) + ((235813547039162125312363310714155941000:ℂ)*Y^3) + ((-476463728105518664674389035670325920:ℂ)*Y^4) + ((-2678541909497455684632001396807025670120:ℂ)*A) + ((204101465272311360746746855122353534280:ℂ)*A*Y) + ((-107360260442180735152708066521690688920:ℂ)*A*Y^2) + ((-2574553883544362847456662298246721440:ℂ)*A*Y^3) + ((594350090911236633655084844116843508640:ℂ)*A^2) + ((-819176516275070575907852698115144400240:ℂ)*A^2*Y) + ((-3797682583507006295674417074827425920:ℂ)*A^2*Y^2) + ((-476041691794095133740173450671970250720:ℂ)*A^3) + ((-1699592428068162112892143812251030400:ℂ)*A^3*Y) + ((-1250233768509172395764823922538417471340:ℂ)*z) + ((-633562798876113487090087605599452299960:ℂ)*z*Y) + ((-76356252669061750044389873243978017920:ℂ)*z*Y^2) + ((555238208416512443404718531645264515800:ℂ)*z*A) + ((90575501035909946918332306152471467040:ℂ)*z*A*Y) + ((166931753704971696962722179396449484960:ℂ)*z*A^2) + ((-584450521772365052165856362659505822940:ℂ)*w^2) + ((-202383385598089252732230604973049461160:ℂ)*w^2*Y) + ((-12489525851724049006058088826006801920:ℂ)*w^2*Y^2) + ((425395010066027861213156999815357525800:ℂ)*w^2*A) + ((31524177463181943273144724889677177440:ℂ)*w^2*A*Y) + ((44013703314905992279202813715683979360:ℂ)*w^2*A^2) + ((18347011971200363252268162985224482820:ℂ)*b*w) + ((6221200547852692491538786879455240600:ℂ)*b*w*Y) + ((476463728105518664674389035670325920:ℂ)*b*w*Y^2) + ((6371563549269877352908430365477665000:ℂ)*b*w*A) + ((986341456525967298542032179345635040:ℂ)*b*w*A*Y) + ((509877728420448633867643143675309120:ℂ)*b*w*A^2)

def remainder3 (b w z A Y : ℂ) : ℂ := ((4609459423647727688917332384716995330200:ℂ)) + ((3368559537617637773582344605715915418760:ℂ)*Y) + ((1420780644946946181265391066879358010320:ℂ)*Y^2) + ((232220722746197243084392890203427820800:ℂ)*Y^3) + ((-1977720494973305761872484124063817600:ℂ)*Y^4) + ((-2615390849663750238380724247356632362380:ℂ)*A) + ((129178743477299009542892363667335221800:ℂ)*A*Y) + ((-102229536953602522314715614734330970000:ℂ)*A*Y^2) + ((-5841995082021311235476045725926673920:ℂ)*A*Y^3) + ((638070837685609140796838659529255075220:ℂ)*A^2) + ((-807875759853789869340245308671032576040:ℂ)*A^2*Y) + ((-5828794679857541780118898665006855840:ℂ)*A^2*Y^2) + ((-473464483154357522238528933525946265640:ℂ)*A^3) + ((-1964520092809536306515337063143999520:ℂ)*A^3*Y) + ((-1225226309204139368423031988536848047080:ℂ)*z) + ((-618413640335969611615168004708890825260:ℂ)*z*Y) + ((-72241802590367541225188436720549735720:ℂ)*z*Y^2) + ((264927664741374193623193250892969120:ℂ)*z*Y^3) + ((528698852573724012940594830539679516420:ℂ)*z*A) + ((92112742474866544235889225529875764160:ℂ)*z*A*Y) + ((529855329482748387246386501785938240:ℂ)*z*A*Y^2) + ((164354545065234085461077662250425499880:ℂ)*z*A^2) + ((264927664741374193623193250892969120:ℂ)*z*A^2*Y) + ((-544513236016566038351352826268939727480:ℂ)*w^2) + ((-164597126235520299737427544659334912860:ℂ)*w^2*Y) + ((1098383030238412151136493070864343480:ℂ)*w^2*Y^2) + ((2031112096350535484444481590179429920:ℂ)*w^2*Y^3) + ((396604089742421340544114786791942630420:ℂ)*w^2*A) + ((25353486773822716251064675333697770560:ℂ)*w^2*A*Y) + ((4062224192701070968888963180358859840:ℂ)*w^2*A*Y^2) + ((24255103743584304099928182262833427080:ℂ)*w^2*A^2) + ((2031112096350535484444481590179429920:ℂ)*w^2*A^2*Y) + ((43354471276233390594060096986793907080:ℂ)*b*w) + ((21370359087996567966458387770016715300:ℂ)*b*w*Y) + ((4590913806799727483875825559098608120:ℂ)*b*w*Y^2) + ((264927664741374193623193250892969120:ℂ)*b*w*Y^3) + ((-20167792293518553111215270740107334380:ℂ)*b*w*A) + ((2523582895482564616098951556749932160:ℂ)*b*w*A*Y) + ((529855329482748387246386501785938240:ℂ)*b*w*A*Y^2) + ((-2067330911317162867776874002348675960:ℂ)*b*w*A^2) + ((264927664741374193623193250892969120:ℂ)*b*w*A^2*Y)

def remainder4 (b w z A Y : ℂ) : ℂ := ((4609459423647727688917332384716995330200:ℂ)) + ((3368559537617637773582344605715915418760:ℂ)*Y) + ((1604808005771510248160420234932928467920:ℂ)*Y^2) + ((321396976890259125720750636837316588800:ℂ)*Y^3) + ((32071394723668503972009564590693712000:ℂ)*Y^4) + ((-2615390849663750238380724247356632362380:ℂ)*A) + ((212433959969588017992151497625782498600:ℂ)*A*Y) + ((-51751934202682514536713987703058586000:ℂ)*A*Y^2) + ((73606818124219656339749451641856814080:ℂ)*A*Y^3) + ((638070837685609140796838659529255075220:ℂ)*A^2) + ((-803291221500690254337532801294466096040:ℂ)*A^2*Y) + ((53141136832916476469253571822655883360:ℂ)*A^2*Y^2) + ((-473464483154357522238528933525946265640:ℂ)*A^3) + ((11605713432365324101513684771492781280:ℂ)*A^3*Y) + ((-1225226309204139368423031988536848047080:ℂ)*z) + ((-618413640335969611615168004708890825260:ℂ)*z*Y) + ((-123720822028075991656176772277385524520:ℂ)*z*Y^2) + ((-10274084188647757390673631351293885280:ℂ)*z*Y^3) + ((528698852573724012940594830539679516420:ℂ)*z*A) + ((68823287641120500022109688056918045760:ℂ)*z*A*Y) + ((-14777076411129982799871445772030055360:ℂ)*z*A*Y^2) + ((164354545065234085461077662250425499880:ℂ)*z*A^2) + ((-4502992222482225409197814420736170080:ℂ)*z*A^2*Y) + ((-544513236016566038351352826268939727480:ℂ)*w^2) + ((-164597126235520299737427544659334912860:ℂ)*w^2*Y) + ((-26059839822725888469936093404001781320:ℂ)*w^2*Y^2) + ((-400967562123879496547093318017536480:ℂ)*w^2*Y^3) + ((396604089742421340544114786791942630420:ℂ)*w^2*A) + ((13066923987515748043795155564499604160:ℂ)*w^2*A*Y) + ((529855329482748387246386501785938240:ℂ)*w^2*A*Y^2) + ((24255103743584304099928182262833427080:ℂ)*w^2*A^2) + ((930822891606627883793479819803474720:ℂ)*w^2*A^2*Y) + ((43354471276233390594060096986793907080:ℂ)*b*w) + ((21370359087996567966458387770016715300:ℂ)*b*w*Y) + ((4590913806799727483875825559098608120:ℂ)*b*w*Y^2) + ((264927664741374193623193250892969120:ℂ)*b*w*Y^3) + ((-20167792293518553111215270740107334380:ℂ)*b*w*A) + ((2523582895482564616098951556749932160:ℂ)*b*w*A*Y) + ((529855329482748387246386501785938240:ℂ)*b*w*A*Y^2) + ((-2067330911317162867776874002348675960:ℂ)*b*w*A^2) + ((264927664741374193623193250892969120:ℂ)*b*w*A^2*Y)

def remainder5 (b w z A Y : ℂ) : ℂ := ((15908017002857327120623509439207308770928:ℂ)) + ((5306959972506347728955742494391209724772:ℂ)*Y) + ((1188345837259111936855849005153742104728:ℂ)*Y^2) + ((106852869044533427663744480757314102208:ℂ)*Y^3) + ((8364166142749958027113759371810562368:ℂ)*Y^4) + ((-6032321506155841403914313868952275029940:ℂ)*A) + ((2041343320245253769809447384929075603442:ℂ)*A*Y) + ((393941632555999404598979356370743142632:ℂ)*A*Y^2) + ((52785528499484404531025857309957694568:ℂ)*A*Y^3) + ((-3124236758043218675921663144083618596582:ℂ)*A^2) + ((-413173680372626951284225802215468023116:ℂ)*A^2*Y) + ((76848365413835022414149377041539032992:ℂ)*A^2*Y^2) + ((-679131979942608267336742058124775735260:ℂ)*A^3) + ((32427003057100575910237279103391900792:ℂ)*A^3*Y) + ((66603926478184955632646482916737110096:ℂ)*z) + ((-21177954512971222013389501387151086176:ℂ)*z*Y) + ((-1482494164032605394705787964220492288:ℂ)*z*Y^2) + ((-367132960533098590784950445160012288:ℂ)*z*Y^3) + ((-154610731705609004564007516386100215592:ℂ)*z*A) + ((-20357160207205441605040832039362069152:ℂ)*z*A*Y) + ((-4364828216746984435088841528311151648:ℂ)*z*A*Y^2) + ((-58349196227128159376841463365085333344:ℂ)*z*A^2) + ((-14409943450596884209086495326870043072:ℂ)*z*A^2*Y) + ((-10412248194382998364782604243718903712:ℂ)*z*A^3) + ((16093558136012685079460001590873936880:ℂ)*w^2) + ((13436212726290541734597165975681798600:ℂ)*w^2*Y) + ((3370275904998800371281791436893236320:ℂ)*w^2*Y^2) + ((264927664741374193623193250892969120:ℂ)*w^2*Y^3) + ((-841025515003873828476397138522280880:ℂ)*w^2*A) + ((2523582895482564616098951556749932160:ℂ)*w^2*A*Y) + ((529855329482748387246386501785938240:ℂ)*w^2*A*Y^2) + ((-846693009516235755182839880143304160:ℂ)*w^2*A^2) + ((264927664741374193623193250892969120:ℂ)*w^2*A^2*Y) + ((16093558136012685079460001590873936880:ℂ)*b*w) + ((13436212726290541734597165975681798600:ℂ)*b*w*Y) + ((3370275904998800371281791436893236320:ℂ)*b*w*Y^2) + ((264927664741374193623193250892969120:ℂ)*b*w*Y^3) + ((-841025515003873828476397138522280880:ℂ)*b*w*A) + ((2523582895482564616098951556749932160:ℂ)*b*w*A*Y) + ((529855329482748387246386501785938240:ℂ)*b*w*A*Y^2) + ((-846693009516235755182839880143304160:ℂ)*b*w*A^2) + ((264927664741374193623193250892969120:ℂ)*b*w*A^2*Y)

def remainder6 (b w z A Y : ℂ) : ℂ := ((15894457863325410921383334477237044902848:ℂ)) + ((5300189678648244664434129047730588805372:ℂ)*Y) + ((1190907933789538152003158912908904242808:ℂ)*Y^2) + ((108592604062465596225493686427789519488:ℂ)*Y^3) + ((8567956654089476637593138795574384768:ℂ)*Y^4) + ((-6032131782955850019128285810183093752260:ℂ)*A) + ((2037720923231085745718931136057407487282:ℂ)*A*Y) + ((393168055934183204390243390347143845992:ℂ)*A*Y^2) + ((52989319010823923141505236733721516968:ℂ)*A*Y^3) + ((-3125924483637798926005765343824085361222:ℂ)*A^2) + ((-415035689697362831012262635540201733836:ℂ)*A^2*Y) + ((76644574902495503803669997617775210592:ℂ)*A^2*Y^2) + ((-678480677627595778294293719755434732060:ℂ)*A^3) + ((32223212545761057299757899679628078392:ℂ)*A^3*Y) + ((66603926478184955632646482916737110096:ℂ)*z) + ((-21177954512971222013389501387151086176:ℂ)*z*Y) + ((-1482494164032605394705787964220492288:ℂ)*z*Y^2) + ((-367132960533098590784950445160012288:ℂ)*z*Y^3) + ((-154610731705609004564007516386100215592:ℂ)*z*A) + ((-20357160207205441605040832039362069152:ℂ)*z*A*Y) + ((-4364828216746984435088841528311151648:ℂ)*z*A*Y^2) + ((-58349196227128159376841463365085333344:ℂ)*z*A^2) + ((-14409943450596884209086495326870043072:ℂ)*z*A^2*Y) + ((-10412248194382998364782604243718903712:ℂ)*z*A^3)

def remainder7 (b w z A Y : ℂ) : ℂ := 0

def coefficient0 (b w z A Y : ℂ) : ℂ := ((12567467397042325089470152778034017250:ℂ)) + ((4075308919142049580863300277842352320:ℂ)*Y) + ((-9983670371885600802065417141570376600:ℂ)*A)

def coefficient1 (b w z A Y : ℂ) : ℂ := ((-16644581168420183589974188996972791210:ℂ)) + ((-4551772647247568245537689313512678240:ℂ)*Y) + ((9473792643465152168197773997895067480:ℂ)*A)

def coefficient2 (b w z A Y : ℂ) : ℂ := ((-2239473967614897970906740358349500680:ℂ)) + ((-1156091155748863657075778555123460360:ℂ)*Y) + ((-264927664741374193623193250892969120:ℂ)*Y^2) + ((2577208639737611501644517146023985080:ℂ)*A) + ((-264927664741374193623193250892969120:ℂ)*A*Y)

def coefficient3 (b w z A Y : ℂ) : ℂ := ((2432079658474414980991574908196966400:ℂ)*Y^2) + ((1100289204743907600651001770375955200:ℂ)*A*Y)

def coefficient4 (b w z A Y : ℂ) : ℂ := ((505905563248191019330127330798073736152:ℂ)) + ((-60447122069755149415183422157262013984:ℂ)*Y) + ((-23707228580918545944895805218883149632:ℂ)*Y^2) + ((205667496788250745098213124598829469620:ℂ)*A) + ((-20821289624735251808723594331899119512:ℂ)*A*Y) + ((57843144881298104062194558423294857784:ℂ)*z) + ((9906951228114658799888680906133872992:ℂ)*z*Y) + ((10412248194382998364782604243718903712:ℂ)*z*A) + ((25101796753100539855111022142976731240:ℂ)*w^2) + ((665895226865253690170286568910505600:ℂ)*w^2*Y) + ((-1220637901800927112594034122205371800:ℂ)*b*w)

def coefficient5 (b w z A Y : ℂ) : ℂ := ((3294744185325431591070551506793089440:ℂ)) + ((2076206157992857194737732095992964080:ℂ)*Y) + ((264927664741374193623193250892969120:ℂ)*Y^2) + ((-846693009516235755182839880143304160:ℂ)*A) + ((264927664741374193623193250892969120:ℂ)*A*Y)

def coefficient6 (b w z A Y : ℂ) : ℂ := ((930210002179349748579686241670361406528:ℂ)) + ((228135070059437241724908850856397829764:ℂ)*Y) + ((36949313070760867999620411055914534312:ℂ)*Y^2) + ((-678480677627595778294293719755434732060:ℂ)*A) + ((32223212545761057299757899679628078392:ℂ)*A*Y) + ((3897939717552809108271931570190721456:ℂ)*z) + ((-1583260892298987672760098794752552992:ℂ)*z*Y) + ((-10412248194382998364782604243718903712:ℂ)*z*A)

end SmallLevelThirtyFourCriticalMMM
end
end

/-! ## ThirtyFourCriticalMMMBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourCriticalMMM

theorem step0 (b w z A Y : ℂ) :
    remainder0 b w z A Y=remainder1 b w z A Y+
      coefficient0 b w z A Y*critical_mmm_row b w z A Y 0 := by
  norm_num [remainder0,remainder1,coefficient0,critical_mmm_row]
  ring

#print axioms step0

theorem step1 (b w z A Y : ℂ) :
    remainder1 b w z A Y=remainder2 b w z A Y+
      coefficient1 b w z A Y*critical_mmm_row b w z A Y 1 := by
  norm_num [remainder1,remainder2,coefficient1,critical_mmm_row]
  ring

#print axioms step1

theorem step2 (b w z A Y : ℂ) :
    remainder2 b w z A Y=remainder3 b w z A Y+
      coefficient2 b w z A Y*critical_mmm_row b w z A Y 2 := by
  norm_num [remainder2,remainder3,coefficient2,critical_mmm_row]
  ring

#print axioms step2

theorem step3 (b w z A Y : ℂ) :
    remainder3 b w z A Y=remainder4 b w z A Y+
      coefficient3 b w z A Y*critical_mmm_row b w z A Y 7 := by
  norm_num [remainder3,remainder4,coefficient3,critical_mmm_row]
  ring

#print axioms step3

theorem step4 (b w z A Y : ℂ) :
    remainder4 b w z A Y=remainder5 b w z A Y+
      coefficient4 b w z A Y*critical_mmm_row b w z A Y 8 := by
  norm_num [remainder4,remainder5,coefficient4,critical_mmm_row]
  ring

#print axioms step4

theorem step5 (b w z A Y : ℂ) :
    remainder5 b w z A Y=remainder6 b w z A Y+
      coefficient5 b w z A Y*critical_mmm_row b w z A Y 11 := by
  norm_num [remainder5,remainder6,coefficient5,critical_mmm_row]
  ring

#print axioms step5

theorem step6 (b w z A Y : ℂ) :
    remainder6 b w z A Y=remainder7 b w z A Y+
      coefficient6 b w z A Y*critical_mmm_row b w z A Y 17 := by
  norm_num [remainder6,remainder7,coefficient6,critical_mmm_row]
  ring

#print axioms step6

end SmallLevelThirtyFourCriticalMMM
end
end

/-! ## ThirtyFourCriticalMMM -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourCriticalMMM
theorem critical_mmm_impossible (b w z A Y : ℂ)
    (h : ∀ i : Fin 18,critical_mmm_row b w z A Y i=0) : False := by
  have h7 : remainder7 b w z A Y=0 := rfl
  have h6 : remainder6 b w z A Y=0 := by
    rw [step6,h 17,mul_zero,add_zero]
    exact h7
  have h5 : remainder5 b w z A Y=0 := by
    rw [step5,h 11,mul_zero,add_zero]
    exact h6
  have h4 : remainder4 b w z A Y=0 := by
    rw [step4,h 8,mul_zero,add_zero]
    exact h5
  have h3 : remainder3 b w z A Y=0 := by
    rw [step3,h 7,mul_zero,add_zero]
    exact h4
  have h2 : remainder2 b w z A Y=0 := by
    rw [step2,h 2,mul_zero,add_zero]
    exact h3
  have h1 : remainder1 b w z A Y=0 := by
    rw [step1,h 1,mul_zero,add_zero]
    exact h2
  have h0 : remainder0 b w z A Y=0 := by
    rw [step0,h 0,mul_zero,add_zero]
    exact h1
  norm_num [remainder0] at h0

#print axioms critical_mmm_impossible

end SmallLevelThirtyFourCriticalMMM
end
end

/-! ## ThirtyFourFiniteJetMMMCriticalRowBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourFiniteJetMMM
open Complex

theorem critical_row_0 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row3 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 0*v 2=0 := by
  norm_num only [Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row3,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((20*W^2)/(3)))*(hR-((2))*hL-(((3)/(850)) + (((-1)*W*b)/(1700)) + (((-1)*W^2)/(850)) + (((-1)*Z)/(850)) + (((-3)*Y*a)/(1700)) + ((7*Y^2)/(1700)) + ((1*Y^4)/(1700)))*hJ)

#print axioms critical_row_0

theorem critical_row_1 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row4 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 1*v 2=0 := by
  have hi : ((1 : Fin 18) : ℕ) = 1 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row4,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-20)*W^2)/(3)))*(hR-((3))*hL-(((1)/(850)) + ((1*W*b)/(1700)) + (((-1)*W^2)/(850)) + (((-1)*Z)/(850)) + (((-1)*Y*a)/(1700)) + ((9*Y^2)/(1700)) + (((-1)*Y^4)/(1700)))*hJ)

#print axioms critical_row_1

theorem critical_row_2 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row5 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 2*v 2=0 := by
  have hi : ((2 : Fin 18) : ℕ) = 2 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row5,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((20*W^2)/(3)))*(hR-(0)*hL-((((-1)*W*b)/(1700)) + (((-1)*W^2)/(1700)) + (((-1)*Z)/(1700)) + ((1*Y*a)/(1700)) + (((-1)*Y^2)/(1700)))*hJ)

#print axioms critical_row_2

theorem critical_row_3 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row6 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 3*v 2=0 := by
  have hi : ((3 : Fin 18) : ℕ) = 3 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row6,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-10)*W^2)/(3)))*(hR-(0)*hL-((((-2))/(425)) + ((1*W*b)/(850)) + ((1*W^2)/(850)) + ((1*Z)/(850)) + ((1*Y*a)/(425)) + (((-3)*Y^2)/(850)) + (((-1)*Y^4)/(850)))*hJ)

#print axioms critical_row_3

theorem critical_row_4 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row23 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 4*v 2=0 := by
  have hi : ((4 : Fin 18) : ℕ) = 4 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row23,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((1*W^2))*(hR-(((-2)))*hL-((((-1))/(170)) + ((3*W^2)/(1700)) + ((3*Z)/(1700)) + ((3*Y*a)/(850)) + (((-4)*Y^2)/(425)) + (((-1)*Y^4)/(1700)))*hJ)

#print axioms critical_row_4

theorem critical_row_5 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row24 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 5*v 2=0 := by
  have hi : ((5 : Fin 18) : ℕ) = 5 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row24,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-10)*W^2)/(3)))*(hR-(((-1)))*hL-((((-7))/(850)) + ((1*W*b)/(850)) + ((3*W^2)/(1700)) + ((3*Z)/(1700)) + ((2*Y*a)/(425)) + (((-7)*Y^2)/(850)) + (((-3)*Y^4)/(1700)))*hJ)

#print axioms critical_row_5

theorem critical_row_6 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row27 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 6*v 2=0 := by
  have hi : ((6 : Fin 18) : ℕ) = 6 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row27,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-20)*W^2)/(3)))*(hR-(0)*hL-((((-2))/(425)) + ((1*W*b)/(1700)) + ((1*W^2)/(1700)) + ((1*Z)/(1700)) + ((1*Y*a)/(340)) + (((-7)*Y^2)/(1700)) + (((-1)*Y^4)/(850)))*hJ)

#print axioms critical_row_6

theorem critical_row_7 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row28 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 7*v 2=0 := by
  have hi : ((7 : Fin 18) : ℕ) = 7 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row28,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((5*W^2)/(3)))*(hR-((5))*hL-(((2)/(425)) + (((-1)*W^2)/(425)) + (((-1)*Z)/(425)) + (((-1)*Y*a)/(425)) + ((4*Y^2)/(425)))*hJ)

#print axioms critical_row_7

theorem critical_row_8 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row43 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 8*v 2=0 := by
  have hi : ((8 : Fin 18) : ℕ) = 8 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row43,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((20*Y^2*W^2)/(3)))*(hR-(0)*hL-(((1)/(850*Y^2)) + (((-1)*a)/(1700*Y)) + ((1)/(1700)))*hJ)

#print axioms critical_row_8

theorem critical_row_9 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row47 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 9*v 2=0 := by
  have hi : ((9 : Fin 18) : ℕ) = 9 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row47,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((20*Y^2*W^2)/(3)))*(hR-(((1)/(Y^2)))*hL-(((3)/(850*Y^2)) + (((-1)*W^2)/(850*Y^2)) + (((-1)*Z)/(850*Y^2)) + ((1*a)/(340*Y)) + (((-1)*W*a*b)/(1700*Y)) + (((-1)*W^2*a)/(1700*Y)) + (((-1)*Z*a)/(1700*Y)) + ((9)/(1700)) + (((-1)*a^2)/(340)) + ((7*Y*a)/(1700)) + ((1*Y^3*a)/(850)))*hJ)

#print axioms critical_row_9

theorem critical_row_10 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row52 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 10*v 2=0 := by
  have hi : ((10 : Fin 18) : ℕ) = 10 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row52,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((10*Y^2*W^2)/(3)))*(hR-(((1)/(Y^2)))*hL-(((1)/(850*Y^2)) + (((-1)*W^2)/(850*Y^2)) + (((-1)*Z)/(850*Y^2)) + (((-1)*a)/(1700*Y)) + ((7)/(1700)))*hJ)

#print axioms critical_row_10

theorem critical_row_11 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row65 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 11*v 2=0 := by
  have hi : ((11 : Fin 18) : ℕ) = 11 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row65,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-20)*W^2)/(13)))*(hR-(0)*hL-(((1)/(1700)) + ((1*W*b)/(1700)) + ((1*W^2)/(1700)))*hJ)

#print axioms critical_row_11

theorem critical_row_12 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row69 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 12*v 2=0 := by
  have hi : ((12 : Fin 18) : ℕ) = 12 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row69,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((2*Y^2*W^2))*(hR-(((-1)))*hL-((((-1))/(850*Y^2)) + (((-1)*W*b)/(850*Y^2)) + (((-1)*W^2*a)/(1700*Y)) + (((-1))/(1700)) + (((-1)*W*b)/(1700)))*hJ)

#print axioms critical_row_12

theorem critical_row_13 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row71 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 13*v 2=0 := by
  have hi : ((13 : Fin 18) : ℕ) = 13 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row71,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-20)*Y^2*W^2)/(13)))*(hR-(0)*hL-(((1*Z)/(1700*Y^2)) + ((1*Z*W*b)/(1700*Y^2)) + ((1*Z*W^2)/(1700*Y^2)))*hJ)

#print axioms critical_row_13

theorem critical_row_14 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row72 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 14*v 2=0 := by
  have hi : ((14 : Fin 18) : ℕ) = 14 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row72,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-5)*W^2)/(4)))*(hR-(0)*hL-((((-7))/(1700)) + ((1*W*b)/(850)) + ((1*W^2)/(850)) + ((1*Z)/(1700)) + ((1*Y*a)/(340)) + (((-7)*Y^2)/(1700)) + (((-1)*Y^4)/(850)))*hJ)

#print axioms critical_row_14

theorem critical_row_15 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row73 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 15*v 2=0 := by
  have hi : ((15 : Fin 18) : ℕ) = 15 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row73,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((2*Y^2*W^2))*(hR-(0)*hL-((((-1)*W*b)/(850*Y^2)) + (((-1)*a)/(1700*Y)) + (((-1)*W^2*a)/(1700*Y)) + (((-1)*W*b)/(1700)))*hJ)

#print axioms critical_row_15

theorem critical_row_16 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row85 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 16*v 2=0 := by
  have hi : ((16 : Fin 18) : ℕ) = 16 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row85,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((20*Y^2*W^2)/(13)))*(hR-(0)*hL-(((1)/(1700*Y^2)) + ((1*W*b)/(1700*Y^2)) + ((1*W^2)/(1700*Y^2)) + (((-1))/(1700)) + (((-1)*W*b)/(1700)) + (((-1)*W^2)/(1700)))*hJ)

#print axioms critical_row_16

theorem critical_row_17 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row90 1 Y Z W a b v=0)
    (hR : row98 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMM.critical_mmm_row b W Z (a*Y) (Y^2) 17*v 2=0 := by
  have hi : ((17 : Fin 18) : ℕ) = 17 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row90,row98,SmallLevelThirtyFourCriticalMMM.critical_mmm_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-5)*Y^2)/(391)))*(hR-(0)*hL-(((9*W^2)/(25*Y^2)) + (((-1)*W^2*a)/(25*Y)) + (((-2)*W^2)/(75)))*hJ)

#print axioms critical_row_17

end SmallLevelThirtyFourFiniteJetMMM
end
end

/-! ## ThirtyFourFiniteJetMMMCriticalKernel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourFiniteJetMMM
open Complex
/-- A finite algebraic kernel theorem. Its rows must still be bound to
original pole vectors before it gives the level34 analytic conclusion. -/
theorem critical_kernel_zero (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hLall : ∀ i : Fin 90,rows 1 Y Z W a b v ⟨i.val,by omega⟩=0)
    (hJ0 : row90 1 Y Z W a b v=0) (hJ8 : row98 1 Y Z W a b v=0) : v=0 := by
  have hL : row0 1 Y Z W a b v=0:=hLall 0
  have hJ : row90 1 Y Z W a b v=0:=hJ0
  have h2 : v 2=0 := by
    by_contra h2
    apply SmallLevelThirtyFourCriticalMMM.critical_mmm_impossible b W Z (a*Y) (Y^2)
    intro i
    fin_cases i
    · exact (mul_eq_zero.mp (critical_row_0 Y Z W a b hY hW v hL hJ (hLall 3))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_1 Y Z W a b hY hW v hL hJ (hLall 4))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_2 Y Z W a b hY hW v hL hJ (hLall 5))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_3 Y Z W a b hY hW v hL hJ (hLall 6))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_4 Y Z W a b hY hW v hL hJ (hLall 23))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_5 Y Z W a b hY hW v hL hJ (hLall 24))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_6 Y Z W a b hY hW v hL hJ (hLall 27))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_7 Y Z W a b hY hW v hL hJ (hLall 28))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_8 Y Z W a b hY hW v hL hJ (hLall 43))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_9 Y Z W a b hY hW v hL hJ (hLall 47))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_10 Y Z W a b hY hW v hL hJ (hLall 52))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_11 Y Z W a b hY hW v hL hJ (hLall 65))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_12 Y Z W a b hY hW v hL hJ (hLall 69))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_13 Y Z W a b hY hW v hL hJ (hLall 71))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_14 Y Z W a b hY hW v hL hJ (hLall 72))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_15 Y Z W a b hY hW v hL hJ (hLall 73))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_16 Y Z W a b hY hW v hL hJ (hLall 85))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_17 Y Z W a b hY hW v hL hJ hJ8)).resolve_right h2
  have h1 : v 1=0 := by
    norm_num only [row90,h2,mul_zero,add_zero,zero_add] at hJ
    linear_combination (norm := (ring_nf; all_goals field_simp [hW]; all_goals ring)) hJ*(W^2/1700)
  have h0 : v 0=0 := by
    norm_num only [row0,h1,h2,mul_zero,add_zero,zero_add] at hL
    linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring)) hL*(-W^2/(2*Y^2))
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

#print axioms critical_kernel_zero

end SmallLevelThirtyFourFiniteJetMMM
end
end

/-! ## ThirtyFourFiniteJetMMMQuadratic -/
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourFiniteJetMMM
open Complex
def quadratic (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-2)*Z)/(Y^2)))*v 1 + (((2*X^2*Z)/(Y^2)) + ((1*X^3*Z)/(Y^2)) + ((1*X^3*Z*a)/(Y)) + (1*X^3*Z))*v 2

theorem quadratic_jet_constraint (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (v : Fin 3→ℂ)
    (hC : quadratic X Y Z W a b v=0) (hJ : row95 X Y Z W a b v=0) :
    ((22*X^2-4*X+8)*(a*Y+Y^2)+39*X^2-28*X+116)*v 2=0 := by
  unfold quadratic at hC
  unfold row95 at hJ
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ]; all_goals ring))
    (20*Y^2/(X*Z))*(hC-(X*Z/(34*Y^2))*hJ)

#print axioms quadratic_jet_constraint

end SmallLevelThirtyFourFiniteJetMMM
end
end

/-! ## ThirtyFourFiniteJetMMMPositiveScalar -/
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourFiniteJetMMM
open Complex QuantitativeArithmeticSmallLevelThirtyFour
theorem positive_scalar_constraint (u : ℝ) (hu : 2≤u) (Y Z W a b : ℂ)
    (hY : Y≠0) (v : Fin 3→ℂ) (hv : v 2≠0)
    (hH : ((22*(u:ℂ)^2-4*u+8)*(a*Y+Y^2)+39*(u:ℂ)^2-28*u+116)*v 2=0)
    (hJ5 : row95 u Y Z W a b v=0) (hJ8 : row98 u Y Z W a b v=0) :
    (shiftD u:ℂ)*Y^2=(shiftN u:ℂ) := by
  have hX : (u:ℂ)≠0 := by exact_mod_cast (show u≠0 by linarith)
  have hQreal : 0<11*u^2-2*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hQ : 11*(u:ℂ)^2-2*u+4≠0 := by exact_mod_cast ne_of_gt hQreal
  have hP : 22*(u:ℂ)^2-4*u+8≠0 := by
    have he : 22*(u:ℂ)^2-4*u+8=2*(11*(u:ℂ)^2-2*u+4) := by ring
    rw [he]; exact mul_ne_zero (by norm_num) hQ
  have hPn : (8:ℂ)-(u:ℂ)*4+(u:ℂ)^2*22≠0 := by
    convert hP using 1 <;> ring
  have hQn : (4:ℂ)-(u:ℂ)*2+(u:ℂ)^2*11≠0 := by
    convert hQ using 1 <;> ring
  have hP2n : (64:ℂ)-(u:ℂ)*64+(u:ℂ)^2*368-(u:ℂ)^3*176+(u:ℂ)^4*484≠0 := by
    convert pow_ne_zero 2 hP using 1 <;> ring
  have hH0 := (mul_eq_zero.mp hH).resolve_right hv
  have ha : a= -(Y^2+(39*(u:ℂ)^2-28*u+116)/(22*(u:ℂ)^2-4*u+8))/Y := by
    have hr : (39*(u:ℂ)^2-28*u+116)/(22*(u:ℂ)^2-4*u+8)= -(a*Y+Y^2) := by
      apply (div_eq_iff hP).2
      linear_combination hH0
    apply (eq_div_iff hY).2
    rw [hr]
    ring
  have he : ((shiftN u:ℂ)-(shiftD u:ℂ)*Y^2)*v 2=0 := by
    unfold row95 at hJ5
    unfold row98 at hJ8
    unfold shiftN shiftD
    push_cast
    rw [ha] at hJ5 hJ8
    linear_combination (norm := (field_simp [hX,hY,hP,hQ,hPn,hQn]; ring_nf; all_goals field_simp [hX,hY,hP,hQ,hPn,hQn,hP2n]; all_goals ring))
      (2*Y^2*(11*(u:ℂ)^2-2*u+4)^2/17)*(hJ8-((((816)/((u:ℂ)*Y^2)) + (((-68))/((u:ℂ))) + (((-204))/(Y^2)) + (((-68)*(-(Y^2+(39*(u:ℂ)^2-28*u+116)/(22*(u:ℂ)^2-4*u+8))/Y))/(Y)) + ((68)/(3)))/(-68/(u:ℂ)))*hJ5)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hv)).symm

#print axioms positive_scalar_constraint

end SmallLevelThirtyFourFiniteJetMMM
end
end

/-! ## ThirtyFourFiniteJetMMMPositiveKernel -/
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourFiniteJetMMM
open Complex QuantitativeArithmeticSmallLevelThirtyFour
theorem positive_kernel_zero (u : ℝ) (hu : 2≤u) (Y Z W a b : ℂ)
    (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (hnorm : 9*u/2≤‖Y^2‖)
    (v : Fin 3→ℂ) (hL : row0 u Y Z W a b v=0)
    (hC : quadratic u Y Z W a b v=0)
    (hJ5 : row95 u Y Z W a b v=0) (hJ8 : row98 u Y Z W a b v=0) : v=0 := by
  have hX : (u:ℂ)≠0 := by exact_mod_cast (show u≠0 by linarith)
  have h2 : v 2=0 := by
    by_contra hv
    exact positive_shift_impossible u hu (Y^2) hnorm
      (positive_scalar_constraint u hu Y Z W a b hY v hv
        (quadratic_jet_constraint u Y Z W a b hX hY hZ v hC hJ5) hJ5 hJ8)
  have h1 : v 1=0 := by
    simp only [row95,h2,mul_zero,zero_mul,add_zero,zero_add] at hJ5
    linear_combination (norm := (ring_nf; all_goals field_simp [hX]; all_goals ring))
      (-u/68:ℂ)*hJ5
  have hplus : (u:ℂ)+1≠0 := by exact_mod_cast (show u+1≠0 by linarith)
  have h0 : v 0=0 := by
    simp only [row0,h1,h2,mul_zero,zero_mul,add_zero,zero_add] at hL
    linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hW,hplus]; all_goals ring))
      (-(u:ℂ)*W^2/(((u:ℂ)+1)*Y^2))*hL
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

#print axioms positive_kernel_zero

end SmallLevelThirtyFourFiniteJetMMM
end
end

/-! ## ThirtyFourUnitMMMFreeCoordinates -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMM
open Complex SmallLevelThirtyFourGrid
theorem free_coordinates_zero (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h0 : v 370=0) (h1 : v 390=0) (h2 : v 435=0) :
    ∀ j : Fin 414,v (supportIndex j)=0 := by
  intro j
  fin_cases j
  · rw [show supportIndex ⟨0,by decide⟩=(0:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_0 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨1,by decide⟩=(1:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_1 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨2,by decide⟩=(2:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_2 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨3,by decide⟩=(3:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_3 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨4,by decide⟩=(4:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_4 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨5,by decide⟩=(5:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_5 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨6,by decide⟩=(6:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_6 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨7,by decide⟩=(7:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_7 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨8,by decide⟩=(8:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_8 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨9,by decide⟩=(9:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_9 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨10,by decide⟩=(10:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_10 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨11,by decide⟩=(11:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_11 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨12,by decide⟩=(12:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_12 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨13,by decide⟩=(13:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_13 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨14,by decide⟩=(14:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_14 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨15,by decide⟩=(15:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_15 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨16,by decide⟩=(16:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_16 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨17,by decide⟩=(17:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_17 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨18,by decide⟩=(18:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_18 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨19,by decide⟩=(19:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_19 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨20,by decide⟩=(20:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_20 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨21,by decide⟩=(21:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_21 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨22,by decide⟩=(22:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_22 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨23,by decide⟩=(24:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_24 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨24,by decide⟩=(25:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_25 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨25,by decide⟩=(26:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_26 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨26,by decide⟩=(27:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_27 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨27,by decide⟩=(28:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_28 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨28,by decide⟩=(29:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_29 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨29,by decide⟩=(30:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_30 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨30,by decide⟩=(31:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_31 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨31,by decide⟩=(32:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_32 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨32,by decide⟩=(33:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_33 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨33,by decide⟩=(34:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_34 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨34,by decide⟩=(35:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_35 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨35,by decide⟩=(36:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_36 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨36,by decide⟩=(37:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_37 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨37,by decide⟩=(39:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_39 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨38,by decide⟩=(40:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_40 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨39,by decide⟩=(41:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_41 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨40,by decide⟩=(42:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_42 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨41,by decide⟩=(43:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_43 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨42,by decide⟩=(44:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_44 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨43,by decide⟩=(45:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_45 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨44,by decide⟩=(48:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_48 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨45,by decide⟩=(50:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_50 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨46,by decide⟩=(51:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_51 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨47,by decide⟩=(54:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_54 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨48,by decide⟩=(55:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_55 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨49,by decide⟩=(57:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_57 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨50,by decide⟩=(60:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_60 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨51,by decide⟩=(62:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_62 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨52,by decide⟩=(63:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_63 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨53,by decide⟩=(65:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_65 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨54,by decide⟩=(66:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_66 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨55,by decide⟩=(68:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_68 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨56,by decide⟩=(69:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_69 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨57,by decide⟩=(70:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_70 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨58,by decide⟩=(71:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_71 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨59,by decide⟩=(72:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_72 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨60,by decide⟩=(74:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_74 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨61,by decide⟩=(75:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_75 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨62,by decide⟩=(76:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_76 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨63,by decide⟩=(77:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_77 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨64,by decide⟩=(78:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_78 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨65,by decide⟩=(79:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_79 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨66,by decide⟩=(80:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_80 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨67,by decide⟩=(81:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_81 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨68,by decide⟩=(82:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_82 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨69,by decide⟩=(83:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_83 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨70,by decide⟩=(84:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_84 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨71,by decide⟩=(85:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_85 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨72,by decide⟩=(86:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_86 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨73,by decide⟩=(87:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_87 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨74,by decide⟩=(88:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_88 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨75,by decide⟩=(89:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_89 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨76,by decide⟩=(90:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_90 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨77,by decide⟩=(91:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_91 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨78,by decide⟩=(92:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_92 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨79,by decide⟩=(93:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_93 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨80,by decide⟩=(94:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_94 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨81,by decide⟩=(95:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_95 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨82,by decide⟩=(96:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_96 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨83,by decide⟩=(98:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_98 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨84,by decide⟩=(99:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_99 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨85,by decide⟩=(100:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_100 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨86,by decide⟩=(101:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_101 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨87,by decide⟩=(102:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_102 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨88,by decide⟩=(105:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_105 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨89,by decide⟩=(107:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_107 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨90,by decide⟩=(108:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_108 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨91,by decide⟩=(110:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_110 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨92,by decide⟩=(111:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_111 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨93,by decide⟩=(114:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_114 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨94,by decide⟩=(115:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_115 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨95,by decide⟩=(116:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_116 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨96,by decide⟩=(117:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_117 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨97,by decide⟩=(119:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_119 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨98,by decide⟩=(120:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_120 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨99,by decide⟩=(122:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_122 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨100,by decide⟩=(123:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_123 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨101,by decide⟩=(125:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_125 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨102,by decide⟩=(126:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_126 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨103,by decide⟩=(127:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_127 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨104,by decide⟩=(128:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_128 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨105,by decide⟩=(129:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_129 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨106,by decide⟩=(130:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_130 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨107,by decide⟩=(132:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_132 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨108,by decide⟩=(133:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_133 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨109,by decide⟩=(135:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_135 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨110,by decide⟩=(136:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_136 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨111,by decide⟩=(138:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_138 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨112,by decide⟩=(139:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_139 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨113,by decide⟩=(140:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_140 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨114,by decide⟩=(141:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_141 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨115,by decide⟩=(142:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_142 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨116,by decide⟩=(144:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_144 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨117,by decide⟩=(145:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_145 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨118,by decide⟩=(147:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_147 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨119,by decide⟩=(148:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_148 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨120,by decide⟩=(150:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_150 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨121,by decide⟩=(151:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_151 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨122,by decide⟩=(153:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_153 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨123,by decide⟩=(154:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_154 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨124,by decide⟩=(155:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_155 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨125,by decide⟩=(156:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_156 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨126,by decide⟩=(157:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_157 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨127,by decide⟩=(158:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_158 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨128,by decide⟩=(159:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_159 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨129,by decide⟩=(160:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_160 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨130,by decide⟩=(162:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_162 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨131,by decide⟩=(163:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_163 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨132,by decide⟩=(164:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_164 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨133,by decide⟩=(165:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_165 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨134,by decide⟩=(166:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_166 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨135,by decide⟩=(167:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_167 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨136,by decide⟩=(168:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_168 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨137,by decide⟩=(169:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_169 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨138,by decide⟩=(170:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_170 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨139,by decide⟩=(171:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_171 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨140,by decide⟩=(172:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_172 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨141,by decide⟩=(173:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_173 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨142,by decide⟩=(174:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_174 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨143,by decide⟩=(175:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_175 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨144,by decide⟩=(176:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_176 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨145,by decide⟩=(177:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_177 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨146,by decide⟩=(178:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_178 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨147,by decide⟩=(180:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_180 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨148,by decide⟩=(181:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_181 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨149,by decide⟩=(182:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_182 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨150,by decide⟩=(183:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_183 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨151,by decide⟩=(184:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_184 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨152,by decide⟩=(185:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_185 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨153,by decide⟩=(186:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_186 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨154,by decide⟩=(187:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_187 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨155,by decide⟩=(189:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_189 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨156,by decide⟩=(190:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_190 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨157,by decide⟩=(192:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_192 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨158,by decide⟩=(195:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_195 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨159,by decide⟩=(196:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_196 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨160,by decide⟩=(198:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_198 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨161,by decide⟩=(199:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_199 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨162,by decide⟩=(200:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_200 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨163,by decide⟩=(201:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_201 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨164,by decide⟩=(202:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_202 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨165,by decide⟩=(204:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_204 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨166,by decide⟩=(205:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_205 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨167,by decide⟩=(207:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_207 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨168,by decide⟩=(210:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_210 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨169,by decide⟩=(211:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_211 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨170,by decide⟩=(212:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_212 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨171,by decide⟩=(213:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_213 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨172,by decide⟩=(214:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_214 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨173,by decide⟩=(215:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_215 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨174,by decide⟩=(216:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_216 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨175,by decide⟩=(218:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_218 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨176,by decide⟩=(219:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_219 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨177,by decide⟩=(220:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_220 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨178,by decide⟩=(221:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_221 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨179,by decide⟩=(222:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_222 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨180,by decide⟩=(224:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_224 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨181,by decide⟩=(225:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_225 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨182,by decide⟩=(228:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_228 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨183,by decide⟩=(230:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_230 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨184,by decide⟩=(231:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_231 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨185,by decide⟩=(232:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_232 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨186,by decide⟩=(233:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_233 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨187,by decide⟩=(234:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_234 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨188,by decide⟩=(235:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_235 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨189,by decide⟩=(237:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_237 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨190,by decide⟩=(238:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_238 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨191,by decide⟩=(239:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_239 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨192,by decide⟩=(240:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_240 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨193,by decide⟩=(241:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_241 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨194,by decide⟩=(242:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_242 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨195,by decide⟩=(243:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_243 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨196,by decide⟩=(244:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_244 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨197,by decide⟩=(245:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_245 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨198,by decide⟩=(246:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_246 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨199,by decide⟩=(247:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_247 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨200,by decide⟩=(248:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_248 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨201,by decide⟩=(249:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_249 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨202,by decide⟩=(250:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_250 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨203,by decide⟩=(251:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_251 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨204,by decide⟩=(252:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_252 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨205,by decide⟩=(253:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_253 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨206,by decide⟩=(254:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_254 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨207,by decide⟩=(255:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_255 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨208,by decide⟩=(256:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_256 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨209,by decide⟩=(257:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_257 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨210,by decide⟩=(258:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_258 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨211,by decide⟩=(259:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_259 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨212,by decide⟩=(260:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_260 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨213,by decide⟩=(261:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_261 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨214,by decide⟩=(262:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_262 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨215,by decide⟩=(263:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_263 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨216,by decide⟩=(264:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_264 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨217,by decide⟩=(265:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_265 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨218,by decide⟩=(266:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_266 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨219,by decide⟩=(267:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_267 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨220,by decide⟩=(268:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_268 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨221,by decide⟩=(269:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_269 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨222,by decide⟩=(270:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_270 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨223,by decide⟩=(271:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_271 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨224,by decide⟩=(272:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_272 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨225,by decide⟩=(273:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_273 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨226,by decide⟩=(275:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_275 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨227,by decide⟩=(276:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_276 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨228,by decide⟩=(277:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_277 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨229,by decide⟩=(278:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_278 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨230,by decide⟩=(279:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_279 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨231,by decide⟩=(280:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_280 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨232,by decide⟩=(282:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_282 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨233,by decide⟩=(285:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_285 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨234,by decide⟩=(286:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_286 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨235,by decide⟩=(288:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_288 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨236,by decide⟩=(289:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_289 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨237,by decide⟩=(290:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_290 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨238,by decide⟩=(291:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_291 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨239,by decide⟩=(292:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_292 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨240,by decide⟩=(294:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_294 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨241,by decide⟩=(295:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_295 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨242,by decide⟩=(296:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_296 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨243,by decide⟩=(297:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_297 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨244,by decide⟩=(298:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_298 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨245,by decide⟩=(299:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_299 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨246,by decide⟩=(300:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_300 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨247,by decide⟩=(303:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_303 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨248,by decide⟩=(305:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_305 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨249,by decide⟩=(306:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_306 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨250,by decide⟩=(308:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_308 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨251,by decide⟩=(309:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_309 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨252,by decide⟩=(310:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_310 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨253,by decide⟩=(311:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_311 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨254,by decide⟩=(312:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_312 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨255,by decide⟩=(314:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_314 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨256,by decide⟩=(315:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_315 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨257,by decide⟩=(318:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_318 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨258,by decide⟩=(320:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_320 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨259,by decide⟩=(321:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_321 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨260,by decide⟩=(323:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_323 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨261,by decide⟩=(324:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_324 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨262,by decide⟩=(325:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_325 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨263,by decide⟩=(326:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_326 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨264,by decide⟩=(327:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_327 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨265,by decide⟩=(328:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_328 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨266,by decide⟩=(329:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_329 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨267,by decide⟩=(330:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_330 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨268,by decide⟩=(332:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_332 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨269,by decide⟩=(333:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_333 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨270,by decide⟩=(334:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_334 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨271,by decide⟩=(335:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_335 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨272,by decide⟩=(336:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_336 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨273,by decide⟩=(337:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_337 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨274,by decide⟩=(338:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_338 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨275,by decide⟩=(339:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_339 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨276,by decide⟩=(340:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_340 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨277,by decide⟩=(341:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_341 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨278,by decide⟩=(342:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_342 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨279,by decide⟩=(343:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_343 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨280,by decide⟩=(344:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_344 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨281,by decide⟩=(345:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_345 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨282,by decide⟩=(346:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_346 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨283,by decide⟩=(347:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_347 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨284,by decide⟩=(348:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_348 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨285,by decide⟩=(350:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_350 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨286,by decide⟩=(351:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_351 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨287,by decide⟩=(352:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_352 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨288,by decide⟩=(353:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_353 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨289,by decide⟩=(354:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_354 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨290,by decide⟩=(355:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_355 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨291,by decide⟩=(356:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_356 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨292,by decide⟩=(357:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_357 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨293,by decide⟩=(359:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_359 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨294,by decide⟩=(360:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_360 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨295,by decide⟩=(362:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_362 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨296,by decide⟩=(363:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_363 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨297,by decide⟩=(365:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_365 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨298,by decide⟩=(366:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_366 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨299,by decide⟩=(368:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_368 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨300,by decide⟩=(369:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_369 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨301,by decide⟩=(370:Fin 510) from by decide +kernel]
    exact h0
  · rw [show supportIndex ⟨302,by decide⟩=(371:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_371 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨303,by decide⟩=(372:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_372 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨304,by decide⟩=(374:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_374 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨305,by decide⟩=(375:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_375 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨306,by decide⟩=(377:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_377 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨307,by decide⟩=(378:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_378 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨308,by decide⟩=(380:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_380 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨309,by decide⟩=(381:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_381 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨310,by decide⟩=(382:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_382 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨311,by decide⟩=(383:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_383 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨312,by decide⟩=(384:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_384 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨313,by decide⟩=(385:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_385 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨314,by decide⟩=(387:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_387 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨315,by decide⟩=(388:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_388 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨316,by decide⟩=(390:Fin 510) from by decide +kernel]
    exact h1
  · rw [show supportIndex ⟨317,by decide⟩=(391:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_391 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨318,by decide⟩=(393:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_393 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨319,by decide⟩=(394:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_394 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨320,by decide⟩=(395:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_395 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨321,by decide⟩=(396:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_396 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨322,by decide⟩=(399:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_399 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨323,by decide⟩=(400:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_400 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨324,by decide⟩=(402:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_402 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨325,by decide⟩=(403:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_403 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨326,by decide⟩=(405:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_405 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨327,by decide⟩=(408:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_408 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨328,by decide⟩=(409:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_409 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨329,by decide⟩=(410:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_410 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨330,by decide⟩=(411:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_411 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨331,by decide⟩=(412:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_412 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨332,by decide⟩=(414:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_414 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨333,by decide⟩=(415:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_415 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨334,by decide⟩=(416:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_416 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨335,by decide⟩=(417:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_417 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨336,by decide⟩=(418:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_418 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨337,by decide⟩=(419:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_419 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨338,by decide⟩=(420:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_420 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨339,by decide⟩=(421:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_421 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨340,by decide⟩=(422:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_422 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨341,by decide⟩=(423:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_423 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨342,by decide⟩=(424:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_424 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨343,by decide⟩=(425:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_425 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨344,by decide⟩=(426:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_426 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨345,by decide⟩=(427:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_427 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨346,by decide⟩=(428:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_428 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨347,by decide⟩=(429:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_429 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨348,by decide⟩=(430:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_430 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨349,by decide⟩=(431:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_431 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨350,by decide⟩=(432:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_432 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨351,by decide⟩=(433:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_433 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨352,by decide⟩=(434:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_434 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨353,by decide⟩=(435:Fin 510) from by decide +kernel]
    exact h2
  · rw [show supportIndex ⟨354,by decide⟩=(436:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_436 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨355,by decide⟩=(438:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_438 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨356,by decide⟩=(439:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_439 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨357,by decide⟩=(440:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_440 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨358,by decide⟩=(441:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_441 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨359,by decide⟩=(442:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_442 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨360,by decide⟩=(444:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_444 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨361,by decide⟩=(445:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_445 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨362,by decide⟩=(447:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_447 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨363,by decide⟩=(448:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_448 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨364,by decide⟩=(450:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_450 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨365,by decide⟩=(453:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_453 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨366,by decide⟩=(455:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_455 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨367,by decide⟩=(456:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_456 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨368,by decide⟩=(459:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_459 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨369,by decide⟩=(460:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_460 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨370,by decide⟩=(462:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_462 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨371,by decide⟩=(465:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_465 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨372,by decide⟩=(466:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_466 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨373,by decide⟩=(467:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_467 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨374,by decide⟩=(468:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_468 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨375,by decide⟩=(469:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_469 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨376,by decide⟩=(470:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_470 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨377,by decide⟩=(471:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_471 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨378,by decide⟩=(473:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_473 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨379,by decide⟩=(474:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_474 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨380,by decide⟩=(475:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_475 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨381,by decide⟩=(476:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_476 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨382,by decide⟩=(477:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_477 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨383,by decide⟩=(478:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_478 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨384,by decide⟩=(479:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_479 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨385,by decide⟩=(480:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_480 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨386,by decide⟩=(481:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_481 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨387,by decide⟩=(482:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_482 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨388,by decide⟩=(483:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_483 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨389,by decide⟩=(484:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_484 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨390,by decide⟩=(485:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_485 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨391,by decide⟩=(486:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_486 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨392,by decide⟩=(488:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_488 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨393,by decide⟩=(489:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_489 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨394,by decide⟩=(490:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_490 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨395,by decide⟩=(491:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_491 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨396,by decide⟩=(492:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_492 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨397,by decide⟩=(493:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_493 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨398,by decide⟩=(494:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_494 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨399,by decide⟩=(495:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_495 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨400,by decide⟩=(496:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_496 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨401,by decide⟩=(497:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_497 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨402,by decide⟩=(498:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_498 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨403,by decide⟩=(499:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_499 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨404,by decide⟩=(500:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_500 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨405,by decide⟩=(501:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_501 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨406,by decide⟩=(502:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_502 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨407,by decide⟩=(503:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_503 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨408,by decide⟩=(504:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_504 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨409,by decide⟩=(505:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_505 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨410,by decide⟩=(506:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_506 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨411,by decide⟩=(507:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_507 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨412,by decide⟩=(508:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_508 X Y Z W a b hX hY hZ hW v hv
  · rw [show supportIndex ⟨413,by decide⟩=(509:Fin 510) from by decide +kernel]
    simpa only [h0,h1,h2,mul_zero,add_zero] using coordinate_expansion_509 X Y Z W a b hX hY hZ hW v hv

#print axioms free_coordinates_zero

end SmallLevelThirtyFourUnitMMM
end
end

/-! ## ThirtyFourUnitMMMQuadraticCoordinates -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMM
open Complex
theorem quadratic_coordinate_binding (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    v 170-v 340=SmallLevelThirtyFourFiniteJetMMM.quadratic X Y Z W a b ![v 370,v 390,v 435] := by
  rw [coordinate_expansion_170 X Y Z W a b hX hY hZ hW v hv,
    coordinate_expansion_340 X Y Z W a b hX hY hZ hW v hv]
  simp only [SmallLevelThirtyFourFiniteJetMMM.quadratic,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms quadratic_coordinate_binding

end SmallLevelThirtyFourUnitMMM
end
end

/-! ## ThirtyFourPhysicalFiniteMMMKernels -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourPhysicalFiniteMMM
open Complex Matrix SmallLevelThirtyFourGrid SmallLevelPrimeRates SmallLevelFiniteGridSupport
open SmallLevelThirtyFourUnitMMM SmallLevelThirtyFourUnitMMMInhomogeneous
theorem support_vector_zero (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (w : Fin 414→ℂ)
    (hs : ∀ i,sourceRows X Y Z W a b (extension supportIndex w) i=0)
    (hfree : ![(extension supportIndex w) 370,(extension supportIndex w) 390,
      (extension supportIndex w) 435]=(0:Fin 3→ℂ)) : w=0 := by
  have h0 : (extension supportIndex w) 370=0 := congrFun hfree 0
  have h1 : (extension supportIndex w) 390=0 := congrFun hfree 1
  have h2 : (extension supportIndex w) 435=0 := congrFun hfree 2
  funext j
  have hj:=free_coordinates_zero X Y Z W a b hX hY hZ hW (extension supportIndex w) hs h0 h1 h2 j
  change extend supportIndex w (supportIndex j)=0 at hj
  simpa only [extend_at supportIndex support_injective,Pi.zero_apply] using hj

theorem extended_quadratic (w : Fin 414→ℂ) :
    (extension supportIndex w) 170-(extension supportIndex w) 340=w 138-w 276 := by
  change extend supportIndex w 170-extend supportIndex w 340=_
  rw [←quadratic_coordinates.1,←quadratic_coordinates.2]
  rw [extend_at supportIndex support_injective,extend_at supportIndex support_injective]

#print axioms support_vector_zero

theorem critical_matrix_kernel_zero (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= -v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0)
    (hjet : firstJetMatrix m f ε u v x *ᵥ w=0) (hx : u*parameter 2 m x=1) : w=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) x)
  have hW:=parameter_ne_zero 5 m (by decide) x
  have hfree : ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435]=0 := by
    apply SmallLevelThirtyFourFiniteJetMMM.critical_kernel_zero (parameter 3 m x) (v*parameter 17 m x)
      (parameter 5 m x) (badParameter f 3) (badParameter f 5) hY hW
    · simpa only [hx] using finite_leading_rows m f ε u v x hu hv hη h₂ h₁₇ w hlead
    · simpa only [hx] using finite_jet_row_0 m f ε u v x hu hv hη h₂ h₁₇ w hlead hjet
    · simpa only [hx] using finite_jet_row_8 m f ε u v x hu hv hη h₂ h₁₇ w hlead hjet
  exact support_vector_zero (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW w (source_kernel m f ε u v x hu hv hη h₂ h₁₇ w hlead) hfree

#print axioms critical_matrix_kernel_zero

theorem positive_matrix_kernel_zero (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= -v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0)
    (hjet : firstJetMatrix m f ε u v x *ᵥ w=0) (t : ℝ) (ht : 2≤t)
    (hx : u*parameter 2 m x=(t:ℂ))
    (hnorm : 9*t/2≤‖parameter 3 m x^2‖) (hC : w 138-w 276=0) : w=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) x)
  have hW:=parameter_ne_zero 5 m (by decide) x
  have hs:=source_kernel m f ε u v x hu hv hη h₂ h₁₇ w hlead
  have hquad : SmallLevelThirtyFourFiniteJetMMM.quadratic (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435]=0 := by
    rw [←quadratic_coordinate_binding (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW (extension supportIndex w) hs,
      extended_quadratic,hC]
  have hfree : ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435]=0 := by
    apply SmallLevelThirtyFourFiniteJetMMM.positive_kernel_zero t ht (parameter 3 m x) (v*parameter 17 m x)
      (parameter 5 m x) (badParameter f 3) (badParameter f 5) hY hZ hW hnorm
    · simpa only [hx] using
        (SmallLevelThirtyFourFiniteJetMMM.leading_binding_0
          (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x)
          (parameter 5 m x) (badParameter f 3) (badParameter f 5)
          hX hY hZ hW (extension supportIndex w) hs)
    · simpa only [hx] using hquad
    · simpa only [hx] using finite_jet_row_5 m f ε u v x hu hv hη h₂ h₁₇ w hlead hjet
    · simpa only [hx] using finite_jet_row_8 m f ε u v x hu hv hη h₂ h₁₇ w hlead hjet
  exact support_vector_zero (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW w hs hfree

#print axioms positive_matrix_kernel_zero

end SmallLevelThirtyFourPhysicalFiniteMMM
end
end

/-! ## ThirtyFourChiThree -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourChiThree
open SmallLevelThirtyFourCenters QuantitativeArithmeticMellinScale
  SmallLevelAdditive SmallLevelTaylor Complex Filter Set MeasureTheory
  FinitenessFourierConstruction FinitenessOriginalFourier

/-- The entire numerator before division by the ramified Hecke factor. -/
def numerator (m : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1
    (coefficients (fullCoefficients f (2*m)) (1/6))) s-
  mellin (FinitenessAllLevelAxisDecay.axis 1
    (coefficients (fullCoefficients f (2*m)) (-(1/6)))) s

def denominator (m : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  1+((Real.sqrt 2:ℂ)*f 2)*(2:ℂ)^((m:ℂ)-s)

theorem original_numerator_entire (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) :
    Differentiable ℂ (numerator m f) := by
  obtain ⟨χ,_,h⟩ := original_centers_entire m hm hf
  exact (entire_at_one (by decide : 0<612) _ (h true).1).sub
    (entire_at_one (by decide : 0<612) _ (h false).1)

theorem denominator_entire (m : ℕ) (f : ℕ → ℂ) : Differentiable ℂ (denominator m f) := by
  unfold denominator
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop

/-- An exact original-input Hecke identity, identifying the odd third-twist
numerator on a half-plane. No division or continuation premise is used. -/
theorem original_hecke_identity (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) :
    ∃ bound : ℝ, ∀ s : ℂ, bound<s.re →
      numerator m f s=denominator m f s*
        (original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) := by
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  obtain ⟨H,hH⟩ := QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan.normalized_additive_bad_hecke hm hf (by decide : Nat.Prime 2) (by decide)
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
  norm_num at h1
  rw [h1] at hp
  have hnum : numerator m f s=original (2*m) f (1/6) s-original (2*m) f (-(1/6)) s := by
    unfold numerator
    have he (r : ℝ) : FinitenessAllLevelAxisDecay.axis 1 (coefficients (fullCoefficients f (2*m)) r)=
        (fun y : ℝ => fourier (fullCoefficients f (2*m)) ((r:ℂ)+(y:ℂ)*I)) :=
      funext (axis_one_translate (fullCoefficients f (2*m)) r)
    rw [he,he,(hB (1/6) s hsB).2,(hB (-(1/6)) s hsB).2]
  rw [hnum]
  unfold denominator
  linear_combination hp-hn

#print axioms original_numerator_entire
#print axioms denominator_entire
#print axioms original_hecke_identity
end SmallLevelThirtyFourChiThree
end
end

/-! ## ThirtyFourChiThreeContinuation -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourChiThree
open Complex Filter Set SmallLevelAdditive
open scoped Topology

/-- Two evaluations exclude an identically zero ramified Hecke factor. -/
theorem denominator_nonzero (m : ℕ) (f : ℕ → ℂ) : ∃ s : ℂ, denominator m f s≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw (m:ℂ)
  have h1 := hw ((m:ℂ)+1)
  have he : (m:ℂ)-((m:ℂ)+1)= -1 := by ring
  norm_num [denominator,he] at h0 h1
  rw [Complex.cpow_neg,Complex.cpow_one] at h1
  norm_num at h1
  have hbad : (1:ℂ)=0 := by linear_combination -h0+2*h1
  norm_num at hbad

/-- The actual odd additive combination modulo3 has a global meromorphic
continuation from the original hypotheses. Its only possible poles are
zeros of the explicit Hecke-2 denominator. Pole removal is still separate. -/
theorem original_continuation (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) :
    ∃ (bound : ℝ) (G : ℂ → ℂ), (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) ∧
      (∀ s, denominator m f s≠0 → AnalyticAt ℂ G s) ∧
      (∀ x, G=ᶠ[𝓝[≠] x] (fun s => numerator m f s/denominator m f s)) := by
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  obtain ⟨H,hH⟩ := original_hecke_identity m hm hf
  obtain ⟨G,hG,hagree,hpole,hgerm⟩ := QuantitativeArithmeticEntireQuotient.continuation
    (numerator m f) (denominator m f)
    (fun s => original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) (max B H)
    (fun z => (original_numerator_entire m hm hf).analyticAt z)
    (fun z => (denominator_entire m f).analyticAt z)
    (denominator_nonzero m f)
    (fun z hz => (hB (1/3) z (lt_of_le_of_lt (le_max_left _ _) hz)).1.sub
      (hB (-(1/3)) z (lt_of_le_of_lt (le_max_left _ _) hz)).1)
    (fun z hz => hH z (lt_of_le_of_lt (le_max_right _ _) hz))
  exact ⟨max B H,G,hG,hagree,hpole,hgerm⟩

#print axioms denominator_nonzero
#print axioms original_continuation
end SmallLevelThirtyFourChiThree
end
end

/-! ## ThirtyFourGridQuadraticGerm -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGrid
open Complex Filter SmallLevelAdditive SmallLevelPrimeRates SmallLevelThirtyFourUnitMMM
open SmallLevelThirtyFourChiThree
open scoped Topology

def PoleSystem.quadratic {m : ℕ} {f : ℕ→ℂ} {ε : ℂ} (S : PoleSystem m f ε) (s : ℂ) : ℂ :=
  S.G s 138-S.G s 276

theorem PoleSystem.quadratic_agreement {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (s : ℂ) (hs : S.B<s.re) :
    S.quadratic s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s := by
  have hp : supportIndex 138=gridIndex 170 := by decide
  have hn : supportIndex 276=gridIndex (-170) := by decide
  unfold PoleSystem.quadratic
  rw [S.agreement s hs]
  change gridVector (2*m) f s (supportIndex 138)-gridVector (2*m) f s (supportIndex 276)=_
  rw [hp,hn,gridVector_index,gridVector_index]
  norm_num [grid]

theorem PoleSystem.quadratic_quotient_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) (x : ℂ) :
    S.quadratic=ᶠ[𝓝[≠] x] (fun s => numerator m f s/denominator m f s) := by
  obtain ⟨B,H,hH,hagree,_hregular,hgerm⟩:=SmallLevelThirtyFourChiThree.original_continuation m hm hf
  have he : S.quadratic=ᶠ[𝓝[≠] x] H := by
    apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) (max S.B B)
    · intro z _
      exact (S.meromorphic 138 z).meromorphicAt.sub (S.meromorphic 276 z).meromorphicAt
    · intro z _
      exact (hH z).meromorphicAt
    · intro z hz
      rw [S.quadratic_agreement z (lt_of_le_of_lt (le_max_left _ _) hz),
        hagree z (lt_of_le_of_lt (le_max_right _ _) hz)]
    · linarith
  exact he.trans (hgerm x)

theorem denominator_zero_parameter (m : ℕ) (f : ℕ→ℂ) (s : ℂ) :
    denominator m f s=0 ↔ parameter 2 m s= -badParameter f 2 := by
  have hx:=parameter_ne_zero 2 m (by decide) s
  have he : (2:ℂ)^((m:ℂ)-s)=(parameter 2 m s)⁻¹ := by
    unfold parameter
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  rw [denominator,he]
  change 1+badParameter f 2*(parameter 2 m s)⁻¹=0 ↔ _
  constructor
  · intro h
    have hmul:=congrArg (fun a : ℂ => a*parameter 2 m s) h
    field_simp [hx] at hmul
    linear_combination hmul
  · intro h
    rw [h] at hx ⊢
    field_simp
    simp_all

/-- Every pole of the actual odd third-twist germ lies on the explicit
ramified Hecke divisor. This is derived from original input, not assumed. -/
theorem PoleSystem.quadratic_pole_parameter {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) (x : ℂ)
    (hpole : meromorphicOrderAt S.quadratic x<0) :
    parameter 2 m x= -badParameter f 2 := by
  apply (denominator_zero_parameter m f x).mp
  by_contra hd
  have hq:=((original_numerator_entire m hm hf).analyticAt x).div
    ((denominator_entire m f).analyticAt x) hd
  have hn:=hq.meromorphicOrderAt_nonneg
  change 0≤meromorphicOrderAt (fun s => numerator m f s/denominator m f s) x at hn
  rw [←meromorphicOrderAt_congr (S.quadratic_quotient_germ hm hf x)] at hn
  exact (not_le_of_gt hpole) hn

#print axioms PoleSystem.quadratic_quotient_germ
#print axioms denominator_zero_parameter
#print axioms PoleSystem.quadratic_pole_parameter
end SmallLevelThirtyFourGrid
end
end

/-! ## ThirtyFourGridQuadraticPoleGeometry -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGrid
open Complex Filter SmallLevelPrimeRates SmallLevelThirtyFourChiThree
open QuantitativeArithmeticUniversalPoleVector
open scoped Topology

theorem denominator_zero_real_part (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.EulerData 34 f) (x : ℂ)
    (hd : denominator m f x=0) : x.re=m := by
  apply real_part_of_parameter_two_norm
  rw [(denominator_zero_parameter m f x).mp hd]
  rcases badParameter_two_sign hf with h|h <;> simp [h]

theorem PoleSystem.quadratic_pole_real_part {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) (x : ℂ)
    (hpole : meromorphicOrderAt S.quadratic x<0) : x.re=m := by
  apply denominator_zero_real_part m hf.toEulerData x
  exact (denominator_zero_parameter m f x).mpr (S.quadratic_pole_parameter hm hf x hpole)

/-- Above the critical line the same weighted common pole vector has zero
odd third-twist coordinate. This follows from the actual quotient germ. -/
theorem PoleSystem.leading_quadratic_zero {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) (x : ℂ)
    (hx : x.re≠m) (w : Fin 414→ℂ)
    (hw : IsLeadingVector (fun z j => (z-((2*m:ℕ):ℂ))*S.G z j) x w) :
    w 138-w 276=0 := by
  classical
  have hd : denominator m f x≠0 := fun h => hx (denominator_zero_real_part m hf.toEulerData x h)
  let A : ℂ→Fin 414→ℂ := fun _ j => (if j=138 then 1 else 0)-(if j=276 then 1 else 0)
  have hsum (z : ℂ) :
      (∑ j,A z j*((z-((2*m:ℕ):ℂ))*S.G z j))=(z-((2*m:ℕ):ℂ))*S.quadratic z := by
    simp [A,sub_mul,Finset.sum_sub_distrib,PoleSystem.quadratic,mul_sub]
    ring
  have h:=hw.2 A (fun z => (z-((2*m:ℕ):ℂ))*(numerator m f z/denominator m f z))
    (fun _ => analyticAt_const)
    ((analyticAt_id.sub analyticAt_const).mul
      (((original_numerator_entire m hm hf).analyticAt x).div
        ((denominator_entire m f).analyticAt x) hd))
    (by
      filter_upwards [S.quadratic_quotient_germ hm hf x] with z hz
      rw [hsum,hz])
  simpa [A,sub_mul,Finset.sum_sub_distrib] using h

#print axioms PoleSystem.quadratic_pole_real_part
#print axioms PoleSystem.leading_quadratic_zero
end SmallLevelThirtyFourGrid
end
end

/-! ## ThirtyFourGridActivePoleVector -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGrid
open Complex Filter Matrix SmallLevelAdditive SmallLevelThirtyFourUnitMMM
open QuantitativeArithmeticUniversalPoleVector
open scoped Topology

theorem PoleSystem.original_analytic_halfplane {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) :
    ∃ B : ℝ,∀ i z,B<z.re → AnalyticAt ℂ (fun s => S.G s i) z := by
  obtain ⟨BF,hF⟩:=original_common_halfplane hf
  refine ⟨max BF S.B,?_⟩
  intro i z hz
  have hFz:=((hF (((supportIndex i:ℕ):ℝ)/510) z (lt_of_le_of_lt (le_max_left _ _) hz)).1)
  change AnalyticAt ℂ (fun s => actualGrid m f s i) z at hFz
  apply hFz.congr
  have hnear : ∀ᶠ w : ℂ in 𝓝 z,S.B<w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (lt_of_le_of_lt (le_max_right _ _) hz)
  filter_upwards [hnear] with w hw
  exact (congrFun (S.agreement w hw) i).symm

/-- Any original grid pole away from the weight supplies a rightmost
active point and a nonzero weighted vector satisfying every leading row.
The same vector is used by the first-Taylor pole lemmas. -/
theorem PoleSystem.exists_active_leading_vector {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f)
    (x : ℂ) (hx : x≠((2*m:ℕ):ℂ))
    (hpole : ∃ j,meromorphicOrderAt (fun z => S.G z j) x<0) :
    ∃ n : ℕ,∃ v : Fin 414→ℂ,
      IsLeadingVector (fun z j => (z-((2*m:ℕ):ℂ))*S.G z j) (x+n) v ∧
      leadingMatrix m f ε (x+n) *ᵥ v=0 ∧
      ∀ a : ℕ,0<a → ∀ j,
        0≤meromorphicOrderAt (fun z => S.G z j) (x+n+a) ∨
        (x+n+a=((2*m:ℕ):ℂ) ∧ (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => S.G z j) (x+n+a)) := by
  obtain ⟨B,hB⟩:=S.original_analytic_halfplane hf
  obtain ⟨n,v,hv,hs⟩:=SmallLevelActivePoleVector.exists_rightmost_active_vector
    S.G ((2*m:ℕ):ℂ) x hx (fun i z => (S.meromorphic i z).meromorphicAt) hpole B hB
  exact ⟨n,v,hv,S.active_weighted_leading_kernel (x+n) v hv hs,hs⟩

#print axioms PoleSystem.original_analytic_halfplane
#print axioms PoleSystem.exists_active_leading_vector
end SmallLevelThirtyFourGrid
end
end

/-! ## ThirtyFourQuadraticPoleMMM -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourQuadraticPoleMMM
open Complex Matrix SmallLevelThirtyFourGrid SmallLevelPrimeRates
open QuantitativeArithmeticSmallLevelThirtyFour SmallLevelThirtyFourPhysicalFiniteMMM

/-- No odd-third-twist pole, for this representative and its four sign scalings.
All matrix kernels come from original Taylor equations on one leading vector. -/
theorem quadratic_order_nonneg {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) (u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= -v) (x : ℂ) :
    0≤meromorphicOrderAt S.quadratic x := by
  by_contra hn
  have hpole : meromorphicOrderAt S.quadratic x<0 := lt_of_not_ge hn
  have hxre:=S.quadratic_pole_real_part hm hf x hpole
  have hx : x≠((2*m:ℕ):ℂ) := by
    intro he
    have hr:=congrArg Complex.re he
    norm_num [hxre] at hr
    have hmreal : (0:ℝ)<m := by exact_mod_cast hm
    nlinarith
  have hgrid : ∃ j,meromorphicOrderAt (fun z => S.G z j) x<0 := by
    by_contra hg
    push Not at hg
    have ha := ((S.meromorphic 138 x).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hg 138)).sub
      ((S.meromorphic 276 x).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hg 276))
    exact (not_le_of_gt hpole) ha.meromorphicOrderAt_nonneg
  obtain ⟨n,w,hw,hlead,htail⟩:=S.exists_active_leading_vector hf x hx hgrid
  have hjet:=SmallLevelThirtyFourUnitMMMInhomogeneous.active_first_jet_kernel S (x+n) u v hu hv hη h₂ h₁₇ w hw htail
  have hbase : u*parameter 2 m x=1 := by
    rw [S.quadratic_pole_parameter hm hf x hpole,h₂]
    rcases hu with rfl|rfl <;> norm_num
  have hX : u*parameter 2 m (x+n)=(2:ℂ)^n := by
    rw [parameter_add_nat 2 m (by decide),Nat.cast_ofNat,←mul_assoc,hbase,one_mul]
  apply hw.1
  by_cases hn0 : n=0
  · have hp0 : (2:ℂ)^n=1 := by rw [hn0,pow_zero]
    exact critical_matrix_kernel_zero m f ε u v (x+n) hu hv hη h₂ h₁₇ w hlead hjet
      (hX.trans hp0)
  · have hn1 : 1≤n := by omega
    have ht : (2:ℝ)≤(2:ℝ)^n := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hn1
    have hnorm : 9*(2:ℝ)^n/2≤‖parameter 3 m (x+n)^2‖ := by
      rw [parameter_three_square_norm m x hxre n]
      convert powers_gap n hn1 using 1; ring
    have hxn : (x+(n:ℂ)).re≠m := by
      simp only [Complex.add_re,Complex.natCast_re,hxre]
      have hnreal : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
      linarith
    apply positive_matrix_kernel_zero m f ε u v (x+n) hu hv hη h₂ h₁₇ w hlead hjet
      ((2:ℝ)^n) ht
    · simpa only [Complex.ofReal_pow,Complex.ofReal_ofNat] using hX
    · exact hnorm
    · exact S.leading_quadratic_zero hm hf (x+n) hxn w hw

#print axioms quadratic_order_nonneg
end SmallLevelThirtyFourQuadraticPoleMMM
end
end

/-! ## ThirtyFourUnitMMPInhomogeneousFirstSourceGerm -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMPInhomogeneous
open Complex Matrix Filter SmallLevelThirtyFourGrid SmallLevelPrimeRates SmallLevelFiniteGridSupport
open SmallLevelThirtyFourUnitMMP
open scoped Topology

def zeroRows (X Y Z W a b : ℂ) (r : Fin 546→ℂ) : Fin 14→ℂ :=
  ![rhsZero0 X Y Z W a b r, rhsZero1 X Y Z W a b r, rhsZero2 X Y Z W a b r, rhsZero3 X Y Z W a b r, rhsZero4 X Y Z W a b r, rhsZero5 X Y Z W a b r, rhsZero6 X Y Z W a b r, rhsZero7 X Y Z W a b r, rhsZero8 X Y Z W a b r, rhsZero9 X Y Z W a b r, rhsZero10 X Y Z W a b r, rhsZero11 X Y Z W a b r, rhsZero12 X Y Z W a b r, rhsZero13 X Y Z W a b r]

theorem zeroRows_of_source (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (w : Fin 510→ℂ) (r : Fin 546→ℂ) (hw : ∀ i,sourceRows X Y Z W a b w i=r i) :
    zeroRows X Y Z W a b r=0 := by
  funext i
  fin_cases i
  · exact zero_row_0 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_1 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_2 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_3 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_4 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_5 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_6 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_7 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_8 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_9 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_10 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_11 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_12 X Y Z W a b hX hY hZ hW w r hw
  · exact zero_row_13 X Y Z W a b hX hY hZ hW w r hw

/-- The fourteen eliminated first-Taylor equations follow from the continued
original source system, with the analytic remainder retained exactly. -/
theorem first_source_zero_germ {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= v)
    (hshift : ∀ n : ℕ,0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => S.G z j) (x+n) ∨
      (x+n=((2*m:ℕ):ℂ) ∧ (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => S.G z j) (x+n))) :
    ∃ R : ℂ→Fin 546→ℂ,(∀ i,AnalyticAt ℂ (fun z => R z i) x) ∧
      ∀ᶠ z in 𝓝[≠] x,
        zeroRows (u*parameter 2 m (z-1)) (parameter 3 m (z-1))
          (v*parameter 17 m (z-1)) (parameter 5 m (z-1))
          (badParameter f 3) (badParameter f 5)
          (fun i => (∑ j,restrictedShiftMatrix selectedSource supportIndex m f ε 0 (z-1) i j*S.G z j)+R z i)=0 := by
  obtain ⟨R,hR,he⟩:=S.first_source_remainder x hshift
  refine ⟨R,hR,?_⟩
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  filter_upwards [he] with z hz
  apply zeroRows_of_source _ _ _ _ _ _
    (mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) (z-1)))
    (parameter_ne_zero 3 m (by decide) (z-1))
    (mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) (z-1)))
    (parameter_ne_zero 5 m (by decide) (z-1))
    (extension supportIndex (S.G (z-1)))
  intro i
  rw [scaled_sourceRows_actual m f ε u v (z-1) hu hv hη h₂ h₁₇]
  rw [←restrictedLeadingMatrix_mulVec]
  exact hz i

#print axioms zeroRows_of_source
#print axioms first_source_zero_germ
end SmallLevelThirtyFourUnitMMPInhomogeneous
end
end

/-! ## ThirtyFourUnitMMPInhomogeneousRhsPropertiesPart26 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMPInhomogeneous
open Complex

theorem rhsZero0_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero0 X Y Z W a b (r+t)=rhsZero0 X Y Z W a b r+rhsZero0 X Y Z W a b t := by
  simp only [rhsZero0, Pi.add_apply, rhsPivot70_add, rhsPivot110_add, rhsPivot126_add, rhsPivot235_add, rhsPivot236_add, rhsPivot256_add]
  ring

theorem rhsZero0_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero0 X Y Z W a b (c • r)=c*rhsZero0 X Y Z W a b r := by
  simp only [rhsZero0, Pi.smul_apply, smul_eq_mul, rhsPivot70_smul, rhsPivot110_smul, rhsPivot126_smul, rhsPivot235_smul, rhsPivot236_smul, rhsPivot256_smul]
  ring

def rhsZero0Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero0 X Y Z W a b
  map_add' := rhsZero0_add X Y Z W a b
  map_smul' c r := rhsZero0_smul X Y Z W a b c r

theorem rhsZero0_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero0 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot70:=rhsPivot70_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot110:=rhsPivot110_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot126:=rhsPivot126_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot236:=rhsPivot236_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero0
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero1_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero1 X Y Z W a b (r+t)=rhsZero1 X Y Z W a b r+rhsZero1 X Y Z W a b t := by
  simp only [rhsZero1, Pi.add_apply, rhsPivot77_add, rhsPivot235_add, rhsPivot236_add, rhsPivot256_add]
  ring

theorem rhsZero1_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero1 X Y Z W a b (c • r)=c*rhsZero1 X Y Z W a b r := by
  simp only [rhsZero1, Pi.smul_apply, smul_eq_mul, rhsPivot77_smul, rhsPivot235_smul, rhsPivot236_smul, rhsPivot256_smul]
  ring

def rhsZero1Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero1 X Y Z W a b
  map_add' := rhsZero1_add X Y Z W a b
  map_smul' c r := rhsZero1_smul X Y Z W a b c r

theorem rhsZero1_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero1 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot77:=rhsPivot77_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot236:=rhsPivot236_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero1
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero2_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero2 X Y Z W a b (r+t)=rhsZero2 X Y Z W a b r+rhsZero2 X Y Z W a b t := by
  simp only [rhsZero2, Pi.add_apply, rhsPivot164_add, rhsPivot239_add, rhsPivot252_add, rhsPivot255_add, rhsPivot256_add]
  ring

theorem rhsZero2_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero2 X Y Z W a b (c • r)=c*rhsZero2 X Y Z W a b r := by
  simp only [rhsZero2, Pi.smul_apply, smul_eq_mul, rhsPivot164_smul, rhsPivot239_smul, rhsPivot252_smul, rhsPivot255_smul, rhsPivot256_smul]
  ring

def rhsZero2Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero2 X Y Z W a b
  map_add' := rhsZero2_add X Y Z W a b
  map_smul' c r := rhsZero2_smul X Y Z W a b c r

theorem rhsZero2_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero2 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot164:=rhsPivot164_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot239:=rhsPivot239_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot252:=rhsPivot252_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot255:=rhsPivot255_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero2
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero3_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero3 X Y Z W a b (r+t)=rhsZero3 X Y Z W a b r+rhsZero3 X Y Z W a b t := by
  simp only [rhsZero3, Pi.add_apply, rhsPivot60_add, rhsPivot93_add, rhsPivot126_add, rhsPivot141_add, rhsPivot235_add, rhsPivot236_add, rhsPivot256_add]
  ring

theorem rhsZero3_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero3 X Y Z W a b (c • r)=c*rhsZero3 X Y Z W a b r := by
  simp only [rhsZero3, Pi.smul_apply, smul_eq_mul, rhsPivot60_smul, rhsPivot93_smul, rhsPivot126_smul, rhsPivot141_smul, rhsPivot235_smul, rhsPivot236_smul, rhsPivot256_smul]
  ring

def rhsZero3Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero3 X Y Z W a b
  map_add' := rhsZero3_add X Y Z W a b
  map_smul' c r := rhsZero3_smul X Y Z W a b c r

theorem rhsZero3_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero3 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot60:=rhsPivot60_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot93:=rhsPivot93_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot126:=rhsPivot126_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot141:=rhsPivot141_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot236:=rhsPivot236_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero3
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero4_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero4 X Y Z W a b (r+t)=rhsZero4 X Y Z W a b r+rhsZero4 X Y Z W a b t := by
  simp only [rhsZero4, Pi.add_apply, rhsPivot86_add, rhsPivot141_add, rhsPivot184_add, rhsPivot186_add, rhsPivot235_add, rhsPivot236_add, rhsPivot256_add]
  ring

theorem rhsZero4_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero4 X Y Z W a b (c • r)=c*rhsZero4 X Y Z W a b r := by
  simp only [rhsZero4, Pi.smul_apply, smul_eq_mul, rhsPivot86_smul, rhsPivot141_smul, rhsPivot184_smul, rhsPivot186_smul, rhsPivot235_smul, rhsPivot236_smul, rhsPivot256_smul]
  ring

def rhsZero4Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero4 X Y Z W a b
  map_add' := rhsZero4_add X Y Z W a b
  map_smul' c r := rhsZero4_smul X Y Z W a b c r

theorem rhsZero4_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero4 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot86:=rhsPivot86_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot141:=rhsPivot141_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot184:=rhsPivot184_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot186:=rhsPivot186_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot236:=rhsPivot236_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero4
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero5_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero5 X Y Z W a b (r+t)=rhsZero5 X Y Z W a b r+rhsZero5 X Y Z W a b t := by
  simp only [rhsZero5, Pi.add_apply, rhsPivot102_add, rhsPivot150_add, rhsPivot189_add, rhsPivot233_add, rhsPivot235_add, rhsPivot257_add]
  ring

theorem rhsZero5_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero5 X Y Z W a b (c • r)=c*rhsZero5 X Y Z W a b r := by
  simp only [rhsZero5, Pi.smul_apply, smul_eq_mul, rhsPivot102_smul, rhsPivot150_smul, rhsPivot189_smul, rhsPivot233_smul, rhsPivot235_smul, rhsPivot257_smul]
  ring

def rhsZero5Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero5 X Y Z W a b
  map_add' := rhsZero5_add X Y Z W a b
  map_smul' c r := rhsZero5_smul X Y Z W a b c r

theorem rhsZero5_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero5 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot102:=rhsPivot102_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot150:=rhsPivot150_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot189:=rhsPivot189_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot233:=rhsPivot233_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot257:=rhsPivot257_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero5
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero6_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero6 X Y Z W a b (r+t)=rhsZero6 X Y Z W a b r+rhsZero6 X Y Z W a b t := by
  simp only [rhsZero6, Pi.add_apply, rhsPivot177_add, rhsPivot178_add, rhsPivot179_add, rhsPivot189_add, rhsPivot233_add, rhsPivot235_add, rhsPivot257_add]
  ring

theorem rhsZero6_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero6 X Y Z W a b (c • r)=c*rhsZero6 X Y Z W a b r := by
  simp only [rhsZero6, Pi.smul_apply, smul_eq_mul, rhsPivot177_smul, rhsPivot178_smul, rhsPivot179_smul, rhsPivot189_smul, rhsPivot233_smul, rhsPivot235_smul, rhsPivot257_smul]
  ring

def rhsZero6Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero6 X Y Z W a b
  map_add' := rhsZero6_add X Y Z W a b
  map_smul' c r := rhsZero6_smul X Y Z W a b c r

theorem rhsZero6_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero6 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot177:=rhsPivot177_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot178:=rhsPivot178_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot179:=rhsPivot179_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot189:=rhsPivot189_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot233:=rhsPivot233_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot257:=rhsPivot257_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero6
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero7_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero7 X Y Z W a b (r+t)=rhsZero7 X Y Z W a b r+rhsZero7 X Y Z W a b t := by
  simp only [rhsZero7, Pi.add_apply, rhsPivot121_add, rhsPivot232_add, rhsPivot235_add, rhsPivot256_add, rhsPivot257_add, rhsPivot317_add, rhsPivot334_add]
  ring

theorem rhsZero7_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero7 X Y Z W a b (c • r)=c*rhsZero7 X Y Z W a b r := by
  simp only [rhsZero7, Pi.smul_apply, smul_eq_mul, rhsPivot121_smul, rhsPivot232_smul, rhsPivot235_smul, rhsPivot256_smul, rhsPivot257_smul, rhsPivot317_smul, rhsPivot334_smul]
  ring

def rhsZero7Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero7 X Y Z W a b
  map_add' := rhsZero7_add X Y Z W a b
  map_smul' c r := rhsZero7_smul X Y Z W a b c r

theorem rhsZero7_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero7 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot121:=rhsPivot121_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot232:=rhsPivot232_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot257:=rhsPivot257_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot317:=rhsPivot317_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot334:=rhsPivot334_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero7
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero8_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero8 X Y Z W a b (r+t)=rhsZero8 X Y Z W a b r+rhsZero8 X Y Z W a b t := by
  simp only [rhsZero8, Pi.add_apply, rhsPivot89_add, rhsPivot102_add, rhsPivot131_add, rhsPivot141_add, rhsPivot194_add, rhsPivot235_add, rhsPivot256_add, rhsPivot277_add, rhsPivot329_add, rhsPivot334_add]
  ring

theorem rhsZero8_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero8 X Y Z W a b (c • r)=c*rhsZero8 X Y Z W a b r := by
  simp only [rhsZero8, Pi.smul_apply, smul_eq_mul, rhsPivot89_smul, rhsPivot102_smul, rhsPivot131_smul, rhsPivot141_smul, rhsPivot194_smul, rhsPivot235_smul, rhsPivot256_smul, rhsPivot277_smul, rhsPivot329_smul, rhsPivot334_smul]
  ring

def rhsZero8Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero8 X Y Z W a b
  map_add' := rhsZero8_add X Y Z W a b
  map_smul' c r := rhsZero8_smul X Y Z W a b c r

theorem rhsZero8_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero8 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot89:=rhsPivot89_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot102:=rhsPivot102_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot131:=rhsPivot131_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot141:=rhsPivot141_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot194:=rhsPivot194_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot277:=rhsPivot277_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot329:=rhsPivot329_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot334:=rhsPivot334_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero8
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero9_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero9 X Y Z W a b (r+t)=rhsZero9 X Y Z W a b r+rhsZero9 X Y Z W a b t := by
  simp only [rhsZero9, Pi.add_apply, rhsPivot66_add, rhsPivot107_add, rhsPivot126_add, rhsPivot161_add, rhsPivot186_add, rhsPivot233_add, rhsPivot236_add, rhsPivot256_add, rhsPivot327_add, rhsPivot329_add, rhsPivot334_add]
  ring

theorem rhsZero9_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero9 X Y Z W a b (c • r)=c*rhsZero9 X Y Z W a b r := by
  simp only [rhsZero9, Pi.smul_apply, smul_eq_mul, rhsPivot66_smul, rhsPivot107_smul, rhsPivot126_smul, rhsPivot161_smul, rhsPivot186_smul, rhsPivot233_smul, rhsPivot236_smul, rhsPivot256_smul, rhsPivot327_smul, rhsPivot329_smul, rhsPivot334_smul]
  ring

def rhsZero9Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero9 X Y Z W a b
  map_add' := rhsZero9_add X Y Z W a b
  map_smul' c r := rhsZero9_smul X Y Z W a b c r

theorem rhsZero9_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero9 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot66:=rhsPivot66_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot107:=rhsPivot107_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot126:=rhsPivot126_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot161:=rhsPivot161_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot186:=rhsPivot186_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot233:=rhsPivot233_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot236:=rhsPivot236_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot327:=rhsPivot327_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot329:=rhsPivot329_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot334:=rhsPivot334_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero9
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero10_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero10 X Y Z W a b (r+t)=rhsZero10 X Y Z W a b r+rhsZero10 X Y Z W a b t := by
  simp only [rhsZero10, Pi.add_apply, rhsPivot79_add, rhsPivot87_add, rhsPivot110_add, rhsPivot174_add, rhsPivot232_add, rhsPivot235_add, rhsPivot256_add, rhsPivot265_add, rhsPivot334_add]
  ring

theorem rhsZero10_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero10 X Y Z W a b (c • r)=c*rhsZero10 X Y Z W a b r := by
  simp only [rhsZero10, Pi.smul_apply, smul_eq_mul, rhsPivot79_smul, rhsPivot87_smul, rhsPivot110_smul, rhsPivot174_smul, rhsPivot232_smul, rhsPivot235_smul, rhsPivot256_smul, rhsPivot265_smul, rhsPivot334_smul]
  ring

def rhsZero10Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero10 X Y Z W a b
  map_add' := rhsZero10_add X Y Z W a b
  map_smul' c r := rhsZero10_smul X Y Z W a b c r

theorem rhsZero10_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero10 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot79:=rhsPivot79_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot87:=rhsPivot87_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot110:=rhsPivot110_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot174:=rhsPivot174_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot232:=rhsPivot232_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot265:=rhsPivot265_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot334:=rhsPivot334_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero10
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero11_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero11 X Y Z W a b (r+t)=rhsZero11 X Y Z W a b r+rhsZero11 X Y Z W a b t := by
  simp only [rhsZero11, Pi.add_apply, rhsPivot93_add, rhsPivot126_add, rhsPivot150_add, rhsPivot189_add, rhsPivot233_add, rhsPivot236_add, rhsPivot256_add, rhsPivot257_add, rhsPivot329_add, rhsPivot334_add]
  ring

theorem rhsZero11_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero11 X Y Z W a b (c • r)=c*rhsZero11 X Y Z W a b r := by
  simp only [rhsZero11, Pi.smul_apply, smul_eq_mul, rhsPivot93_smul, rhsPivot126_smul, rhsPivot150_smul, rhsPivot189_smul, rhsPivot233_smul, rhsPivot236_smul, rhsPivot256_smul, rhsPivot257_smul, rhsPivot329_smul, rhsPivot334_smul]
  ring

def rhsZero11Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero11 X Y Z W a b
  map_add' := rhsZero11_add X Y Z W a b
  map_smul' c r := rhsZero11_smul X Y Z W a b c r

theorem rhsZero11_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero11 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot93:=rhsPivot93_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot126:=rhsPivot126_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot150:=rhsPivot150_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot189:=rhsPivot189_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot233:=rhsPivot233_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot236:=rhsPivot236_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot257:=rhsPivot257_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot329:=rhsPivot329_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot334:=rhsPivot334_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero11
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero12_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero12 X Y Z W a b (r+t)=rhsZero12 X Y Z W a b r+rhsZero12 X Y Z W a b t := by
  simp only [rhsZero12, Pi.add_apply, rhsPivot86_add, rhsPivot115_add, rhsPivot141_add, rhsPivot235_add, rhsPivot256_add, rhsPivot277_add, rhsPivot307_add, rhsPivot310_add, rhsPivot329_add, rhsPivot334_add]
  ring

theorem rhsZero12_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero12 X Y Z W a b (c • r)=c*rhsZero12 X Y Z W a b r := by
  simp only [rhsZero12, Pi.smul_apply, smul_eq_mul, rhsPivot86_smul, rhsPivot115_smul, rhsPivot141_smul, rhsPivot235_smul, rhsPivot256_smul, rhsPivot277_smul, rhsPivot307_smul, rhsPivot310_smul, rhsPivot329_smul, rhsPivot334_smul]
  ring

def rhsZero12Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero12 X Y Z W a b
  map_add' := rhsZero12_add X Y Z W a b
  map_smul' c r := rhsZero12_smul X Y Z W a b c r

theorem rhsZero12_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero12 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot86:=rhsPivot86_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot115:=rhsPivot115_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot141:=rhsPivot141_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot235:=rhsPivot235_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot256:=rhsPivot256_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot277:=rhsPivot277_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot307:=rhsPivot307_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot310:=rhsPivot310_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot329:=rhsPivot329_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot334:=rhsPivot334_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero12
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

theorem rhsZero13_add (X Y Z W a b : ℂ) (r t : Fin 546→ℂ) :
    rhsZero13 X Y Z W a b (r+t)=rhsZero13 X Y Z W a b r+rhsZero13 X Y Z W a b t := by
  simp only [rhsZero13, Pi.add_apply, rhsPivot25_add, rhsPivot220_add, rhsPivot268_add, rhsPivot354_add, rhsPivot355_add, rhsPivot357_add, rhsPivot382_add]
  ring

theorem rhsZero13_smul (X Y Z W a b c : ℂ) (r : Fin 546→ℂ) :
    rhsZero13 X Y Z W a b (c • r)=c*rhsZero13 X Y Z W a b r := by
  simp only [rhsZero13, Pi.smul_apply, smul_eq_mul, rhsPivot25_smul, rhsPivot220_smul, rhsPivot268_smul, rhsPivot354_smul, rhsPivot355_smul, rhsPivot357_smul, rhsPivot382_smul]
  ring

def rhsZero13Map (X Y Z W a b : ℂ) : (Fin 546→ℂ)→ₗ[ℂ]ℂ where
  toFun := rhsZero13 X Y Z W a b
  map_add' := rhsZero13_add X Y Z W a b
  map_smul' c r := rhsZero13_smul X Y Z W a b c r

theorem rhsZero13_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) :
    AnalyticAt ℂ (fun z => rhsZero13 (X z) (Y z) (Z z) (W z) (a z) (b z) (r z)) x := by
  have hrhsPivot25:=rhsPivot25_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot220:=rhsPivot220_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot268:=rhsPivot268_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot354:=rhsPivot354_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot355:=rhsPivot355_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot357:=rhsPivot357_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  have hrhsPivot382:=rhsPivot382_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  unfold rhsZero13
  fun_prop (disch := simp_all [mul_eq_zero,div_eq_zero_iff])

#print axioms rhsZero13_analytic
#print axioms rhsZero13Map
end SmallLevelThirtyFourUnitMMPInhomogeneous
end
end

/-! ## ThirtyFourUnitMMPInhomogeneousFirstJetPole -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMPInhomogeneous
open Complex Matrix Filter SmallLevelThirtyFourGrid SmallLevelPrimeRates
open QuantitativeArithmeticUniversalPoleVector SmallLevelLinearSourcePoleKernel
open scoped Topology

def zeroMap (X Y Z W a b : ℂ) (l : Fin 14) : (Fin 546→ℂ)→ₗ[ℂ]ℂ :=
  ![rhsZero0Map X Y Z W a b, rhsZero1Map X Y Z W a b, rhsZero2Map X Y Z W a b, rhsZero3Map X Y Z W a b, rhsZero4Map X Y Z W a b, rhsZero5Map X Y Z W a b, rhsZero6Map X Y Z W a b, rhsZero7Map X Y Z W a b, rhsZero8Map X Y Z W a b, rhsZero9Map X Y Z W a b, rhsZero10Map X Y Z W a b, rhsZero11Map X Y Z W a b, rhsZero12Map X Y Z W a b, rhsZero13Map X Y Z W a b] l

theorem zeroMap_apply (X Y Z W a b : ℂ) (l : Fin 14) (r : Fin 546→ℂ) :
    zeroMap X Y Z W a b l r=zeroRows X Y Z W a b r l := by
  fin_cases l <;> rfl

theorem zeroMap_analytic (X Y Z W a b : ℂ→ℂ) (r : ℂ→Fin 546→ℂ) (x : ℂ)
    (hX : AnalyticAt ℂ X x) (hY : AnalyticAt ℂ Y x)
    (hZ : AnalyticAt ℂ Z x) (hW : AnalyticAt ℂ W x)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hX0 : X x≠0) (hY0 : Y x≠0) (hZ0 : Z x≠0) (hW0 : W x≠0)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) (l : Fin 14) :
    AnalyticAt ℂ (fun z => zeroMap (X z) (Y z) (Z z) (W z) (a z) (b z) l (r z)) x := by
  fin_cases l
  · exact rhsZero0_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero1_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero2_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero3_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero4_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero5_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero6_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero7_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero8_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero9_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero10_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero11_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero12_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr
  · exact rhsZero13_analytic X Y Z W a b r x hX hY hZ hW ha hb hX0 hY0 hZ0 hW0 hr

def physicalZeroMap (m : ℕ) (f : ℕ→ℂ) (u v z : ℂ) (l : Fin 14) : (Fin 546→ℂ)→ₗ[ℂ]ℂ :=
  zeroMap (u*parameter 2 m (z-1)) (parameter 3 m (z-1))
    (v*parameter 17 m (z-1)) (parameter 5 m (z-1)) (badParameter f 3) (badParameter f 5) l

theorem physicalZeroMap_analytic (m : ℕ) (f : ℕ→ℂ) (u v x : ℂ)
    (hu : u≠0) (hv : v≠0) (r : ℂ→Fin 546→ℂ)
    (hr : ∀ i,AnalyticAt ℂ (fun z => r z i) x) (l : Fin 14) :
    AnalyticAt ℂ (fun z => physicalZeroMap m f u v z l (r z)) x := by
  have hp (p : ℕ) (hp : p≠0) : AnalyticAt ℂ (fun z => parameter p m (z-1)) x :=
    (parameter_analytic p m hp (x-1)).comp (f:=fun z : ℂ => z-1) (analyticAt_id.sub analyticAt_const)
  exact zeroMap_analytic _ _ _ _ _ _ r x
    (analyticAt_const.mul (hp 2 (by decide))) (hp 3 (by decide))
    (analyticAt_const.mul (hp 17 (by decide))) (hp 5 (by decide))
    analyticAt_const analyticAt_const
    (mul_ne_zero hu (parameter_ne_zero 2 m (by decide) (x-1)))
    (parameter_ne_zero 3 m (by decide) (x-1))
    (mul_ne_zero hv (parameter_ne_zero 17 m (by decide) (x-1)))
    (parameter_ne_zero 5 m (by decide) (x-1)) hr l

def firstJetMatrix (m : ℕ) (f : ℕ→ℂ) (ε u v z : ℂ) : Matrix (Fin 14) (Fin 414) ℂ :=
  fun l j => physicalZeroMap m f u v z l
    (fun i => restrictedSlopeMatrix selectedSource supportIndex m f ε (z-1) i j)

/-- All fourteen first-Taylor rows annihilate the SAME weighted pole vector
as the leading rows. This includes higher poles at the weight. -/
theorem active_first_jet_kernel {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (x u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= v)
    (w : Fin 414→ℂ)
    (hw : IsLeadingVector (fun z j => (z-((2*m:ℕ):ℂ))*S.G z j) x w)
    (hshift : ∀ n : ℕ,0<n → ∀ j,
      0≤meromorphicOrderAt (fun z => S.G z j) (x+n) ∨
      (x+n=((2*m:ℕ):ℂ) ∧ (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => S.G z j) (x+n))) :
    firstJetMatrix m f ε u v x *ᵥ w=0 := by
  obtain ⟨R,hR,he⟩:=first_source_zero_germ S x u v hu hv hη h₂ h₁₇ hshift
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  funext l
  apply eliminated_first_source_kernel _ x w hw
    (fun z => physicalZeroMap m f u v z l)
    (fun z i j => restrictedSlopeMatrix selectedSource supportIndex m f ε (z-1) i j) R
    (fun r hr => physicalZeroMap_analytic m f u v x hu0 hv0 r hr l)
    (fun i j => (restrictedSlopeMatrix_analytic selectedSource supportIndex m f ε i j (x-1)).comp (f:=fun z : ℂ => z-1)
      (analyticAt_id.sub analyticAt_const)) hR
  filter_upwards [he] with z hz
  change zeroMap _ _ _ _ _ _ l _=0
  rw [zeroMap_apply]
  simpa only [first_source_weighted,Pi.zero_apply] using congrFun hz l

#print axioms physicalZeroMap_analytic
#print axioms active_first_jet_kernel
end SmallLevelThirtyFourUnitMMPInhomogeneous
end
end

/-! ## ThirtyFourUnitMMPInhomogeneousFirstJetSource -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMPInhomogeneous
open Complex Matrix SmallLevelThirtyFourGrid SmallLevelPrimeRates SmallLevelFiniteGridSupport
open SmallLevelThirtyFourUnitMMP SmallLevelLinearSourcePoleKernel

theorem firstJetMatrix_source_apply (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= v) (w : Fin 414→ℂ) (l : Fin 14) :
    (firstJetMatrix m f ε u v x *ᵥ w) l=
      zeroRows (u*parameter 2 m (x-1)) (parameter 3 m (x-1))
        (v*parameter 17 m (x-1)) (parameter 5 m (x-1)) (badParameter f 3) (badParameter f 5)
        (sourceSlopeRows (u*parameter 2 m (x-1)) (parameter 3 m (x-1))
          (v*parameter 17 m (x-1)) (parameter 5 m (x-1)) (badParameter f 3) (badParameter f 5)
          (extension supportIndex w)) l := by
  change (∑ j,physicalZeroMap m f u v x l
    (fun i => restrictedSlopeMatrix selectedSource supportIndex m f ε (x-1) i j)*w j)=_
  rw [←apply_matrix]
  have he : (fun i => ∑ j,restrictedSlopeMatrix selectedSource supportIndex m f ε (x-1) i j*w j)=
      (fun i => slopeRows m f ε 1 (x-1) (extension supportIndex w) (selectedSource i)) := by
    funext i
    exact restrictedSlopeMatrix_mulVec selectedSource supportIndex m f ε (x-1) w i
  rw [he]
  have hs := funext (scaled_sourceSlopeRows_actual m f ε u v (x-1) hu hv hη h₂ h₁₇
    (extension supportIndex w))
  rw [←hs]
  exact zeroMap_apply _ _ _ _ _ _ l _

#print axioms firstJetMatrix_source_apply
end SmallLevelThirtyFourUnitMMPInhomogeneous
end
end

/-! ## ThirtyFourFiniteJetMMPDataBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourFiniteJetMMP
open Complex

def row0 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 0 + (((1)/(X)) + ((2)/(W^2)) + (((-1)*X)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-2)*X^2)/(W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 2
def row1 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2*Z)/(X*W^2)) + (((-1)*Y^2*Z)/(W^2)))*v 0 + (((1*Z)/(X)) + ((2*Z)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X^2*Y^2*Z)/(W^2)))*v 1 + ((((-1)*Z)/(2*W^2)) + (((-1)*Y*Z*a)/(2*W^2)) + (((-1)*Y^2*Z)/(2*W^2)) + (((-2)*X^2*Z)/(W^2)) + ((1*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + (((-3)*X^3*Y^2*Z)/(2*W^2)) + ((1*X^4*Z)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2*Z*a^2)/(2*W^2)) + ((1*X^4*Y^3*Z*a)/(2*W^2)))*v 2
def row2 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1*Z)/(X*Y^2)) + (((-1)*Z)/(Y^2)))*v 1 + ((((-1)*X*Z)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + (((-1)*X^2*Z*a)/(2*Y)) + (((-1)*X^2*Z)/(2)) + ((1*X^3*Z)/(2*Y^2)) + ((1*X^3*Z*a)/(2*Y)) + ((1*X^3*Z)/(2)))*v 2
def row3 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 0 + (((1)/(X^2)) + ((2)/(X*W^2)) + ((1)/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((4*Y^2)/(X*W^2)) + ((3)/(W^2)) + (((-1)*b)/(W)) + ((-2)) + (((-1)*Z)/(W^2)) + (((-2)*Y*a)/(W^2)) + ((3*Y^2)/(W^2)) + ((1*Y^4)/(W^2)) + (((-1)*X)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + (((-1)*Y^4)/(2*X*W^2)) + (((-3))/(2*W^2)) + (((-3)*Y*a)/(2*W^2)) + ((4*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + (((-3)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + (((-4)*X)/(W^2)) + (((-1)*X*b)/(W)) + ((1*X)/(2)) + ((1*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((2*X*Y^2)/(W^2)) + (((-2)*X*Y^2*a^2)/(W^2)) + ((1*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-2)*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(W^2)) + (((-7)*X^2)/(W^2)) + ((3*X^2)/(2)) + ((3*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-9)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-2)*X^2*Y^3*a)/(W^2)) + (((-3)*X^2*Y^4)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + ((1*X^3)/(2)) + ((1*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-7)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + ((2*X^4)/(W^2)) + ((1*X^4*Y*a)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + ((1*X^4*Y^3*a)/(W^2)))*v 2
def row4 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-2)*Y^2)/(X*W^2)) + (((-2)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 0 + ((((-1))/(X^2)) + ((1)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1))/(W^2)) + ((1*b)/(W)) + (2) + ((1*Y*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((1*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((3*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((4*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 1 + (((1)/(2*X*W^2)) + ((1*Y*a)/(2*X*W^2)) + ((1*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + (((-1))/(2*W^2)) + (((-7)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + (((-2)*X)/(W^2)) + ((1*X*b)/(W)) + (((-1)*X)/(2)) + ((1*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y*Z*a)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(W^2)) + (((-1)*X*Y^2)/(2)) + ((1*X*Y^2*Z)/(2*W^2)) + (((-2)*X*Y^4)/(W^2)) + (((-1)*X^2)/(2*W^2)) + (((-3)*X^2)/(2)) + (((-2)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + ((9*X^2*Y^2)/(2*W^2)) + (((-3)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + (((-5)*X^3)/(W^2)) + (((-1)*X^3)/(2)) + ((1*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a)/(2)) + ((3*X^3*Y^2)/(W^2)) + (((-3)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-5)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(W^2)) + (((-11)*X^4)/(2*W^2)) + ((3*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2)/(2*W^2)) + (((-3)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-5)*X^4*Y^3*a)/(2*W^2)) + (((-1)*X^4*Y^4)/(W^2)) + (((-1)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-1)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-1)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 2
def row5 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^3*W^2)) + ((1*X*Y^2)/(W^2)))*v 0 + (((1)/(X^4)) + ((2)/(X^3*W^2)) + ((2)/(X^3)) + (((-1)*Z)/(X^3*W^2)) + (((-1)*Y*a)/(X^3*W^2)) + ((4*Y^2)/(X^3*W^2)) + (((-2)*b)/(X^2*W)) + (((-4))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-2)*Y*a)/(X^2*W^2)) + ((1*Y^2)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + (((-1))/(X*W^2)) + ((2*b)/(X*W)) + ((1*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-4))/(W^2)) + (((-1)*b)/(W)) + (((-1)*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-1)*X)/(W^2)) + ((2*X*Z)/(W^2)) + ((2*X*Y*a)/(W^2)) + (((-3)*X*Y^2)/(W^2)) + ((2*X^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X^3*W^2)) + (((-1)*Y*a)/(2*X^3*W^2)) + (((-1)*Y^3*a)/(2*X^3*W^2)) + (((-1)*Y^4)/(2*X^3*W^2)) + (((-2))/(X^2*W^2)) + (((-2)*Y*a)/(X^2*W^2)) + ((4*Y^2)/(X^2*W^2)) + (((-1)*Y^2*a^2)/(X^2*W^2)) + (((-2)*Y^3*a)/(X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-7))/(2*X*W^2)) + (((-1)*b)/(X*W)) + ((1)/(2*X)) + ((1*Z)/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + ((1*Y*a)/(2*X)) + (((-1)*Y*Z*a)/(2*X*W^2)) + (((-2)*Y^2*a^2)/(X*W^2)) + ((1*Y^2)/(2*X)) + (((-1)*Y^2*Z)/(2*X*W^2)) + (((-3)*Y^3*a)/(2*X*W^2)) + ((3*Y^4)/(2*X*W^2)) + (((-11))/(2*W^2)) + ((2*b)/(W)) + (2) + ((2*Z)/(W^2)) + ((1*Y*a)/(W^2)) + ((1*Y*Z*a)/(W^2)) + (((-3)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^2*Z)/(W^2)) + (((-2)*Y^3*a)/(W^2)) + (((-3)*Y^4)/(W^2)) + (((-1)*Y^4*a^2)/(2*W^2)) + (((-1)*Y^5*a)/(2*W^2)) + (((-1)*X)/(2*W^2)) + (((-1)*X*b)/(W)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + (1*X*Y*a) + (((-3)*X*Y^2*a^2)/(2*W^2)) + (1*X*Y^2) + (((-1)*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((7*X^2)/(2*W^2)) + ((-1)*X^2) + ((1*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-7)*X^2*Y^2)/(2*W^2)) + ((5*X^2*Y^2*a^2)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((9*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-3)*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + ((1*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(W^2)) + ((1*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*Z*a)/(W^2)) + ((1*X^4*Y^2)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^2*Z)/(W^2)) + ((2*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(W^2)))*v 2
def row6 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 0 + ((((-1))/(X^3)) + (((-2))/(X^2*W^2)) + (((-1))/(X^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-4)*Y^2)/(X^2*W^2)) + (((-3))/(X*W^2)) + ((1*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-3)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + ((1)/(W^2)) + (((-1)*Z)/(W^2)) + ((1*X*Z)/(W^2)) + ((2*X*Y^2)/(W^2)))*v 1 + (((1)/(2*X^2*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(2*X^2*W^2)) + ((3)/(2*X*W^2)) + ((3*Y*a)/(2*X*W^2)) + (((-4)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(X*W^2)) + ((3*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((4)/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + (((-1)*Z)/(2*W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((2*Y^2*a^2)/(W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((2*Y^3*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((7*X)/(W^2)) + (((-3)*X)/(2)) + (((-3)*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((9*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((2*X*Y^3*a)/(W^2)) + ((3*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + (((-1)*X^2)/(2)) + ((1*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((7*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)) + (((-2)*X^3)/(W^2)) + (((-1)*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)))*v 2
def row7 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 0 + (((1)/(X^3)) + (((-1))/(X^2*W^2)) + ((1)/(X^2)) + ((2*Y^2)/(X^2*W^2)) + ((3)/(X*W^2)) + (((-1)*b)/(X*W)) + (((-2))/(X)) + (((-1)*Y*a)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-2))/(W^2)) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-1)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-5)*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + ((3*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + ((2)/(W^2)) + (((-1)*b)/(W)) + ((1)/(2)) + (((-1)*Z)/(2*W^2)) + ((1*Y*a)/(2)) + (((-1)*Y*Z*a)/(2*W^2)) + ((1*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(W^2)) + ((1*Y^2)/(2)) + (((-1)*Y^2*Z)/(2*W^2)) + ((2*Y^4)/(W^2)) + (((-3)*X)/(2*W^2)) + ((3*X)/(2)) + ((2*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + (((-9)*X*Y^2)/(2*W^2)) + ((3*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^2)/(2)) + ((1*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + ((11*X^2)/(2*W^2)) + ((1*X^2)/(2)) + (((-1)*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(2)) + (((-9)*X^2*Y^2)/(2*W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((13*X^3)/(2*W^2)) + (((-3)*X^3*Z)/(2*W^2)) + ((3*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)) + ((2*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((3*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(W^2)) + ((1*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 2

def row8 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1))/(X^3)) + (((-1))/(X^2)) + (((-1))/(X)) + ((-1)))*v 0 + ((((-1)*W^2)/(X^4*Y^2)) + ((1)/(X^3*Y^2)) + (((-1)*W^2)/(X^3*Y^2)) + (((-2))/(X^3)) + (((-3))/(X^2*Y^2)) + ((1*W*b)/(X^2*Y^2)) + ((2*W^2)/(X^2*Y^2)) + ((1*a)/(X^2*Y)) + (((-1)*Y^2)/(X^2)) + ((2)/(X*Y^2)) + (((-1)*Z)/(X*Y^2)) + (((-1)*a)/(X*Y)) + ((3)/(X)) + ((1)/(Y^2)) + (((-1)*Z)/(Y^2)) + (((-1)*a)/(Y)) + (5) + (((-1)*X)/(Y^2)) + (1*X))*v 1 + (((1)/(2*X^3*Y^2)) + ((1*a)/(2*X^3*Y)) + ((1*Y*a)/(2*X^3)) + ((1*Y^2)/(2*X^3)) + ((1*a)/(2*X^2*Y)) + (((-3))/(X^2)) + ((1*a^2)/(2*X^2)) + ((1*Y*a)/(2*X^2)) + (((-2))/(X*Y^2)) + ((1*W*b)/(X*Y^2)) + (((-1)*W^2)/(2*X*Y^2)) + ((1*Z)/(2*X*Y^2)) + (((-1)*W^2*a)/(2*X*Y)) + ((1*Z*a)/(2*X*Y)) + (((-1))/(X)) + ((1*a^2)/(X)) + (((-1)*W^2)/(2*X)) + ((1*Z)/(2*X)) + (((-2)*Y^2)/(X)) + ((3)/(2*Y^2)) + (((-3)*W^2)/(2*Y^2)) + (((-2)*a)/(Y)) + (((-1)*W^2*a)/(2*Y)) + ((9)/(2)) + (((-3)*a^2)/(2)) + (((-1)*W^2)/(2)) + ((-1)*Y*a) + ((1*Y^2*a^2)/(2)) + ((1*Y^3*a)/(2)) + (((-11)*X)/(2*Y^2)) + (((-1)*X*W^2)/(2*Y^2)) + ((1*X*Z)/(Y^2)) + (((-1)*X*W^2*a)/(2*Y)) + ((9*X)/(2)) + (((-3)*X*a^2)/(2)) + (((-1)*X*W^2)/(2)) + (((-5)*X*Y*a)/(2)) + ((-1)*X*Y^2) + (((-13)*X^2)/(2*Y^2)) + ((3*X^2*Z)/(2*Y^2)) + (((-3)*X^2*a)/(2*Y)) + ((1*X^2*Z*a)/(2*Y)) + (((-1)*X^2)/(2)) + ((-2)*X^2*a^2) + ((1*X^2*Z)/(2)) + ((-3)*X^2*Y*a) + ((-1)*X^2*Y^2) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-1)*X^3*a)/(2*Y)) + ((1*X^3*Z*a)/(2*Y)) + (((-1)*X^3)/(2)) + (((-1)*X^3*a^2)/(2)) + ((1*X^3*Z)/(2)) + ((-1)*X^3*Y*a) + (((-1)*X^3*Y^2)/(2)))*v 2
def row9 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1))/(X^3)) + (((-1))/(X^2)) + (((-1))/(X)) + ((-1)))*v 0 + (((1*W^2)/(X^4*Y^2)) + ((2)/(X^3*Y^2)) + ((1*W^2)/(X^3*Y^2)) + (((-1)*Z)/(X^3*Y^2)) + (((-1)*a)/(X^3*Y)) + ((4)/(X^3)) + ((3)/(X^2*Y^2)) + (((-1)*W*b)/(X^2*Y^2)) + (((-2)*W^2)/(X^2*Y^2)) + (((-1)*Z)/(X^2*Y^2)) + (((-2)*a)/(X^2*Y)) + ((3)/(X^2)) + ((1*Y^2)/(X^2)) + (((-1))/(X*Y^2)) + ((1*Z)/(X*Y^2)) + (((-1)*Z)/(Y^2)) + ((-2)))*v 1 + ((((-1))/(2*X^3*Y^2)) + (((-1)*a)/(2*X^3*Y)) + (((-1)*Y*a)/(2*X^3)) + (((-1)*Y^2)/(2*X^3)) + (((-3))/(2*X^2*Y^2)) + (((-3)*a)/(2*X^2*Y)) + ((4)/(X^2)) + (((-1)*a^2)/(X^2)) + (((-3)*Y*a)/(2*X^2)) + (((-1)*Y^2)/(2*X^2)) + (((-4))/(X*Y^2)) + (((-1)*W*b)/(X*Y^2)) + ((1*W^2)/(2*X*Y^2)) + ((1*Z)/(2*X*Y^2)) + (((-1)*a)/(X*Y)) + ((1*W^2*a)/(2*X*Y)) + (((-1)*Z*a)/(2*X*Y)) + ((2)/(X)) + (((-2)*a^2)/(X)) + ((1*W^2)/(2*X)) + (((-1)*Z)/(2*X)) + (((-2)*Y*a)/(X)) + ((1*Y^2)/(X)) + (((-7))/(Y^2)) + ((3*W^2)/(2*Y^2)) + ((3*Z)/(2*Y^2)) + ((1*W^2*a)/(2*Y)) + ((1*Z*a)/(2*Y)) + (((-9))/(2)) + ((1*W^2)/(2)) + ((1*Z)/(2)) + ((-2)*Y*a) + (((-3)*Y^2)/(2)) + (((-1)*Y^2*a^2)/(2)) + (((-1)*Y^3*a)/(2)) + ((1*X*W^2)/(2*Y^2)) + (((-1)*X*Z)/(2*Y^2)) + (((-1)*X*a)/(Y)) + ((1*X*W^2*a)/(2*Y)) + ((1*X*Z*a)/(2*Y)) + (((-7)*X)/(2)) + ((1*X*W^2)/(2)) + ((1*X*Z)/(2)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y^2)/(2)) + ((2*X^2)/(Y^2)) + ((1*X^2*Z)/(2*Y^2)) + ((1*X^2*a)/(Y)) + (((-1)*X^2*Z*a)/(2*Y)) + (1*X^2*a^2) + (((-1)*X^2*Z)/(2)) + (1*X^2*Y*a) + ((1*X^3*Z)/(2*Y^2)) + ((1*X^3*Z*a)/(2*Y)) + ((1*X^3*Z)/(2)))*v 2
def row10 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1)/(X^2)) + ((-1)*X^2))*v 0 + ((((-1)*W^2)/(X^3*Y^2)) + (((-2))/(X^2*Y^2)) + (((-2)*W^2)/(X^2*Y^2)) + ((1*Z)/(X^2*Y^2)) + ((1*a)/(X^2*Y)) + (((-4))/(X^2)) + ((2*W*b)/(X*Y^2)) + ((4*W^2)/(X*Y^2)) + ((1*Z)/(X*Y^2)) + ((2*a)/(X*Y)) + (((-1))/(X)) + (((-1)*Y^2)/(X)) + ((1)/(Y^2)) + (((-2)*W*b)/(Y^2)) + (((-1)*a)/(Y)) + ((-2)) + (1*Y^2) + ((4*X)/(Y^2)) + ((1*X*W*b)/(Y^2)) + ((1*X*Z)/(Y^2)) + (((-1)*X*a)/(Y)) + (3*X) + ((1*X^2)/(Y^2)) + (((-2)*X^2*Z)/(Y^2)) + (((-2)*X^2*a)/(Y)) + (3*X^2) + (((-2)*X^3)/(Y^2)) + (2*X^3))*v 1 + (((1)/(2*X^2*Y^2)) + ((1*a)/(2*X^2*Y)) + ((1*Y*a)/(2*X^2)) + ((1*Y^2)/(2*X^2)) + ((2)/(X*Y^2)) + ((2*a)/(X*Y)) + (((-4))/(X)) + ((1*a^2)/(X)) + ((2*Y*a)/(X)) + ((1*Y^2)/(X)) + ((7)/(2*Y^2)) + ((1*W*b)/(Y^2)) + (((-1)*W^2)/(2*Y^2)) + (((-1)*Z)/(2*Y^2)) + ((1*a)/(2*Y)) + (((-1)*W^2*a)/(2*Y)) + ((1*Z*a)/(2*Y)) + (2*a^2) + (((-1)*W^2)/(2)) + ((1*Z)/(2)) + ((3*Y*a)/(2)) + (((-3)*Y^2)/(2)) + ((11*X)/(2*Y^2)) + (((-2)*X*W*b)/(Y^2)) + (((-2)*X*W^2)/(Y^2)) + (((-2)*X*Z)/(Y^2)) + (((-1)*X*a)/(Y)) + (((-1)*X*Z*a)/(Y)) + ((3*X)/(2)) + (((-1)*X*a^2)/(2)) + ((-1)*X*Z) + (2*X*Y*a) + (3*X*Y^2) + ((1*X*Y^2*a^2)/(2)) + ((1*X*Y^3*a)/(2)) + ((1*X^2)/(2*Y^2)) + ((1*X^2*W*b)/(Y^2)) + ((1*X^2*Z)/(Y^2)) + ((1*X^2*a)/(Y)) + (((-1)*X^2*W^2*a)/(Y)) + ((3*X^2*a^2)/(2)) + ((-1)*X^2*W^2) + ((1*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*a^2)/(2)) + (((-1)*X^2*Y^3*a)/(2)) + (((-7)*X^3)/(2*Y^2)) + ((1*X^3*W^2)/(Y^2)) + (((-1)*X^3*Z)/(Y^2)) + (((-1)*X^3*a)/(Y)) + ((7*X^3)/(2)) + (((-5)*X^3*a^2)/(2)) + (((-5)*X^3*Y*a)/(2)) + (((-9)*X^4)/(2*Y^2)) + ((1*X^4*W^2)/(2*Y^2)) + ((3*X^4*Z)/(2*Y^2)) + ((1*X^4*W^2*a)/(2*Y)) + (((-1)*X^4*Z*a)/(2*Y)) + (((-1)*X^4*a^2)/(2)) + ((1*X^4*W^2)/(2)) + (((-1)*X^4*Z)/(2)) + ((-1)*X^4*Y*a) + (((-1)*X^4*Y^2)/(2)) + (((-2)*X^5)/(Y^2)) + ((1*X^5*Z)/(Y^2)) + (((-1)*X^5*a)/(Y)) + ((1*X^5*Z*a)/(Y)) + ((-1)*X^5) + ((-1)*X^5*a^2) + (1*X^5*Z) + ((-2)*X^5*Y*a) + ((-1)*X^5*Y^2))*v 2
def row11 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((2*Y^2)/(X^2)) + ((2*Y^2)/(X)) + (1*Y^2) + (1*X*Y^2))*v 0 + (((1*W^2)/(X^3)) + (((-1))/(X^2)) + ((2*Y^2)/(X^2)) + ((1)/(X)) + (((-1)*W*b)/(X)) + (((-2)*W^2)/(X)) + (((-1)*Y*a)/(X)) + ((1*Y^4)/(X)) + ((-1)) + (1*Z) + (1*Y*a) + ((-3)*Y^2) + ((-1)*X) + (1*X*Z) + (1*X*Y*a) + ((-4)*X*Y^2) + (1*X^2) + ((-1)*X^2*Y^2))*v 1 + ((((-1))/(2*X^2)) + (((-1)*Y*a)/(2*X^2)) + (((-1)*Y^3*a)/(2*X^2)) + (((-1)*Y^4)/(2*X^2)) + ((1)/(2*X)) + ((7*Y^2)/(2*X)) + (((-1)*Y^2*a^2)/(2*X)) + (((-1)*Y^3*a)/(2*X)) + (2) + ((-1)*W*b) + ((1*W^2)/(2)) + (((-1)*Z)/(2)) + ((1*Y*W^2*a)/(2)) + (((-1)*Y*Z*a)/(2)) + (1*Y^2) + ((-1)*Y^2*a^2) + ((1*Y^2*W^2)/(2)) + (((-1)*Y^2*Z)/(2)) + (2*Y^4) + ((1*X)/(2)) + ((3*X*W^2)/(2)) + (2*X*Y*a) + ((1*X*Y*W^2*a)/(2)) + (((-9)*X*Y^2)/(2)) + ((3*X*Y^2*a^2)/(2)) + ((1*X*Y^2*W^2)/(2)) + (1*X*Y^3*a) + (((-1)*X*Y^4*a^2)/(2)) + (((-1)*X*Y^5*a)/(2)) + (5*X^2) + ((1*X^2*W^2)/(2)) + ((-1)*X^2*Z) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*W^2*a)/(2)) + ((-3)*X^2*Y^2) + ((3*X^2*Y^2*a^2)/(2)) + ((1*X^2*Y^2*W^2)/(2)) + ((5*X^2*Y^3*a)/(2)) + (1*X^2*Y^4) + ((11*X^3)/(2)) + (((-3)*X^3*Z)/(2)) + (1*X^3*Y*a) + (((-1)*X^3*Y*Z*a)/(2)) + ((1*X^3*Y^2)/(2)) + ((3*X^3*Y^2*a^2)/(2)) + (((-1)*X^3*Y^2*Z)/(2)) + ((5*X^3*Y^3*a)/(2)) + (1*X^3*Y^4) + (1*X^4) + (((-1)*X^4*Z)/(2)) + ((1*X^4*Y*a)/(2)) + (((-1)*X^4*Y*Z*a)/(2)) + ((1*X^4*Y^2)/(2)) + ((1*X^4*Y^2*a^2)/(2)) + (((-1)*X^4*Y^2*Z)/(2)) + (1*X^4*Y^3*a) + ((1*X^4*Y^4)/(2)))*v 2
def row12 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2)) + ((1*Y^2)/(X)) + (1*Y^2) + (1*X*Y^2))*v 0 + ((((-1)*W^2)/(X^3)) + (((-2))/(X^2)) + (((-1)*W^2)/(X^2)) + ((1*Z)/(X^2)) + ((1*Y*a)/(X^2)) + (((-4)*Y^2)/(X^2)) + (((-3))/(X)) + ((1*W*b)/(X)) + ((2*W^2)/(X)) + ((1*Z)/(X)) + ((2*Y*a)/(X)) + (((-3)*Y^2)/(X)) + (((-1)*Y^4)/(X)) + (1) + (2*X*Y^2))*v 1 + (((1)/(2*X^2)) + ((1*Y*a)/(2*X^2)) + ((1*Y^3*a)/(2*X^2)) + ((1*Y^4)/(2*X^2)) + ((3)/(2*X)) + ((3*Y*a)/(2*X)) + (((-4)*Y^2)/(X)) + ((1*Y^2*a^2)/(X)) + ((3*Y^3*a)/(2*X)) + ((1*Y^4)/(2*X)) + (4) + (1*W*b) + (((-1)*W^2)/(2)) + (((-1)*Z)/(2)) + (1*Y*a) + (((-1)*Y*W^2*a)/(2)) + ((1*Y*Z*a)/(2)) + ((-2)*Y^2) + (2*Y^2*a^2) + (((-1)*Y^2*W^2)/(2)) + ((1*Y^2*Z)/(2)) + (2*Y^3*a) + ((-1)*Y^4) + (7*X) + (((-3)*X*W^2)/(2)) + (((-3)*X*Z)/(2)) + (((-1)*X*Y*W^2*a)/(2)) + (((-1)*X*Y*Z*a)/(2)) + ((9*X*Y^2)/(2)) + (((-1)*X*Y^2*W^2)/(2)) + (((-1)*X*Y^2*Z)/(2)) + (2*X*Y^3*a) + ((3*X*Y^4)/(2)) + ((1*X*Y^4*a^2)/(2)) + ((1*X*Y^5*a)/(2)) + (((-1)*X^2*W^2)/(2)) + (((-1)*X^2*Z)/(2)) + (1*X^2*Y*a) + (((-1)*X^2*Y*W^2*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2)) + ((7*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*W^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2)) + ((1*X^2*Y^3*a)/(2)) + ((1*X^2*Y^4)/(2)) + ((-2)*X^3) + ((-1)*X^3*Y*a) + ((-1)*X^3*Y^2*a^2) + ((-1)*X^3*Y^3*a))*v 2
def row13 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((-1)*Z) + (1*X*Z))*v 1 + ((1*X^2*Z) + (((-1)*X^3*Z)/(2)) + ((1*X^3*Y*Z*a)/(2)) + ((1*X^3*Y^2*Z)/(2)) + (((-1)*X^4*Z)/(2)) + (((-1)*X^4*Y*Z*a)/(2)) + (((-1)*X^4*Y^2*Z)/(2)))*v 2
def row14 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 0 + ((((-1))/(X^3)) + (((-2))/(X^2*W^2)) + (((-1))/(X^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-4)*Y^2)/(X^2*W^2)) + (((-3))/(X*W^2)) + ((1*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-3)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + ((1)/(W^2)) + ((2*X*Y^2)/(W^2)))*v 1 + (((1)/(2*X^2*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(2*X^2*W^2)) + ((3)/(2*X*W^2)) + ((3*Y*a)/(2*X*W^2)) + (((-4)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(X*W^2)) + ((3*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((4)/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + (((-1)*Z)/(2*W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((2*Y^2*a^2)/(W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((2*Y^3*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((7*X)/(W^2)) + (((-3)*X)/(2)) + (((-3)*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((9*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((2*X*Y^3*a)/(W^2)) + ((3*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((7*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)) + (((-2)*X^3)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^3*a)/(W^2)))*v 2
def row15 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1)/(X)) + (1) + (1*X) + (1*X^2))*v 0 + ((((-1)*W^2)/(X^2*Y^2)) + (((-2))/(X*Y^2)) + (((-1)*W^2)/(X*Y^2)) + ((1*Z)/(X*Y^2)) + ((1*a)/(X*Y)) + (((-4))/(X)) + (((-3))/(Y^2)) + ((1*W*b)/(Y^2)) + ((2*W^2)/(Y^2)) + ((1*Z)/(Y^2)) + ((2*a)/(Y)) + ((-3)) + ((-1)*Y^2) + ((1*X)/(Y^2)) + (2*X^2))*v 1 + (((1)/(2*X*Y^2)) + ((1*a)/(2*X*Y)) + ((1*Y*a)/(2*X)) + ((1*Y^2)/(2*X)) + ((3)/(2*Y^2)) + ((3*a)/(2*Y)) + ((-4)) + (1*a^2) + ((3*Y*a)/(2)) + ((1*Y^2)/(2)) + ((4*X)/(Y^2)) + ((1*X*W*b)/(Y^2)) + (((-1)*X*W^2)/(2*Y^2)) + (((-1)*X*Z)/(2*Y^2)) + ((1*X*a)/(Y)) + (((-1)*X*W^2*a)/(2*Y)) + ((1*X*Z*a)/(2*Y)) + ((-2)*X) + (2*X*a^2) + (((-1)*X*W^2)/(2)) + ((1*X*Z)/(2)) + (2*X*Y*a) + ((-1)*X*Y^2) + ((7*X^2)/(Y^2)) + (((-3)*X^2*W^2)/(2*Y^2)) + (((-3)*X^2*Z)/(2*Y^2)) + (((-1)*X^2*W^2*a)/(2*Y)) + (((-1)*X^2*Z*a)/(2*Y)) + ((9*X^2)/(2)) + (((-1)*X^2*W^2)/(2)) + (((-1)*X^2*Z)/(2)) + (2*X^2*Y*a) + ((3*X^2*Y^2)/(2)) + ((1*X^2*Y^2*a^2)/(2)) + ((1*X^2*Y^3*a)/(2)) + (((-1)*X^3*W^2)/(2*Y^2)) + (((-1)*X^3*Z)/(2*Y^2)) + ((1*X^3*a)/(Y)) + (((-1)*X^3*W^2*a)/(2*Y)) + (((-1)*X^3*Z*a)/(2*Y)) + ((7*X^3)/(2)) + (((-1)*X^3*W^2)/(2)) + (((-1)*X^3*Z)/(2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2)) + (((-2)*X^4)/(Y^2)) + (((-1)*X^4*a)/(Y)) + ((-1)*X^4*a^2) + ((-1)*X^4*Y*a))*v 2

def row16 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((2)/(X)) + (2) + (1*X) + (1*X^2))*v 0 + (((1*W^2)/(X^2*Y^2)) + (((-1))/(X*Y^2)) + ((2)/(X)) + ((1)/(Y^2)) + (((-1)*W*b)/(Y^2)) + (((-2)*W^2)/(Y^2)) + (((-1)*a)/(Y)) + (1*Y^2) + (((-1)*X)/(Y^2)) + ((1*X*Z)/(Y^2)) + ((1*X*a)/(Y)) + ((-3)*X) + (((-1)*X^2)/(Y^2)) + ((1*X^2*Z)/(Y^2)) + ((1*X^2*a)/(Y)) + ((-4)*X^2) + ((1*X^3)/(Y^2)) + ((-1)*X^3))*v 1 + ((((-1))/(2*X*Y^2)) + (((-1)*a)/(2*X*Y)) + (((-1)*Y*a)/(2*X)) + (((-1)*Y^2)/(2*X)) + ((1)/(2*Y^2)) + ((7)/(2)) + (((-1)*a^2)/(2)) + (((-1)*Y*a)/(2)) + ((2*X)/(Y^2)) + (((-1)*X*W*b)/(Y^2)) + ((1*X*W^2)/(2*Y^2)) + (((-1)*X*Z)/(2*Y^2)) + ((1*X*W^2*a)/(2*Y)) + (((-1)*X*Z*a)/(2*Y)) + (1*X) + ((-1)*X*a^2) + ((1*X*W^2)/(2)) + (((-1)*X*Z)/(2)) + (2*X*Y^2) + ((1*X^2)/(2*Y^2)) + ((3*X^2*W^2)/(2*Y^2)) + ((2*X^2*a)/(Y)) + ((1*X^2*W^2*a)/(2*Y)) + (((-9)*X^2)/(2)) + ((3*X^2*a^2)/(2)) + ((1*X^2*W^2)/(2)) + (1*X^2*Y*a) + (((-1)*X^2*Y^2*a^2)/(2)) + (((-1)*X^2*Y^3*a)/(2)) + ((5*X^3)/(Y^2)) + ((1*X^3*W^2)/(2*Y^2)) + (((-1)*X^3*Z)/(Y^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3*W^2*a)/(2*Y)) + ((-3)*X^3) + ((3*X^3*a^2)/(2)) + ((1*X^3*W^2)/(2)) + ((5*X^3*Y*a)/(2)) + (1*X^3*Y^2) + ((11*X^4)/(2*Y^2)) + (((-3)*X^4*Z)/(2*Y^2)) + ((1*X^4*a)/(Y)) + (((-1)*X^4*Z*a)/(2*Y)) + ((1*X^4)/(2)) + ((3*X^4*a^2)/(2)) + (((-1)*X^4*Z)/(2)) + ((5*X^4*Y*a)/(2)) + (1*X^4*Y^2) + ((1*X^5)/(Y^2)) + (((-1)*X^5*Z)/(2*Y^2)) + ((1*X^5*a)/(2*Y)) + (((-1)*X^5*Z*a)/(2*Y)) + ((1*X^5)/(2)) + ((1*X^5*a^2)/(2)) + (((-1)*X^5*Z)/(2)) + (1*X^5*Y*a) + ((1*X^5*Y^2)/(2)))*v 2
def row17 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^2)) + (((-1)*Y^2)/(X)) + ((-1)*Y^2) + ((-1)*X*Y^2))*v 0 + ((((-1)*W^2)/(X^3)) + ((1)/(X^2)) + (((-1)*W^2)/(X^2)) + (((-2)*Y^2)/(X^2)) + (((-3))/(X)) + ((1*W*b)/(X)) + ((2*W^2)/(X)) + ((1*Y*a)/(X)) + (((-1)*Y^4)/(X)) + (2) + ((-1)*Z) + ((-1)*Y*a) + (3*Y^2) + (1*X) + ((-1)*X*Z) + ((-1)*X*Y*a) + (5*X*Y^2) + ((-1)*X^2) + (1*X^2*Y^2))*v 1 + (((1)/(2*X^2)) + ((1*Y*a)/(2*X^2)) + ((1*Y^3*a)/(2*X^2)) + ((1*Y^4)/(2*X^2)) + ((1*Y*a)/(2*X)) + (((-3)*Y^2)/(X)) + ((1*Y^2*a^2)/(2*X)) + ((1*Y^3*a)/(2*X)) + ((-2)) + (1*W*b) + (((-1)*W^2)/(2)) + ((1*Z)/(2)) + (((-1)*Y*W^2*a)/(2)) + ((1*Y*Z*a)/(2)) + ((-1)*Y^2) + (1*Y^2*a^2) + (((-1)*Y^2*W^2)/(2)) + ((1*Y^2*Z)/(2)) + ((-2)*Y^4) + ((3*X)/(2)) + (((-3)*X*W^2)/(2)) + ((-2)*X*Y*a) + (((-1)*X*Y*W^2*a)/(2)) + ((9*X*Y^2)/(2)) + (((-3)*X*Y^2*a^2)/(2)) + (((-1)*X*Y^2*W^2)/(2)) + ((-1)*X*Y^3*a) + ((1*X*Y^4*a^2)/(2)) + ((1*X*Y^5*a)/(2)) + (((-11)*X^2)/(2)) + (((-1)*X^2*W^2)/(2)) + (1*X^2*Z) + (((-1)*X^2*Y*W^2*a)/(2)) + ((9*X^2*Y^2)/(2)) + (((-3)*X^2*Y^2*a^2)/(2)) + (((-1)*X^2*Y^2*W^2)/(2)) + (((-5)*X^2*Y^3*a)/(2)) + ((-1)*X^2*Y^4) + (((-13)*X^3)/(2)) + ((3*X^3*Z)/(2)) + (((-3)*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2)) + (((-1)*X^3*Y^2)/(2)) + ((-2)*X^3*Y^2*a^2) + ((1*X^3*Y^2*Z)/(2)) + ((-3)*X^3*Y^3*a) + ((-1)*X^3*Y^4) + ((-1)*X^4) + ((1*X^4*Z)/(2)) + (((-1)*X^4*Y*a)/(2)) + ((1*X^4*Y*Z*a)/(2)) + (((-1)*X^4*Y^2)/(2)) + (((-1)*X^4*Y^2*a^2)/(2)) + ((1*X^4*Y^2*Z)/(2)) + ((-1)*X^4*Y^3*a) + (((-1)*X^4*Y^4)/(2)))*v 2
def row18 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^2)) + (((-1)*Y^2)/(X)) + ((-1)*Y^2) + ((-1)*X*Y^2))*v 0 + (((1*W^2)/(X^3)) + ((2)/(X^2)) + ((1*W^2)/(X^2)) + (((-1)*Z)/(X^2)) + (((-1)*Y*a)/(X^2)) + ((4*Y^2)/(X^2)) + ((3)/(X)) + (((-1)*W*b)/(X)) + (((-2)*W^2)/(X)) + (((-1)*Z)/(X)) + (((-2)*Y*a)/(X)) + ((3*Y^2)/(X)) + ((1*Y^4)/(X)) + ((-1)) + ((-2)*X*Y^2))*v 1 + ((((-1))/(2*X^2)) + (((-1)*Y*a)/(2*X^2)) + (((-1)*Y^3*a)/(2*X^2)) + (((-1)*Y^4)/(2*X^2)) + (((-3))/(2*X)) + (((-3)*Y*a)/(2*X)) + ((4*Y^2)/(X)) + (((-1)*Y^2*a^2)/(X)) + (((-3)*Y^3*a)/(2*X)) + (((-1)*Y^4)/(2*X)) + ((-4)) + ((-1)*W*b) + ((1*W^2)/(2)) + ((1*Z)/(2)) + ((-1)*Y*a) + ((1*Y*W^2*a)/(2)) + (((-1)*Y*Z*a)/(2)) + (2*Y^2) + ((-2)*Y^2*a^2) + ((1*Y^2*W^2)/(2)) + (((-1)*Y^2*Z)/(2)) + ((-2)*Y^3*a) + (1*Y^4) + ((-7)*X) + ((3*X*W^2)/(2)) + ((3*X*Z)/(2)) + ((1*X*Y*W^2*a)/(2)) + ((1*X*Y*Z*a)/(2)) + (((-9)*X*Y^2)/(2)) + ((1*X*Y^2*W^2)/(2)) + ((1*X*Y^2*Z)/(2)) + ((-2)*X*Y^3*a) + (((-3)*X*Y^4)/(2)) + (((-1)*X*Y^4*a^2)/(2)) + (((-1)*X*Y^5*a)/(2)) + ((1*X^2*W^2)/(2)) + ((1*X^2*Z)/(2)) + ((-1)*X^2*Y*a) + ((1*X^2*Y*W^2*a)/(2)) + ((1*X^2*Y*Z*a)/(2)) + (((-7)*X^2*Y^2)/(2)) + ((1*X^2*Y^2*W^2)/(2)) + ((1*X^2*Y^2*Z)/(2)) + (((-1)*X^2*Y^3*a)/(2)) + (((-1)*X^2*Y^4)/(2)) + (2*X^3) + (1*X^3*Y*a) + (1*X^3*Y^2*a^2) + (1*X^3*Y^3*a))*v 2
def row19 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1)*Z)/(Y^2)) + ((1*X*Z)/(Y^2)))*v 1 + (((1*X^2*Z)/(Y^2)) + (((-1)*X^3*Z)/(2*Y^2)) + ((1*X^3*Z*a)/(2*Y)) + ((1*X^3*Z)/(2)) + (((-1)*X^4*Z)/(2*Y^2)) + (((-1)*X^4*Z*a)/(2*Y)) + (((-1)*X^4*Z)/(2)))*v 2
def row20 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((2*Y^2)/(X^2*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 0 + ((((-3))/(X^2*W^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-2)*Y^2)/(X^2*W^2)) + ((3)/(X*W^2)) + ((1)/(X)) + (((-1)*Y^2)/(X*W^2)) + ((1)/(W^2)) + (((-1)*X)/(W^2)) + ((2*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 1 + (((3)/(2*X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(2*X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((4)/(W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(W^2)) + ((1*Y^4)/(2*W^2)) + (((-1)*X)/(2*W^2)) + (((-1)*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((1*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-2)*X^2)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + (((-5)*X^4)/(2*W^2)) + ((1*X^4*Z)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)) + (((-1)*X^4*Y^4)/(2*W^2)) + (((-1)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-1)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-1)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 2
def row21 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-3)*Y^2)/(X^3*W^2)) + (((-1)*Y^2)/(X^2*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)) + ((2*X*Y^2)/(W^2)))*v 0 + (((1)/(X^4)) + ((5)/(X^3*W^2)) + ((1)/(X^3)) + (((-2)*Z)/(X^3*W^2)) + (((-2)*Y*a)/(X^3*W^2)) + ((6*Y^2)/(X^3*W^2)) + (((-2))/(X^2*W^2)) + (((-2)*b)/(X^2*W)) + (((-5))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-2)*Y*a)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + (((-3))/(X*W^2)) + ((3*b)/(X*W)) + ((2)/(X)) + ((2*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-2)*Y^4)/(X*W^2)) + (((-2))/(W^2)) + (((-1)*b)/(W)) + (((-2)*Z)/(W^2)) + (((-2)*X)/(W^2)) + ((2*X*Z)/(W^2)) + ((2*X*Y*a)/(W^2)) + ((2*X^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X^3*W^2)) + (((-1)*Y*a)/(2*X^3*W^2)) + (((-1)*Y^3*a)/(2*X^3*W^2)) + (((-1)*Y^4)/(2*X^3*W^2)) + (((-3))/(X^2*W^2)) + (((-5)*Y*a)/(2*X^2*W^2)) + ((5*Y^2)/(X^2*W^2)) + (((-3)*Y^2*a^2)/(2*X^2*W^2)) + (((-5)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-8))/(X*W^2)) + (((-1)*b)/(X*W)) + ((1)/(2*X)) + ((3*Z)/(2*X*W^2)) + ((1*Y*a)/(2*X)) + (((-1)*Y*Z*a)/(2*X*W^2)) + (((-3)*Y^2)/(X*W^2)) + (((-2)*Y^2*a^2)/(X*W^2)) + ((1*Y^2)/(2*X)) + (((-1)*Y^2*Z)/(2*X*W^2)) + (((-2)*Y^3*a)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-7))/(W^2)) + ((3*b)/(W)) + ((3)/(2)) + ((3*Z)/(W^2)) + (((-1)*Y*a)/(2)) + ((2*Y*Z*a)/(W^2)) + (((-7)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(W^2)) + (((-1)*Y^2)/(2)) + ((2*Y^2*Z)/(W^2)) + (((-3)*Y^3*a)/(W^2)) + (((-11)*Y^4)/(2*W^2)) + (((-1)*Y^4*a^2)/(2*W^2)) + (((-1)*Y^5*a)/(2*W^2)) + ((1*X)/(W^2)) + (((-1)*X*b)/(W)) + (((-3)*X)/(2)) + (((-1)*X*Z)/(W^2)) + (((-2)*X*Y*a)/(W^2)) + ((1*X*Y*a)/(2)) + ((11*X*Y^2)/(2*W^2)) + (((-3)*X*Y^2*a^2)/(W^2)) + ((1*X*Y^2)/(2)) + (((-3)*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(W^2)) + ((1*X*Y^5*a)/(W^2)) + (((-1)*X^2)/(W^2)) + (((-3)*X^2)/(2)) + ((2*X^2*Z)/(W^2)) + ((3*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2*W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(2)) + ((1*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + ((3*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + (((-3)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(W^2)) + (((-1)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(W^2)) + ((1*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*Z*a)/(W^2)) + ((1*X^4*Y^2)/(W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^2*Z)/(W^2)) + ((2*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(W^2)))*v 2
def row22 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-3)*Y^2)/(X^3*W^2)) + (((-1)*Y^2)/(W^2)) + ((2*X*Y^2)/(W^2)))*v 0 + (((1)/(X^4)) + ((5)/(X^3*W^2)) + ((3)/(X^3)) + (((-2)*Z)/(X^3*W^2)) + (((-2)*Y*a)/(X^3*W^2)) + ((6*Y^2)/(X^3*W^2)) + (((-1))/(X^2*W^2)) + (((-2)*b)/(X^2*W)) + (((-4))/(X^2)) + (((-2)*Z)/(X^2*W^2)) + (((-3)*Y*a)/(X^2*W^2)) + ((6*Y^2)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + ((1)/(X*W^2)) + ((1*b)/(X*W)) + (((-2))/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((5*Y^2)/(X*W^2)) + (((-4))/(W^2)) + (((-1)*b)/(W)) + (((-1)*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-3)*X)/(W^2)) + ((3*X*Z)/(W^2)) + ((3*X*Y*a)/(W^2)) + (((-6)*X*Y^2)/(W^2)) + ((3*X^2)/(W^2)) + (((-3)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X^3*W^2)) + (((-1)*Y*a)/(2*X^3*W^2)) + (((-1)*Y^3*a)/(2*X^3*W^2)) + (((-1)*Y^4)/(2*X^3*W^2)) + (((-4))/(X^2*W^2)) + (((-7)*Y*a)/(2*X^2*W^2)) + ((5*Y^2)/(X^2*W^2)) + (((-3)*Y^2*a^2)/(2*X^2*W^2)) + (((-7)*Y^3*a)/(2*X^2*W^2)) + (((-2)*Y^4)/(X^2*W^2)) + (((-9))/(X*W^2)) + (((-1)*b)/(X*W)) + ((1)/(2*X)) + ((3*Z)/(2*X*W^2)) + (((-3)*Y*a)/(2*X*W^2)) + ((1*Y*a)/(2*X)) + (((-1)*Y*Z*a)/(2*X*W^2)) + ((9*Y^2)/(2*X*W^2)) + (((-7)*Y^2*a^2)/(2*X*W^2)) + ((1*Y^2)/(2*X)) + (((-1)*Y^2*Z)/(2*X*W^2)) + (((-4)*Y^3*a)/(X*W^2)) + ((1*Y^4)/(2*X*W^2)) + (((-9))/(W^2)) + ((1*b)/(W)) + ((5)/(2)) + ((3*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((1*Y*a)/(2)) + ((1*Y*Z*a)/(W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-2)*Y^2*a^2)/(W^2)) + ((1*Y^2)/(2)) + ((1*Y^2*Z)/(W^2)) + (((-5)*Y^3*a)/(W^2)) + (((-5)*Y^4)/(2*W^2)) + (((-1)*Y^4*a^2)/(2*W^2)) + (((-1)*Y^5*a)/(2*W^2)) + (((-11)*X)/(2*W^2)) + (((-1)*X*b)/(W)) + ((3*X)/(2)) + ((1*X*Z)/(2*W^2)) + ((3*X*Y*a)/(2)) + ((1*X*Y*Z*a)/(2*W^2)) + (((-7)*X*Y^2)/(2*W^2)) + (((-3)*X*Y^2*a^2)/(2*W^2)) + ((3*X*Y^2)/(2)) + ((1*X*Y^2*Z)/(2*W^2)) + (((-5)*X*Y^3*a)/(2*W^2)) + (((-1)*X*Y^4)/(W^2)) + ((4*X^2)/(W^2)) + (((-1)*X^2)/(2)) + ((3*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-7)*X^2*Y^2)/(W^2)) + ((3*X^2*Y^2*a^2)/(W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + ((3*X^2*Y^3*a)/(W^2)) + ((9*X^3)/(W^2)) + (((-1)*X^3)/(2)) + (((-5)*X^3*Z)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + ((3*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + ((5*X^3*Y^3*a)/(2*W^2)) + ((1*X^3*Y^4)/(W^2)) + ((3*X^4)/(W^2)) + (((-3)*X^4*Z)/(2*W^2)) + ((3*X^4*Y*a)/(2*W^2)) + (((-3)*X^4*Y*Z*a)/(2*W^2)) + ((3*X^4*Y^2)/(2*W^2)) + ((3*X^4*Y^2*a^2)/(2*W^2)) + (((-3)*X^4*Y^2*Z)/(2*W^2)) + ((3*X^4*Y^3*a)/(W^2)) + ((3*X^4*Y^4)/(2*W^2)))*v 2
def row23 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((3*Y^2)/(X^2*W^2)) + ((1*X*Y^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 0 + ((((-1))/(X^3)) + (((-5))/(X^2*W^2)) + (((-3))/(X^2)) + ((2*Z)/(X^2*W^2)) + ((2*Y*a)/(X^2*W^2)) + (((-6)*Y^2)/(X^2*W^2)) + ((1)/(X*W^2)) + ((2*b)/(X*W)) + ((4)/(X)) + ((2*Z)/(X*W^2)) + ((3*Y*a)/(X*W^2)) + (((-6)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-1))/(W^2)) + (((-1)*b)/(W)) + (2) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-5)*Y^2)/(W^2)) + ((4*X)/(W^2)) + ((1*X*b)/(W)) + ((1*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((3*X*Y^2)/(W^2)) + ((3*X^2)/(W^2)) + (((-3)*X^2*Z)/(W^2)) + (((-3)*X^2*Y*a)/(W^2)) + ((6*X^2*Y^2)/(W^2)) + (((-3)*X^3)/(W^2)) + ((3*X^3*Y^2)/(W^2)))*v 1 + (((1)/(2*X^2*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(2*X^2*W^2)) + ((4)/(X*W^2)) + ((7*Y*a)/(2*X*W^2)) + (((-5)*Y^2)/(X*W^2)) + ((3*Y^2*a^2)/(2*X*W^2)) + ((7*Y^3*a)/(2*X*W^2)) + ((2*Y^4)/(X*W^2)) + ((9)/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + (((-3)*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-9)*Y^2)/(2*W^2)) + ((7*Y^2*a^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((4*Y^3*a)/(W^2)) + (((-1)*Y^4)/(2*W^2)) + ((9*X)/(W^2)) + (((-1)*X*b)/(W)) + (((-5)*X)/(2)) + (((-3)*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(W^2)) + ((1*X*Y^2)/(2*W^2)) + ((2*X*Y^2*a^2)/(W^2)) + (((-1)*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(W^2)) + ((5*X*Y^3*a)/(W^2)) + ((5*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((11*X^2)/(2*W^2)) + ((1*X^2*b)/(W)) + (((-3)*X^2)/(2)) + (((-1)*X^2*Z)/(2*W^2)) + (((-3)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((7*X^2*Y^2)/(2*W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + (((-3)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + (((-4)*X^3)/(W^2)) + ((1*X^3)/(2)) + (((-3)*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((7*X^3*Y^2)/(W^2)) + (((-3)*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + (((-3)*X^3*Y^3*a)/(W^2)) + (((-9)*X^4)/(W^2)) + ((1*X^4)/(2)) + ((5*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y*a)/(2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + (((-3)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2)/(2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + (((-5)*X^4*Y^3*a)/(2*W^2)) + (((-1)*X^4*Y^4)/(W^2)) + (((-3)*X^5)/(W^2)) + ((3*X^5*Z)/(2*W^2)) + (((-3)*X^5*Y*a)/(2*W^2)) + ((3*X^5*Y*Z*a)/(2*W^2)) + (((-3)*X^5*Y^2)/(2*W^2)) + (((-3)*X^5*Y^2*a^2)/(2*W^2)) + ((3*X^5*Y^2*Z)/(2*W^2)) + (((-3)*X^5*Y^3*a)/(W^2)) + (((-3)*X^5*Y^4)/(2*W^2)))*v 2

def row24 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((3*Y^2)/(X^2*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 0 + ((((-1))/(X^3)) + (((-5))/(X^2*W^2)) + (((-1))/(X^2)) + ((2*Z)/(X^2*W^2)) + ((2*Y*a)/(X^2*W^2)) + (((-6)*Y^2)/(X^2*W^2)) + ((2)/(X*W^2)) + ((2*b)/(X*W)) + ((5)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + ((3)/(W^2)) + (((-3)*b)/(W)) + ((-2)) + (((-2)*Y*a)/(W^2)) + (((-2)*Y^2)/(W^2)) + ((2*Y^4)/(W^2)) + ((2*X)/(W^2)) + ((1*X*b)/(W)) + ((2*X*Z)/(W^2)) + ((2*X^2)/(W^2)) + (((-2)*X^2*Z)/(W^2)) + (((-2)*X^2*Y*a)/(W^2)) + (((-2)*X^3)/(W^2)) + ((2*X^3*Y^2)/(W^2)))*v 1 + (((1)/(2*X^2*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(2*X^2*W^2)) + ((3)/(X*W^2)) + ((5*Y*a)/(2*X*W^2)) + (((-5)*Y^2)/(X*W^2)) + ((3*Y^2*a^2)/(2*X*W^2)) + ((5*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(X*W^2)) + ((8)/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + (((-3)*Z)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + ((3*Y^2)/(W^2)) + ((2*Y^2*a^2)/(W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((2*Y^3*a)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((7*X)/(W^2)) + (((-3)*X*b)/(W)) + (((-3)*X)/(2)) + (((-3)*X*Z)/(W^2)) + ((1*X*Y*a)/(2)) + (((-2)*X*Y*Z*a)/(W^2)) + ((7*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(W^2)) + ((1*X*Y^2)/(2)) + (((-2)*X*Y^2*Z)/(W^2)) + ((3*X*Y^3*a)/(W^2)) + ((11*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*b)/(W)) + ((3*X^2)/(2)) + ((1*X^2*Z)/(W^2)) + ((2*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-11)*X^2*Y^2)/(2*W^2)) + ((3*X^2*Y^2*a^2)/(W^2)) + (((-1)*X^2*Y^2)/(2)) + ((3*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(W^2)) + (((-1)*X^2*Y^5*a)/(W^2)) + ((1*X^3)/(W^2)) + ((3*X^3)/(2)) + (((-2)*X^3*Z)/(W^2)) + (((-3)*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2*W^2)) + (((-3)*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^2)/(2)) + (((-1)*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(2*W^2)) + (((-3)*X^4)/(2*W^2)) + ((1*X^4)/(2)) + ((1*X^4*Z)/(W^2)) + ((3*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y*a)/(2)) + (((-1)*X^4*Y*Z*a)/(W^2)) + ((1*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + ((1*X^4*Y^2)/(2)) + (((-1)*X^4*Y^2*Z)/(W^2)) + ((1*X^4*Y^3*a)/(W^2)) + (((-2)*X^5)/(W^2)) + ((1*X^5*Z)/(W^2)) + (((-1)*X^5*Y*a)/(W^2)) + ((1*X^5*Y*Z*a)/(W^2)) + (((-1)*X^5*Y^2)/(W^2)) + (((-1)*X^5*Y^2*a^2)/(W^2)) + ((1*X^5*Y^2*Z)/(W^2)) + (((-2)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(W^2)))*v 2
def row25 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 0 + (((2)/(X^3)) + ((1)/(X^2*W^2)) + ((2)/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + ((6*Y^2)/(X^2*W^2)) + ((6)/(X*W^2)) + (((-2)*b)/(X*W)) + (((-3))/(X)) + (((-1)*Z)/(X*W^2)) + (((-3)*Y*a)/(X*W^2)) + ((3*Y^2)/(X*W^2)) + ((2*Y^4)/(X*W^2)) + (((-1))/(W^2)) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-2)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-7)*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-2)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + (((-1)*Y^3*a)/(X^2*W^2)) + (((-1)*Y^4)/(X^2*W^2)) + (((-3))/(2*X*W^2)) + (((-2)*Y*a)/(X*W^2)) + ((7*Y^2)/(X*W^2)) + (((-3)*Y^2*a^2)/(2*X*W^2)) + (((-2)*Y^3*a)/(X*W^2)) + (((-1)*Y^4)/(2*X*W^2)) + (((-5))/(2*W^2)) + (((-2)*b)/(W)) + (1) + (((-3)*Y*a)/(2*W^2)) + (1*Y*a) + (((-1)*Y*Z*a)/(W^2)) + ((5*Y^2)/(2*W^2)) + (((-3)*Y^2*a^2)/(W^2)) + (1*Y^2) + (((-1)*Y^2*Z)/(W^2)) + (((-2)*Y^3*a)/(W^2)) + ((3*Y^4)/(W^2)) + (((-17)*X)/(2*W^2)) + (3*X) + ((3*X*Z)/(2*W^2)) + ((2*X*Y*a)/(W^2)) + (1*X*Y*a) + ((1*X*Y*Z*a)/(2*W^2)) + (((-9)*X*Y^2)/(W^2)) + ((3*X*Y^2*a^2)/(2*W^2)) + (1*X*Y^2) + ((1*X*Y^2*Z)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + (((-3)*X*Y^4)/(2*W^2)) + (((-1)*X*Y^4*a^2)/(W^2)) + (((-1)*X*Y^5*a)/(W^2)) + ((7*X^2)/(2*W^2)) + (1*X^2) + (((-1)*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + (1*X^2*Y*a) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-8)*X^2*Y^2)/(W^2)) + ((3*X^2*Y^2*a^2)/(2*W^2)) + (1*X^2*Y^2) + ((1*X^2*Y^2*Z)/(2*W^2)) + ((2*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4)/(2*W^2)) + ((9*X^3)/(W^2)) + (((-3)*X^3*Z)/(2*W^2)) + ((2*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(W^2)) + ((3*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((4*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(W^2)) + ((2*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((3*X^4*Y^3*a)/(2*W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 2
def row26 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)))*v 0 + ((((-2))/(X^3)) + (((-1))/(X^2*W^2)) + (((-2))/(X^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-6)*Y^2)/(X^2*W^2)) + (((-6))/(X*W^2)) + ((2*b)/(X*W)) + ((3)/(X)) + ((1*Z)/(X*W^2)) + ((3*Y*a)/(X*W^2)) + (((-3)*Y^2)/(X*W^2)) + (((-2)*Y^4)/(X*W^2)) + ((1)/(W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((3*Y^2)/(W^2)) + ((2*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((7*X*Y^2)/(W^2)) + (((-1)*X^2)/(W^2)) + ((2*X^2*Y^2)/(W^2)))*v 1 + (((1)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + ((1*Y^3*a)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + ((3)/(2*X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-7)*Y^2)/(X*W^2)) + ((3*Y^2*a^2)/(2*X*W^2)) + ((2*Y^3*a)/(X*W^2)) + ((1*Y^4)/(2*X*W^2)) + ((5)/(2*W^2)) + ((2*b)/(W)) + ((-1)) + ((3*Y*a)/(2*W^2)) + ((-1)*Y*a) + ((1*Y*Z*a)/(W^2)) + (((-5)*Y^2)/(2*W^2)) + ((3*Y^2*a^2)/(W^2)) + ((-1)*Y^2) + ((1*Y^2*Z)/(W^2)) + ((2*Y^3*a)/(W^2)) + (((-3)*Y^4)/(W^2)) + ((17*X)/(2*W^2)) + ((-3)*X) + (((-3)*X*Z)/(2*W^2)) + (((-2)*X*Y*a)/(W^2)) + ((-1)*X*Y*a) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((9*X*Y^2)/(W^2)) + (((-3)*X*Y^2*a^2)/(2*W^2)) + ((-1)*X*Y^2) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((1*X*Y^3*a)/(W^2)) + ((3*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(W^2)) + ((1*X*Y^5*a)/(W^2)) + (((-7)*X^2)/(2*W^2)) + ((-1)*X^2) + ((1*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((8*X^2*Y^2)/(W^2)) + (((-3)*X^2*Y^2*a^2)/(2*W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + (((-2)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + (((-9)*X^3)/(W^2)) + ((3*X^3*Z)/(2*W^2)) + (((-2)*X^3*Y*a)/(W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2)/(W^2)) + (((-3)*X^3*Y^2*a^2)/(W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-4)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(W^2)) + (((-2)*X^4)/(W^2)) + ((1*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-3)*X^4*Y^3*a)/(2*W^2)) + (((-1)*X^4*Y^4)/(2*W^2)))*v 2
def row27 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*W^2)) + (((-1))/(W^2)))*v 1 + ((((-1)*X)/(W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + ((1*X^3)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)))*v 2
def row28 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*Y^2*W^2)) + (((-1))/(Y^2*W^2)))*v 1 + ((((-1)*X)/(Y^2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(2*W^2)) + ((1*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3)/(2*W^2)))*v 2
def row29 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X)) + (1))*v 1 + ((1*X) + (((-1)*X^2)/(2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y^2)/(2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)))*v 2
def row30 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 0 + (((2)/(X*W^2)) + (((-1))/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-1))/(W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((3*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(W^2)) + (((-1)*Y*a)/(2*W^2)) + ((3*Y^2)/(2*W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + (((-1)*Y^3*a)/(W^2)) + (((-1)*Y^4)/(2*W^2)) + (((-5)*X)/(W^2)) + ((1*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(W^2)) + (((-2)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(W^2)) + (((-5)*X^2)/(2*W^2)) + ((3*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-2)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(W^2)) + (((-3)*X^3)/(2*W^2)) + ((1*X^3*Z)/(2*W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2)/(W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + (((-1)*X^4)/(W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 2
def row31 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X*Y^2)) + ((1)/(Y^2)))*v 1 + (((1*X)/(Y^2)) + (((-1)*X^2)/(2*Y^2)) + ((1*X^2*a)/(2*Y)) + ((1*X^2)/(2)) + (((-1)*X^3)/(2*Y^2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3)/(2)))*v 2

def row32 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1)*Z)/(X*Y^2)) + ((1*Z)/(Y^2)))*v 1 + (((1*X*Z)/(Y^2)) + (((-1)*X^2*Z)/(2*Y^2)) + ((1*X^2*Z*a)/(2*Y)) + ((1*X^2*Z)/(2)) + (((-1)*X^3*Z)/(2*Y^2)) + (((-1)*X^3*Z*a)/(2*Y)) + (((-1)*X^3*Z)/(2)))*v 2
def row33 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X*Y^2*W^2)) + ((1)/(Y^2*W^2)))*v 1 + (((1*X)/(Y^2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + ((1*X^2*a)/(2*Y*W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(2*Y*W^2)) + (((-1)*X^3)/(2*W^2)))*v 2
def row34 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X)) + ((-1)))*v 1 + (((-1)*X) + ((1*X^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2)))*v 2
def row35 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)))*v 0 + ((((-2))/(X*W^2)) + ((1)/(X)) + ((1*Z)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + ((1)/(W^2)) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-3)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 1 + (((1)/(W^2)) + ((1*Y*a)/(2*W^2)) + (((-3)*Y^2)/(2*W^2)) + ((1*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(W^2)) + ((1*Y^4)/(2*W^2)) + ((5*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(W^2)) + ((2*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(W^2)) + ((5*X^2)/(2*W^2)) + (((-3)*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((1*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((2*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4)/(W^2)) + ((3*X^3)/(2*W^2)) + (((-1)*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((1*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 2
def row36 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*Y^2)) + (((-1))/(Y^2)))*v 1 + ((((-1)*X)/(Y^2)) + ((1*X^2)/(2*Y^2)) + (((-1)*X^2*a)/(2*Y)) + (((-1)*X^2)/(2)) + ((1*X^3)/(2*Y^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3)/(2)))*v 2
def row37 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^2*W^2)) + (((-1)*Y^2)/(X*W^2)))*v 0 + (((1)/(X^2)) + ((2)/(X*W^2)) + (((-1))/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + (((-1)*Y^2)/(2*X*W^2)) + (((-2)*X)/(W^2)) + ((1*X^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-3)*X^2*Y^2)/(2*W^2)) + ((1*X^3)/(W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^3*a)/(2*W^2)))*v 2
def row38 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^3*W^2)) + ((1*Y^2)/(X^2*W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 0 + (((1)/(X^4)) + (((-1))/(X^3*W^2)) + ((1)/(X^3)) + ((2*Y^2)/(X^3*W^2)) + ((3)/(X^2*W^2)) + (((-1)*b)/(X^2*W)) + (((-1))/(X^2)) + (((-1)*Y*a)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + ((3)/(X*W^2)) + (((-2))/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((3*Y^2)/(X*W^2)) + (((-2))/(W^2)) + (((-1)*b)/(W)) + ((-1)) + (((-1)*Z)/(W^2)) + (((-2)*Y*a)/(W^2)) + ((1*Y^2)/(W^2)) + ((1*Y^4)/(W^2)) + ((1*X)/(W^2)))*v 1 + ((((-1))/(2*X^3*W^2)) + (((-1)*Y*a)/(2*X^3*W^2)) + (((-1)*Y^3*a)/(2*X^3*W^2)) + (((-1)*Y^4)/(2*X^3*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + ((3*Y^2)/(X^2*W^2)) + (((-1)*Y^2*a^2)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + ((3)/(2*X*W^2)) + (((-1)*b)/(X*W)) + ((1)/(2*X)) + (((-1)*Z)/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + ((1*Y*a)/(2*X)) + (((-1)*Y*Z*a)/(2*X*W^2)) + ((1*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + ((1*Y^2)/(2*X)) + (((-1)*Y^2*Z)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + ((3*Y^4)/(2*X*W^2)) + (((-7))/(2*W^2)) + ((3)/(2)) + ((1*Y*a)/(2*W^2)) + ((1*Y*a)/(2)) + ((3*Y^2)/(2*W^2)) + ((1*Y^2)/(2)) + (((-3)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(W^2)) + (((-1)*Y^4*a^2)/(2*W^2)) + (((-1)*Y^5*a)/(2*W^2)) + (((-9)*X)/(2*W^2)) + (((-1)*X*b)/(W)) + (2*X) + ((1*X*Z)/(2*W^2)) + (((-2)*X*Y*a)/(W^2)) + (1*X*Y*a) + (((-1)*X*Y*Z*a)/(2*W^2)) + (((-3)*X*Y^2)/(2*W^2)) + (((-3)*X*Y^2*a^2)/(2*W^2)) + (1*X*Y^2) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-3)*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(W^2)) + (((-1)*X^2)/(2*W^2)) + (1*X^2) + ((3*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + (1*X^2*Y*a) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-5)*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + (1*X^2*Y^2) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(W^2)) + (((-3)*X^2*Y^4)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-1)*X^3)/(2*W^2)) + ((1*X^3*Z)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)))*v 2
def row39 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2*W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 0 + (((1)/(X^3)) + (((-3))/(X^2*W^2)) + (((-1)*b)/(X^2*W)) + (((-3))/(X^2)) + (((-2)*Y^2)/(X^2*W^2)) + (((-2))/(X*W^2)) + ((2*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-3))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((3*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + ((1)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + ((2)/(W^2)) + ((2*b)/(W)) + ((1)/(2)) + ((1*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((3*Y^2*a^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((3*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(W^2)) + ((7*X)/(2*W^2)) + ((-2)*X) + (((-2)*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + ((3*X*Y^2)/(2*W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + ((2*X*Y^3*a)/(W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((3*X^2)/(W^2)) + ((-2)*X^2) + (((-1)*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((2*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-5)*X^4)/(2*W^2)) + ((1*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + (((-1)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-1)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-1)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 2

def row40 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X*W^2)) + ((1)/(W^2)))*v 1 + (((1*X)/(W^2)) + (((-1)*X^2)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y^2)/(2*W^2)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)))*v 2
def row41 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1)*a)/(Y*W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X^2)/(Y^2*W^2)) + ((1*X^2)/(W^2)))*v 1 + (((1*X^2)/(Y^2*W^2)) + ((1*X^2*a)/(Y*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3)/(W^2)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + (((-1)*X^4)/(Y^2*W^2)) + (((-1)*X^4*a)/(2*Y*W^2)) + (((-1)*X^4*a^2)/(2*W^2)) + (((-1)*X^4*Y*a)/(2*W^2)))*v 2
def row42 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1*a)/(X*Y)) + (((-1))/(Y^2)) + (((-1)*X)/(Y^2)) + ((-1)*X))*v 1 + ((((-1)*X)/(Y^2)) + (((-1)*X*a)/(Y)) + (((-1)*X^2*a)/(2*Y)) + ((-1)*X^2) + (((-1)*X^2*a^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + ((1*X^3)/(Y^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3*a^2)/(2)) + ((1*X^3*Y*a)/(2)))*v 2
def row43 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*Y^2)) + (((-1)*a)/(X*Y)) + ((1)/(Y^2)) + (1))*v 1 + (((1)/(Y^2)) + ((1*X*a)/(Y)) + (1*X) + (((-1)*X^2)/(Y^2)))*v 2
def row44 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1))/(X^2*W^2)) + (((-1))/(X*W^2)))*v 0 + (((1)/(X^2*Y^2)) + ((2)/(X*Y^2*W^2)) + ((1*a)/(X*Y)) + (((-1))/(Y^2*W^2)) + (((-1)*a)/(Y)) + (((-1)*X)/(W^2)))*v 1 + ((((-1))/(2*X*Y^2*W^2)) + (((-1)*a)/(2*X*Y*W^2)) + (((-1))/(2*X*W^2)) + (((-2)*X)/(Y^2*W^2)) + (((-1)*X*a)/(Y)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + ((1*X^2*a)/(2*Y)) + (((-3)*X^2)/(2*W^2)) + (((-1)*X^2*a^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*a^2)/(2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a)/(2)))*v 2
def row45 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y*a)/(X^2*W^2)) + (((-1))/(W^2)) + (((-1)*X)/(W^2)) + ((1*X^2*Y*a)/(W^2)))*v 0 + ((((-1)*a)/(X^3*Y)) + ((1)/(X^2*Y^2*W^2)) + ((2*a)/(X^2*Y*W^2)) + ((1*a*b)/(X^2*Y*W)) + ((3*a)/(X^2*Y)) + ((2*Y*a)/(X^2*W^2)) + ((1)/(X*Y^2*W^2)) + ((2*a)/(X*Y*W^2)) + (((-2)*a*b)/(X*Y*W)) + (((-2)*a)/(X*Y)) + (((-1)*Z*a)/(X*Y*W^2)) + ((1)/(X*W^2)) + (((-2)*a^2)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((2)/(Y^2*W^2)) + (((-1))/(Y^2)) + (((-1)*Z)/(Y^2*W^2)) + ((2*a)/(Y*W^2)) + (((-1)*a)/(Y)) + ((2)/(W^2)) + (((-3)*a^2)/(W^2)) + ((4*Y*a)/(W^2)) + ((1*Y^3*a)/(W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*Z)/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + (((-1)*X*Z*a)/(Y*W^2)) + ((3*X)/(W^2)) + (((-1)*X*a^2)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-3)*X^2*a)/(Y*W^2)) + ((1*X^2*Z*a)/(Y*W^2)) + ((1*X^2)/(W^2)) + ((1*X^2*a^2)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^3*a)/(Y*W^2)) + ((1*X^3)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)))*v 1 + (((1*a)/(2*X^2*Y*W^2)) + ((1*a^2)/(2*X^2*W^2)) + ((1*Y^2*a^2)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1)/(X*Y^2*W^2)) + (((-1)*a)/(X*Y*W^2)) + (((-1)*a^2)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + (((-1)*Y^3*a)/(X*W^2)) + (((-1)*a)/(Y*W^2)) + (((-2)*a*b)/(Y*W)) + (((-1)*a)/(2*Y)) + (((-1)*Z*a)/(2*Y*W^2)) + ((1)/(W^2)) + (((-3)*a^2)/(2*W^2)) + ((1*a^2)/(2)) + (((-1)*Z*a^2)/(2*W^2)) + ((2*Y*a)/(W^2)) + (((-3)*Y*a^3)/(2*W^2)) + ((1*Y*a)/(2)) + (((-1)*Y*Z*a)/(2*W^2)) + (((-3)*Y^2*a^2)/(2*W^2)) + ((1*Y^3*a)/(W^2)) + (((-2)*X)/(Y^2*W^2)) + (((-4)*X*a)/(Y*W^2)) + ((2*X*a)/(Y)) + ((2*X*Z*a)/(Y*W^2)) + ((3*X)/(2*W^2)) + (((-3)*X*a^2)/(2*W^2)) + (((-5)*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y^2)/(2*W^2)) + (((-2)*X*Y^2*a^2)/(W^2)) + (((-1)*X*Y^3*a^3)/(2*W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-5)*X^2)/(Y^2*W^2)) + ((1*X^2*Z)/(Y^2*W^2)) + (((-4)*X^2*a)/(Y*W^2)) + ((2*X^2*a)/(Y)) + ((1*X^2*Z*a)/(2*Y*W^2)) + ((1*X^2)/(W^2)) + (1*X^2*a^2) + ((1*X^2*Z*a^2)/(2*W^2)) + (((-4)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a^3)/(W^2)) + (1*X^2*Y*a) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-5)*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^3*a^3)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-5)*X^3)/(2*Y^2*W^2)) + ((3*X^3*Z)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(Y*W^2)) + ((1*X^3*a)/(2*Y)) + ((3*X^3*Z*a)/(2*Y*W^2)) + (((-1)*X^3)/(2*W^2)) + ((1*X^3*a^2)/(2)) + ((1*X^3*Z)/(2*W^2)) + (((-7)*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a^3)/(2*W^2)) + ((1*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + (((-3)*X^4)/(2*Y^2*W^2)) + ((1*X^4*Z)/(2*Y^2*W^2)) + ((5*X^4*a)/(2*Y*W^2)) + ((1*X^4)/(W^2)) + (((-1)*X^4*a^2)/(W^2)) + ((1*X^4*Z)/(2*W^2)) + ((1*X^4*Z*a^2)/(2*W^2)) + (((-3)*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2)/(2*W^2)) + (((-1)*X^5)/(Y^2*W^2)) + ((1*X^5*a)/(2*Y*W^2)) + (((-1)*X^5*Z*a)/(2*Y*W^2)) + (((-1)*X^5*Z*a^2)/(2*W^2)) + ((1*X^5*Y*a^3)/(2*W^2)) + (((-1)*X^5*Y*Z*a)/(2*W^2)) + ((1*X^5*Y^2*a^2)/(W^2)) + ((1*X^5*Y^3*a)/(2*W^2)))*v 2
def row46 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(Y^2)) + ((1*a)/(Y)) + (((-1)*X)/(Y^2)) + ((-1)*X))*v 1 + ((((-1)*X)/(Y^2)) + (((-1)*X^2*a)/(Y)) + ((-1)*X^2) + ((1*X^3)/(Y^2)))*v 2
def row47 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1))/(X*W^2)) + (((-1))/(W^2)))*v 0 + (((1)/(X*Y^2)) + ((2)/(Y^2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X^2)/(W^2)))*v 1 + ((((-1))/(2*Y^2*W^2)) + (((-1)*a)/(2*Y*W^2)) + (((-1))/(2*W^2)) + (((-2)*X^2)/(Y^2*W^2)) + ((1*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(2*Y*W^2)) + (((-3)*X^3)/(2*W^2)) + ((1*X^4)/(Y^2*W^2)) + ((1*X^4*a)/(2*Y*W^2)) + ((1*X^4*a^2)/(2*W^2)) + ((1*X^4*Y*a)/(2*W^2)))*v 2

def row48 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(Y^2*W^2)) + (((-1)*a)/(Y*W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X)/(W^2)))*v 1 + (((1*X)/(Y^2*W^2)) + ((1*X^2*a)/(Y*W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^3)/(Y^2*W^2)))*v 2
def row49 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(Y^2*W^2)) + ((1*a)/(Y*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X)/(W^2)))*v 1 + ((((-1)*X)/(Y^2*W^2)) + (((-1)*X^2*a)/(Y*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^3)/(Y^2*W^2)))*v 2
def row50 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1))/(X*W^2)) + (((-1))/(W^2)))*v 0 + (((2)/(X*Y^2*W^2)) + (((-1))/(X*Y^2)) + (((-1)*Z)/(X*Y^2*W^2)) + (((-1)*a)/(X*Y*W^2)) + ((2)/(X*W^2)) + (((-1))/(Y^2*W^2)) + (((-1)*Z)/(Y^2*W^2)) + ((3)/(W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X)/(W^2)) + (((-1)*X^2)/(Y^2*W^2)))*v 1 + ((((-1))/(Y^2*W^2)) + (((-1)*a)/(2*Y*W^2)) + ((3)/(2*W^2)) + (((-1)*a^2)/(2*W^2)) + (((-1)*Y*a)/(W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-5)*X)/(Y^2*W^2)) + ((1*X*Z)/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + ((1*X)/(W^2)) + (((-1)*X*a^2)/(W^2)) + (((-2)*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-7)*X^2)/(2*Y^2*W^2)) + ((3*X^2*Z)/(2*Y^2*W^2)) + (((-3)*X^2*a)/(2*Y*W^2)) + ((1*X^2*Z*a)/(2*Y*W^2)) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*a^2)/(W^2)) + ((1*X^2*Z)/(2*W^2)) + (((-2)*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-3)*X^3)/(2*Y^2*W^2)) + ((1*X^3*Z)/(2*Y^2*W^2)) + (((-1)*X^3*a)/(2*Y*W^2)) + ((1*X^3*Z*a)/(2*Y*W^2)) + (((-1)*X^3*a^2)/(W^2)) + ((1*X^3*Z)/(2*W^2)) + (((-3)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)))*v 2
def row51 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)))*v 0 + (((1)/(X*Y^2*W^2)) + (((-1))/(X)) + (((-1))/(Y^2*W^2)) + (((-2))/(W^2)) + ((1*X)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 1 + (((1)/(2*W^2)) + ((1*Y*a)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + ((3*X^2)/(2*W^2)) + ((1*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^4)/(W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 2
def row52 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(Y^2)) + (((-1)*a)/(Y)) + ((1*X)/(Y^2)) + (1*X))*v 1 + (((1*X)/(Y^2)) + ((1*X^2*a)/(Y)) + (1*X^2) + (((-1)*X^3)/(Y^2)))*v 2
def row53 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^3*W^2)) + ((1*Y^2)/(X^2*W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 0 + (((1)/(X^4)) + (((-1))/(X^3*W^2)) + ((1)/(X^3)) + ((2*Y^2)/(X^3*W^2)) + ((3)/(X^2*W^2)) + (((-1)*b)/(X^2*W)) + (((-1))/(X^2)) + (((-1)*Y*a)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + (((-1))/(X*Y^2)) + ((3)/(X*W^2)) + (((-2))/(X)) + (((-1)*Z)/(X*W^2)) + (((-1)*Y*a)/(X*W^2)) + ((3*Y^2)/(X*W^2)) + ((1)/(Y^2)) + (((-2))/(W^2)) + (((-1)*b)/(W)) + ((-1)) + (((-1)*Z)/(W^2)) + (((-2)*Y*a)/(W^2)) + ((1*Y^2)/(W^2)) + ((1*Y^4)/(W^2)) + ((1*X)/(W^2)))*v 1 + ((((-1))/(2*X^3*W^2)) + (((-1)*Y*a)/(2*X^3*W^2)) + (((-1)*Y^3*a)/(2*X^3*W^2)) + (((-1)*Y^4)/(2*X^3*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + ((3*Y^2)/(X^2*W^2)) + (((-1)*Y^2*a^2)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + ((3)/(2*X*W^2)) + (((-1)*b)/(X*W)) + ((1)/(2*X)) + (((-1)*Z)/(2*X*W^2)) + (((-1)*Y*a)/(2*X*W^2)) + ((1*Y*a)/(2*X)) + (((-1)*Y*Z*a)/(2*X*W^2)) + ((1*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + ((1*Y^2)/(2*X)) + (((-1)*Y^2*Z)/(2*X*W^2)) + (((-1)*Y^3*a)/(2*X*W^2)) + ((3*Y^4)/(2*X*W^2)) + (((-7))/(2*W^2)) + ((3)/(2)) + ((1*Y*a)/(2*W^2)) + ((1*Y*a)/(2)) + ((3*Y^2)/(2*W^2)) + ((1*Y^2)/(2)) + (((-3)*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(W^2)) + (((-1)*Y^4*a^2)/(2*W^2)) + (((-1)*Y^5*a)/(2*W^2)) + ((1*X)/(Y^2)) + (((-9)*X)/(2*W^2)) + (((-1)*X*b)/(W)) + (2*X) + ((1*X*Z)/(2*W^2)) + (((-2)*X*Y*a)/(W^2)) + (1*X*Y*a) + (((-1)*X*Y*Z*a)/(2*W^2)) + (((-3)*X*Y^2)/(2*W^2)) + (((-3)*X*Y^2*a^2)/(2*W^2)) + (1*X*Y^2) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-3)*X*Y^3*a)/(2*W^2)) + ((1*X*Y^4)/(W^2)) + (((-1)*X^2)/(2*Y^2)) + ((1*X^2*a)/(2*Y)) + (((-1)*X^2)/(2*W^2)) + ((3*X^2)/(2)) + ((3*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + (1*X^2*Y*a) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-5)*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + (1*X^2*Y^2) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(W^2)) + (((-3)*X^2*Y^4)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-1)*X^3)/(2*Y^2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + ((1*X^3*Z)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)))*v 2
def row54 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 0 + (((2)/(W^2)) + ((-1)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((2*Y^2)/(W^2)) + (((-1)*X)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((3*X*Y^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 1 + ((((-1)*X)/(W^2)) + (((-1)*X*Y*a)/(2*W^2)) + ((3*X*Y^2)/(2*W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-5)*X^2)/(W^2)) + ((1*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + (((-2)*X^2*Y^3*a)/(W^2)) + (((-1)*X^2*Y^4)/(W^2)) + (((-5)*X^3)/(2*W^2)) + ((3*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + (((-2)*X^3*Y^3*a)/(W^2)) + (((-1)*X^3*Y^4)/(W^2)) + (((-3)*X^4)/(2*W^2)) + ((1*X^4*Z)/(2*W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2)/(W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(W^2)) + (((-1)*X^4*Y^4)/(2*W^2)) + (((-1)*X^5)/(W^2)) + (((-1)*X^5*Y*a)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(2*W^2)))*v 2
def row55 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1)*a)/(X*Y)) + ((1*a)/(Y)))*v 1 + (((1*X*a)/(Y)) + (((-1)*X^2*a)/(2*Y)) + ((1*X^2*a^2)/(2)) + ((1*X^2*Y*a)/(2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3*a^2)/(2)) + (((-1)*X^3*Y*a)/(2)))*v 2

def row56 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X*Y^2*W^2)) + ((1*a)/(X*Y*W^2)) + (((-1))/(Y^2*W^2)) + (((-1))/(W^2)))*v 1 + ((((-1))/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + (((-1)*X)/(W^2)) + ((1*X^2)/(Y^2*W^2)))*v 2
def row57 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*Y^2*W^2)) + (((-1)*a)/(X*Y*W^2)) + ((1)/(Y^2*W^2)) + ((1)/(W^2)))*v 1 + (((1)/(Y^2*W^2)) + ((1*X*a)/(Y*W^2)) + ((1*X)/(W^2)) + (((-1)*X^2)/(Y^2*W^2)))*v 2
def row58 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X*Y^2)) + ((1*a)/(X*Y)) + (((-1))/(Y^2)) + ((-1)))*v 1 + ((((-1))/(Y^2)) + (((-1)*X*a)/(Y)) + ((-1)*X) + ((1*X^2)/(Y^2)))*v 2
def row59 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(Y^2)) + (((-1)*X)/(Y^2)))*v 1 + ((((-1)*X^2)/(Y^2)) + ((1*X^3)/(2*Y^2)) + (((-1)*X^3*a)/(2*Y)) + (((-1)*X^3)/(2)) + ((1*X^4)/(2*Y^2)) + ((1*X^4*a)/(2*Y)) + ((1*X^4)/(2)))*v 2
def row60 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(W^2)) + ((1*X*Y^2)/(W^2)))*v 0 + ((((-1))/(Y^2*W^2)) + (((-2))/(W^2)) + (1) + ((1*Z)/(W^2)) + ((1*Y*a)/(W^2)) + (((-2)*Y^2)/(W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-3)*X*Y^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)) + (((-1)*X^3*Y^2)/(W^2)))*v 1 + (((1*X)/(W^2)) + ((1*X*Y*a)/(2*W^2)) + (((-3)*X*Y^2)/(2*W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(2*W^2)) + ((1*X^2)/(Y^2*W^2)) + ((5*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((2*X^2*Y^3*a)/(W^2)) + ((1*X^2*Y^4)/(W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((3*X^3)/(W^2)) + (((-3)*X^3*Z)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*Z*a)/(2*W^2)) + ((1*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(W^2)) + (((-1)*X^3*Y^2*Z)/(2*W^2)) + ((2*X^3*Y^3*a)/(W^2)) + ((1*X^3*Y^4)/(W^2)) + (((-1)*X^4)/(2*Y^2*W^2)) + (((-1)*X^4*a)/(2*Y*W^2)) + ((1*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2)/(W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)) + ((1*X^5)/(W^2)) + ((1*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^3*a)/(2*W^2)))*v 2
def row61 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1)/(W^2)) + ((1*X)/(W^2)))*v 0 + ((((-2))/(Y^2*W^2)) + ((1)/(Y^2)) + ((1*Z)/(Y^2*W^2)) + ((1*a)/(Y*W^2)) + (((-2))/(W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X*Z)/(Y^2*W^2)) + ((1*X*a)/(Y*W^2)) + (((-3)*X)/(W^2)) + (((-1)*X^2)/(W^2)) + (((-1)*X^3)/(W^2)))*v 1 + (((1*X)/(Y^2*W^2)) + ((1*X*a)/(2*Y*W^2)) + (((-3)*X)/(2*W^2)) + ((1*X*a^2)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + ((1*X*Y^2)/(2*W^2)) + ((5*X^2)/(Y^2*W^2)) + (((-1)*X^2*Z)/(Y^2*W^2)) + ((1*X^2*a)/(Y*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*a^2)/(W^2)) + ((2*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + ((5*X^3)/(2*Y^2*W^2)) + (((-3)*X^3*Z)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + (((-1)*X^3*Z*a)/(2*Y*W^2)) + ((1*X^3)/(2*W^2)) + ((1*X^3*a^2)/(W^2)) + (((-1)*X^3*Z)/(2*W^2)) + ((2*X^3*Y*a)/(W^2)) + ((1*X^3*Y^2)/(W^2)) + ((3*X^4)/(2*Y^2*W^2)) + (((-1)*X^4*Z)/(2*Y^2*W^2)) + (((-1)*X^4*Z*a)/(2*Y*W^2)) + (((-1)*X^4)/(W^2)) + ((1*X^4*a^2)/(2*W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(W^2)) + ((1*X^4*Y^2)/(2*W^2)) + ((1*X^5)/(Y^2*W^2)) + ((1*X^5*a)/(2*Y*W^2)) + ((1*X^5*a^2)/(2*W^2)) + ((1*X^5*Y*a)/(2*W^2)))*v 2
def row62 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1*Z)/(X*Y^2)) + (((-1)*a)/(X*Y)) + ((1)/(Y^2)) + (((-1)*Z)/(Y^2)) + ((1*X)/(Y^2)) + (1*X))*v 1 + (((1*X)/(Y^2)) + (((-1)*X*Z)/(Y^2)) + ((1*X*a)/(Y)) + ((1*X^2*Z)/(2*Y^2)) + ((1*X^2*a)/(2*Y)) + (((-1)*X^2*Z*a)/(2*Y)) + (1*X^2) + ((1*X^2*a^2)/(2)) + (((-1)*X^2*Z)/(2)) + ((1*X^2*Y*a)/(2)) + (((-1)*X^3)/(Y^2)) + ((1*X^3*Z)/(2*Y^2)) + (((-1)*X^3*a)/(2*Y)) + ((1*X^3*Z*a)/(2*Y)) + (((-1)*X^3*a^2)/(2)) + ((1*X^3*Z)/(2)) + (((-1)*X^3*Y*a)/(2)))*v 2
def row63 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1*a)/(X*Y*W^2)) + (((-1))/(Y^2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X)/(W^2)))*v 1 + ((((-1)*X)/(Y^2*W^2)) + (((-1)*X*a)/(Y*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2)/(W^2)) + (((-1)*X^2*a^2)/(2*W^2)) + (((-1)*X^2*Y*a)/(2*W^2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*Y*a)/(2*W^2)))*v 2

def row64 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*W^2)) + ((1*b)/(X*W)) + ((1)/(X)))*v 1 + (((1)/(2*W^2)) + ((1*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + ((1*Y^4)/(2*W^2)) + (((-1)*X)/(W^2)) + (((-1)*X*b)/(W)) + ((-1)*X) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*b)/(2*W)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a*b)/(2*W)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2*W^2)) + (((-1)*X^2*Y^2*b)/(2*W)) + (((-1)*X^2*Y^2)/(2)))*v 2
def row65 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^2*W^2)) + ((1*X^2*Y^2)/(W^2)))*v 0 + (((1)/(X^3)) + ((1)/(X^2*W^2)) + (((-2))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + (((-5))/(X*W^2)) + ((1*b)/(X*W)) + ((1)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-3))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + (((-1)*Y^2*a^2)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-4))/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + ((3*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-3)*Y^2)/(W^2)) + ((3*Y^2*a^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + (((-2)*Y^4)/(W^2)) + ((7*X)/(2*W^2)) + ((1*X*b)/(2*W)) + (((-3)*X)/(2)) + (((-3)*X*Z)/(2*W^2)) + (((-1)*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a*b)/(2*W)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y*Z*a)/(2*W^2)) + (((-1)*X*Y^2*b)/(2*W)) + (((-1)*X*Y^2)/(2)) + ((1*X*Y^2*Z)/(2*W^2)) + ((1*X*Y^3*a)/(W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((4*X^2)/(W^2)) + ((1*X^2*b)/(2*W)) + (((-3)*X^2)/(2)) + (((-1)*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a*b)/(2*W)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((3*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((1*X^2*Y^2*b)/(2*W)) + (((-1)*X^2*Y^2)/(2)) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((2*X^3)/(W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + ((1*X^3*Y^3*a)/(2*W^2)) + ((1*X^3*Y^4)/(2*W^2)) + ((1*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 2
def row66 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (0)*v 1 + ((((-1)*Z)/(2*Y^2*W^2)) + (((-1)*Z)/(W^2)) + ((1*Z*a^2)/(2*W^2)) + (((-1)*Y^2*Z)/(2*W^2)) + ((1*X*Z)/(2*Y^2*W^2)) + ((1*X*Z)/(W^2)) + (((-1)*X*Z*a^2)/(2*W^2)) + ((1*X*Y^2*Z)/(2*W^2)))*v 2
def row67 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (0)*v 1 + ((((-1)*X)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((1*X^2)/(2*W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^4)/(2*W^2)))*v 2
def row68 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X*W^2)) + ((1*Y^2)/(W^2)))*v 0 + ((((-1)*a)/(X*Y)) + (((-1))/(X)) + (((-1))/(Y^2*W^2)) + (((-1)*b)/(Y^2*W)) + (((-2))/(W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X*b)/(W)) + ((1*X^2*Y^2)/(W^2)))*v 1 + ((((-1)*a)/(2*Y*W^2)) + ((1)/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + ((1*Y*a^3)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + ((1*X*a)/(Y)) + ((1*X^2*a)/(2*Y)) + ((1*X^2)/(W^2)) + (((-1)*X^2*b)/(W)) + ((1*X^2*a^2)/(2)) + ((1*X^2*Y*a)/(2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3*b)/(Y^2*W)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a*b)/(2*Y*W)) + (((-1)*X^3)/(2*W^2)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*a^2*b)/(2*W)) + ((1*X^3*Y*a)/(W^2)) + ((1*X^3*Y*a*b)/(2*W)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^4)/(W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(2*W^2)))*v 2
def row69 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2*W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 0 + (((2)/(X^4)) + (((-1))/(X^3)) + (((-1)*Z)/(X^3*W^2)) + (((-1)*Y*a)/(X^3*W^2)) + ((2*Y^2)/(X^3*W^2)) + (((-2))/(X^2*W^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + (((-1)*Y^2)/(X^2*W^2)) + (((-1))/(X)) + (((-1)*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-2))/(W^2)) + (((-1)*b)/(W)) + ((-1)) + (((-1)*Y*a)/(W^2)) + ((1*Y^4)/(W^2)) + ((2*X)/(W^2)) + (((-1)*X*Y^2)/(W^2)))*v 1 + ((((-1))/(X^3*W^2)) + (((-1)*Y*a)/(X^3*W^2)) + (((-1)*Y^3*a)/(X^3*W^2)) + (((-1)*Y^4)/(X^3*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + ((3*Y^2)/(X^2*W^2)) + (((-3)*Y^2*a^2)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + (((-5))/(2*X*W^2)) + ((1*Z)/(X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + ((1*Y^2*a^2)/(2*X*W^2)) + (((-1)*Y^4)/(2*X*W^2)) + ((1*b)/(2*W)) + (((-3)*Z)/(2*W^2)) + (((-1)*Y*a*b)/(2*W)) + ((1*Y*Z*a)/(2*W^2)) + ((3*Y^2)/(2*W^2)) + (((-1)*Y^2*b)/(2*W)) + ((1*Y^2*Z)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + (((-3)*Y^4)/(2*W^2)) + (((-1)*X)/(W^2)) + (((-1)*X*b)/(2*W)) + ((1*X)/(2)) + (((-2)*X*Y*a)/(W^2)) + ((1*X*Y*a*b)/(2*W)) + ((1*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(W^2)) + ((1*X*Y^2)/(2*W^2)) + ((1*X*Y^2*b)/(2*W)) + ((1*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(W^2)) + ((1*X*Y^3*a)/(W^2)) + ((3*X*Y^4)/(2*W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((2*X^2)/(W^2)) + ((1*X^2)/(2)) + ((1*X^2*Z)/(2*W^2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-7)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + ((1*X^3)/(2*W^2)) + ((1*X^3*Y*a)/(W^2)) + ((1*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*a^2)/(2*W^2)) + ((1*X^3*Y^3*a)/(2*W^2)))*v 2
def row70 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1*Z)/(Y^2*W^2)) + ((1*Z*b)/(Y^2*W)) + ((1*Z)/(Y^2)))*v 1 + (((1*X*Z)/(2*Y^2*W^2)) + ((1*X*Z)/(W^2)) + (((-1)*X*Z*a^2)/(2*W^2)) + ((1*X*Y^2*Z)/(2*W^2)) + (((-1)*X^2*Z)/(Y^2*W^2)) + (((-1)*X^2*Z*b)/(Y^2*W)) + (((-1)*X^2*Z)/(Y^2)) + (((-1)*X^3*Z)/(2*Y^2*W^2)) + (((-1)*X^3*Z*b)/(2*Y^2*W)) + (((-1)*X^3*Z)/(2*Y^2)) + (((-1)*X^3*Z*a)/(2*Y*W^2)) + (((-1)*X^3*Z*a*b)/(2*Y*W)) + (((-1)*X^3*Z*a)/(2*Y)) + (((-1)*X^3*Z)/(2*W^2)) + (((-1)*X^3*Z*b)/(2*W)) + (((-1)*X^3*Z)/(2)))*v 2
def row71 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2*W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 0 + (((1)/(X^3)) + (((-2))/(X^2*W^2)) + (((-2))/(X^2)) + (((-2)*Y^2)/(X^2*W^2)) + (((-2))/(X*W^2)) + ((2*b)/(X*W)) + ((2)/(X)) + ((1*Z)/(X*W^2)) + ((2*Y*a)/(X*W^2)) + (((-2)*Y^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + (((-3))/(W^2)) + (1) + ((3*Y*a)/(W^2)) + (((-4)*Y^2)/(W^2)) + (((-1)*Y^4)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((3*X^2)/(W^2)) + (((-1)*X^2*Z)/(W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y^2)/(W^2)) + (((-1)*X^3)/(W^2)) + ((1*X^3*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X^2*W^2)) + (((-1)*Y*a)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(2*X^2*W^2)) + (((-1)*Y^4)/(2*X^2*W^2)) + ((3)/(2*X*W^2)) + ((1*Y*a)/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2*a^2)/(2*X*W^2)) + ((1*Y^3*a)/(X*W^2)) + ((3*Y^4)/(2*X*W^2)) + ((1)/(W^2)) + ((1*b)/(W)) + (((-1))/(2)) + ((1*Z)/(2*W^2)) + ((3*Y*a)/(2*W^2)) + (((-1)*Y*a)/(2)) + ((1*Y*Z*a)/(2*W^2)) + (((-2)*Y^2)/(W^2)) + ((3*Y^2*a^2)/(2*W^2)) + (((-1)*Y^2)/(2)) + ((1*Y^2*Z)/(2*W^2)) + ((3*Y^3*a)/(2*W^2)) + (((-1)*Y^4)/(W^2)) + ((3*X)/(W^2)) + (((-1)*X*b)/(2*W)) + (((-5)*X)/(2)) + (((-2)*X*Z)/(W^2)) + ((1*X*Y*a)/(2*W^2)) + (((-1)*X*Y*a*b)/(2*W)) + (((-1)*X*Y*a)/(2)) + ((1*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^2*b)/(2*W)) + (((-1)*X*Y^2)/(2)) + ((2*X*Y^3*a)/(W^2)) + ((1*X*Y^4*a^2)/(2*W^2)) + ((1*X*Y^5*a)/(2*W^2)) + ((3*X^2)/(W^2)) + ((-2)*X^2) + (((-1)*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((-1)*X^2*Y*a) + (((-1)*X^2*Y*Z*a)/(2*W^2)) + ((2*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((-1)*X^2*Y^2) + (((-1)*X^2*Y^2*Z)/(2*W^2)) + ((5*X^2*Y^3*a)/(2*W^2)) + ((1*X^2*Y^4)/(W^2)) + ((1*X^2*Y^4*a^2)/(2*W^2)) + ((1*X^2*Y^5*a)/(2*W^2)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Z)/(W^2)) + (((-1)*X^3*Y*a)/(W^2)) + (((-1)*X^3*Y*a)/(2)) + ((3*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*a^2)/(2*W^2)) + (((-1)*X^3*Y^2)/(2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-5)*X^4)/(2*W^2)) + ((1*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + (((-1)*X^5)/(W^2)) + ((1*X^5*Z)/(2*W^2)) + (((-1)*X^5*Y*a)/(2*W^2)) + ((1*X^5*Y*Z*a)/(2*W^2)) + (((-1)*X^5*Y^2)/(2*W^2)) + (((-1)*X^5*Y^2*a^2)/(2*W^2)) + ((1*X^5*Y^2*Z)/(2*W^2)) + (((-1)*X^5*Y^3*a)/(W^2)) + (((-1)*X^5*Y^4)/(2*W^2)))*v 2

def row72 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1)*a)/(Y*W^2)) + (((-1)*a)/(Y)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X^2*b)/(Y^2*W)) + (((-1)*X^2*b)/(W)))*v 1 + ((((-1)*X*a)/(2*Y*W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + (((-1)*X^2*b)/(Y^2*W)) + ((1*X^2*a)/(Y*W^2)) + ((1*X^2*a)/(Y)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a)/(2*Y)) + ((1*X^3*a^2)/(2*W^2)) + (((-1)*X^3*b)/(W)) + ((1*X^3*a^2)/(2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a)/(2)) + ((1*X^4*b)/(Y^2*W)) + ((1*X^4*a*b)/(2*Y*W)) + ((1*X^4*a^2*b)/(2*W)) + ((1*X^4*Y*a*b)/(2*W)))*v 2
def row73 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(W^2)) + ((1*b)/(W)) + (1))*v 1 + (((1*X)/(2*W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(W^2)) + (((-1)*X^2*b)/(W)) + ((-1)*X^2) + (((-1)*X^3)/(2*W^2)) + (((-1)*X^3*b)/(2*W)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a*b)/(2*W)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2*W^2)) + (((-1)*X^3*Y^2*b)/(2*W)) + (((-1)*X^3*Y^2)/(2)))*v 2
def row74 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X^2*W^2)) + ((1)/(X*W^2)) + (((-1))/(X)) + (1))*v 1 + (((1)/(W^2)) + (((-1)*X)/(2*W^2)) + (1*X) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y^2)/(2*W^2)) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*a)/(2)) + (((-1)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2)/(2)) + (((-1)*X^3)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2)))*v 2
def row75 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(W^2)) + (((-1)*b)/(W)) + ((-1)))*v 1 + ((((-1)*X)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + ((1*X^2)/(W^2)) + ((1*X^2*b)/(W)) + (1*X^2) + ((1*X^3)/(2*W^2)) + ((1*X^3*b)/(2*W)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a*b)/(2*W)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*b)/(2*W)) + ((1*X^3*Y^2)/(2)))*v 2
def row76 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1)/(X*W^2)) + ((1)/(W^2)))*v 0 + ((((-1))/(X*Y^2)) + (((-2))/(Y^2*W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X^2)/(W^2)))*v 1 + (((1)/(2*Y^2*W^2)) + ((1*a)/(2*Y*W^2)) + ((1)/(2*W^2)) + ((1*X*a)/(2*Y*W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + ((1*X*Y^3*a)/(2*W^2)) + ((2*X^2)/(Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a^3)/(2*W^2)) + (((-1)*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + ((3*X^3)/(2*W^2)) + (((-1)*X^4)/(Y^2*W^2)) + (((-1)*X^4*a)/(2*Y*W^2)) + (((-1)*X^4*a^2)/(2*W^2)) + (((-1)*X^4*Y*a)/(2*W^2)))*v 2
def row77 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*Y^2*W^2)) + (((-1)*Z*b)/(X*Y^2*W)) + (((-1))/(Y^2*W^2)) + ((1*Z*b)/(Y^2*W)))*v 1 + ((((-1)*X)/(Y^2*W^2)) + ((1*X*Z*b)/(Y^2*W)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*Z*b)/(2*Y^2*W)) + (((-1)*X^2*a)/(2*Y*W^2)) + ((1*X^2*Z*a*b)/(2*Y*W)) + (((-1)*X^2)/(2*W^2)) + ((1*X^2*Z*b)/(2*W)) + ((1*X^3)/(2*Y^2*W^2)) + (((-1)*X^3*Z*b)/(2*Y^2*W)) + ((1*X^3*a)/(2*Y*W^2)) + (((-1)*X^3*Z*a*b)/(2*Y*W)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*Z*b)/(2*W)))*v 2
def row78 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (((1*Y^2)/(X^2*W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 0 + ((((-1))/(X^3)) + (((-1))/(X^2*W^2)) + ((2)/(X^2)) + ((1*Z)/(X^2*W^2)) + ((1*Y*a)/(X^2*W^2)) + ((5)/(X*W^2)) + (((-1)*b)/(X*W)) + (((-1))/(X)) + (((-1)*Z)/(X*W^2)) + (((-2)*Y*a)/(X*W^2)) + ((1*Y^2)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + ((3)/(W^2)) + ((-1)) + (((-3)*Y*a)/(W^2)) + ((4*Y^2)/(W^2)) + ((1*Y^4)/(W^2)) + (((-1)*X*Z)/(W^2)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2*Y^2)/(W^2)))*v 1 + (((1)/(2*X^2*W^2)) + ((1*Y*a)/(2*X^2*W^2)) + ((1*Y^3*a)/(2*X^2*W^2)) + ((1*Y^4)/(2*X^2*W^2)) + ((1*Y^2*a^2)/(X*W^2)) + (((-1)*Y^4)/(X*W^2)) + ((4)/(W^2)) + (((-1)*b)/(W)) + ((1)/(2)) + (((-3)*Z)/(2*W^2)) + (((-3)*Y*a)/(2*W^2)) + ((1*Y*a)/(2)) + (((-1)*Y*Z*a)/(2*W^2)) + ((3*Y^2)/(W^2)) + (((-3)*Y^2*a^2)/(2*W^2)) + ((1*Y^2)/(2)) + (((-1)*Y^2*Z)/(2*W^2)) + (((-1)*Y^3*a)/(2*W^2)) + ((2*Y^4)/(W^2)) + (((-7)*X)/(2*W^2)) + (((-1)*X*b)/(2*W)) + ((3*X)/(2)) + ((3*X*Z)/(2*W^2)) + ((1*X*Y*a)/(2*W^2)) + ((1*X*Y*a*b)/(2*W)) + ((1*X*Y*a)/(2)) + (((-1)*X*Y*Z*a)/(2*W^2)) + ((1*X*Y^2*b)/(2*W)) + ((1*X*Y^2)/(2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + (((-1)*X*Y^3*a)/(W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + (((-4)*X^2)/(W^2)) + (((-1)*X^2*b)/(2*W)) + ((3*X^2)/(2)) + ((1*X^2*Z)/(2*W^2)) + (((-1)*X^2*Y*a*b)/(2*W)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y*Z*a)/(2*W^2)) + (((-3)*X^2*Y^2)/(W^2)) + (((-1)*X^2*Y^2*a^2)/(W^2)) + (((-1)*X^2*Y^2*b)/(2*W)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^2*Z)/(2*W^2)) + (((-5)*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^2*Y^4)/(W^2)) + (((-1)*X^2*Y^4*a^2)/(2*W^2)) + (((-1)*X^2*Y^5*a)/(2*W^2)) + (((-2)*X^3)/(W^2)) + ((1*X^3)/(2)) + ((1*X^3*Z)/(W^2)) + ((1*X^3*Y*a)/(2)) + (((-1)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2)/(2)) + (((-1)*X^3*Y^3*a)/(2*W^2)) + (((-1)*X^3*Y^4)/(2*W^2)) + (((-1)*X^4)/(W^2)) + ((1*X^4*Z)/(2*W^2)) + (((-1)*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y*Z*a)/(2*W^2)) + (((-1)*X^4*Y^2)/(2*W^2)) + (((-1)*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^2*Z)/(2*W^2)) + (((-1)*X^4*Y^3*a)/(W^2)) + (((-1)*X^4*Y^4)/(2*W^2)))*v 2
def row79 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1)*Z)/(Y^2*W^2)) + (((-1)*Z*b)/(Y^2*W)) + (((-1)*Z)/(Y^2)))*v 1 + ((((-1)*X*Z)/(2*Y^2*W^2)) + (((-1)*X*Z)/(W^2)) + ((1*X*Z*a^2)/(2*W^2)) + (((-1)*X*Y^2*Z)/(2*W^2)) + ((1*X^2*Z)/(Y^2*W^2)) + ((1*X^2*Z*b)/(Y^2*W)) + ((1*X^2*Z)/(Y^2)) + ((1*X^3*Z)/(2*Y^2*W^2)) + ((1*X^3*Z*b)/(2*Y^2*W)) + ((1*X^3*Z)/(2*Y^2)) + ((1*X^3*Z*a)/(2*Y*W^2)) + ((1*X^3*Z*a*b)/(2*Y*W)) + ((1*X^3*Z*a)/(2*Y)) + ((1*X^3*Z)/(2*W^2)) + ((1*X^3*Z*b)/(2*W)) + ((1*X^3*Z)/(2)))*v 2

def row80 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1)*Y^2)/(X^3*W^2)) + ((1*X*Y^2)/(W^2)))*v 0 + ((((-1))/(X^4)) + ((2)/(X^3*W^2)) + ((2)/(X^3)) + ((2*Y^2)/(X^3*W^2)) + ((2)/(X^2*W^2)) + (((-2)*b)/(X^2*W)) + (((-2))/(X^2)) + (((-1)*Z)/(X^2*W^2)) + (((-2)*Y*a)/(X^2*W^2)) + ((2*Y^2)/(X^2*W^2)) + ((1*Y^4)/(X^2*W^2)) + ((3)/(X*W^2)) + (((-1))/(X)) + (((-3)*Y*a)/(X*W^2)) + ((4*Y^2)/(X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-1)*Z)/(W^2)) + (((-1)*Y*a)/(W^2)) + ((1*Y^2)/(W^2)) + (((-3)*X)/(W^2)) + ((1*X*Z)/(W^2)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X^2)/(W^2)) + (((-1)*X^2*Y^2)/(W^2)))*v 1 + (((1)/(2*X^3*W^2)) + ((1*Y*a)/(2*X^3*W^2)) + ((1*Y^3*a)/(2*X^3*W^2)) + ((1*Y^4)/(2*X^3*W^2)) + (((-3))/(2*X^2*W^2)) + (((-1)*Y*a)/(X^2*W^2)) + ((1*Y^2)/(X^2*W^2)) + ((1*Y^2*a^2)/(2*X^2*W^2)) + (((-1)*Y^3*a)/(X^2*W^2)) + (((-3)*Y^4)/(2*X^2*W^2)) + (((-1))/(X*W^2)) + (((-1)*b)/(X*W)) + ((1)/(2*X)) + (((-1)*Z)/(2*X*W^2)) + (((-3)*Y*a)/(2*X*W^2)) + ((1*Y*a)/(2*X)) + (((-1)*Y*Z*a)/(2*X*W^2)) + ((2*Y^2)/(X*W^2)) + (((-3)*Y^2*a^2)/(2*X*W^2)) + ((1*Y^2)/(2*X)) + (((-1)*Y^2*Z)/(2*X*W^2)) + (((-3)*Y^3*a)/(2*X*W^2)) + ((1*Y^4)/(X*W^2)) + (((-3))/(W^2)) + ((1*b)/(2*W)) + ((5)/(2)) + ((2*Z)/(W^2)) + (((-1)*Y*a)/(2*W^2)) + ((1*Y*a*b)/(2*W)) + ((1*Y*a)/(2)) + (((-1)*Y^2)/(W^2)) + (((-1)*Y^2*a^2)/(2*W^2)) + ((1*Y^2*b)/(2*W)) + ((1*Y^2)/(2)) + (((-2)*Y^3*a)/(W^2)) + (((-1)*Y^4*a^2)/(2*W^2)) + (((-1)*Y^5*a)/(2*W^2)) + (((-5)*X)/(2*W^2)) + (2*X) + ((1*X*Z)/(2*W^2)) + ((1*X*Y*a)/(W^2)) + (1*X*Y*a) + ((1*X*Y*Z*a)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + (((-3)*X*Y^2*a^2)/(2*W^2)) + (1*X*Y^2) + ((1*X*Y^2*Z)/(2*W^2)) + (((-5)*X*Y^3*a)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-1)*X*Y^4*a^2)/(2*W^2)) + (((-1)*X*Y^5*a)/(2*W^2)) + (((-1)*X^2)/(W^2)) + ((1*X^2)/(2)) + ((1*X^2*Z)/(W^2)) + ((1*X^2*Y*a)/(W^2)) + ((1*X^2*Y*a)/(2)) + (((-5)*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*a^2)/(W^2)) + ((1*X^2*Y^2)/(2)) + ((1*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^2*Y^4)/(2*W^2)) + ((5*X^3)/(2*W^2)) + (((-1)*X^3*Z)/(2*W^2)) + (((-1)*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*Z*a)/(2*W^2)) + (((-1)*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*Z)/(2*W^2)) + ((1*X^4)/(W^2)) + (((-1)*X^4*Z)/(2*W^2)) + ((1*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*Z*a)/(2*W^2)) + ((1*X^4*Y^2)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + (((-1)*X^4*Y^2*Z)/(2*W^2)) + ((1*X^4*Y^3*a)/(W^2)) + ((1*X^4*Y^4)/(2*W^2)))*v 2
def row81 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1*a)/(X*Y*W^2)) + ((1*a)/(X*Y)) + ((1*b)/(Y^2*W)) + ((1*X*b)/(Y^2*W)) + ((1*X*b)/(W)))*v 1 + (((1*a)/(2*Y*W^2)) + ((1*Y*a)/(W^2)) + (((-1)*Y*a^3)/(2*W^2)) + ((1*Y^3*a)/(2*W^2)) + ((1*X*b)/(Y^2*W)) + (((-1)*X*a)/(Y*W^2)) + (((-1)*X*a)/(Y)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a)/(2*Y)) + (((-1)*X^2*a^2)/(2*W^2)) + ((1*X^2*b)/(W)) + (((-1)*X^2*a^2)/(2)) + (((-1)*X^2*Y*a)/(2*W^2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^3*b)/(Y^2*W)) + (((-1)*X^3*a*b)/(2*Y*W)) + (((-1)*X^3*a^2*b)/(2*W)) + (((-1)*X^3*Y*a*b)/(2*W)))*v 2
def row82 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(X*W^2)) + (((-1)*b)/(X*W)) + (((-1))/(X)))*v 1 + ((((-1))/(2*W^2)) + (((-1)*Y^2)/(W^2)) + ((1*Y^2*a^2)/(2*W^2)) + (((-1)*Y^4)/(2*W^2)) + ((1*X)/(W^2)) + ((1*X*b)/(W)) + (1*X) + ((1*X^2)/(2*W^2)) + ((1*X^2*b)/(2*W)) + ((1*X^2)/(2)) + ((1*X^2*Y*a)/(2*W^2)) + ((1*X^2*Y*a*b)/(2*W)) + ((1*X^2*Y*a)/(2)) + ((1*X^2*Y^2)/(2*W^2)) + ((1*X^2*Y^2*b)/(2*W)) + ((1*X^2*Y^2)/(2)))*v 2
def row83 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1))/(Y^2*W^2)) + ((1*a)/(Y)) + ((2*X)/(Y^2*W^2)) + ((1*X*b)/(Y^2*W)) + ((1*X^2)/(Y^2*W^2)) + ((1*X^2*b)/(Y^2*W)) + ((1*X^2)/(W^2)) + ((1*X^2*b)/(W)))*v 1 + (((2*X^2)/(Y^2*W^2)) + ((1*X^2*b)/(Y^2*W)) + ((1*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a)/(Y)) + ((1*X^2*Y*a)/(W^2)) + (((-1)*X^2*Y*a^3)/(2*W^2)) + ((1*X^2*Y^3*a)/(2*W^2)) + (((-1)*X^3)/(2*Y^2*W^2)) + ((1*X^3*a)/(2*Y*W^2)) + (((-1)*X^3*a)/(2*Y)) + ((3*X^3)/(2*W^2)) + ((1*X^3*b)/(W)) + (((-1)*X^3*a^2)/(2)) + (((-1)*X^3*Y*a)/(2)) + (((-3)*X^4)/(2*Y^2*W^2)) + (((-1)*X^4*b)/(Y^2*W)) + (((-1)*X^4*a)/(Y*W^2)) + (((-1)*X^4*a*b)/(2*Y*W)) + (((-1)*X^4)/(2*W^2)) + (((-1)*X^4*a^2)/(2*W^2)) + (((-1)*X^4*a^2*b)/(2*W)) + (((-1)*X^4*Y*a)/(2*W^2)) + (((-1)*X^4*Y*a*b)/(2*W)))*v 2
def row84 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((1)/(X*Y^2*W^2)) + ((1*b)/(X*Y^2*W)) + ((1)/(X*Y^2)) + (((-1))/(W^2)) + (((-1)*b)/(W)) + ((-1)))*v 1 + (((1)/(2*Y^2*W^2)) + ((1)/(W^2)) + (((-1)*a^2)/(2*W^2)) + ((1*Y^2)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X)/(Y^2)) + (((-1)*X)/(2*W^2)) + (((-1)*X*Y^2)/(W^2)) + ((1*X*Y^2*a^2)/(2*W^2)) + (((-1)*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*b)/(2*Y^2*W)) + (((-1)*X^2)/(2*Y^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a*b)/(2*Y*W)) + (((-1)*X^2*a)/(2*Y)) + ((1*X^2)/(2*W^2)) + ((1*X^2*b)/(2*W)) + ((1*X^2)/(2)) + ((1*X^3)/(2*W^2)) + ((1*X^3*b)/(2*W)) + ((1*X^3)/(2)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a*b)/(2*W)) + ((1*X^3*Y*a)/(2)) + ((1*X^3*Y^2)/(2*W^2)) + ((1*X^3*Y^2*b)/(2*W)) + ((1*X^3*Y^2)/(2)))*v 2
def row85 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := ((((-1))/(X^2*W^2)) + (((-1))/(X*W^2)) + (((-1)*Y^2)/(X*W^2)) + (((-1)*Y^2)/(W^2)))*v 0 + (((1)/(X^2*Y^2)) + ((2)/(X*Y^2*W^2)) + ((1*a)/(X*Y)) + ((1)/(X)) + ((1*b)/(Y^2*W)) + ((2)/(W^2)) + ((1*X)/(Y^2*W^2)) + ((1*X*b)/(Y^2*W)) + (((-1)*X)/(W^2)) + ((1*X*b)/(W)) + (((-1)*X^2*Y^2)/(W^2)))*v 1 + ((((-1))/(2*X*Y^2*W^2)) + (((-1)*a)/(2*X*Y*W^2)) + (((-1))/(2*X*W^2)) + (((-1))/(2*W^2)) + (((-1)*Y*a)/(2*W^2)) + (((-1)*Y^2)/(2*W^2)) + (((-1)*X)/(Y^2*W^2)) + ((1*X*b)/(Y^2*W)) + ((1*X*a)/(2*Y*W^2)) + (((-1)*X*a)/(Y)) + ((1*X*Y*a)/(W^2)) + (((-1)*X*Y*a^3)/(2*W^2)) + ((1*X*Y^3*a)/(2*W^2)) + ((1*X^2)/(2*Y^2*W^2)) + (((-1)*X^2*a)/(2*Y*W^2)) + (((-1)*X^2*a)/(2*Y)) + (((-5)*X^2)/(2*W^2)) + ((1*X^2*b)/(W)) + (((-1)*X^2*a^2)/(2)) + (((-1)*X^2*Y*a)/(2)) + (((-1)*X^3*b)/(Y^2*W)) + (((-1)*X^3*a*b)/(2*Y*W)) + ((1*X^3)/(2*W^2)) + (((-1)*X^3*a^2*b)/(2*W)) + (((-1)*X^3*Y*a)/(2*W^2)) + (((-1)*X^3*Y*a*b)/(2*W)) + (((-3)*X^3*Y^2)/(2*W^2)) + ((1*X^4)/(W^2)) + ((1*X^4*Y*a)/(2*W^2)) + ((1*X^4*Y^2*a^2)/(2*W^2)) + ((1*X^4*Y^3*a)/(2*W^2)))*v 2
def row86 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (0)*v 1 + (((1*X)/(2*W^2)) + ((1*X*Y^2)/(W^2)) + (((-1)*X*Y^2*a^2)/(2*W^2)) + ((1*X*Y^4)/(2*W^2)) + (((-1)*X^2)/(2*W^2)) + (((-1)*X^2*Y^2)/(W^2)) + ((1*X^2*Y^2*a^2)/(2*W^2)) + (((-1)*X^2*Y^4)/(2*W^2)))*v 2
def row87 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (0)*v 1 + (((1*Z)/(2*Y^2*W^2)) + ((1*Z)/(W^2)) + (((-1)*Z*a^2)/(2*W^2)) + ((1*Y^2*Z)/(2*W^2)) + (((-1)*X*Z)/(2*Y^2*W^2)) + (((-1)*X*Z)/(W^2)) + ((1*X*Z*a^2)/(2*W^2)) + (((-1)*X*Y^2*Z)/(2*W^2)))*v 2

def row88 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-1)*a)/(X*Y)) + (((-1))/(Y^2*W^2)) + (((-1)*b)/(Y^2*W)) + (((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X)/(W^2)) + (((-1)*X*b)/(W)))*v 1 + ((((-1)*X)/(Y^2*W^2)) + (((-1)*X*b)/(Y^2*W)) + (((-1)*X*a)/(2*Y*W^2)) + ((1*X*a)/(Y)) + (((-1)*X*Y*a)/(W^2)) + ((1*X*Y*a^3)/(2*W^2)) + (((-1)*X*Y^3*a)/(2*W^2)) + ((1*X^2*a)/(2*Y)) + (((-1)*X^2)/(W^2)) + (((-1)*X^2*b)/(W)) + ((1*X^2*a^2)/(2)) + ((1*X^2*Y*a)/(2)) + ((1*X^3)/(Y^2*W^2)) + ((1*X^3*b)/(Y^2*W)) + ((1*X^3*a)/(2*Y*W^2)) + ((1*X^3*a*b)/(2*Y*W)) + ((1*X^3*a^2)/(2*W^2)) + ((1*X^3*a^2*b)/(2*W)) + ((1*X^3*Y*a)/(2*W^2)) + ((1*X^3*Y*a*b)/(2*W)))*v 2
def row89 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((3400)/(3*X*W^2)) + ((1700)/(3*W^2)))*v 1 + (((4930)/(W^2)) + ((340*Y*a)/(W^2)) + ((340*Y^2)/(W^2)) + (((-6970)*X)/(3*W^2)) + (((-170)*X*Y*a)/(W^2)) + (((-170)*X*Y^2)/(W^2)) + ((3145*X^2)/(6*W^2)) + ((1105*X^2*Y*a)/(3*W^2)) + ((1105*X^2*Y^2)/(3*W^2)) + (((-850)*X^3)/(3*W^2)) + (((-850)*X^3*Y*a)/(3*W^2)) + (((-850)*X^3*Y^2)/(3*W^2)))*v 2
def row90 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((136)/(3*X)) + ((68)/(3)))*v 1 + (((986)/(5)) + ((68*Y*a)/(5)) + ((68*Y^2)/(5)) + (((-1394)*X)/(15)) + (((-34)*X*Y*a)/(5)) + (((-34)*X*Y^2)/(5)) + ((629*X^2)/(30)) + ((221*X^2*Y*a)/(15)) + ((221*X^2*Y^2)/(15)) + (((-34)*X^3)/(3)) + (((-34)*X^3*Y*a)/(3)) + (((-34)*X^3*Y^2)/(3)))*v 2
def row91 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-136))/(3*X)) + (((-68))/(3)))*v 1 + ((((-986))/(5)) + (((-68)*Y*a)/(5)) + (((-68)*Y^2)/(5)) + ((1394*X)/(15)) + ((34*X*Y*a)/(5)) + ((34*X*Y^2)/(5)) + (((-629)*X^2)/(30)) + (((-221)*X^2*Y*a)/(15)) + (((-221)*X^2*Y^2)/(15)) + ((34*X^3)/(3)) + ((34*X^3*Y*a)/(3)) + ((34*X^3*Y^2)/(3)))*v 2
def row92 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((408)/(X*Y^2)) + ((204)/(Y^2)))*v 1 + (((8874)/(5*Y^2)) + ((612*a)/(5*Y)) + ((612)/(5)) + (((-4182)*X)/(5*Y^2)) + (((-306)*X*a)/(5*Y)) + (((-306)*X)/(5)) + ((1887*X^2)/(10*Y^2)) + ((663*X^2*a)/(5*Y)) + ((663*X^2)/(5)) + (((-102)*X^3)/(Y^2)) + (((-102)*X^3*a)/(Y)) + ((-102)*X^3))*v 2
def row93 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((10200)/(X*Y^2*W^2)) + ((5100)/(Y^2*W^2)))*v 1 + (((44370)/(Y^2*W^2)) + ((3060*a)/(Y*W^2)) + ((3060)/(W^2)) + (((-20910)*X)/(Y^2*W^2)) + (((-1530)*X*a)/(Y*W^2)) + (((-1530)*X)/(W^2)) + ((9435*X^2)/(2*Y^2*W^2)) + ((3315*X^2*a)/(Y*W^2)) + ((3315*X^2)/(W^2)) + (((-2550)*X^3)/(Y^2*W^2)) + (((-2550)*X^3*a)/(Y*W^2)) + (((-2550)*X^3)/(W^2)))*v 2
def row94 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-68))/(X)))*v 1 + ((((-986))/(5)) + (((-68)*Y*a)/(5)) + (((-68)*Y^2)/(5)) + ((578*X)/(5)) + ((34*X*Y*a)/(5)) + ((34*X*Y^2)/(5)) + (((-323)*X^2)/(10)) + (((-17)*X^2*Y*a)/(5)) + (((-17)*X^2*Y^2)/(5)))*v 2
def row95 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-15300))/(X*Y^2*W^2)))*v 1 + ((((-44370))/(Y^2*W^2)) + (((-3060)*a)/(Y*W^2)) + (((-3060))/(W^2)) + ((26010*X)/(Y^2*W^2)) + ((1530*X*a)/(Y*W^2)) + ((1530*X)/(W^2)) + (((-14535)*X^2)/(2*Y^2*W^2)) + (((-765)*X^2*a)/(Y*W^2)) + (((-765)*X^2)/(W^2)))*v 2

def row96 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-68)*a)/(Y)) + (((-34)*X*a)/(Y)))*v 1 + ((((-1479)*X*a)/(5*Y)) + (((-102)*X*a^2)/(5)) + (((-102)*X*Y*a)/(5)) + ((697*X^2*a)/(5*Y)) + ((51*X^2*a^2)/(5)) + ((51*X^2*Y*a)/(5)) + (((-629)*X^3*a)/(20*Y)) + (((-221)*X^3*a^2)/(10)) + (((-221)*X^3*Y*a)/(10)) + ((17*X^4*a)/(Y)) + (17*X^4*a^2) + (17*X^4*Y*a))*v 2
def row97 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((816)/(X*Y^2)) + (((-68))/(X)) + (((-204))/(Y^2)) + (((-68)*a)/(Y)) + ((68)/(3)))*v 1 + ((((-714))/(Y^2)) + (((-2958)*a)/(5*Y)) + (((-986))/(5)) + (((-204)*a^2)/(5)) + (((-272)*Y*a)/(5)) + (((-68)*Y^2)/(5)) + ((1122*X)/(5*Y^2)) + ((204*X*a)/(Y)) + ((1156*X)/(5)) + ((102*X*a^2)/(5)) + ((102*X*Y*a)/(5)) + ((357*X^2)/(2*Y^2)) + (((-136)*X^2*a)/(Y)) + (((-374)*X^2)/(3)) + ((-102)*X^2*a^2) + ((-102)*X^2*Y*a) + ((34*X^3*a)/(Y)) + (((-34)*X^3)/(3)) + (34*X^3*a^2) + ((68*X^3*Y*a)/(3)) + (((-34)*X^3*Y^2)/(3)))*v 2
def row98 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-10200))/(X*Y^2*W^2)) + ((8500)/(3*X*W^2)) + ((10200)/(Y^2*W^2)) + ((1700*a)/(Y*W^2)))*v 1 + (((62220)/(Y^2*W^2)) + ((17850*a)/(Y*W^2)) + ((12920)/(W^2)) + ((1020*a^2)/(W^2)) + ((1700*Y*a)/(W^2)) + ((680*Y^2)/(W^2)) + (((-26520)*X)/(Y^2*W^2)) + (((-6630)*X*a)/(Y*W^2)) + (((-28900)*X)/(3*W^2)) + (((-510)*X*a^2)/(W^2)) + (((-680)*X*Y*a)/(W^2)) + (((-170)*X*Y^2)/(W^2)) + ((255*X^2)/(Y^2*W^2)) + ((6715*X^2*a)/(Y*W^2)) + ((41735*X^2)/(6*W^2)) + ((2550*X^2*a^2)/(W^2)) + ((8755*X^2*Y*a)/(3*W^2)) + ((1105*X^2*Y^2)/(3*W^2)) + (((-2550)*X^3)/(Y^2*W^2)) + (((-3400)*X^3*a)/(Y*W^2)) + (((-2550)*X^3)/(W^2)) + (((-850)*X^3*a^2)/(W^2)) + (((-850)*X^3*Y*a)/(W^2)))*v 2
def row99 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-3400)*a)/(X*Y*W^2)) + (((-1700)*a)/(Y*W^2)))*v 1 + ((((-14790)*a)/(Y*W^2)) + (((-1020)*a^2)/(W^2)) + (((-1020)*Y*a)/(W^2)) + ((6970*X*a)/(Y*W^2)) + ((510*X*a^2)/(W^2)) + ((510*X*Y*a)/(W^2)) + (((-3145)*X^2*a)/(2*Y*W^2)) + (((-1105)*X^2*a^2)/(W^2)) + (((-1105)*X^2*Y*a)/(W^2)) + ((850*X^3*a)/(Y*W^2)) + ((850*X^3*a^2)/(W^2)) + ((850*X^3*Y*a)/(W^2)))*v 2
def row100 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-204))/(Y^2)) + ((204*X)/(Y^2)) + ((34*X*a)/(Y)) + (((-34)*X)/(3)))*v 1 + (((6222*X)/(5*Y^2)) + ((357*X*a)/(Y)) + ((306*X)/(5)) + ((102*X*a^2)/(5)) + ((102*X*Y*a)/(5)) + (((-2652)*X^2)/(5*Y^2)) + (((-663)*X^2*a)/(5*Y)) + (((-442)*X^2)/(5)) + (((-51)*X^2*a^2)/(5)) + (((-34)*X^2*Y*a)/(5)) + ((17*X^2*Y^2)/(5)) + ((51*X^3)/(10*Y^2)) + ((1343*X^3*a)/(10*Y)) + ((6749*X^3)/(60)) + (51*X^3*a^2) + ((493*X^3*Y*a)/(10)) + (((-17)*X^3*Y^2)/(10)) + (((-51)*X^4)/(Y^2)) + (((-68)*X^4*a)/(Y)) + (((-136)*X^4)/(3)) + ((-17)*X^4*a^2) + (((-34)*X^4*Y*a)/(3)) + ((17*X^4*Y^2)/(3)))*v 2
def row101 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + (((10200)/(Y^2*W^2)) + (((-4250))/(3*W^2)) + (((-2550)*X)/(Y^2*W^2)) + (((-850)*X*a)/(Y*W^2)))*v 1 + ((((-8925)*X)/(Y^2*W^2)) + (((-7395)*X*a)/(Y*W^2)) + (((-4930)*X)/(W^2)) + (((-510)*X*a^2)/(W^2)) + (((-850)*X*Y*a)/(W^2)) + (((-340)*X*Y^2)/(W^2)) + ((2805*X^2)/(Y^2*W^2)) + ((2550*X^2*a)/(Y*W^2)) + ((12155*X^2)/(3*W^2)) + ((255*X^2*a^2)/(W^2)) + ((340*X^2*Y*a)/(W^2)) + ((85*X^2*Y^2)/(W^2)) + ((8925*X^3)/(4*Y^2*W^2)) + (((-1700)*X^3*a)/(Y*W^2)) + (((-21845)*X^3)/(12*W^2)) + (((-1275)*X^3*a^2)/(W^2)) + (((-8755)*X^3*Y*a)/(6*W^2)) + (((-1105)*X^3*Y^2)/(6*W^2)) + ((425*X^4*a)/(Y*W^2)) + ((425*X^4*a^2)/(W^2)) + ((425*X^4*Y*a)/(W^2)))*v 2
def row102 (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-5100)*X)/(Y^2*W^2)) + ((2125*X)/(3*W^2)) + ((1275*X^2)/(Y^2*W^2)) + ((425*X^2*a)/(Y*W^2)))*v 1 + (((8925*X^2)/(2*Y^2*W^2)) + ((7395*X^2*a)/(2*Y*W^2)) + ((2465*X^2)/(W^2)) + ((255*X^2*a^2)/(W^2)) + ((425*X^2*Y*a)/(W^2)) + ((170*X^2*Y^2)/(W^2)) + (((-2805)*X^3)/(2*Y^2*W^2)) + (((-1275)*X^3*a)/(Y*W^2)) + (((-12155)*X^3)/(6*W^2)) + (((-255)*X^3*a^2)/(2*W^2)) + (((-170)*X^3*Y*a)/(W^2)) + (((-85)*X^3*Y^2)/(2*W^2)) + (((-8925)*X^4)/(8*Y^2*W^2)) + ((850*X^4*a)/(Y*W^2)) + ((21845*X^4)/(24*W^2)) + ((1275*X^4*a^2)/(2*W^2)) + ((8755*X^4*Y*a)/(12*W^2)) + ((1105*X^4*Y^2)/(12*W^2)) + (((-425)*X^5*a)/(2*Y*W^2)) + (((-425)*X^5*a^2)/(2*W^2)) + (((-425)*X^5*Y*a)/(2*W^2)))*v 2

end SmallLevelThirtyFourFiniteJetMMP
end
end

/-! ## ThirtyFourFiniteJetMMPData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourFiniteJetMMP
open Complex
def rows (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : Fin 103→ℂ
  | 0 => row0 X Y Z W a b v
  | 1 => row1 X Y Z W a b v
  | 2 => row2 X Y Z W a b v
  | 3 => row3 X Y Z W a b v
  | 4 => row4 X Y Z W a b v
  | 5 => row5 X Y Z W a b v
  | 6 => row6 X Y Z W a b v
  | 7 => row7 X Y Z W a b v
  | 8 => row8 X Y Z W a b v
  | 9 => row9 X Y Z W a b v
  | 10 => row10 X Y Z W a b v
  | 11 => row11 X Y Z W a b v
  | 12 => row12 X Y Z W a b v
  | 13 => row13 X Y Z W a b v
  | 14 => row14 X Y Z W a b v
  | 15 => row15 X Y Z W a b v
  | 16 => row16 X Y Z W a b v
  | 17 => row17 X Y Z W a b v
  | 18 => row18 X Y Z W a b v
  | 19 => row19 X Y Z W a b v
  | 20 => row20 X Y Z W a b v
  | 21 => row21 X Y Z W a b v
  | 22 => row22 X Y Z W a b v
  | 23 => row23 X Y Z W a b v
  | 24 => row24 X Y Z W a b v
  | 25 => row25 X Y Z W a b v
  | 26 => row26 X Y Z W a b v
  | 27 => row27 X Y Z W a b v
  | 28 => row28 X Y Z W a b v
  | 29 => row29 X Y Z W a b v
  | 30 => row30 X Y Z W a b v
  | 31 => row31 X Y Z W a b v
  | 32 => row32 X Y Z W a b v
  | 33 => row33 X Y Z W a b v
  | 34 => row34 X Y Z W a b v
  | 35 => row35 X Y Z W a b v
  | 36 => row36 X Y Z W a b v
  | 37 => row37 X Y Z W a b v
  | 38 => row38 X Y Z W a b v
  | 39 => row39 X Y Z W a b v
  | 40 => row40 X Y Z W a b v
  | 41 => row41 X Y Z W a b v
  | 42 => row42 X Y Z W a b v
  | 43 => row43 X Y Z W a b v
  | 44 => row44 X Y Z W a b v
  | 45 => row45 X Y Z W a b v
  | 46 => row46 X Y Z W a b v
  | 47 => row47 X Y Z W a b v
  | 48 => row48 X Y Z W a b v
  | 49 => row49 X Y Z W a b v
  | 50 => row50 X Y Z W a b v
  | 51 => row51 X Y Z W a b v
  | 52 => row52 X Y Z W a b v
  | 53 => row53 X Y Z W a b v
  | 54 => row54 X Y Z W a b v
  | 55 => row55 X Y Z W a b v
  | 56 => row56 X Y Z W a b v
  | 57 => row57 X Y Z W a b v
  | 58 => row58 X Y Z W a b v
  | 59 => row59 X Y Z W a b v
  | 60 => row60 X Y Z W a b v
  | 61 => row61 X Y Z W a b v
  | 62 => row62 X Y Z W a b v
  | 63 => row63 X Y Z W a b v
  | 64 => row64 X Y Z W a b v
  | 65 => row65 X Y Z W a b v
  | 66 => row66 X Y Z W a b v
  | 67 => row67 X Y Z W a b v
  | 68 => row68 X Y Z W a b v
  | 69 => row69 X Y Z W a b v
  | 70 => row70 X Y Z W a b v
  | 71 => row71 X Y Z W a b v
  | 72 => row72 X Y Z W a b v
  | 73 => row73 X Y Z W a b v
  | 74 => row74 X Y Z W a b v
  | 75 => row75 X Y Z W a b v
  | 76 => row76 X Y Z W a b v
  | 77 => row77 X Y Z W a b v
  | 78 => row78 X Y Z W a b v
  | 79 => row79 X Y Z W a b v
  | 80 => row80 X Y Z W a b v
  | 81 => row81 X Y Z W a b v
  | 82 => row82 X Y Z W a b v
  | 83 => row83 X Y Z W a b v
  | 84 => row84 X Y Z W a b v
  | 85 => row85 X Y Z W a b v
  | 86 => row86 X Y Z W a b v
  | 87 => row87 X Y Z W a b v
  | 88 => row88 X Y Z W a b v
  | 89 => row89 X Y Z W a b v
  | 90 => row90 X Y Z W a b v
  | 91 => row91 X Y Z W a b v
  | 92 => row92 X Y Z W a b v
  | 93 => row93 X Y Z W a b v
  | 94 => row94 X Y Z W a b v
  | 95 => row95 X Y Z W a b v
  | 96 => row96 X Y Z W a b v
  | 97 => row97 X Y Z W a b v
  | 98 => row98 X Y Z W a b v
  | 99 => row99 X Y Z W a b v
  | 100 => row100 X Y Z W a b v
  | 101 => row101 X Y Z W a b v
  | _ => row102 X Y Z W a b v

end SmallLevelThirtyFourFiniteJetMMP
end
end

/-! ## ThirtyFourFiniteJetMMPLeadingBindingBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourFiniteJetMMP
open Complex SmallLevelThirtyFourUnitMMP

theorem leading_binding_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row0 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_0 X Y Z W a b hX hY hZ hW v hv
  simpa only [row0,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_0
theorem leading_binding_1 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row1 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_1 X Y Z W a b hX hY hZ hW v hv
  simpa only [row1,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_1
theorem leading_binding_2 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row2 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_2 X Y Z W a b hX hY hZ hW v hv
  simpa only [row2,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_2
theorem leading_binding_3 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row3 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_3 X Y Z W a b hX hY hZ hW v hv
  simpa only [row3,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_3
theorem leading_binding_4 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row4 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_4 X Y Z W a b hX hY hZ hW v hv
  simpa only [row4,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_4
theorem leading_binding_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row5 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_5 X Y Z W a b hX hY hZ hW v hv
  simpa only [row5,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_5
theorem leading_binding_6 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row6 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_6 X Y Z W a b hX hY hZ hW v hv
  simpa only [row6,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_6
theorem leading_binding_7 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row7 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_7 X Y Z W a b hX hY hZ hW v hv
  simpa only [row7,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_7

theorem leading_binding_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row8 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_8 X Y Z W a b hX hY hZ hW v hv
  simpa only [row8,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_8
theorem leading_binding_9 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row9 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_9 X Y Z W a b hX hY hZ hW v hv
  simpa only [row9,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_9
theorem leading_binding_10 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row10 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_10 X Y Z W a b hX hY hZ hW v hv
  simpa only [row10,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_10
theorem leading_binding_11 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row11 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_11 X Y Z W a b hX hY hZ hW v hv
  simpa only [row11,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_11
theorem leading_binding_12 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row12 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_12 X Y Z W a b hX hY hZ hW v hv
  simpa only [row12,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_12
theorem leading_binding_13 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row13 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_13 X Y Z W a b hX hY hZ hW v hv
  simpa only [row13,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_13
theorem leading_binding_14 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row14 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_14 X Y Z W a b hX hY hZ hW v hv
  simpa only [row14,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_14
theorem leading_binding_15 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row15 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_18 X Y Z W a b hX hY hZ hW v hv
  simpa only [row15,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_15

theorem leading_binding_16 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row16 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_19 X Y Z W a b hX hY hZ hW v hv
  simpa only [row16,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_16
theorem leading_binding_17 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row17 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_20 X Y Z W a b hX hY hZ hW v hv
  simpa only [row17,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_17
theorem leading_binding_18 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row18 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_21 X Y Z W a b hX hY hZ hW v hv
  simpa only [row18,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_18
theorem leading_binding_19 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row19 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_23 X Y Z W a b hX hY hZ hW v hv
  simpa only [row19,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_19
theorem leading_binding_20 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row20 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_24 X Y Z W a b hX hY hZ hW v hv
  simpa only [row20,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_20
theorem leading_binding_21 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row21 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_25 X Y Z W a b hX hY hZ hW v hv
  simpa only [row21,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_21
theorem leading_binding_22 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row22 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_26 X Y Z W a b hX hY hZ hW v hv
  simpa only [row22,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_22
theorem leading_binding_23 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row23 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_27 X Y Z W a b hX hY hZ hW v hv
  simpa only [row23,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_23

theorem leading_binding_24 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row24 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_28 X Y Z W a b hX hY hZ hW v hv
  simpa only [row24,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_24
theorem leading_binding_25 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row25 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_31 X Y Z W a b hX hY hZ hW v hv
  simpa only [row25,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_25
theorem leading_binding_26 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row26 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_32 X Y Z W a b hX hY hZ hW v hv
  simpa only [row26,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_26
theorem leading_binding_27 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row27 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_33 X Y Z W a b hX hY hZ hW v hv
  simpa only [row27,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_27
theorem leading_binding_28 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row28 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_34 X Y Z W a b hX hY hZ hW v hv
  simpa only [row28,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_28
theorem leading_binding_29 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row29 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_35 X Y Z W a b hX hY hZ hW v hv
  simpa only [row29,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_29
theorem leading_binding_30 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row30 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_36 X Y Z W a b hX hY hZ hW v hv
  simpa only [row30,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_30
theorem leading_binding_31 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row31 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_38 X Y Z W a b hX hY hZ hW v hv
  simpa only [row31,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_31

theorem leading_binding_32 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row32 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_39 X Y Z W a b hX hY hZ hW v hv
  simpa only [row32,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_32
theorem leading_binding_33 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row33 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_40 X Y Z W a b hX hY hZ hW v hv
  simpa only [row33,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_33
theorem leading_binding_34 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row34 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_41 X Y Z W a b hX hY hZ hW v hv
  simpa only [row34,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_34
theorem leading_binding_35 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row35 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_43 X Y Z W a b hX hY hZ hW v hv
  simpa only [row35,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_35
theorem leading_binding_36 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row36 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_46 X Y Z W a b hX hY hZ hW v hv
  simpa only [row36,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_36
theorem leading_binding_37 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row37 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_47 X Y Z W a b hX hY hZ hW v hv
  simpa only [row37,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_37
theorem leading_binding_38 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row38 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_48 X Y Z W a b hX hY hZ hW v hv
  simpa only [row38,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_38
theorem leading_binding_39 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row39 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_49 X Y Z W a b hX hY hZ hW v hv
  simpa only [row39,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_39

theorem leading_binding_40 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row40 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_53 X Y Z W a b hX hY hZ hW v hv
  simpa only [row40,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_40
theorem leading_binding_41 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row41 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_54 X Y Z W a b hX hY hZ hW v hv
  simpa only [row41,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_41
theorem leading_binding_42 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row42 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_56 X Y Z W a b hX hY hZ hW v hv
  simpa only [row42,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_42
theorem leading_binding_43 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row43 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_57 X Y Z W a b hX hY hZ hW v hv
  simpa only [row43,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_43
theorem leading_binding_44 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row44 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_59 X Y Z W a b hX hY hZ hW v hv
  simpa only [row44,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_44
theorem leading_binding_45 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row45 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_60 X Y Z W a b hX hY hZ hW v hv
  simpa only [row45,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_45
theorem leading_binding_46 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row46 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_61 X Y Z W a b hX hY hZ hW v hv
  simpa only [row46,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_46
theorem leading_binding_47 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row47 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_62 X Y Z W a b hX hY hZ hW v hv
  simpa only [row47,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_47

theorem leading_binding_48 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row48 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_63 X Y Z W a b hX hY hZ hW v hv
  simpa only [row48,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_48
theorem leading_binding_49 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row49 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_64 X Y Z W a b hX hY hZ hW v hv
  simpa only [row49,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_49
theorem leading_binding_50 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row50 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_65 X Y Z W a b hX hY hZ hW v hv
  simpa only [row50,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_50
theorem leading_binding_51 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row51 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_66 X Y Z W a b hX hY hZ hW v hv
  simpa only [row51,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_51
theorem leading_binding_52 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row52 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_67 X Y Z W a b hX hY hZ hW v hv
  simpa only [row52,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_52
theorem leading_binding_53 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row53 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_68 X Y Z W a b hX hY hZ hW v hv
  simpa only [row53,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_53
theorem leading_binding_54 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row54 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_69 X Y Z W a b hX hY hZ hW v hv
  simpa only [row54,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_54
theorem leading_binding_55 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row55 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_71 X Y Z W a b hX hY hZ hW v hv
  simpa only [row55,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_55

theorem leading_binding_56 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row56 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_73 X Y Z W a b hX hY hZ hW v hv
  simpa only [row56,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_56
theorem leading_binding_57 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row57 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_74 X Y Z W a b hX hY hZ hW v hv
  simpa only [row57,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_57
theorem leading_binding_58 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row58 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_75 X Y Z W a b hX hY hZ hW v hv
  simpa only [row58,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_58
theorem leading_binding_59 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row59 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_76 X Y Z W a b hX hY hZ hW v hv
  simpa only [row59,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_59
theorem leading_binding_60 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row60 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_77 X Y Z W a b hX hY hZ hW v hv
  simpa only [row60,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_60
theorem leading_binding_61 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row61 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_78 X Y Z W a b hX hY hZ hW v hv
  simpa only [row61,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_61
theorem leading_binding_62 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row62 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_79 X Y Z W a b hX hY hZ hW v hv
  simpa only [row62,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_62
theorem leading_binding_63 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row63 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_80 X Y Z W a b hX hY hZ hW v hv
  simpa only [row63,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_63

theorem leading_binding_64 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row64 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_81 X Y Z W a b hX hY hZ hW v hv
  simpa only [row64,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_64
theorem leading_binding_65 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row65 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_82 X Y Z W a b hX hY hZ hW v hv
  simpa only [row65,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_65
theorem leading_binding_66 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row66 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_83 X Y Z W a b hX hY hZ hW v hv
  simpa only [row66,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_66
theorem leading_binding_67 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row67 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_84 X Y Z W a b hX hY hZ hW v hv
  simpa only [row67,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_67
theorem leading_binding_68 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row68 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_85 X Y Z W a b hX hY hZ hW v hv
  simpa only [row68,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_68
theorem leading_binding_69 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row69 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_86 X Y Z W a b hX hY hZ hW v hv
  simpa only [row69,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_69
theorem leading_binding_70 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row70 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_87 X Y Z W a b hX hY hZ hW v hv
  simpa only [row70,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_70
theorem leading_binding_71 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row71 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_88 X Y Z W a b hX hY hZ hW v hv
  simpa only [row71,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_71

theorem leading_binding_72 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row72 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_89 X Y Z W a b hX hY hZ hW v hv
  simpa only [row72,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_72
theorem leading_binding_73 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row73 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_90 X Y Z W a b hX hY hZ hW v hv
  simpa only [row73,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_73
theorem leading_binding_74 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row74 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_91 X Y Z W a b hX hY hZ hW v hv
  simpa only [row74,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_74
theorem leading_binding_75 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row75 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_94 X Y Z W a b hX hY hZ hW v hv
  simpa only [row75,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_75
theorem leading_binding_76 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row76 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_95 X Y Z W a b hX hY hZ hW v hv
  simpa only [row76,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_76
theorem leading_binding_77 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row77 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_97 X Y Z W a b hX hY hZ hW v hv
  simpa only [row77,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_77
theorem leading_binding_78 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row78 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_98 X Y Z W a b hX hY hZ hW v hv
  simpa only [row78,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_78
theorem leading_binding_79 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row79 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_99 X Y Z W a b hX hY hZ hW v hv
  simpa only [row79,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_79

theorem leading_binding_80 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row80 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_100 X Y Z W a b hX hY hZ hW v hv
  simpa only [row80,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_80
theorem leading_binding_81 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row81 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_101 X Y Z W a b hX hY hZ hW v hv
  simpa only [row81,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_81
theorem leading_binding_82 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row82 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_102 X Y Z W a b hX hY hZ hW v hv
  simpa only [row82,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_82
theorem leading_binding_83 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row83 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_103 X Y Z W a b hX hY hZ hW v hv
  simpa only [row83,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_83
theorem leading_binding_84 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row84 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_104 X Y Z W a b hX hY hZ hW v hv
  simpa only [row84,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_84
theorem leading_binding_85 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row85 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_106 X Y Z W a b hX hY hZ hW v hv
  simpa only [row85,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_85
theorem leading_binding_86 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row86 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_107 X Y Z W a b hX hY hZ hW v hv
  simpa only [row86,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_86
theorem leading_binding_87 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row87 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_108 X Y Z W a b hX hY hZ hW v hv
  simpa only [row87,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_87

theorem leading_binding_88 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    row88 X Y Z W a b ![v 370,v 390,v 435]=0 := by
  have h:=residual_109 X Y Z W a b hX hY hZ hW v hv
  simpa only [row88,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,zero_mul,add_zero,zero_add] using h

#print axioms leading_binding_88

end SmallLevelThirtyFourFiniteJetMMP
end
end

/-! ## ThirtyFourFiniteJetMMPLeadingBindings -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourFiniteJetMMP
open Complex SmallLevelThirtyFourUnitMMP
theorem leading_rows_of_source (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ j,sourceRows X Y Z W a b v j=0) :
    ∀ i : Fin 89,rows X Y Z W a b ![v 370,v 390,v 435] ⟨i.val,by omega⟩=0 := by
  intro i
  fin_cases i
  · exact leading_binding_0 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_1 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_2 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_3 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_4 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_5 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_6 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_7 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_8 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_9 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_10 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_11 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_12 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_13 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_14 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_15 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_16 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_17 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_18 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_19 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_20 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_21 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_22 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_23 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_24 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_25 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_26 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_27 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_28 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_29 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_30 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_31 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_32 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_33 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_34 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_35 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_36 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_37 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_38 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_39 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_40 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_41 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_42 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_43 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_44 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_45 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_46 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_47 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_48 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_49 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_50 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_51 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_52 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_53 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_54 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_55 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_56 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_57 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_58 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_59 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_60 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_61 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_62 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_63 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_64 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_65 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_66 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_67 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_68 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_69 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_70 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_71 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_72 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_73 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_74 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_75 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_76 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_77 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_78 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_79 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_80 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_81 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_82 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_83 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_84 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_85 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_86 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_87 X Y Z W a b hX hY hZ hW v hv
  · exact leading_binding_88 X Y Z W a b hX hY hZ hW v hv

#print axioms leading_rows_of_source

end SmallLevelThirtyFourFiniteJetMMP
end
end

/-! ## ThirtyFourJetOperatorMMP -/
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourJetOperatorMMP
open Complex SmallLevelThirtyFourUnitMMPInhomogeneous

theorem jet_value_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : CanonicalSourceValues X Y Z W a b v r) :
    rhsZero0 (X/2) (Y/3) (Z/17) (W/5) a b r=
      SmallLevelThirtyFourFiniteJetMMP.row89 X Y Z W a b v := by
  have hs:=hr 265 (by decide)
  change r 265=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsZero0,hs]
  rw [pivot_value_70 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_110 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_126 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_235 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_236 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_256 X Y Z W a b hX hY hZ hW v r hr]
  unfold SmallLevelThirtyFourFiniteJetMMP.row89
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms jet_value_0

theorem jet_value_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : CanonicalSourceValues X Y Z W a b v r) :
    rhsZero5 (X/2) (Y/3) (Z/17) (W/5) a b r=
      SmallLevelThirtyFourFiniteJetMMP.row94 X Y Z W a b v := by
  have hs:=hr 354 (by decide)
  change r 354=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsZero5,hs]
  rw [pivot_value_102 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_150 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_189 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_233 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_235 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_257 X Y Z W a b hX hY hZ hW v r hr]
  unfold SmallLevelThirtyFourFiniteJetMMP.row94
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms jet_value_5

theorem jet_value_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 3→ℂ) (r : Fin 546→ℂ) (hr : CanonicalSourceValues X Y Z W a b v r) :
    rhsZero8 (X/2) (Y/3) (Z/17) (W/5) a b r=
      SmallLevelThirtyFourFiniteJetMMP.row97 X Y Z W a b v := by
  have hs:=hr 447 (by decide)
  change r 447=(0)*v 0 + (0)*v 1 + (0)*v 2 at hs
  rw [rhsZero8,hs]
  rw [pivot_value_89 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_102 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_131 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_141 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_194 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_235 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_256 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_277 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_329 X Y Z W a b hX hY hZ hW v r hr]
  rw [pivot_value_334 X Y Z W a b hX hY hZ hW v r hr]
  unfold SmallLevelThirtyFourFiniteJetMMP.row97
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms jet_value_8

end SmallLevelThirtyFourJetOperatorMMP
end
end

/-! ## ThirtyFourJetSourceMMP -/
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourJetSourceMMP
open Complex SmallLevelThirtyFourUnitMMP SmallLevelThirtyFourJetOperatorMMP SmallLevelThirtyFourSlopeLiteralMMP
theorem actual_source_values (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    CanonicalSourceValues X Y Z W a b ![v 370,v 390,v 435]
      (sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v) := by
  intro i hi
  simp only [canonicalRequiredSources,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact source_value_1 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_3 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_4 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_6 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_7 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_8 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_9 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_10 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_12 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_20 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_21 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_22 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_24 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_25 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_28 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_29 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_30 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_31 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_32 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_34 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_35 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_37 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_38 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_42 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_43 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_61 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_62 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_63 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_64 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_66 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_67 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_68 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_69 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_71 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_73 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_77 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_78 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_79 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_81 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_82 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_83 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_84 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_85 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_86 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_94 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_95 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_98 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_99 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_102 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_105 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_106 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_107 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_108 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_142 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_144 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_148 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_152 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_157 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_170 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_172 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_173 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_174 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_176 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_183 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_189 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_199 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_201 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_202 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_225 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_246 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_260 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_263 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_266 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_275 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_277 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_279 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_285 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_286 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_288 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_290 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_296 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_297 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_305 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_319 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_326 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_328 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_331 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_344 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_352 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_355 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_379 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_384 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_393 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_399 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_401 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_404 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_411 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_485 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_636 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_675 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_1177 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_1585 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2331 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2334 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2338 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2339 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2340 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2341 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2356 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2386 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2395 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2396 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2407 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2425 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2441 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2459 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2461 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2464 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2465 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2469 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2475 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2480 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2485 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2486 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2498 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2504 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2512 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2523 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2525 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2526 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2530 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2546 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2547 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2559 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2568 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2575 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2586 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2588 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2599 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2601 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2619 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2620 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2656 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2664 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2672 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2675 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2686 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2692 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2699 X Y Z W a b hX hY hZ hW v hv
  · exact source_value_2746 X Y Z W a b hX hY hZ hW v hv

#print axioms actual_source_values

theorem actual_jet_value_0 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    SmallLevelThirtyFourUnitMMPInhomogeneous.rhsZero0 (X/2) (Y/3) (Z/17) (W/5) a b
      (sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v)=
      SmallLevelThirtyFourFiniteJetMMP.row89 X Y Z W a b ![v 370,v 390,v 435] :=
  jet_value_0 X Y Z W a b hX hY hZ hW _ _ (actual_source_values X Y Z W a b hX hY hZ hW v hv)

#print axioms actual_jet_value_0

theorem actual_jet_value_5 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    SmallLevelThirtyFourUnitMMPInhomogeneous.rhsZero5 (X/2) (Y/3) (Z/17) (W/5) a b
      (sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v)=
      SmallLevelThirtyFourFiniteJetMMP.row94 X Y Z W a b ![v 370,v 390,v 435] :=
  jet_value_5 X Y Z W a b hX hY hZ hW _ _ (actual_source_values X Y Z W a b hX hY hZ hW v hv)

#print axioms actual_jet_value_5

theorem actual_jet_value_8 (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    SmallLevelThirtyFourUnitMMPInhomogeneous.rhsZero8 (X/2) (Y/3) (Z/17) (W/5) a b
      (sourceSlopeRows (X/2) (Y/3) (Z/17) (W/5) a b v)=
      SmallLevelThirtyFourFiniteJetMMP.row97 X Y Z W a b ![v 370,v 390,v 435] :=
  jet_value_8 X Y Z W a b hX hY hZ hW _ _ (actual_source_values X Y Z W a b hX hY hZ hW v hv)

#print axioms actual_jet_value_8

end SmallLevelThirtyFourJetSourceMMP
end
end

/-! ## ThirtyFourPhysicalFiniteMMP -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourPhysicalFiniteMMP
open Complex Matrix SmallLevelThirtyFourGrid SmallLevelPrimeRates SmallLevelFiniteGridSupport
open SmallLevelThirtyFourUnitMMP SmallLevelThirtyFourUnitMMPInhomogeneous
theorem source_kernel (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0) :
    ∀ i,sourceRows (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) (extension supportIndex w) i=0 := by
  intro i
  rw [scaled_sourceRows_actual m f ε u v x hu hv hη h₂ h₁₇]
  have h:=congrFun hlead i
  simpa only [SmallLevelThirtyFourUnitMMM.leadingMatrix,restrictedLeadingMatrix_mulVec,
    Pi.zero_apply] using h

theorem finite_leading_rows (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0) :
    ∀ i : Fin 89,SmallLevelThirtyFourFiniteJetMMP.rows (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435] ⟨i.val,by omega⟩=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) x)
  have hW:=parameter_ne_zero 5 m (by decide) x
  have hs:=source_kernel m f ε u v x hu hv hη h₂ h₁₇ w hlead
  exact SmallLevelThirtyFourFiniteJetMMP.leading_rows_of_source (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW (extension supportIndex w) hs

theorem finite_jet_row_0 (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0)
    (hjet : firstJetMatrix m f ε u v x *ᵥ w=0) :
    SmallLevelThirtyFourFiniteJetMMP.row89 (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435]=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) x)
  have hW:=parameter_ne_zero 5 m (by decide) x
  have hs:=source_kernel m f ε u v x hu hv hη h₂ h₁₇ w hlead
  rw [←SmallLevelThirtyFourJetSourceMMP.actual_jet_value_0 (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW (extension supportIndex w) hs]
  have hj:=congrFun hjet (0:Fin 14)
  rw [firstJetMatrix_source_apply m f ε u v x hu hv hη h₂ h₁₇] at hj
  change rhsZero0 _ _ _ _ _ _ _=0 at hj
  simpa only [parameter_shift 2 m (by decide),parameter_shift 3 m (by decide),
    parameter_shift 17 m (by decide),parameter_shift 5 m (by decide),←mul_div_assoc,Nat.cast_ofNat] using hj

#print axioms finite_jet_row_0

theorem finite_jet_row_5 (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0)
    (hjet : firstJetMatrix m f ε u v x *ᵥ w=0) :
    SmallLevelThirtyFourFiniteJetMMP.row94 (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435]=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) x)
  have hW:=parameter_ne_zero 5 m (by decide) x
  have hs:=source_kernel m f ε u v x hu hv hη h₂ h₁₇ w hlead
  rw [←SmallLevelThirtyFourJetSourceMMP.actual_jet_value_5 (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW (extension supportIndex w) hs]
  have hj:=congrFun hjet (5:Fin 14)
  rw [firstJetMatrix_source_apply m f ε u v x hu hv hη h₂ h₁₇] at hj
  change rhsZero5 _ _ _ _ _ _ _=0 at hj
  simpa only [parameter_shift 2 m (by decide),parameter_shift 3 m (by decide),
    parameter_shift 17 m (by decide),parameter_shift 5 m (by decide),←mul_div_assoc,Nat.cast_ofNat] using hj

#print axioms finite_jet_row_5

theorem finite_jet_row_8 (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0)
    (hjet : firstJetMatrix m f ε u v x *ᵥ w=0) :
    SmallLevelThirtyFourFiniteJetMMP.row97 (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435]=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) x)
  have hW:=parameter_ne_zero 5 m (by decide) x
  have hs:=source_kernel m f ε u v x hu hv hη h₂ h₁₇ w hlead
  rw [←SmallLevelThirtyFourJetSourceMMP.actual_jet_value_8 (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW (extension supportIndex w) hs]
  have hj:=congrFun hjet (8:Fin 14)
  rw [firstJetMatrix_source_apply m f ε u v x hu hv hη h₂ h₁₇] at hj
  change rhsZero8 _ _ _ _ _ _ _=0 at hj
  simpa only [parameter_shift 2 m (by decide),parameter_shift 3 m (by decide),
    parameter_shift 17 m (by decide),parameter_shift 5 m (by decide),←mul_div_assoc,Nat.cast_ofNat] using hj

#print axioms finite_jet_row_8

#print axioms finite_leading_rows
end SmallLevelThirtyFourPhysicalFiniteMMP
end
end

/-! ## ThirtyFourCriticalMMPData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourCriticalMMP
def critical_mmp_row (b w z A Y : ℂ) (i : Fin 19) : ℂ :=
  match i.val with
  | 0 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (9/2:ℂ)*b*w + (12:ℂ)*w^2*A + (12:ℂ)*w^2*Y + (39:ℂ)*w^2 + (16/3:ℂ)*z*A + (16/3:ℂ)*z*Y + (39:ℂ)*z + (-10/3:ℂ)*A^2*Y + (-17:ℂ)*A^2 + (-13/3:ℂ)*A*Y^2 + (-142/3:ℂ)*A*Y + (109/6:ℂ)*A + (-1:ℂ)*Y^3 + (-63/2:ℂ)*Y^2 + (-401/6:ℂ)*Y + (-247/3:ℂ)
  | 1 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (9/2:ℂ)*b*w + (8:ℂ)*w^2*A + (8:ℂ)*w^2*Y + (-17/3:ℂ)*w^2 + (-12:ℂ)*z*A + (-12:ℂ)*z*Y + (-137/3:ℂ)*z + (-10/3:ℂ)*A^2*Y + (97/3:ℂ)*A^2 + (-13/3:ℂ)*A*Y^2 + (58:ℂ)*A*Y + (1/6:ℂ)*A + (-1:ℂ)*Y^3 + (49/2:ℂ)*Y^2 + (271/6:ℂ)*Y + (51:ℂ)
  | 2 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (67/6:ℂ)*b*w + (23/3:ℂ)*w^2*A + (23/3:ℂ)*w^2*Y + (107/6:ℂ)*w^2 + (1:ℂ)*z*A + (1:ℂ)*z*Y + (67/6:ℂ)*z + (-1:ℂ)*A^2 + (-20/3:ℂ)*A*Y + (-95/6:ℂ)*A + (-17/3:ℂ)*Y^2 + (79/6:ℂ)*Y + (9:ℂ)
  | 3 => (1:ℂ)*b*w + (-1/20:ℂ)*w^2*A + (-1/20:ℂ)*w^2*Y + (141/40:ℂ)*w^2 + (39/20:ℂ)*z*A + (39/20:ℂ)*z*Y + (341/40:ℂ)*z + (1/2:ℂ)*A^2*Y + (-5:ℂ)*A^2 + (13/20:ℂ)*A*Y^2 + (-97/10:ℂ)*A*Y + (-12/5:ℂ)*A + (3/20:ℂ)*Y^3 + (-181/40:ℂ)*Y^2 + (-24/5:ℂ)*Y + (-63/10:ℂ)
  | 4 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (47/6:ℂ)*b*w + (59/6:ℂ)*w^2*A + (59/6:ℂ)*w^2*Y + (341/12:ℂ)*w^2 + (19/6:ℂ)*z*A + (19/6:ℂ)*z*Y + (301/12:ℂ)*z + (-5/3:ℂ)*A^2*Y + (-9:ℂ)*A^2 + (-13/6:ℂ)*A*Y^2 + (-27:ℂ)*A*Y + (7/6:ℂ)*A + (-1/2:ℂ)*Y^3 + (-223/12:ℂ)*Y^2 + (-161/6:ℂ)*Y + (-110/3:ℂ)
  | 5 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (9/2:ℂ)*b*w + (10:ℂ)*w^2*A + (10:ℂ)*w^2*Y + (50/3:ℂ)*w^2 + (-10/3:ℂ)*z*A + (-10/3:ℂ)*z*Y + (-10/3:ℂ)*z + (-10/3:ℂ)*A^2*Y + (23/3:ℂ)*A^2 + (-13/3:ℂ)*A*Y^2 + (16/3:ℂ)*A*Y + (55/6:ℂ)*A + (-1:ℂ)*Y^3 + (-7/2:ℂ)*Y^2 + (-65/6:ℂ)*Y + (-47/3:ℂ)
  | 6 => (1:ℂ)*w^2*A + (1:ℂ)*w^2*Y + (67/6:ℂ)*w^2 + (13/3:ℂ)*z*A + (13/3:ℂ)*z*Y + (127/6:ℂ)*z + (-37/3:ℂ)*A^2 + (-79/3:ℂ)*A*Y + (9/2:ℂ)*A + (-14:ℂ)*Y^2 + (-28:ℂ)*Y + (-100/3:ℂ)
  | 7 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (9/2:ℂ)*b*w + (11:ℂ)*w^2*A + (11:ℂ)*w^2*Y + (167/6:ℂ)*w^2 + (1:ℂ)*z*A + (1:ℂ)*z*Y + (107/6:ℂ)*z + (-10/3:ℂ)*A^2*Y + (-14/3:ℂ)*A^2 + (-13/3:ℂ)*A*Y^2 + (-21:ℂ)*A*Y + (41/3:ℂ)*A + (-1:ℂ)*Y^3 + (-35/2:ℂ)*Y^2 + (-233/6:ℂ)*Y + (-49:ℂ)
  | 8 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (-13/6:ℂ)*b*w + (43/3:ℂ)*w^2*A + (43/3:ℂ)*w^2*Y + (227/6:ℂ)*w^2 + (1:ℂ)*z*A + (1:ℂ)*z*Y + (49/2:ℂ)*z + (-20/3:ℂ)*A^2*Y + (-25/3:ℂ)*A^2 + (-26/3:ℂ)*A*Y^2 + (-106/3:ℂ)*A*Y + (259/6:ℂ)*A + (-2:ℂ)*Y^3 + (-88/3:ℂ)*Y^2 + (-545/6:ℂ)*Y + (-107:ℂ)
  | 9 => (1:ℂ)*A^2 + (95/6:ℂ)*A + (-1:ℂ)*Y^2 + (-13/2:ℂ)*Y + (-67/3:ℂ)
  | 10 => (1:ℂ)*b*w*A^2 + (1:ℂ)*b*w*A*Y + (-13/6:ℂ)*b*w*A + (43/3:ℂ)*w^2*A^2 + (43/3:ℂ)*w^2*A*Y + (239/6:ℂ)*w^2*A + (2:ℂ)*w^2*Y + (67/3:ℂ)*w^2 + (1:ℂ)*z*A^2 + (1:ℂ)*z*A*Y + (199/6:ℂ)*z*A + (26/3:ℂ)*z*Y + (127/3:ℂ)*z + (-20/3:ℂ)*A^3*Y + (-25/3:ℂ)*A^3 + (-26/3:ℂ)*A^2*Y^2 + (-106/3:ℂ)*A^2*Y + (39/2:ℂ)*A^2 + (-2:ℂ)*A*Y^3 + (-88/3:ℂ)*A*Y^2 + (-287/2:ℂ)*A*Y + (-493/6:ℂ)*A + (-29:ℂ)*Y^2 + (-125/2:ℂ)*Y + (-89:ℂ)
  | 11 => (1:ℂ)*w^2*A + (1:ℂ)*w^2*Y + (67/6:ℂ)*w^2 + (13/3:ℂ)*z*A + (13/3:ℂ)*z*Y + (127/6:ℂ)*z + (-77/6:ℂ)*A^2 + (-79/3:ℂ)*A*Y + (-41/12:ℂ)*A + (-27/2:ℂ)*Y^2 + (-99/4:ℂ)*Y + (-133/6:ℂ)
  | 12 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (127/26:ℂ)*b*w + (1:ℂ)*w^2*A + (1:ℂ)*w^2*Y + (127/26:ℂ)*w^2 + (10/13:ℂ)*A^2 + (1:ℂ)*A + (-10/13:ℂ)*Y^2 + (-7/13:ℂ)*Y + (107/26:ℂ)
  | 13 => (1:ℂ)*b*w*A^2 + (13/10:ℂ)*b*w*A*Y + (8/5:ℂ)*b*w*A + (3/10:ℂ)*b*w*Y^2 + (39/20:ℂ)*b*w*Y + (67/10:ℂ)*b*w + (13/10:ℂ)*w^2*A^2 + (13/10:ℂ)*w^2*A*Y + (127/20:ℂ)*w^2*A + (1:ℂ)*A^3 + (1:ℂ)*A^2 + (-1:ℂ)*A*Y^2 + (-7/10:ℂ)*A*Y + (3/5:ℂ)*A + (3/10:ℂ)*Y^2 + (39/20:ℂ)*Y + (67/10:ℂ)
  | 14 => (1:ℂ)*b*w*z*A + (1:ℂ)*b*w*z*Y + (127/26:ℂ)*b*w*z + (1:ℂ)*w^2*z*A + (1:ℂ)*w^2*z*Y + (127/26:ℂ)*w^2*z + (10/13:ℂ)*z*A^2 + (1:ℂ)*z*A + (-10/13:ℂ)*z*Y^2 + (-7/13:ℂ)*z*Y + (107/26:ℂ)*z
  | 15 => (1:ℂ)*b*w*A + (1:ℂ)*b*w*Y + (57/16:ℂ)*b*w + (7/2:ℂ)*w^2*A + (7/2:ℂ)*w^2*Y + (177/16:ℂ)*w^2 + (3/16:ℂ)*z*A + (3/16:ℂ)*z*Y + (147/32:ℂ)*z + (-5/4:ℂ)*A^2*Y + (-15/16:ℂ)*A^2 + (-13/8:ℂ)*A*Y^2 + (-53/8:ℂ)*A*Y + (285/32:ℂ)*A + (-3/8:ℂ)*Y^3 + (-49/8:ℂ)*Y^2 + (-559/32:ℂ)*Y + (-535/32:ℂ)
  | 16 => (1:ℂ)*b*w*A^2 + (13/10:ℂ)*b*w*A*Y + (8/5:ℂ)*b*w*A + (3/10:ℂ)*b*w*Y^2 + (39/20:ℂ)*b*w*Y + (67/10:ℂ)*b*w + (13/10:ℂ)*w^2*A^2 + (13/10:ℂ)*w^2*A*Y + (127/20:ℂ)*w^2*A + (1:ℂ)*A^3 + (13/10:ℂ)*A^2 + (-1:ℂ)*A*Y^2 + (-7/10:ℂ)*A*Y + (107/20:ℂ)*A
  | 17 => (1:ℂ)*b*w*A*Y + (-1:ℂ)*b*w*A + (1:ℂ)*b*w*Y^2 + (101/26:ℂ)*b*w*Y + (-127/26:ℂ)*b*w + (1:ℂ)*w^2*A*Y + (-1:ℂ)*w^2*A + (1:ℂ)*w^2*Y^2 + (101/26:ℂ)*w^2*Y + (-127/26:ℂ)*w^2 + (10/13:ℂ)*A^2*Y + (-10/13:ℂ)*A^2 + (1:ℂ)*A*Y + (-1:ℂ)*A + (-10/13:ℂ)*Y^3 + (3/13:ℂ)*Y^2 + (121/26:ℂ)*Y + (-107/26:ℂ)
  | _ => (1:ℂ)*A^2 + (85/69:ℂ)*A*Y + (275/46:ℂ)*A + (16/69:ℂ)*Y^2 + (104/69:ℂ)*Y + (393/23:ℂ)
/-- Explicit rational Nullstellensatz identity, checked by Lean's ring
normalizer. No external polynomial-system solver is trusted. -/

def remainder0 (b w z A Y : ℂ) : ℂ := ((351695100276965041508883887610179514120:ℂ))

def remainder1 (b w z A Y : ℂ) : ℂ := ((898227098281310605035237957019895473170:ℂ)) + ((620498634329813061392435177832867623835:ℂ)*Y) + ((352659735381283685632748313556114193715:ℂ)*Y^2) + ((74301671631115329812648001560347464510:ℂ)*Y^3) + ((2148051783159494861916971168585139240:ℂ)*Y^4) + ((-558249727172561344901064898616369869575:ℂ)*A) + ((-80087788379923189643038010992376957160:ℂ)*A*Y) + ((-37005011607834344323854409202839479090:ℂ)*A*Y^2) + ((3992532181703446571236002468138664440:ℂ)*A*Y^3) + ((209415096364827618844154373459887002050:ℂ)*A^2) + ((-192965749515068812445665871610011369820:ℂ)*A^2*Y) + ((-15874493641415041058694988463991826800:ℂ)*A^2*Y^2) + ((-90366767603790863116871500794081295200:ℂ)*A^3) + ((-17718974039958992768014019763545352000:ℂ)*A^3*Y) + ((-258883578002058424828272980246707559550:ℂ)*z) + ((-119176902005040255146833394241036848760:ℂ)*z*Y) + ((-11456276176850639263557179565787409280:ℂ)*z*Y^2) + ((171909113805700259853692512567264200000:ℂ)*z*A) + ((16894082287083749165265252055885153920:ℂ)*z*A*Y) + ((28350358463934388428822431621672563200:ℂ)*z*A^2) + ((-258883578002058424828272980246707559550:ℂ)*w^2) + ((-163430505082315199561922792573807371760:ℂ)*w^2*Y) + ((-25776621397913938343003654023021670880:ℂ)*w^2*Y^2) + ((127655510728425315438603114234493677000:ℂ)*w^2*A) + ((38011685145938435621846817125741596320:ℂ)*w^2*A*Y) + ((63788306543852373964850471148763267200:ℂ)*w^2*A^2) + ((-29871182077160587480185343874620103025:ℂ)*b*w) + ((-16304273485808968540889780008548705030:ℂ)*b*w*Y) + ((-2148051783159494861916971168585139240:ℂ)*b*w*Y^2) + ((17282574492353398574555516930870646750:ℂ)*b*w*A) + ((3167640428828202968487234760478466360:ℂ)*b*w*A*Y) + ((5315692211987697830404205929063605600:ℂ)*b*w*A^2)

def remainder2 (b w z A Y : ℂ) : ℂ := ((1349724708642849440767040932045183165440:ℂ)) + ((1143721541881731929594345176521002019060:ℂ)*Y) + ((678812201722983356041781246241914211060:ℂ)*Y^2) + ((124713403346524004126019890393284020600:ℂ)*Y^3) + ((-270912544849613762103652525296455040:ℂ)*Y^4) + ((-812261011573256257484549602169500984440:ℂ)*A) + ((207518818767567672239286414706934719320:ℂ)*A*Y) + ((-57801461587103811482586002502848302440:ℂ)*A*Y^2) + ((-1480102126189017719532969443956253280:ℂ)*A*Y^3) + ((494823755330027085526802860015687069920:ℂ)*A^2) + ((-434815795227348962158693395225783635280:ℂ)*A^2*Y) + ((-2229682131919486458819789699787403040:ℂ)*A^2*Y^2) + ((-252342038050766292703119906523533443040:ℂ)*A^3) + ((-1020492550580082501390472781127604800:ℂ)*A^3*Y) + ((-663165751985919996692697866380461898380:ℂ)*z) + ((-335877671500563392678709242934246366120:ℂ)*z*Y) + ((-40483848112959942751804663892366540640:ℂ)*z*Y^2) + ((294443578360417486804834406220437291400:ℂ)*z*A) + ((47981043712738522636862536866009912480:ℂ)*z*A*Y) + ((88464891825698465388667200758376453120:ℂ)*z*A^2) + ((-309049979153340517687362199693961747580:ℂ)*w^2) + ((-106314815041184252630305860168503042520:ℂ)*w^2*Y) + ((-6424906773841069350838664471968916640:ℂ)*w^2*Y^2) + ((226866083826885358692930277441903877400:ℂ)*w^2*A) + ((17287044195501919974115293918991757280:ℂ)*w^2*A*Y) + ((23711950969342989324953958390960673920:ℂ)*w^2*A^2) + ((9966842366504603907914918627611163940:ℂ)*b*w) + ((3433960311046507242336418281080973000:ℂ)*b*w*Y) + ((270912544849613762103652525296455040:ℂ)*b*w*Y^2) + ((3592518802506356689747120171769191800:ℂ)*b*w*A) + ((577060310023638512520794359634736480:ℂ)*b*w*A*Y) + ((306147765174024750417141834338281440:ℂ)*b*w*A^2)

def remainder3 (b w z A Y : ℂ) : ℂ := ((1359472659281115788699015921871472903080:ℂ)) + ((1163271414271176850255547006896402604880:ℂ)*Y) + ((681678948934443189387680672273949999960:ℂ)*Y^2) + ((123236528965578680750963276203772304480:ℂ)*Y^3) + ((-1068503124650410015505078665027370400:ℂ)*Y^4) + ((-842160641075660016061256021718084697380:ℂ)*A) + ((173606739702800123744156563679040232440:ℂ)*A*Y) + ((-54066496938038236218759026615557941840:ℂ)*A*Y^2) + ((-3216034564578986035759602806900010240:ℂ)*A*Y^3) + ((516172009387015835417910456860080653660:ℂ)*A^2) + ((-428187238743645676874533009630203790200:ℂ)*A^2*Y) + ((-3308775269297034331068778006482170880:ℂ)*A^2*Y^2) + ((-250925320597073906057843111004755674680:ℂ)*A^3) + ((-1161243829368458310814253864609531040:ℂ)*A^3*Y) + ((-651071072490293231665988156781176483160:ℂ)*z) + ((-328232310875232034627185066716356924020:ℂ)*z*Y) + ((-38324460873059737511430724419010252440:ℂ)*z*Y^2) + ((140751278788375809423781083481926240:ℂ)*z*Y^3) + ((279706672420659874591685188463673293340:ℂ)*z*A) + ((48723713498946341231959680820588432320:ℂ)*z*A*Y) + ((281502557576751618847562166963852480:ℂ)*z*A*Y^2) + ((87048174372006078743390405239598684760:ℂ)*z*A^2) + ((140751278788375809423781083481926240:ℂ)*z*A^2*Y) + ((-289734595481220161599930275408535785960:ℂ)*w^2) + ((-87530986060937023283781353434641197220:ℂ)*w^2*Y) + ((590586503070588186638598054432069960:ℂ)*w^2*Y^2) + ((1079093137377547872248988306694767840:ℂ)*w^2*Y^3) + ((209905099039005426571991304246095303340:ℂ)*w^2*A) + ((13441036994105279897803790801429853120:ℂ)*w^2*A*Y) + ((2158186274755095744497976613389535680:ℂ)*w^2*A*Y^2) + ((12850450491034691711165192746997783160:ℂ)*w^2*A^2) + ((1079093137377547872248988306694767840:ℂ)*w^2*A^2*Y) + ((22061521862131368934624628226896579160:ℂ)*b*w) + ((11079320936377865293860594498970415100:ℂ)*b*w*Y) + ((2430299784749819002477591998652743240:ℂ)*b*w*Y^2) + ((140751278788375809423781083481926240:ℂ)*b*w*Y^3) + ((-11144387137251255523402097584994806260:ℂ)*b*w*A) + ((1319730096231457107617938314213256320:ℂ)*b*w*A*Y) + ((281502557576751618847562166963852480:ℂ)*b*w*A*Y^2) + ((-1110569688518361894859653684439486920:ℂ)*b*w*A^2) + ((140751278788375809423781083481926240:ℂ)*b*w*A^2*Y)

def remainder4 (b w z A Y : ℂ) : ℂ := ((1359472659281115788699015921871472903080:ℂ)) + ((1163271414271176850255547006896402604880:ℂ)*Y) + ((724693840484758934972123568962043759960:ℂ)*Y^2) + ((159369037867843907041895309421771062880:ℂ)*Y^3) + ((16997751326482203129960937943972008800:ℂ)*Y^4) + ((-842160641075660016061256021718084697380:ℂ)*A) + ((193147972058429182348060815205135912440:ℂ)*A*Y) + ((-43458872118602452645379246386530228240:ℂ)*A*Y^2) + ((38973047349534657589590071217654245760:ℂ)*A*Y^3) + ((516172009387015835417910456860080653660:ℂ)*A^2) + ((-430825305111655599786060083586226707000:ℂ)*A^2*Y) + ((28044308165266747832259452473728107520:ℂ)*A^2*Y^2) + ((-250925320597073906057843111004755674680:ℂ)*A^3) + ((6069012142214293372630319200045870560:ℂ)*A^3*Y) + ((-651071072490293231665988156781176483160:ℂ)*z) + ((-328232310875232034627185066716356924020:ℂ)*z*Y) + ((-65638917007510235957551963815949790040:ℂ)*z*Y^2) + ((-5451184622752671116553795485970262560:ℂ)*z*Y^3) + ((279706672420659874591685188463673293340:ℂ)*z*A) + ((36315030953121889018480481101517675520:ℂ)*z*A*Y) + ((-7850793550196072925637567100880774720:ℂ)*z*A*Y^2) + ((87048174372006078743390405239598684760:ℂ)*z*A^2) + ((-2399608927443401809083771614910512160:ℂ)*z*A^2*Y) + ((-289734595481220161599930275408535785960:ℂ)*w^2) + ((-87530986060937023283781353434641197220:ℂ)*w^2*Y) + ((-13819402166285186584149772336079339640:ℂ)*w^2*Y^2) + ((-211353609131924495284298593948044960:ℂ)*w^2*Y^3) + ((209905099039005426571991304246095303340:ℂ)*w^2*A) + ((6894724154969545265495866540187800320:ℂ)*w^2*A*Y) + ((281502557576751618847562166963852480:ℂ)*w^2*A*Y^2) + ((12850450491034691711165192746997783160:ℂ)*w^2*A^2) + ((492856166708676114131860760911897440:ℂ)*w^2*A^2*Y) + ((22061521862131368934624628226896579160:ℂ)*b*w) + ((11079320936377865293860594498970415100:ℂ)*b*w*Y) + ((2430299784749819002477591998652743240:ℂ)*b*w*Y^2) + ((140751278788375809423781083481926240:ℂ)*b*w*Y^3) + ((-11144387137251255523402097584994806260:ℂ)*b*w*A) + ((1319730096231457107617938314213256320:ℂ)*b*w*A*Y) + ((281502557576751618847562166963852480:ℂ)*b*w*A*Y^2) + ((-1110569688518361894859653684439486920:ℂ)*b*w*A^2) + ((140751278788375809423781083481926240:ℂ)*b*w*A^2*Y)

def remainder5 (b w z A Y : ℂ) : ℂ := ((8630726320948611545268322161679184918880:ℂ)) + ((2800225549845206569252215693537371502700:ℂ)*Y) + ((630187378707773874060242907000829831304:ℂ)*Y^2) + ((56244648319115486807600770354629612864:ℂ)*Y^3) + ((4434225897585126508792126083921575616:ℂ)*Y^4) + ((-3315886382059586657278531639783098697668:ℂ)*A) + ((1067359904777213856865641377082610427926:ℂ)*A*Y) + ((203933933291297157000372049216734395512:ℂ)*A*Y^2) + ((27959749584804005072379324117056973816:ℂ)*A*Y^3) + ((-1710305132393137297163053700697413954250:ℂ)*A^2) + ((-234986616242522846066859325849956266900:ℂ)*A^2*Y) + ((40607833594163824453428264333778540704:ℂ)*A^2*Y^2) + ((-370982075520185710563624741644437373988:ℂ)*A^3) + ((17082309906944945889841066300643142504:ℂ)*A^3*Y) + ((33769295291248493621797721228065868592:ℂ)*z) + ((-11583562066066278298656042401607094752:ℂ)*z*Y) + ((-826274014787200451785077731284171776:ℂ)*z*Y^2) + ((-197623251529207963802879909288587776:ℂ)*z*Y^3) + ((-82517804304078534497783561991550128984:ℂ)*z*A) + ((-10981502932094129002306153636579735104:ℂ)*z*A*Y) + ((-2330046705197793659314049886619886496:ℂ)*z*A*Y^2) + ((-31028144753570534652951218822433444288:ℂ)*z*A^2) + ((-7653170298666864961834687191592186944:ℂ)*z*A^2*Y) + ((-5520746844998279266323517214260888224:ℂ)*z*A^3) + ((7332426368194783093294302488635763760:ℂ)*w^2) + ((6792494635903784340040574321416894200:ℂ)*w^2*Y) + ((1770788046215345009582204279029124640:ℂ)*w^2*Y^2) + ((140751278788375809423781083481926240:ℂ)*w^2*Y^3) + ((-702117943788750635891792024287511760:ℂ)*w^2*A) + ((1319730096231457107617938314213256320:ℂ)*w^2*A*Y) + ((281502557576751618847562166963852480:ℂ)*w^2*A*Y^2) + ((-451057949983887901964265964815868320:ℂ)*w^2*A^2) + ((140751278788375809423781083481926240:ℂ)*w^2*A^2*Y) + ((7332426368194783093294302488635763760:ℂ)*b*w) + ((6792494635903784340040574321416894200:ℂ)*b*w*Y) + ((1770788046215345009582204279029124640:ℂ)*b*w*Y^2) + ((140751278788375809423781083481926240:ℂ)*b*w*Y^3) + ((-702117943788750635891792024287511760:ℂ)*b*w*A) + ((1319730096231457107617938314213256320:ℂ)*b*w*A*Y) + ((281502557576751618847562166963852480:ℂ)*b*w*A*Y^2) + ((-451057949983887901964265964815868320:ℂ)*b*w*A^2) + ((140751278788375809423781083481926240:ℂ)*b*w*A^2*Y)

def remainder6 (b w z A Y : ℂ) : ℂ := ((8624548607394305704394444284779310692720:ℂ)) + ((2796575767132804788950188950087340186900:ℂ)*Y) + ((631346146281348307244918919300965655464:ℂ)*Y^2) + ((57153723764956424150317632170366999424:ℂ)*Y^3) + ((4542496112037723285271957686599980416:ℂ)*Y^4) + ((-3315531231769631666567227744654823392308:ℂ)*A) + ((1065454509587767476685327476579051163606:ℂ)*A*Y) + ((203522003508791839009896253359115146232:ℂ)*A*Y^2) + ((28068019799256601848859155719735378616:ℂ)*A*Y^3) + ((-1711008787257042351480505860321359623530:ℂ)*A^2) + ((-235960653817035341475464086627300696340:ℂ)*A^2*Y) + ((40499563379711227676948432731100135904:ℂ)*A^2*Y^2) + ((-370635107866351950639036844748425167588:ℂ)*A^3) + ((16974039692492349113361234697964737704:ℂ)*A^3*Y) + ((33769295291248493621797721228065868592:ℂ)*z) + ((-11583562066066278298656042401607094752:ℂ)*z*Y) + ((-826274014787200451785077731284171776:ℂ)*z*Y^2) + ((-197623251529207963802879909288587776:ℂ)*z*Y^3) + ((-82517804304078534497783561991550128984:ℂ)*z*A) + ((-10981502932094129002306153636579735104:ℂ)*z*A*Y) + ((-2330046705197793659314049886619886496:ℂ)*z*A*Y^2) + ((-31028144753570534652951218822433444288:ℂ)*z*A^2) + ((-7653170298666864961834687191592186944:ℂ)*z*A^2*Y) + ((-5520746844998279266323517214260888224:ℂ)*z*A^3)

def remainder7 (b w z A Y : ℂ) : ℂ := 0

def coefficient0 (b w z A Y : ℂ) : ℂ := ((6638040461591241662263409749915578450:ℂ)) + ((2148051783159494861916971168585139240:ℂ)*Y) + ((-5315692211987697830404205929063605600:ℂ)*A)

def coefficient1 (b w z A Y : ℂ) : ℂ := ((-8852894320814486975133391667162503770:ℂ)) + ((-2418964328009108624020623693881594280:ℂ)*Y) + ((5009544446813673079987064094725324160:ℂ)*A)

def coefficient2 (b w z A Y : ℂ) : ℂ := ((-1083105626474038659108332202921081960:ℂ)) + ((-587664626763342035141717374474778520:ℂ)*Y) + ((-140751278788375809423781083481926240:ℂ)*Y^2) + ((1416717453692386645276795518777768360:ℂ)*A) + ((-140751278788375809423781083481926240:ℂ)*A*Y)

def coefficient3 (b w z A Y : ℂ) : ℂ := ((1290446746509472367533286900642812800:ℂ)*Y^2) + ((586236970668871758117127545782870400:ℂ)*A*Y)

def coefficient4 (b w z A Y : ℂ) : ℂ := ((325578522164216227906088339095867702200:ℂ)) + ((-21461474260897422196697261976813634320:ℂ)*Y) + ((-12563525428897076621168811860050433184:ℂ)*Y^2) + ((120056754923111804505781630639681699308:ℂ)*A) + ((-11013297764730652517210747100597271944:ℂ)*A*Y) + ((30664494079770525012885934836234732168:ℂ)*z) + ((5253561371223463152750915576681674784:ℂ)*z*Y) + ((5520746844998279266323517214260888224:ℂ)*z*A) + ((13301508441018579613129458711813651480:ℂ)*w^2) + ((352104887920300304708079677429971200:ℂ)*w^2*Y) + ((-659511738534473992895387719623618600:ℂ)*b*w)

def coefficient5 (b w z A Y : ℂ) : ℂ := ((1501126658055624885241353265389998880:ℂ)) + ((1083272184441355478935273602021254160:ℂ)*Y) + ((140751278788375809423781083481926240:ℂ)*Y^2) + ((-451057949983887901964265964815868320:ℂ)*A) + ((140751278788375809423781083481926240:ℂ)*A*Y)

def coefficient6 (b w z A Y : ℂ) : ℂ := ((504744574987453005600692668065964747920:ℂ)) + ((119143589595817148307965224832201983980:ℂ)*Y) + ((19589514483162681667735317523462415544:ℂ)*Y^2) + ((-370635107866351950639036844748425167588:ℂ)*A) + ((16974039692492349113361234697964737704:ℂ)*A*Y) + ((1976320080658308787026329741082735312:ℂ)*z) + ((-852250272219709343899919608807034784:ℂ)*z*Y) + ((-5520746844998279266323517214260888224:ℂ)*z*A)

end SmallLevelThirtyFourCriticalMMP
end
end

/-! ## ThirtyFourCriticalMMPBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourCriticalMMP

theorem step0 (b w z A Y : ℂ) :
    remainder0 b w z A Y=remainder1 b w z A Y+
      coefficient0 b w z A Y*critical_mmp_row b w z A Y 0 := by
  norm_num [remainder0,remainder1,coefficient0,critical_mmp_row]
  ring

#print axioms step0

theorem step1 (b w z A Y : ℂ) :
    remainder1 b w z A Y=remainder2 b w z A Y+
      coefficient1 b w z A Y*critical_mmp_row b w z A Y 1 := by
  norm_num [remainder1,remainder2,coefficient1,critical_mmp_row]
  ring

#print axioms step1

theorem step2 (b w z A Y : ℂ) :
    remainder2 b w z A Y=remainder3 b w z A Y+
      coefficient2 b w z A Y*critical_mmp_row b w z A Y 2 := by
  norm_num [remainder2,remainder3,coefficient2,critical_mmp_row]
  ring

#print axioms step2

theorem step3 (b w z A Y : ℂ) :
    remainder3 b w z A Y=remainder4 b w z A Y+
      coefficient3 b w z A Y*critical_mmp_row b w z A Y 6 := by
  norm_num [remainder3,remainder4,coefficient3,critical_mmp_row]
  ring

#print axioms step3

theorem step4 (b w z A Y : ℂ) :
    remainder4 b w z A Y=remainder5 b w z A Y+
      coefficient4 b w z A Y*critical_mmp_row b w z A Y 9 := by
  norm_num [remainder4,remainder5,coefficient4,critical_mmp_row]
  ring

#print axioms step4

theorem step5 (b w z A Y : ℂ) :
    remainder5 b w z A Y=remainder6 b w z A Y+
      coefficient5 b w z A Y*critical_mmp_row b w z A Y 12 := by
  norm_num [remainder5,remainder6,coefficient5,critical_mmp_row]
  ring

#print axioms step5

theorem step6 (b w z A Y : ℂ) :
    remainder6 b w z A Y=remainder7 b w z A Y+
      coefficient6 b w z A Y*critical_mmp_row b w z A Y 18 := by
  norm_num [remainder6,remainder7,coefficient6,critical_mmp_row]
  ring

#print axioms step6

end SmallLevelThirtyFourCriticalMMP
end
end

/-! ## ThirtyFourCriticalMMP -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourCriticalMMP
theorem critical_mmp_impossible (b w z A Y : ℂ)
    (h : ∀ i : Fin 19,critical_mmp_row b w z A Y i=0) : False := by
  have h7 : remainder7 b w z A Y=0 := rfl
  have h6 : remainder6 b w z A Y=0 := by
    rw [step6,h 18,mul_zero,add_zero]
    exact h7
  have h5 : remainder5 b w z A Y=0 := by
    rw [step5,h 12,mul_zero,add_zero]
    exact h6
  have h4 : remainder4 b w z A Y=0 := by
    rw [step4,h 9,mul_zero,add_zero]
    exact h5
  have h3 : remainder3 b w z A Y=0 := by
    rw [step3,h 6,mul_zero,add_zero]
    exact h4
  have h2 : remainder2 b w z A Y=0 := by
    rw [step2,h 2,mul_zero,add_zero]
    exact h3
  have h1 : remainder1 b w z A Y=0 := by
    rw [step1,h 1,mul_zero,add_zero]
    exact h2
  have h0 : remainder0 b w z A Y=0 := by
    rw [step0,h 0,mul_zero,add_zero]
    exact h1
  norm_num [remainder0] at h0

#print axioms critical_mmp_impossible

end SmallLevelThirtyFourCriticalMMP
end
end

/-! ## ThirtyFourFiniteJetMMPCriticalRowBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 8192
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace SmallLevelThirtyFourFiniteJetMMP
open Complex

theorem critical_row_0 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row3 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 0*v 2=0 := by
  have hi : ((0 : Fin 19) : ℕ) = 0 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row3,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((20*W^2)/(3)))*(hR-((2))*hL-(((1)/(850)) + (((-1)*W*b)/(1700)) + (((-1)*W^2)/(850)) + (((-1)*Z)/(850)) + (((-3)*Y*a)/(1700)) + ((7*Y^2)/(1700)) + ((1*Y^4)/(1700)))*hJ)

#print axioms critical_row_0

theorem critical_row_1 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row4 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 1*v 2=0 := by
  have hi : ((1 : Fin 19) : ℕ) = 1 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row4,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-20)*W^2)/(3)))*(hR-((3))*hL-((((-1))/(850)) + ((1*W*b)/(1700)) + (((-1)*W^2)/(850)) + (((-1)*Z)/(850)) + (((-1)*Y*a)/(1700)) + ((9*Y^2)/(1700)) + (((-1)*Y^4)/(1700)))*hJ)

#print axioms critical_row_1

theorem critical_row_2 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row5 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 2*v 2=0 := by
  have hi : ((2 : Fin 19) : ℕ) = 2 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row5,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((20*W^2)/(3)))*(hR-(0)*hL-((((-1))/(850)) + (((-1)*W*b)/(1700)) + (((-1)*W^2)/(1700)) + (((-1)*Z)/(1700)) + ((1*Y*a)/(1700)) + (((-1)*Y^2)/(1700)))*hJ)

#print axioms critical_row_2

theorem critical_row_3 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row21 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 3*v 2=0 := by
  have hi : ((3 : Fin 19) : ℕ) = 3 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row21,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((1*W^2))*(hR-((2))*hL-((((-1))/(425)) + (((-3)*W^2)/(1700)) + (((-3)*Z)/(1700)) + ((2*Y^2)/(425)) + (((-1)*Y^4)/(1700)))*hJ)

#print axioms critical_row_3

theorem critical_row_4 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row22 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 4*v 2=0 := by
  have hi : ((4 : Fin 19) : ℕ) = 4 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row22,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((10*W^2)/(3)))*(hR-((1))*hL-((((-1)*W*b)/(850)) + (((-3)*W^2)/(1700)) + (((-3)*Z)/(1700)) + (((-1)*Y*a)/(850)) + ((3*Y^2)/(850)) + ((1*Y^4)/(1700)))*hJ)

#print axioms critical_row_4

theorem critical_row_5 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row25 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 5*v 2=0 := by
  have hi : ((5 : Fin 19) : ℕ) = 5 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row25,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((10*W^2)/(3)))*(hR-((1))*hL-(((1)/(425)) + (((-1)*W*b)/(850)) + (((-1)*Y*a)/(850)) + (((-1)*Y^2)/(850)) + ((1*Y^4)/(850)))*hJ)

#print axioms critical_row_5

theorem critical_row_6 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row30 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 6*v 2=0 := by
  have hi : ((6 : Fin 19) : ℕ) = 6 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row30,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((10*W^2)/(3)))*(hR-((1))*hL-((((-1)*W^2)/(850)) + (((-1)*Z)/(850)) + (((-1)*Y*a)/(850)) + ((2*Y^2)/(425)))*hJ)

#print axioms critical_row_6

theorem critical_row_7 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row38 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 7*v 2=0 := by
  have hi : ((7 : Fin 19) : ℕ) = 7 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row38,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((10*W^2)/(3)))*(hR-(0)*hL-(((1)/(425)) + (((-1)*W*b)/(850)) + (((-1)*W^2)/(850)) + (((-1)*Z)/(850)) + (((-1)*Y*a)/(425)) + ((3*Y^2)/(850)) + ((1*Y^4)/(850)))*hJ)

#print axioms critical_row_7

theorem critical_row_8 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row39 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 8*v 2=0 := by
  have hi : ((8 : Fin 19) : ℕ) = 8 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row39,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-20)*W^2)/(3)))*(hR-(0)*hL-((((-3))/(850)) + ((1*W*b)/(1700)) + ((1*W^2)/(1700)) + ((1*Z)/(1700)) + ((1*Y*a)/(340)) + (((-7)*Y^2)/(1700)) + (((-1)*Y^4)/(850)))*hJ)

#print axioms critical_row_8

theorem critical_row_9 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row41 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 9*v 2=0 := by
  have hi : ((9 : Fin 19) : ℕ) = 9 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row41,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((20*Y^2*W^2)/(3)))*(hR-(0)*hL-(((1)/(850*Y^2)) + (((-1)*a)/(1700*Y)) + ((1)/(1700)))*hJ)

#print axioms critical_row_9

theorem critical_row_10 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row45 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 10*v 2=0 := by
  have hi : ((10 : Fin 19) : ℕ) = 10 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row45,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((20*Y^2*W^2)/(3)))*(hR-(((1)/(Y^2)))*hL-(((1)/(850*Y^2)) + (((-1)*W^2)/(850*Y^2)) + (((-1)*Z)/(850*Y^2)) + ((3*a)/(1700*Y)) + (((-1)*W*a*b)/(1700*Y)) + (((-1)*W^2*a)/(1700*Y)) + (((-1)*Z*a)/(1700*Y)) + ((9)/(1700)) + (((-1)*a^2)/(340)) + ((7*Y*a)/(1700)) + ((1*Y^3*a)/(850)))*hJ)

#print axioms critical_row_10

theorem critical_row_11 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row50 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 11*v 2=0 := by
  have hi : ((11 : Fin 19) : ℕ) = 11 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row50,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((10*Y^2*W^2)/(3)))*(hR-(((1)/(Y^2)))*hL-((((-1))/(850*Y^2)) + (((-1)*W^2)/(850*Y^2)) + (((-1)*Z)/(850*Y^2)) + (((-1)*a)/(1700*Y)) + ((7)/(1700)))*hJ)

#print axioms critical_row_11

theorem critical_row_12 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row64 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 12*v 2=0 := by
  have hi : ((12 : Fin 19) : ℕ) = 12 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row64,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-20)*W^2)/(13)))*(hR-(0)*hL-(((1)/(1700)) + ((1*W*b)/(1700)) + ((1*W^2)/(1700)))*hJ)

#print axioms critical_row_12

theorem critical_row_13 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row68 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 13*v 2=0 := by
  have hi : ((13 : Fin 19) : ℕ) = 13 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row68,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((2*Y^2*W^2))*(hR-(((-1)))*hL-((((-1))/(850*Y^2)) + (((-1)*W*b)/(850*Y^2)) + (((-1)*W^2*a)/(1700*Y)) + (((-1))/(1700)) + (((-1)*W*b)/(1700)))*hJ)

#print axioms critical_row_13

theorem critical_row_14 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row70 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 14*v 2=0 := by
  have hi : ((14 : Fin 19) : ℕ) = 14 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row70,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-20)*Y^2*W^2)/(13)))*(hR-(0)*hL-(((1*Z)/(1700*Y^2)) + ((1*Z*W*b)/(1700*Y^2)) + ((1*Z*W^2)/(1700*Y^2)))*hJ)

#print axioms critical_row_14

theorem critical_row_15 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row71 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 15*v 2=0 := by
  have hi : ((15 : Fin 19) : ℕ) = 15 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row71,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-5)*W^2)/(4)))*(hR-(0)*hL-((((-1))/(340)) + ((1*W*b)/(850)) + ((1*W^2)/(850)) + ((1*Z)/(1700)) + ((1*Y*a)/(340)) + (((-7)*Y^2)/(1700)) + (((-1)*Y^4)/(850)))*hJ)

#print axioms critical_row_15

theorem critical_row_16 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row72 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 16*v 2=0 := by
  have hi : ((16 : Fin 19) : ℕ) = 16 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row72,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((2*Y^2*W^2))*(hR-(0)*hL-((((-1)*W*b)/(850*Y^2)) + (((-1)*a)/(1700*Y)) + (((-1)*W^2*a)/(1700*Y)) + (((-1)*W*b)/(1700)))*hJ)

#print axioms critical_row_16

theorem critical_row_17 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row84 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 17*v 2=0 := by
  have hi : ((17 : Fin 19) : ℕ) = 17 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row84,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    (((20*Y^2*W^2)/(13)))*(hR-(0)*hL-(((1)/(1700*Y^2)) + ((1*W*b)/(1700*Y^2)) + ((1*W^2)/(1700*Y^2)) + (((-1))/(1700)) + (((-1)*W*b)/(1700)) + (((-1)*W^2)/(1700)))*hJ)

#print axioms critical_row_17

theorem critical_row_18 (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hL : row0 1 Y Z W a b v=0) (hJ : row89 1 Y Z W a b v=0)
    (hR : row97 1 Y Z W a b v=0) :
    SmallLevelThirtyFourCriticalMMP.critical_mmp_row b W Z (a*Y) (Y^2) 18*v 2=0 := by
  have hi : ((18 : Fin 19) : ℕ) = 18 := rfl
  norm_num only [hi,Fin.val_zero,Fin.val_ofNat,Fin.val_natCast,row0,row89,row97,SmallLevelThirtyFourCriticalMMP.critical_mmp_row] at hL hJ hR ⊢
  linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring))
    ((((-5)*Y^2)/(391)))*(hR-(0)*hL-(((9*W^2)/(25*Y^2)) + (((-1)*W^2*a)/(25*Y)) + (((-2)*W^2)/(75)))*hJ)

#print axioms critical_row_18

end SmallLevelThirtyFourFiniteJetMMP
end
end

/-! ## ThirtyFourFiniteJetMMPCriticalKernel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourFiniteJetMMP
open Complex
/-- A finite algebraic kernel theorem. Its rows must still be bound to
original pole vectors before it gives the level34 analytic conclusion. -/
theorem critical_kernel_zero (Y Z W a b : ℂ) (hY : Y≠0) (hW : W≠0) (v : Fin 3→ℂ)
    (hLall : ∀ i : Fin 89,rows 1 Y Z W a b v ⟨i.val,by omega⟩=0)
    (hJ0 : row89 1 Y Z W a b v=0) (hJ8 : row97 1 Y Z W a b v=0) : v=0 := by
  have hL : row0 1 Y Z W a b v=0:=hLall 0
  have hJ : row89 1 Y Z W a b v=0:=hJ0
  have h2 : v 2=0 := by
    by_contra h2
    apply SmallLevelThirtyFourCriticalMMP.critical_mmp_impossible b W Z (a*Y) (Y^2)
    intro i
    fin_cases i
    · exact (mul_eq_zero.mp (critical_row_0 Y Z W a b hY hW v hL hJ (hLall 3))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_1 Y Z W a b hY hW v hL hJ (hLall 4))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_2 Y Z W a b hY hW v hL hJ (hLall 5))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_3 Y Z W a b hY hW v hL hJ (hLall 21))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_4 Y Z W a b hY hW v hL hJ (hLall 22))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_5 Y Z W a b hY hW v hL hJ (hLall 25))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_6 Y Z W a b hY hW v hL hJ (hLall 30))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_7 Y Z W a b hY hW v hL hJ (hLall 38))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_8 Y Z W a b hY hW v hL hJ (hLall 39))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_9 Y Z W a b hY hW v hL hJ (hLall 41))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_10 Y Z W a b hY hW v hL hJ (hLall 45))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_11 Y Z W a b hY hW v hL hJ (hLall 50))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_12 Y Z W a b hY hW v hL hJ (hLall 64))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_13 Y Z W a b hY hW v hL hJ (hLall 68))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_14 Y Z W a b hY hW v hL hJ (hLall 70))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_15 Y Z W a b hY hW v hL hJ (hLall 71))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_16 Y Z W a b hY hW v hL hJ (hLall 72))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_17 Y Z W a b hY hW v hL hJ (hLall 84))).resolve_right h2
    · exact (mul_eq_zero.mp (critical_row_18 Y Z W a b hY hW v hL hJ hJ8)).resolve_right h2
  have h1 : v 1=0 := by
    norm_num only [row89,h2,mul_zero,add_zero,zero_add] at hJ
    linear_combination (norm := (ring_nf; all_goals field_simp [hW]; all_goals ring)) hJ*(W^2/1700)
  have h0 : v 0=0 := by
    norm_num only [row0,h1,h2,mul_zero,add_zero,zero_add] at hL
    linear_combination (norm := (ring_nf; all_goals field_simp [hY,hW]; all_goals ring)) hL*(-W^2/(2*Y^2))
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

#print axioms critical_kernel_zero

end SmallLevelThirtyFourFiniteJetMMP
end
end

/-! ## ThirtyFourFiniteJetMMPQuadratic -/
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourFiniteJetMMP
open Complex
def quadratic (X Y Z W a b : ℂ) (v : Fin 3→ℂ) : ℂ := (0)*v 0 + ((((-2)*Z)/(Y^2)))*v 1 + (((2*X^2*Z)/(Y^2)) + ((1*X^3*Z)/(Y^2)) + ((1*X^3*Z*a)/(Y)) + (1*X^3*Z))*v 2

theorem quadratic_jet_constraint (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (v : Fin 3→ℂ)
    (hC : quadratic X Y Z W a b v=0) (hJ : row94 X Y Z W a b v=0) :
    ((22*X^2-4*X+8)*(a*Y+Y^2)+39*X^2-28*X+116)*v 2=0 := by
  unfold quadratic at hC
  unfold row94 at hJ
  linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hZ]; all_goals ring))
    (20*Y^2/(X*Z))*(hC-(X*Z/(34*Y^2))*hJ)

#print axioms quadratic_jet_constraint

end SmallLevelThirtyFourFiniteJetMMP
end
end

/-! ## ThirtyFourFiniteJetMMPPositiveScalar -/
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourFiniteJetMMP
open Complex QuantitativeArithmeticSmallLevelThirtyFour
theorem positive_scalar_constraint (u : ℝ) (hu : 2≤u) (Y Z W a b : ℂ)
    (hY : Y≠0) (v : Fin 3→ℂ) (hv : v 2≠0)
    (hH : ((22*(u:ℂ)^2-4*u+8)*(a*Y+Y^2)+39*(u:ℂ)^2-28*u+116)*v 2=0)
    (hJ5 : row94 u Y Z W a b v=0) (hJ8 : row97 u Y Z W a b v=0) :
    (shiftD u:ℂ)*Y^2=(shiftN u:ℂ) := by
  have hX : (u:ℂ)≠0 := by exact_mod_cast (show u≠0 by linarith)
  have hQreal : 0<11*u^2-2*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hQ : 11*(u:ℂ)^2-2*u+4≠0 := by exact_mod_cast ne_of_gt hQreal
  have hP : 22*(u:ℂ)^2-4*u+8≠0 := by
    have he : 22*(u:ℂ)^2-4*u+8=2*(11*(u:ℂ)^2-2*u+4) := by ring
    rw [he]; exact mul_ne_zero (by norm_num) hQ
  have hPn : (8:ℂ)-(u:ℂ)*4+(u:ℂ)^2*22≠0 := by
    convert hP using 1 <;> ring
  have hQn : (4:ℂ)-(u:ℂ)*2+(u:ℂ)^2*11≠0 := by
    convert hQ using 1 <;> ring
  have hP2n : (64:ℂ)-(u:ℂ)*64+(u:ℂ)^2*368-(u:ℂ)^3*176+(u:ℂ)^4*484≠0 := by
    convert pow_ne_zero 2 hP using 1 <;> ring
  have hH0 := (mul_eq_zero.mp hH).resolve_right hv
  have ha : a= -(Y^2+(39*(u:ℂ)^2-28*u+116)/(22*(u:ℂ)^2-4*u+8))/Y := by
    have hr : (39*(u:ℂ)^2-28*u+116)/(22*(u:ℂ)^2-4*u+8)= -(a*Y+Y^2) := by
      apply (div_eq_iff hP).2
      linear_combination hH0
    apply (eq_div_iff hY).2
    rw [hr]
    ring
  have he : ((shiftN u:ℂ)-(shiftD u:ℂ)*Y^2)*v 2=0 := by
    unfold row94 at hJ5
    unfold row97 at hJ8
    unfold shiftN shiftD
    push_cast
    rw [ha] at hJ5 hJ8
    linear_combination (norm := (field_simp [hX,hY,hP,hQ,hPn,hQn]; ring_nf; all_goals field_simp [hX,hY,hP,hQ,hPn,hQn,hP2n]; all_goals ring))
      (2*Y^2*(11*(u:ℂ)^2-2*u+4)^2/17)*(hJ8-((((816)/((u:ℂ)*Y^2)) + (((-68))/((u:ℂ))) + (((-204))/(Y^2)) + (((-68)*(-(Y^2+(39*(u:ℂ)^2-28*u+116)/(22*(u:ℂ)^2-4*u+8))/Y))/(Y)) + ((68)/(3)))/(-68/(u:ℂ)))*hJ5)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hv)).symm

#print axioms positive_scalar_constraint

end SmallLevelThirtyFourFiniteJetMMP
end
end

/-! ## ThirtyFourFiniteJetMMPPositiveKernel -/
section
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourFiniteJetMMP
open Complex QuantitativeArithmeticSmallLevelThirtyFour
theorem positive_kernel_zero (u : ℝ) (hu : 2≤u) (Y Z W a b : ℂ)
    (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (hnorm : 9*u/2≤‖Y^2‖)
    (v : Fin 3→ℂ) (hL : row0 u Y Z W a b v=0)
    (hC : quadratic u Y Z W a b v=0)
    (hJ5 : row94 u Y Z W a b v=0) (hJ8 : row97 u Y Z W a b v=0) : v=0 := by
  have hX : (u:ℂ)≠0 := by exact_mod_cast (show u≠0 by linarith)
  have h2 : v 2=0 := by
    by_contra hv
    exact positive_shift_impossible u hu (Y^2) hnorm
      (positive_scalar_constraint u hu Y Z W a b hY v hv
        (quadratic_jet_constraint u Y Z W a b hX hY hZ v hC hJ5) hJ5 hJ8)
  have h1 : v 1=0 := by
    simp only [row94,h2,mul_zero,zero_mul,add_zero,zero_add] at hJ5
    linear_combination (norm := (ring_nf; all_goals field_simp [hX]; all_goals ring))
      (-u/68:ℂ)*hJ5
  have hplus : (u:ℂ)+1≠0 := by exact_mod_cast (show u+1≠0 by linarith)
  have h0 : v 0=0 := by
    simp only [row0,h1,h2,mul_zero,zero_mul,add_zero,zero_add] at hL
    linear_combination (norm := (ring_nf; all_goals field_simp [hX,hY,hW,hplus]; all_goals ring))
      (-(u:ℂ)*W^2/(((u:ℂ)+1)*Y^2))*hL
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

#print axioms positive_kernel_zero

end SmallLevelThirtyFourFiniteJetMMP
end
end

/-! ## ThirtyFourUnitMMPFreeCoordinates -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMP
open Complex SmallLevelThirtyFourGrid
theorem free_coordinates_zero (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0)
    (h0 : v 370=0) (h1 : v 390=0) (h2 : v 435=0) :
    ∀ j : Fin 414,v (supportIndex j)=0 := by
  intro j
  fin_cases j
  · rw [show supportIndex ⟨0,by decide⟩=(0:Fin 510) from by decide +kernel]
    exact free_back_zero_0 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨1,by decide⟩=(1:Fin 510) from by decide +kernel]
    exact free_back_zero_1 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨2,by decide⟩=(2:Fin 510) from by decide +kernel]
    exact free_back_zero_2 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨3,by decide⟩=(3:Fin 510) from by decide +kernel]
    exact free_back_zero_3 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨4,by decide⟩=(4:Fin 510) from by decide +kernel]
    exact free_back_zero_4 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨5,by decide⟩=(5:Fin 510) from by decide +kernel]
    exact free_back_zero_5 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨6,by decide⟩=(6:Fin 510) from by decide +kernel]
    exact free_back_zero_6 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨7,by decide⟩=(7:Fin 510) from by decide +kernel]
    exact free_back_zero_7 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨8,by decide⟩=(8:Fin 510) from by decide +kernel]
    exact free_back_zero_8 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨9,by decide⟩=(9:Fin 510) from by decide +kernel]
    exact free_back_zero_9 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨10,by decide⟩=(10:Fin 510) from by decide +kernel]
    exact free_back_zero_10 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨11,by decide⟩=(11:Fin 510) from by decide +kernel]
    exact free_back_zero_11 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨12,by decide⟩=(12:Fin 510) from by decide +kernel]
    exact free_back_zero_12 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨13,by decide⟩=(13:Fin 510) from by decide +kernel]
    exact free_back_zero_13 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨14,by decide⟩=(14:Fin 510) from by decide +kernel]
    exact free_back_zero_14 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨15,by decide⟩=(15:Fin 510) from by decide +kernel]
    exact free_back_zero_15 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨16,by decide⟩=(16:Fin 510) from by decide +kernel]
    exact free_back_zero_16 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨17,by decide⟩=(17:Fin 510) from by decide +kernel]
    exact free_back_zero_17 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨18,by decide⟩=(18:Fin 510) from by decide +kernel]
    exact free_back_zero_18 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨19,by decide⟩=(19:Fin 510) from by decide +kernel]
    exact free_back_zero_19 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨20,by decide⟩=(20:Fin 510) from by decide +kernel]
    exact free_back_zero_20 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨21,by decide⟩=(21:Fin 510) from by decide +kernel]
    exact free_back_zero_21 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨22,by decide⟩=(22:Fin 510) from by decide +kernel]
    exact free_back_zero_22 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨23,by decide⟩=(24:Fin 510) from by decide +kernel]
    exact free_back_zero_24 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨24,by decide⟩=(25:Fin 510) from by decide +kernel]
    exact free_back_zero_25 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨25,by decide⟩=(26:Fin 510) from by decide +kernel]
    exact free_back_zero_26 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨26,by decide⟩=(27:Fin 510) from by decide +kernel]
    exact free_back_zero_27 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨27,by decide⟩=(28:Fin 510) from by decide +kernel]
    exact free_back_zero_28 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨28,by decide⟩=(29:Fin 510) from by decide +kernel]
    exact free_back_zero_29 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨29,by decide⟩=(30:Fin 510) from by decide +kernel]
    exact free_back_zero_30 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨30,by decide⟩=(31:Fin 510) from by decide +kernel]
    exact free_back_zero_31 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨31,by decide⟩=(32:Fin 510) from by decide +kernel]
    exact free_back_zero_32 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨32,by decide⟩=(33:Fin 510) from by decide +kernel]
    exact free_back_zero_33 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨33,by decide⟩=(34:Fin 510) from by decide +kernel]
    exact free_back_zero_34 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨34,by decide⟩=(35:Fin 510) from by decide +kernel]
    exact free_back_zero_35 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨35,by decide⟩=(36:Fin 510) from by decide +kernel]
    exact free_back_zero_36 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨36,by decide⟩=(37:Fin 510) from by decide +kernel]
    exact free_back_zero_37 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨37,by decide⟩=(39:Fin 510) from by decide +kernel]
    exact free_back_zero_39 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨38,by decide⟩=(40:Fin 510) from by decide +kernel]
    exact free_back_zero_40 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨39,by decide⟩=(41:Fin 510) from by decide +kernel]
    exact free_back_zero_41 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨40,by decide⟩=(42:Fin 510) from by decide +kernel]
    exact free_back_zero_42 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨41,by decide⟩=(43:Fin 510) from by decide +kernel]
    exact free_back_zero_43 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨42,by decide⟩=(44:Fin 510) from by decide +kernel]
    exact free_back_zero_44 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨43,by decide⟩=(45:Fin 510) from by decide +kernel]
    exact free_back_zero_45 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨44,by decide⟩=(48:Fin 510) from by decide +kernel]
    exact free_back_zero_48 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨45,by decide⟩=(50:Fin 510) from by decide +kernel]
    exact free_back_zero_50 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨46,by decide⟩=(51:Fin 510) from by decide +kernel]
    exact free_back_zero_51 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨47,by decide⟩=(54:Fin 510) from by decide +kernel]
    exact free_back_zero_54 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨48,by decide⟩=(55:Fin 510) from by decide +kernel]
    exact free_back_zero_55 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨49,by decide⟩=(57:Fin 510) from by decide +kernel]
    exact free_back_zero_57 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨50,by decide⟩=(60:Fin 510) from by decide +kernel]
    exact free_back_zero_60 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨51,by decide⟩=(62:Fin 510) from by decide +kernel]
    exact free_back_zero_62 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨52,by decide⟩=(63:Fin 510) from by decide +kernel]
    exact free_back_zero_63 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨53,by decide⟩=(65:Fin 510) from by decide +kernel]
    exact free_back_zero_65 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨54,by decide⟩=(66:Fin 510) from by decide +kernel]
    exact free_back_zero_66 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨55,by decide⟩=(68:Fin 510) from by decide +kernel]
    exact free_back_zero_68 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨56,by decide⟩=(69:Fin 510) from by decide +kernel]
    exact free_back_zero_69 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨57,by decide⟩=(70:Fin 510) from by decide +kernel]
    exact free_back_zero_70 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨58,by decide⟩=(71:Fin 510) from by decide +kernel]
    exact free_back_zero_71 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨59,by decide⟩=(72:Fin 510) from by decide +kernel]
    exact free_back_zero_72 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨60,by decide⟩=(74:Fin 510) from by decide +kernel]
    exact free_back_zero_74 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨61,by decide⟩=(75:Fin 510) from by decide +kernel]
    exact free_back_zero_75 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨62,by decide⟩=(76:Fin 510) from by decide +kernel]
    exact free_back_zero_76 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨63,by decide⟩=(77:Fin 510) from by decide +kernel]
    exact free_back_zero_77 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨64,by decide⟩=(78:Fin 510) from by decide +kernel]
    exact free_back_zero_78 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨65,by decide⟩=(79:Fin 510) from by decide +kernel]
    exact free_back_zero_79 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨66,by decide⟩=(80:Fin 510) from by decide +kernel]
    exact free_back_zero_80 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨67,by decide⟩=(81:Fin 510) from by decide +kernel]
    exact free_back_zero_81 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨68,by decide⟩=(82:Fin 510) from by decide +kernel]
    exact free_back_zero_82 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨69,by decide⟩=(83:Fin 510) from by decide +kernel]
    exact free_back_zero_83 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨70,by decide⟩=(84:Fin 510) from by decide +kernel]
    exact free_back_zero_84 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨71,by decide⟩=(85:Fin 510) from by decide +kernel]
    exact free_back_zero_85 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨72,by decide⟩=(86:Fin 510) from by decide +kernel]
    exact free_back_zero_86 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨73,by decide⟩=(87:Fin 510) from by decide +kernel]
    exact free_back_zero_87 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨74,by decide⟩=(88:Fin 510) from by decide +kernel]
    exact free_back_zero_88 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨75,by decide⟩=(89:Fin 510) from by decide +kernel]
    exact free_back_zero_89 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨76,by decide⟩=(90:Fin 510) from by decide +kernel]
    exact free_back_zero_90 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨77,by decide⟩=(91:Fin 510) from by decide +kernel]
    exact free_back_zero_91 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨78,by decide⟩=(92:Fin 510) from by decide +kernel]
    exact free_back_zero_92 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨79,by decide⟩=(93:Fin 510) from by decide +kernel]
    exact free_back_zero_93 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨80,by decide⟩=(94:Fin 510) from by decide +kernel]
    exact free_back_zero_94 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨81,by decide⟩=(95:Fin 510) from by decide +kernel]
    exact free_back_zero_95 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨82,by decide⟩=(96:Fin 510) from by decide +kernel]
    exact free_back_zero_96 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨83,by decide⟩=(98:Fin 510) from by decide +kernel]
    exact free_back_zero_98 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨84,by decide⟩=(99:Fin 510) from by decide +kernel]
    exact free_back_zero_99 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨85,by decide⟩=(100:Fin 510) from by decide +kernel]
    exact free_back_zero_100 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨86,by decide⟩=(101:Fin 510) from by decide +kernel]
    exact free_back_zero_101 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨87,by decide⟩=(102:Fin 510) from by decide +kernel]
    exact free_back_zero_102 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨88,by decide⟩=(105:Fin 510) from by decide +kernel]
    exact free_back_zero_105 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨89,by decide⟩=(107:Fin 510) from by decide +kernel]
    exact free_back_zero_107 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨90,by decide⟩=(108:Fin 510) from by decide +kernel]
    exact free_back_zero_108 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨91,by decide⟩=(110:Fin 510) from by decide +kernel]
    exact free_back_zero_110 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨92,by decide⟩=(111:Fin 510) from by decide +kernel]
    exact free_back_zero_111 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨93,by decide⟩=(114:Fin 510) from by decide +kernel]
    exact free_back_zero_114 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨94,by decide⟩=(115:Fin 510) from by decide +kernel]
    exact free_back_zero_115 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨95,by decide⟩=(116:Fin 510) from by decide +kernel]
    exact free_back_zero_116 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨96,by decide⟩=(117:Fin 510) from by decide +kernel]
    exact free_back_zero_117 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨97,by decide⟩=(119:Fin 510) from by decide +kernel]
    exact free_back_zero_119 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨98,by decide⟩=(120:Fin 510) from by decide +kernel]
    exact free_back_zero_120 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨99,by decide⟩=(122:Fin 510) from by decide +kernel]
    exact free_back_zero_122 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨100,by decide⟩=(123:Fin 510) from by decide +kernel]
    exact free_back_zero_123 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨101,by decide⟩=(125:Fin 510) from by decide +kernel]
    exact free_back_zero_125 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨102,by decide⟩=(126:Fin 510) from by decide +kernel]
    exact free_back_zero_126 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨103,by decide⟩=(127:Fin 510) from by decide +kernel]
    exact free_back_zero_127 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨104,by decide⟩=(128:Fin 510) from by decide +kernel]
    exact free_back_zero_128 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨105,by decide⟩=(129:Fin 510) from by decide +kernel]
    exact free_back_zero_129 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨106,by decide⟩=(130:Fin 510) from by decide +kernel]
    exact free_back_zero_130 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨107,by decide⟩=(132:Fin 510) from by decide +kernel]
    exact free_back_zero_132 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨108,by decide⟩=(133:Fin 510) from by decide +kernel]
    exact free_back_zero_133 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨109,by decide⟩=(135:Fin 510) from by decide +kernel]
    exact free_back_zero_135 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨110,by decide⟩=(136:Fin 510) from by decide +kernel]
    exact free_back_zero_136 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨111,by decide⟩=(138:Fin 510) from by decide +kernel]
    exact free_back_zero_138 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨112,by decide⟩=(139:Fin 510) from by decide +kernel]
    exact free_back_zero_139 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨113,by decide⟩=(140:Fin 510) from by decide +kernel]
    exact free_back_zero_140 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨114,by decide⟩=(141:Fin 510) from by decide +kernel]
    exact free_back_zero_141 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨115,by decide⟩=(142:Fin 510) from by decide +kernel]
    exact free_back_zero_142 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨116,by decide⟩=(144:Fin 510) from by decide +kernel]
    exact free_back_zero_144 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨117,by decide⟩=(145:Fin 510) from by decide +kernel]
    exact free_back_zero_145 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨118,by decide⟩=(147:Fin 510) from by decide +kernel]
    exact free_back_zero_147 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨119,by decide⟩=(148:Fin 510) from by decide +kernel]
    exact free_back_zero_148 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨120,by decide⟩=(150:Fin 510) from by decide +kernel]
    exact free_back_zero_150 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨121,by decide⟩=(151:Fin 510) from by decide +kernel]
    exact free_back_zero_151 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨122,by decide⟩=(153:Fin 510) from by decide +kernel]
    exact free_back_zero_153 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨123,by decide⟩=(154:Fin 510) from by decide +kernel]
    exact free_back_zero_154 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨124,by decide⟩=(155:Fin 510) from by decide +kernel]
    exact free_back_zero_155 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨125,by decide⟩=(156:Fin 510) from by decide +kernel]
    exact free_back_zero_156 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨126,by decide⟩=(157:Fin 510) from by decide +kernel]
    exact free_back_zero_157 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨127,by decide⟩=(158:Fin 510) from by decide +kernel]
    exact free_back_zero_158 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨128,by decide⟩=(159:Fin 510) from by decide +kernel]
    exact free_back_zero_159 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨129,by decide⟩=(160:Fin 510) from by decide +kernel]
    exact free_back_zero_160 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨130,by decide⟩=(162:Fin 510) from by decide +kernel]
    exact free_back_zero_162 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨131,by decide⟩=(163:Fin 510) from by decide +kernel]
    exact free_back_zero_163 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨132,by decide⟩=(164:Fin 510) from by decide +kernel]
    exact free_back_zero_164 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨133,by decide⟩=(165:Fin 510) from by decide +kernel]
    exact free_back_zero_165 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨134,by decide⟩=(166:Fin 510) from by decide +kernel]
    exact free_back_zero_166 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨135,by decide⟩=(167:Fin 510) from by decide +kernel]
    exact free_back_zero_167 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨136,by decide⟩=(168:Fin 510) from by decide +kernel]
    exact free_back_zero_168 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨137,by decide⟩=(169:Fin 510) from by decide +kernel]
    exact free_back_zero_169 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨138,by decide⟩=(170:Fin 510) from by decide +kernel]
    exact free_back_zero_170 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨139,by decide⟩=(171:Fin 510) from by decide +kernel]
    exact free_back_zero_171 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨140,by decide⟩=(172:Fin 510) from by decide +kernel]
    exact free_back_zero_172 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨141,by decide⟩=(173:Fin 510) from by decide +kernel]
    exact free_back_zero_173 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨142,by decide⟩=(174:Fin 510) from by decide +kernel]
    exact free_back_zero_174 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨143,by decide⟩=(175:Fin 510) from by decide +kernel]
    exact free_back_zero_175 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨144,by decide⟩=(176:Fin 510) from by decide +kernel]
    exact free_back_zero_176 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨145,by decide⟩=(177:Fin 510) from by decide +kernel]
    exact free_back_zero_177 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨146,by decide⟩=(178:Fin 510) from by decide +kernel]
    exact free_back_zero_178 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨147,by decide⟩=(180:Fin 510) from by decide +kernel]
    exact free_back_zero_180 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨148,by decide⟩=(181:Fin 510) from by decide +kernel]
    exact free_back_zero_181 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨149,by decide⟩=(182:Fin 510) from by decide +kernel]
    exact free_back_zero_182 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨150,by decide⟩=(183:Fin 510) from by decide +kernel]
    exact free_back_zero_183 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨151,by decide⟩=(184:Fin 510) from by decide +kernel]
    exact free_back_zero_184 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨152,by decide⟩=(185:Fin 510) from by decide +kernel]
    exact free_back_zero_185 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨153,by decide⟩=(186:Fin 510) from by decide +kernel]
    exact free_back_zero_186 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨154,by decide⟩=(187:Fin 510) from by decide +kernel]
    exact free_back_zero_187 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨155,by decide⟩=(189:Fin 510) from by decide +kernel]
    exact free_back_zero_189 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨156,by decide⟩=(190:Fin 510) from by decide +kernel]
    exact free_back_zero_190 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨157,by decide⟩=(192:Fin 510) from by decide +kernel]
    exact free_back_zero_192 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨158,by decide⟩=(195:Fin 510) from by decide +kernel]
    exact free_back_zero_195 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨159,by decide⟩=(196:Fin 510) from by decide +kernel]
    exact free_back_zero_196 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨160,by decide⟩=(198:Fin 510) from by decide +kernel]
    exact free_back_zero_198 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨161,by decide⟩=(199:Fin 510) from by decide +kernel]
    exact free_back_zero_199 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨162,by decide⟩=(200:Fin 510) from by decide +kernel]
    exact free_back_zero_200 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨163,by decide⟩=(201:Fin 510) from by decide +kernel]
    exact free_back_zero_201 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨164,by decide⟩=(202:Fin 510) from by decide +kernel]
    exact free_back_zero_202 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨165,by decide⟩=(204:Fin 510) from by decide +kernel]
    exact free_back_zero_204 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨166,by decide⟩=(205:Fin 510) from by decide +kernel]
    exact free_back_zero_205 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨167,by decide⟩=(207:Fin 510) from by decide +kernel]
    exact free_back_zero_207 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨168,by decide⟩=(210:Fin 510) from by decide +kernel]
    exact free_back_zero_210 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨169,by decide⟩=(211:Fin 510) from by decide +kernel]
    exact free_back_zero_211 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨170,by decide⟩=(212:Fin 510) from by decide +kernel]
    exact free_back_zero_212 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨171,by decide⟩=(213:Fin 510) from by decide +kernel]
    exact free_back_zero_213 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨172,by decide⟩=(214:Fin 510) from by decide +kernel]
    exact free_back_zero_214 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨173,by decide⟩=(215:Fin 510) from by decide +kernel]
    exact free_back_zero_215 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨174,by decide⟩=(216:Fin 510) from by decide +kernel]
    exact free_back_zero_216 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨175,by decide⟩=(218:Fin 510) from by decide +kernel]
    exact free_back_zero_218 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨176,by decide⟩=(219:Fin 510) from by decide +kernel]
    exact free_back_zero_219 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨177,by decide⟩=(220:Fin 510) from by decide +kernel]
    exact free_back_zero_220 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨178,by decide⟩=(221:Fin 510) from by decide +kernel]
    exact free_back_zero_221 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨179,by decide⟩=(222:Fin 510) from by decide +kernel]
    exact free_back_zero_222 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨180,by decide⟩=(224:Fin 510) from by decide +kernel]
    exact free_back_zero_224 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨181,by decide⟩=(225:Fin 510) from by decide +kernel]
    exact free_back_zero_225 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨182,by decide⟩=(228:Fin 510) from by decide +kernel]
    exact free_back_zero_228 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨183,by decide⟩=(230:Fin 510) from by decide +kernel]
    exact free_back_zero_230 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨184,by decide⟩=(231:Fin 510) from by decide +kernel]
    exact free_back_zero_231 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨185,by decide⟩=(232:Fin 510) from by decide +kernel]
    exact free_back_zero_232 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨186,by decide⟩=(233:Fin 510) from by decide +kernel]
    exact free_back_zero_233 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨187,by decide⟩=(234:Fin 510) from by decide +kernel]
    exact free_back_zero_234 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨188,by decide⟩=(235:Fin 510) from by decide +kernel]
    exact free_back_zero_235 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨189,by decide⟩=(237:Fin 510) from by decide +kernel]
    exact free_back_zero_237 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨190,by decide⟩=(238:Fin 510) from by decide +kernel]
    exact free_back_zero_238 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨191,by decide⟩=(239:Fin 510) from by decide +kernel]
    exact free_back_zero_239 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨192,by decide⟩=(240:Fin 510) from by decide +kernel]
    exact free_back_zero_240 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨193,by decide⟩=(241:Fin 510) from by decide +kernel]
    exact free_back_zero_241 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨194,by decide⟩=(242:Fin 510) from by decide +kernel]
    exact free_back_zero_242 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨195,by decide⟩=(243:Fin 510) from by decide +kernel]
    exact free_back_zero_243 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨196,by decide⟩=(244:Fin 510) from by decide +kernel]
    exact free_back_zero_244 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨197,by decide⟩=(245:Fin 510) from by decide +kernel]
    exact free_back_zero_245 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨198,by decide⟩=(246:Fin 510) from by decide +kernel]
    exact free_back_zero_246 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨199,by decide⟩=(247:Fin 510) from by decide +kernel]
    exact free_back_zero_247 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨200,by decide⟩=(248:Fin 510) from by decide +kernel]
    exact free_back_zero_248 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨201,by decide⟩=(249:Fin 510) from by decide +kernel]
    exact free_back_zero_249 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨202,by decide⟩=(250:Fin 510) from by decide +kernel]
    exact free_back_zero_250 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨203,by decide⟩=(251:Fin 510) from by decide +kernel]
    exact free_back_zero_251 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨204,by decide⟩=(252:Fin 510) from by decide +kernel]
    exact free_back_zero_252 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨205,by decide⟩=(253:Fin 510) from by decide +kernel]
    exact free_back_zero_253 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨206,by decide⟩=(254:Fin 510) from by decide +kernel]
    exact free_back_zero_254 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨207,by decide⟩=(255:Fin 510) from by decide +kernel]
    exact free_back_zero_255 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨208,by decide⟩=(256:Fin 510) from by decide +kernel]
    exact free_back_zero_256 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨209,by decide⟩=(257:Fin 510) from by decide +kernel]
    exact free_back_zero_257 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨210,by decide⟩=(258:Fin 510) from by decide +kernel]
    exact free_back_zero_258 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨211,by decide⟩=(259:Fin 510) from by decide +kernel]
    exact free_back_zero_259 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨212,by decide⟩=(260:Fin 510) from by decide +kernel]
    exact free_back_zero_260 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨213,by decide⟩=(261:Fin 510) from by decide +kernel]
    exact free_back_zero_261 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨214,by decide⟩=(262:Fin 510) from by decide +kernel]
    exact free_back_zero_262 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨215,by decide⟩=(263:Fin 510) from by decide +kernel]
    exact free_back_zero_263 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨216,by decide⟩=(264:Fin 510) from by decide +kernel]
    exact free_back_zero_264 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨217,by decide⟩=(265:Fin 510) from by decide +kernel]
    exact free_back_zero_265 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨218,by decide⟩=(266:Fin 510) from by decide +kernel]
    exact free_back_zero_266 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨219,by decide⟩=(267:Fin 510) from by decide +kernel]
    exact free_back_zero_267 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨220,by decide⟩=(268:Fin 510) from by decide +kernel]
    exact free_back_zero_268 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨221,by decide⟩=(269:Fin 510) from by decide +kernel]
    exact free_back_zero_269 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨222,by decide⟩=(270:Fin 510) from by decide +kernel]
    exact free_back_zero_270 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨223,by decide⟩=(271:Fin 510) from by decide +kernel]
    exact free_back_zero_271 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨224,by decide⟩=(272:Fin 510) from by decide +kernel]
    exact free_back_zero_272 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨225,by decide⟩=(273:Fin 510) from by decide +kernel]
    exact free_back_zero_273 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨226,by decide⟩=(275:Fin 510) from by decide +kernel]
    exact free_back_zero_275 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨227,by decide⟩=(276:Fin 510) from by decide +kernel]
    exact free_back_zero_276 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨228,by decide⟩=(277:Fin 510) from by decide +kernel]
    exact free_back_zero_277 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨229,by decide⟩=(278:Fin 510) from by decide +kernel]
    exact free_back_zero_278 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨230,by decide⟩=(279:Fin 510) from by decide +kernel]
    exact free_back_zero_279 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨231,by decide⟩=(280:Fin 510) from by decide +kernel]
    exact free_back_zero_280 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨232,by decide⟩=(282:Fin 510) from by decide +kernel]
    exact free_back_zero_282 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨233,by decide⟩=(285:Fin 510) from by decide +kernel]
    exact free_back_zero_285 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨234,by decide⟩=(286:Fin 510) from by decide +kernel]
    exact free_back_zero_286 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨235,by decide⟩=(288:Fin 510) from by decide +kernel]
    exact free_back_zero_288 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨236,by decide⟩=(289:Fin 510) from by decide +kernel]
    exact free_back_zero_289 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨237,by decide⟩=(290:Fin 510) from by decide +kernel]
    exact free_back_zero_290 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨238,by decide⟩=(291:Fin 510) from by decide +kernel]
    exact free_back_zero_291 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨239,by decide⟩=(292:Fin 510) from by decide +kernel]
    exact free_back_zero_292 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨240,by decide⟩=(294:Fin 510) from by decide +kernel]
    exact free_back_zero_294 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨241,by decide⟩=(295:Fin 510) from by decide +kernel]
    exact free_back_zero_295 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨242,by decide⟩=(296:Fin 510) from by decide +kernel]
    exact free_back_zero_296 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨243,by decide⟩=(297:Fin 510) from by decide +kernel]
    exact free_back_zero_297 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨244,by decide⟩=(298:Fin 510) from by decide +kernel]
    exact free_back_zero_298 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨245,by decide⟩=(299:Fin 510) from by decide +kernel]
    exact free_back_zero_299 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨246,by decide⟩=(300:Fin 510) from by decide +kernel]
    exact free_back_zero_300 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨247,by decide⟩=(303:Fin 510) from by decide +kernel]
    exact free_back_zero_303 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨248,by decide⟩=(305:Fin 510) from by decide +kernel]
    exact free_back_zero_305 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨249,by decide⟩=(306:Fin 510) from by decide +kernel]
    exact free_back_zero_306 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨250,by decide⟩=(308:Fin 510) from by decide +kernel]
    exact free_back_zero_308 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨251,by decide⟩=(309:Fin 510) from by decide +kernel]
    exact free_back_zero_309 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨252,by decide⟩=(310:Fin 510) from by decide +kernel]
    exact free_back_zero_310 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨253,by decide⟩=(311:Fin 510) from by decide +kernel]
    exact free_back_zero_311 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨254,by decide⟩=(312:Fin 510) from by decide +kernel]
    exact free_back_zero_312 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨255,by decide⟩=(314:Fin 510) from by decide +kernel]
    exact free_back_zero_314 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨256,by decide⟩=(315:Fin 510) from by decide +kernel]
    exact free_back_zero_315 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨257,by decide⟩=(318:Fin 510) from by decide +kernel]
    exact free_back_zero_318 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨258,by decide⟩=(320:Fin 510) from by decide +kernel]
    exact free_back_zero_320 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨259,by decide⟩=(321:Fin 510) from by decide +kernel]
    exact free_back_zero_321 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨260,by decide⟩=(323:Fin 510) from by decide +kernel]
    exact free_back_zero_323 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨261,by decide⟩=(324:Fin 510) from by decide +kernel]
    exact free_back_zero_324 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨262,by decide⟩=(325:Fin 510) from by decide +kernel]
    exact free_back_zero_325 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨263,by decide⟩=(326:Fin 510) from by decide +kernel]
    exact free_back_zero_326 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨264,by decide⟩=(327:Fin 510) from by decide +kernel]
    exact free_back_zero_327 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨265,by decide⟩=(328:Fin 510) from by decide +kernel]
    exact free_back_zero_328 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨266,by decide⟩=(329:Fin 510) from by decide +kernel]
    exact free_back_zero_329 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨267,by decide⟩=(330:Fin 510) from by decide +kernel]
    exact free_back_zero_330 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨268,by decide⟩=(332:Fin 510) from by decide +kernel]
    exact free_back_zero_332 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨269,by decide⟩=(333:Fin 510) from by decide +kernel]
    exact free_back_zero_333 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨270,by decide⟩=(334:Fin 510) from by decide +kernel]
    exact free_back_zero_334 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨271,by decide⟩=(335:Fin 510) from by decide +kernel]
    exact free_back_zero_335 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨272,by decide⟩=(336:Fin 510) from by decide +kernel]
    exact free_back_zero_336 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨273,by decide⟩=(337:Fin 510) from by decide +kernel]
    exact free_back_zero_337 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨274,by decide⟩=(338:Fin 510) from by decide +kernel]
    exact free_back_zero_338 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨275,by decide⟩=(339:Fin 510) from by decide +kernel]
    exact free_back_zero_339 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨276,by decide⟩=(340:Fin 510) from by decide +kernel]
    exact free_back_zero_340 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨277,by decide⟩=(341:Fin 510) from by decide +kernel]
    exact free_back_zero_341 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨278,by decide⟩=(342:Fin 510) from by decide +kernel]
    exact free_back_zero_342 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨279,by decide⟩=(343:Fin 510) from by decide +kernel]
    exact free_back_zero_343 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨280,by decide⟩=(344:Fin 510) from by decide +kernel]
    exact free_back_zero_344 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨281,by decide⟩=(345:Fin 510) from by decide +kernel]
    exact free_back_zero_345 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨282,by decide⟩=(346:Fin 510) from by decide +kernel]
    exact free_back_zero_346 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨283,by decide⟩=(347:Fin 510) from by decide +kernel]
    exact free_back_zero_347 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨284,by decide⟩=(348:Fin 510) from by decide +kernel]
    exact free_back_zero_348 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨285,by decide⟩=(350:Fin 510) from by decide +kernel]
    exact free_back_zero_350 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨286,by decide⟩=(351:Fin 510) from by decide +kernel]
    exact free_back_zero_351 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨287,by decide⟩=(352:Fin 510) from by decide +kernel]
    exact free_back_zero_352 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨288,by decide⟩=(353:Fin 510) from by decide +kernel]
    exact free_back_zero_353 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨289,by decide⟩=(354:Fin 510) from by decide +kernel]
    exact free_back_zero_354 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨290,by decide⟩=(355:Fin 510) from by decide +kernel]
    exact free_back_zero_355 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨291,by decide⟩=(356:Fin 510) from by decide +kernel]
    exact free_back_zero_356 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨292,by decide⟩=(357:Fin 510) from by decide +kernel]
    exact free_back_zero_357 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨293,by decide⟩=(359:Fin 510) from by decide +kernel]
    exact free_back_zero_359 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨294,by decide⟩=(360:Fin 510) from by decide +kernel]
    exact free_back_zero_360 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨295,by decide⟩=(362:Fin 510) from by decide +kernel]
    exact free_back_zero_362 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨296,by decide⟩=(363:Fin 510) from by decide +kernel]
    exact free_back_zero_363 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨297,by decide⟩=(365:Fin 510) from by decide +kernel]
    exact free_back_zero_365 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨298,by decide⟩=(366:Fin 510) from by decide +kernel]
    exact free_back_zero_366 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨299,by decide⟩=(368:Fin 510) from by decide +kernel]
    exact free_back_zero_368 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨300,by decide⟩=(369:Fin 510) from by decide +kernel]
    exact free_back_zero_369 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨301,by decide⟩=(370:Fin 510) from by decide +kernel]
    exact h0
  · rw [show supportIndex ⟨302,by decide⟩=(371:Fin 510) from by decide +kernel]
    exact free_back_zero_371 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨303,by decide⟩=(372:Fin 510) from by decide +kernel]
    exact free_back_zero_372 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨304,by decide⟩=(374:Fin 510) from by decide +kernel]
    exact free_back_zero_374 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨305,by decide⟩=(375:Fin 510) from by decide +kernel]
    exact free_back_zero_375 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨306,by decide⟩=(377:Fin 510) from by decide +kernel]
    exact free_back_zero_377 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨307,by decide⟩=(378:Fin 510) from by decide +kernel]
    exact free_back_zero_378 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨308,by decide⟩=(380:Fin 510) from by decide +kernel]
    exact free_back_zero_380 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨309,by decide⟩=(381:Fin 510) from by decide +kernel]
    exact free_back_zero_381 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨310,by decide⟩=(382:Fin 510) from by decide +kernel]
    exact free_back_zero_382 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨311,by decide⟩=(383:Fin 510) from by decide +kernel]
    exact free_back_zero_383 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨312,by decide⟩=(384:Fin 510) from by decide +kernel]
    exact free_back_zero_384 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨313,by decide⟩=(385:Fin 510) from by decide +kernel]
    exact free_back_zero_385 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨314,by decide⟩=(387:Fin 510) from by decide +kernel]
    exact free_back_zero_387 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨315,by decide⟩=(388:Fin 510) from by decide +kernel]
    exact free_back_zero_388 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨316,by decide⟩=(390:Fin 510) from by decide +kernel]
    exact h1
  · rw [show supportIndex ⟨317,by decide⟩=(391:Fin 510) from by decide +kernel]
    exact free_back_zero_391 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨318,by decide⟩=(393:Fin 510) from by decide +kernel]
    exact free_back_zero_393 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨319,by decide⟩=(394:Fin 510) from by decide +kernel]
    exact free_back_zero_394 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨320,by decide⟩=(395:Fin 510) from by decide +kernel]
    exact free_back_zero_395 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨321,by decide⟩=(396:Fin 510) from by decide +kernel]
    exact free_back_zero_396 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨322,by decide⟩=(399:Fin 510) from by decide +kernel]
    exact free_back_zero_399 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨323,by decide⟩=(400:Fin 510) from by decide +kernel]
    exact free_back_zero_400 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨324,by decide⟩=(402:Fin 510) from by decide +kernel]
    exact free_back_zero_402 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨325,by decide⟩=(403:Fin 510) from by decide +kernel]
    exact free_back_zero_403 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨326,by decide⟩=(405:Fin 510) from by decide +kernel]
    exact free_back_zero_405 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨327,by decide⟩=(408:Fin 510) from by decide +kernel]
    exact free_back_zero_408 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨328,by decide⟩=(409:Fin 510) from by decide +kernel]
    exact free_back_zero_409 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨329,by decide⟩=(410:Fin 510) from by decide +kernel]
    exact free_back_zero_410 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨330,by decide⟩=(411:Fin 510) from by decide +kernel]
    exact free_back_zero_411 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨331,by decide⟩=(412:Fin 510) from by decide +kernel]
    exact free_back_zero_412 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨332,by decide⟩=(414:Fin 510) from by decide +kernel]
    exact free_back_zero_414 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨333,by decide⟩=(415:Fin 510) from by decide +kernel]
    exact free_back_zero_415 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨334,by decide⟩=(416:Fin 510) from by decide +kernel]
    exact free_back_zero_416 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨335,by decide⟩=(417:Fin 510) from by decide +kernel]
    exact free_back_zero_417 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨336,by decide⟩=(418:Fin 510) from by decide +kernel]
    exact free_back_zero_418 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨337,by decide⟩=(419:Fin 510) from by decide +kernel]
    exact free_back_zero_419 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨338,by decide⟩=(420:Fin 510) from by decide +kernel]
    exact free_back_zero_420 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨339,by decide⟩=(421:Fin 510) from by decide +kernel]
    exact free_back_zero_421 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨340,by decide⟩=(422:Fin 510) from by decide +kernel]
    exact free_back_zero_422 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨341,by decide⟩=(423:Fin 510) from by decide +kernel]
    exact free_back_zero_423 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨342,by decide⟩=(424:Fin 510) from by decide +kernel]
    exact free_back_zero_424 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨343,by decide⟩=(425:Fin 510) from by decide +kernel]
    exact free_back_zero_425 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨344,by decide⟩=(426:Fin 510) from by decide +kernel]
    exact free_back_zero_426 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨345,by decide⟩=(427:Fin 510) from by decide +kernel]
    exact free_back_zero_427 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨346,by decide⟩=(428:Fin 510) from by decide +kernel]
    exact free_back_zero_428 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨347,by decide⟩=(429:Fin 510) from by decide +kernel]
    exact free_back_zero_429 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨348,by decide⟩=(430:Fin 510) from by decide +kernel]
    exact free_back_zero_430 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨349,by decide⟩=(431:Fin 510) from by decide +kernel]
    exact free_back_zero_431 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨350,by decide⟩=(432:Fin 510) from by decide +kernel]
    exact free_back_zero_432 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨351,by decide⟩=(433:Fin 510) from by decide +kernel]
    exact free_back_zero_433 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨352,by decide⟩=(434:Fin 510) from by decide +kernel]
    exact free_back_zero_434 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨353,by decide⟩=(435:Fin 510) from by decide +kernel]
    exact h2
  · rw [show supportIndex ⟨354,by decide⟩=(436:Fin 510) from by decide +kernel]
    exact free_back_zero_436 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨355,by decide⟩=(438:Fin 510) from by decide +kernel]
    exact free_back_zero_438 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨356,by decide⟩=(439:Fin 510) from by decide +kernel]
    exact free_back_zero_439 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨357,by decide⟩=(440:Fin 510) from by decide +kernel]
    exact free_back_zero_440 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨358,by decide⟩=(441:Fin 510) from by decide +kernel]
    exact free_back_zero_441 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨359,by decide⟩=(442:Fin 510) from by decide +kernel]
    exact free_back_zero_442 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨360,by decide⟩=(444:Fin 510) from by decide +kernel]
    exact free_back_zero_444 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨361,by decide⟩=(445:Fin 510) from by decide +kernel]
    exact free_back_zero_445 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨362,by decide⟩=(447:Fin 510) from by decide +kernel]
    exact free_back_zero_447 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨363,by decide⟩=(448:Fin 510) from by decide +kernel]
    exact free_back_zero_448 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨364,by decide⟩=(450:Fin 510) from by decide +kernel]
    exact free_back_zero_450 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨365,by decide⟩=(453:Fin 510) from by decide +kernel]
    exact free_back_zero_453 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨366,by decide⟩=(455:Fin 510) from by decide +kernel]
    exact free_back_zero_455 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨367,by decide⟩=(456:Fin 510) from by decide +kernel]
    exact free_back_zero_456 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨368,by decide⟩=(459:Fin 510) from by decide +kernel]
    exact free_back_zero_459 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨369,by decide⟩=(460:Fin 510) from by decide +kernel]
    exact free_back_zero_460 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨370,by decide⟩=(462:Fin 510) from by decide +kernel]
    exact free_back_zero_462 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨371,by decide⟩=(465:Fin 510) from by decide +kernel]
    exact free_back_zero_465 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨372,by decide⟩=(466:Fin 510) from by decide +kernel]
    exact free_back_zero_466 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨373,by decide⟩=(467:Fin 510) from by decide +kernel]
    exact free_back_zero_467 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨374,by decide⟩=(468:Fin 510) from by decide +kernel]
    exact free_back_zero_468 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨375,by decide⟩=(469:Fin 510) from by decide +kernel]
    exact free_back_zero_469 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨376,by decide⟩=(470:Fin 510) from by decide +kernel]
    exact free_back_zero_470 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨377,by decide⟩=(471:Fin 510) from by decide +kernel]
    exact free_back_zero_471 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨378,by decide⟩=(473:Fin 510) from by decide +kernel]
    exact free_back_zero_473 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨379,by decide⟩=(474:Fin 510) from by decide +kernel]
    exact free_back_zero_474 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨380,by decide⟩=(475:Fin 510) from by decide +kernel]
    exact free_back_zero_475 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨381,by decide⟩=(476:Fin 510) from by decide +kernel]
    exact free_back_zero_476 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨382,by decide⟩=(477:Fin 510) from by decide +kernel]
    exact free_back_zero_477 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨383,by decide⟩=(478:Fin 510) from by decide +kernel]
    exact free_back_zero_478 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨384,by decide⟩=(479:Fin 510) from by decide +kernel]
    exact free_back_zero_479 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨385,by decide⟩=(480:Fin 510) from by decide +kernel]
    exact free_back_zero_480 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨386,by decide⟩=(481:Fin 510) from by decide +kernel]
    exact free_back_zero_481 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨387,by decide⟩=(482:Fin 510) from by decide +kernel]
    exact free_back_zero_482 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨388,by decide⟩=(483:Fin 510) from by decide +kernel]
    exact free_back_zero_483 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨389,by decide⟩=(484:Fin 510) from by decide +kernel]
    exact free_back_zero_484 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨390,by decide⟩=(485:Fin 510) from by decide +kernel]
    exact free_back_zero_485 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨391,by decide⟩=(486:Fin 510) from by decide +kernel]
    exact free_back_zero_486 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨392,by decide⟩=(488:Fin 510) from by decide +kernel]
    exact free_back_zero_488 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨393,by decide⟩=(489:Fin 510) from by decide +kernel]
    exact free_back_zero_489 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨394,by decide⟩=(490:Fin 510) from by decide +kernel]
    exact free_back_zero_490 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨395,by decide⟩=(491:Fin 510) from by decide +kernel]
    exact free_back_zero_491 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨396,by decide⟩=(492:Fin 510) from by decide +kernel]
    exact free_back_zero_492 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨397,by decide⟩=(493:Fin 510) from by decide +kernel]
    exact free_back_zero_493 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨398,by decide⟩=(494:Fin 510) from by decide +kernel]
    exact free_back_zero_494 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨399,by decide⟩=(495:Fin 510) from by decide +kernel]
    exact free_back_zero_495 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨400,by decide⟩=(496:Fin 510) from by decide +kernel]
    exact free_back_zero_496 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨401,by decide⟩=(497:Fin 510) from by decide +kernel]
    exact free_back_zero_497 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨402,by decide⟩=(498:Fin 510) from by decide +kernel]
    exact free_back_zero_498 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨403,by decide⟩=(499:Fin 510) from by decide +kernel]
    exact free_back_zero_499 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨404,by decide⟩=(500:Fin 510) from by decide +kernel]
    exact free_back_zero_500 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨405,by decide⟩=(501:Fin 510) from by decide +kernel]
    exact free_back_zero_501 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨406,by decide⟩=(502:Fin 510) from by decide +kernel]
    exact free_back_zero_502 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨407,by decide⟩=(503:Fin 510) from by decide +kernel]
    exact free_back_zero_503 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨408,by decide⟩=(504:Fin 510) from by decide +kernel]
    exact free_back_zero_504 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨409,by decide⟩=(505:Fin 510) from by decide +kernel]
    exact free_back_zero_505 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨410,by decide⟩=(506:Fin 510) from by decide +kernel]
    exact free_back_zero_506 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨411,by decide⟩=(507:Fin 510) from by decide +kernel]
    exact free_back_zero_507 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨412,by decide⟩=(508:Fin 510) from by decide +kernel]
    exact free_back_zero_508 X Y Z W a b hX hY hZ hW v hv h0 h1 h2
  · rw [show supportIndex ⟨413,by decide⟩=(509:Fin 510) from by decide +kernel]
    exact free_back_zero_509 X Y Z W a b hX hY hZ hW v hv h0 h1 h2

#print axioms free_coordinates_zero

end SmallLevelThirtyFourUnitMMP
end
end

/-! ## ThirtyFourUnitMMPQuadraticCoordinates -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourUnitMMP
open Complex
theorem quadratic_coordinate_binding (X Y Z W a b : ℂ) (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (v : Fin 510→ℂ) (hv : ∀ i,sourceRows X Y Z W a b v i=0) :
    v 170-v 340=SmallLevelThirtyFourFiniteJetMMP.quadratic X Y Z W a b ![v 370,v 390,v 435] := by
  rw [coordinate_expansion_170 X Y Z W a b hX hY hZ hW v hv,
    coordinate_expansion_340 X Y Z W a b hX hY hZ hW v hv]
  simp only [SmallLevelThirtyFourFiniteJetMMP.quadratic,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  field_simp [hX,hY,hZ,hW]
  <;> ring

#print axioms quadratic_coordinate_binding

end SmallLevelThirtyFourUnitMMP
end
end

/-! ## ThirtyFourPhysicalFiniteMMPKernels -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourPhysicalFiniteMMP
open Complex Matrix SmallLevelThirtyFourGrid SmallLevelPrimeRates SmallLevelFiniteGridSupport
open SmallLevelThirtyFourUnitMMP SmallLevelThirtyFourUnitMMPInhomogeneous
theorem support_vector_zero (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (w : Fin 414→ℂ)
    (hs : ∀ i,sourceRows X Y Z W a b (extension supportIndex w) i=0)
    (hfree : ![(extension supportIndex w) 370,(extension supportIndex w) 390,
      (extension supportIndex w) 435]=(0:Fin 3→ℂ)) : w=0 := by
  have h0 : (extension supportIndex w) 370=0 := congrFun hfree 0
  have h1 : (extension supportIndex w) 390=0 := congrFun hfree 1
  have h2 : (extension supportIndex w) 435=0 := congrFun hfree 2
  funext j
  have hj:=free_coordinates_zero X Y Z W a b hX hY hZ hW (extension supportIndex w) hs h0 h1 h2 j
  change extend supportIndex w (supportIndex j)=0 at hj
  simpa only [extend_at supportIndex support_injective,Pi.zero_apply] using hj

theorem extended_quadratic (w : Fin 414→ℂ) :
    (extension supportIndex w) 170-(extension supportIndex w) 340=w 138-w 276 := by
  change extend supportIndex w 170-extend supportIndex w 340=_
  rw [←quadratic_coordinates.1,←quadratic_coordinates.2]
  rw [extend_at supportIndex support_injective,extend_at supportIndex support_injective]

#print axioms support_vector_zero

theorem critical_matrix_kernel_zero (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0)
    (hjet : firstJetMatrix m f ε u v x *ᵥ w=0) (hx : u*parameter 2 m x=1) : w=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) x)
  have hW:=parameter_ne_zero 5 m (by decide) x
  have hfree : ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435]=0 := by
    apply SmallLevelThirtyFourFiniteJetMMP.critical_kernel_zero (parameter 3 m x) (v*parameter 17 m x)
      (parameter 5 m x) (badParameter f 3) (badParameter f 5) hY hW
    · simpa only [hx] using finite_leading_rows m f ε u v x hu hv hη h₂ h₁₇ w hlead
    · simpa only [hx] using finite_jet_row_0 m f ε u v x hu hv hη h₂ h₁₇ w hlead hjet
    · simpa only [hx] using finite_jet_row_8 m f ε u v x hu hv hη h₂ h₁₇ w hlead hjet
  exact support_vector_zero (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW w (source_kernel m f ε u v x hu hv hη h₂ h₁₇ w hlead) hfree

#print axioms critical_matrix_kernel_zero

theorem positive_matrix_kernel_zero (m : ℕ) (f : ℕ→ℂ) (ε u v x : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= v) (w : Fin 414→ℂ)
    (hlead : SmallLevelThirtyFourUnitMMM.leadingMatrix m f ε x *ᵥ w=0)
    (hjet : firstJetMatrix m f ε u v x *ᵥ w=0) (t : ℝ) (ht : 2≤t)
    (hx : u*parameter 2 m x=(t:ℂ))
    (hnorm : 9*t/2≤‖parameter 3 m x^2‖) (hC : w 138-w 276=0) : w=0 := by
  have hu0 : u≠0 := by rcases hu with rfl|rfl <;> norm_num
  have hv0 : v≠0 := by rcases hv with rfl|rfl <;> norm_num
  have hX:=mul_ne_zero hu0 (parameter_ne_zero 2 m (by decide) x)
  have hY:=parameter_ne_zero 3 m (by decide) x
  have hZ:=mul_ne_zero hv0 (parameter_ne_zero 17 m (by decide) x)
  have hW:=parameter_ne_zero 5 m (by decide) x
  have hs:=source_kernel m f ε u v x hu hv hη h₂ h₁₇ w hlead
  have hquad : SmallLevelThirtyFourFiniteJetMMP.quadratic (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435]=0 := by
    rw [←quadratic_coordinate_binding (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW (extension supportIndex w) hs,
      extended_quadratic,hC]
  have hfree : ![(extension supportIndex w) 370,(extension supportIndex w) 390,(extension supportIndex w) 435]=0 := by
    apply SmallLevelThirtyFourFiniteJetMMP.positive_kernel_zero t ht (parameter 3 m x) (v*parameter 17 m x)
      (parameter 5 m x) (badParameter f 3) (badParameter f 5) hY hZ hW hnorm
    · simpa only [hx] using
        (SmallLevelThirtyFourFiniteJetMMP.leading_binding_0
          (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x)
          (parameter 5 m x) (badParameter f 3) (badParameter f 5)
          hX hY hZ hW (extension supportIndex w) hs)
    · simpa only [hx] using hquad
    · simpa only [hx] using finite_jet_row_5 m f ε u v x hu hv hη h₂ h₁₇ w hlead hjet
    · simpa only [hx] using finite_jet_row_8 m f ε u v x hu hv hη h₂ h₁₇ w hlead hjet
  exact support_vector_zero (u*parameter 2 m x) (parameter 3 m x) (v*parameter 17 m x) (parameter 5 m x) (badParameter f 3) (badParameter f 5) hX hY hZ hW w hs hfree

#print axioms positive_matrix_kernel_zero

end SmallLevelThirtyFourPhysicalFiniteMMP
end
end

/-! ## ThirtyFourQuadraticPoleMMP -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourQuadraticPoleMMP
open Complex Matrix SmallLevelThirtyFourGrid SmallLevelPrimeRates
open QuantitativeArithmeticSmallLevelThirtyFour SmallLevelThirtyFourPhysicalFiniteMMP

/-- No odd-third-twist pole, for this representative and its four sign scalings.
All matrix kernels come from original Taylor equations on one leading vector. -/
theorem quadratic_order_nonneg {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) (u v : ℂ)
    (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1)
    (hη : phase m ε= -u*v) (h₂ : badParameter f 2= -u)
    (h₁₇ : badParameter f 17= v) (x : ℂ) :
    0≤meromorphicOrderAt S.quadratic x := by
  by_contra hn
  have hpole : meromorphicOrderAt S.quadratic x<0 := lt_of_not_ge hn
  have hxre:=S.quadratic_pole_real_part hm hf x hpole
  have hx : x≠((2*m:ℕ):ℂ) := by
    intro he
    have hr:=congrArg Complex.re he
    norm_num [hxre] at hr
    have hmreal : (0:ℝ)<m := by exact_mod_cast hm
    nlinarith
  have hgrid : ∃ j,meromorphicOrderAt (fun z => S.G z j) x<0 := by
    by_contra hg
    push Not at hg
    have ha := ((S.meromorphic 138 x).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hg 138)).sub
      ((S.meromorphic 276 x).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hg 276))
    exact (not_le_of_gt hpole) ha.meromorphicOrderAt_nonneg
  obtain ⟨n,w,hw,hlead,htail⟩:=S.exists_active_leading_vector hf x hx hgrid
  have hjet:=SmallLevelThirtyFourUnitMMPInhomogeneous.active_first_jet_kernel S (x+n) u v hu hv hη h₂ h₁₇ w hw htail
  have hbase : u*parameter 2 m x=1 := by
    rw [S.quadratic_pole_parameter hm hf x hpole,h₂]
    rcases hu with rfl|rfl <;> norm_num
  have hX : u*parameter 2 m (x+n)=(2:ℂ)^n := by
    rw [parameter_add_nat 2 m (by decide),Nat.cast_ofNat,←mul_assoc,hbase,one_mul]
  apply hw.1
  by_cases hn0 : n=0
  · have hp0 : (2:ℂ)^n=1 := by rw [hn0,pow_zero]
    exact critical_matrix_kernel_zero m f ε u v (x+n) hu hv hη h₂ h₁₇ w hlead hjet
      (hX.trans hp0)
  · have hn1 : 1≤n := by omega
    have ht : (2:ℝ)≤(2:ℝ)^n := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hn1
    have hnorm : 9*(2:ℝ)^n/2≤‖parameter 3 m (x+n)^2‖ := by
      rw [parameter_three_square_norm m x hxre n]
      convert powers_gap n hn1 using 1; ring
    have hxn : (x+(n:ℂ)).re≠m := by
      simp only [Complex.add_re,Complex.natCast_re,hxre]
      have hnreal : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
      linarith
    apply positive_matrix_kernel_zero m f ε u v (x+n) hu hv hη h₂ h₁₇ w hlead hjet
      ((2:ℝ)^n) ht
    · simpa only [Complex.ofReal_pow,Complex.ofReal_ofNat] using hX
    · exact hnorm
    · exact S.leading_quadratic_zero hm hf (x+n) hxn w hw

#print axioms quadratic_order_nonneg
end SmallLevelThirtyFourQuadraticPoleMMP
end
end

/-! ## ThirtyFourChiThreeFiniteOrder -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourChiThree
open Complex Filter SmallLevelAdditive SmallLevelTaylor SmallLevelThirtyFourCenters
open scoped Topology

theorem original_numerator_bound (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) :
    FinitenessFiniteOrder.Bound (numerator m f) := by
  obtain ⟨χ,_hχ,hcent⟩ := original_centers_entire m hm hf
  exact FinitenessFiniteOrderClosure.sub
    (SmallLevelMellinUnscale.finite_order_at_one (by decide : 0<612) _ (hcent true).2.1)
    (SmallLevelMellinUnscale.finite_order_at_one (by decide : 0<612) _ (hcent false).2.1)

theorem uniform_product_identity {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f)
    {G : ℂ→ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s,B<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) :
    ∀ s,denominator m f s*G s=numerator m f s := by
  obtain ⟨C,hC⟩ := original_hecke_identity m hm hf
  have hleft := (denominator_entire m f).mul hG
  have hright := original_numerator_entire m hm hf
  intro s
  have he : (fun z => denominator m f z*G z)=ᶠ[𝓝[≠] s] numerator m f := by
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
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f)
    {G : ℂ→ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s,B<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) :
    FinitenessOriginalInput.FiniteOrder G := by
  apply QuantitativeArithmeticQuadraticTwistQuotient.finiteOrder_of_two_factor
    ((Real.sqrt 2:ℂ)*f 2) (m:ℂ)
    (original_numerator_entire m hm hf).continuous
    (FinitenessInputBounds.bound_finiteOrder (original_numerator_bound m hm hf)) hG
  intro s
  exact uniform_product_identity hm hf hG B hGF s

#print axioms uniform_finiteOrder
end SmallLevelThirtyFourChiThree
end
end

/-! ## ThirtyFourChiThreeEntire -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGrid
open Complex

theorem PoleSystem.quadratic_order_nonneg {m : ℕ} {f : ℕ→ℂ} {ε : ℂ}
    (S : PoleSystem m f ε) (hm : 0<m)
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f)
    (hε : ε=1 ∨ ε= -1) (x : ℂ) : 0≤meromorphicOrderAt S.quadratic x := by
  have hη : phase m ε=1 ∨ phase m ε= -1 := grid_physical_sign m hε
  have h₂:=badParameter_two_sign hf.toEulerData
  have h₁₇:=badParameter_seventeen_sign hf.toEulerData
  rcases hη with hη|hη <;> rcases h₂ with h₂|h₂ <;> rcases h₁₇ with h₁₇|h₁₇
  · exact SmallLevelThirtyFourQuadraticPoleMMP.quadratic_order_nonneg S hm hf
      (-1) 1 (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇) x
  · exact SmallLevelThirtyFourQuadraticPoleMMM.quadratic_order_nonneg S hm hf
      (-1) 1 (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇) x
  · exact SmallLevelThirtyFourQuadraticPoleMMM.quadratic_order_nonneg S hm hf
      1 (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇) x
  · exact SmallLevelThirtyFourQuadraticPoleMMP.quadratic_order_nonneg S hm hf
      1 (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇) x
  · exact SmallLevelThirtyFourQuadraticPoleMMM.quadratic_order_nonneg S hm hf
      (-1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇) x
  · exact SmallLevelThirtyFourQuadraticPoleMMP.quadratic_order_nonneg S hm hf
      (-1) (-1) (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇) x
  · exact SmallLevelThirtyFourQuadraticPoleMMP.quadratic_order_nonneg S hm hf
      1 1 (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇) x
  · exact SmallLevelThirtyFourQuadraticPoleMMM.quadratic_order_nonneg S hm hf
      1 1 (by norm_num) (by norm_num)
      (by simpa using hη) (by simpa using h₂) (by simpa using h₁₇) x

#print axioms PoleSystem.quadratic_order_nonneg
end SmallLevelThirtyFourGrid

namespace SmallLevelThirtyFourChiThree
open Complex SmallLevelAdditive SmallLevelThirtyFourGrid

theorem original_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) :
    ∃ (B : ℝ) (G : ℂ→ℂ), Differentiable ℂ G ∧
      FinitenessOriginalInput.FiniteOrder G ∧
      ∀ s,B<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s := by
  obtain ⟨ε,hε,⟨S⟩⟩:=original_pole_system m hm hf
  obtain ⟨B,G,hG,hagree,_hregular,hgerm⟩:=original_continuation m hm hf
  have hent : Differentiable ℂ G := by
    intro x
    apply AnalyticAt.differentiableAt
    apply (hG x).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_congr ((hgerm x).trans (S.quadratic_quotient_germ hm hf x).symm)]
    exact S.quadratic_order_nonneg hm hf hε x
  exact ⟨B,G,hent,uniform_finiteOrder hm hf hent B hagree,hagree⟩

#print axioms original_entire
end SmallLevelThirtyFourChiThree
end
end

/-! ## ThirtyFourCoherentCenters -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourCenters
open SmallLevelNormalized SmallLevelThirtyFour SmallLevelOriginal
  QuantitativeArithmeticTranslatedFricke Complex Filter Set MeasureTheory
  FinitenessPolynomialSeries FinitenessFourierConstruction Matrix UpperHalfPlane
open scoped Topology MatrixGroups ModularForm

/-- The two denominator-six centers have the root belonging to the fixed
original Fricke law, rather than independently chosen signs. -/
theorem coherent_centers_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 34 (2*m) f ε) :
    ∀ positive : Bool,Differentiable ℂ (centeredMellin m f positive) ∧
      FinitenessFiniteOrder.Bound (centeredMellin m f positive) ∧
      ∀ s : ℂ,centeredMellin m f positive s=
        (ε*FinitenessNormalizedTwistProduct.root 34 f 2)*
          centeredMellin m f positive ((2*m:ℕ)-s) := by
  obtain ⟨hχ,hF⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<34) m ε hε hlaw
  let χ : ℂ := ε*Complex.I^(2*m)
  let δ := FinitenessNormalizedTwistProduct.root 34 f 2
  have hδ : δ=1 ∨ δ= -1 := FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2
  have hχδ : χ*δ=1 ∨ χ*δ= -1 := by
    rcases hχ with h|h <;> rcases hδ with hd|hd <;> simp [χ,h,hd]
  have hcenter (positive : Bool) :
      (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center positive))
        ∣[((2*m:ℕ):ℤ)] fricke 612 (by decide)=
      (χ*δ) • (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center positive)) := by
    cases positive
    · exact translated_slash_eigen 34 612 (2*m) (by decide) (by decide) _ χ δ _ A A_det
        hF (SmallLevelSixEigen.thirty_four_A (by omega) hf) fricke_branch_neg
    · exact translated_slash_eigen 34 612 (2*m) (by decide) (by decide) _ χ δ _ B B_det
        hF (SmallLevelSixEigen.thirty_four_B (by omega) hf) fricke_branch_pos
  obtain ⟨τ,_,hg⟩ := hf.growth
  intro positive
  obtain ⟨hhol,hbound,hfe⟩ := translated_mellin_entire 612 (2*m) (by decide) (by omega) _
    (FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m))
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)) (center positive)
    (χ*δ) hχδ (hcenter positive)
  have he : χ*δ/(Complex.I^(2*m))=ε*δ := by
    dsimp only [χ]
    field_simp [Complex.I_ne_zero]
  exact ⟨hhol,hbound,by simpa only [he,centeredMellin,δ] using hfe⟩

#print axioms coherent_centers_entire
end SmallLevelThirtyFourCenters
end
end

/-! ## ThirtyFourChiThreeReflection -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourChiThree
open Complex SmallLevelAdditive SmallLevelThirtyFourCenters SmallLevelThirtyFourGrid
open FinitenessOriginalFourier

def scaleTwo (m : ℕ) (f : ℕ→ℂ) (s : ℂ) : ℂ :=
  badParameter f 2*(2:ℂ)^((m:ℂ)-s)

def reflectionMultiplier (m : ℕ) (ε s : ℂ) : ℂ :=
  -ε*(306:ℂ)^((m:ℂ)-s)

theorem scaleTwo_ne_zero (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.EulerData 34 f) (s : ℂ) : scaleTwo m f s≠0 := by
  apply mul_ne_zero
  · rcases badParameter_two_sign hf with h|h <;> simp [h]
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

theorem scaleTwo_product (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.EulerData 34 f) (s : ℂ) :
    scaleTwo m f s*scaleTwo m f (((2*m:ℕ):ℂ)-s)=1 := by
  have hp : (2:ℂ)^((m:ℂ)-s)*(2:ℂ)^((m:ℂ)-(((2*m:ℕ):ℂ)-s))=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    rw [show (m:ℂ)-s+((m:ℂ)-(((2*m:ℕ):ℂ)-s))=0 by push_cast; ring,Complex.cpow_zero]
  have hs : badParameter f 2*badParameter f 2=1 := by
    rcases badParameter_two_sign hf with h|h <;> simp [h]
  unfold scaleTwo
  calc
    _=(badParameter f 2*badParameter f 2)*
        ((2:ℂ)^((m:ℂ)-s)*(2:ℂ)^((m:ℂ)-(((2*m:ℕ):ℂ)-s))) := by ring
    _=1 := by rw [hs,hp,one_mul]

theorem denominator_reflection (m : ℕ) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.EulerData 34 f) (s : ℂ) :
    denominator m f s=scaleTwo m f s*denominator m f (((2*m:ℕ):ℂ)-s) := by
  have hp:=scaleTwo_product m hf s
  change 1+scaleTwo m f s=scaleTwo m f s*(1+scaleTwo m f (((2*m:ℕ):ℂ)-s))
  linear_combination -hp

theorem center_conductor_factor (m : ℕ) (s : ℂ) :
    (Real.sqrt 612:ℂ)^(((2*m:ℕ):ℂ)-2*s)=
      (2:ℂ)^((m:ℂ)-s)*(306:ℂ)^((m:ℂ)-s) := by
  have hn : (Real.sqrt 612:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs : (Real.sqrt 612:ℂ)*(Real.sqrt 612:ℂ)=612 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ)≤612)
  have hp:=Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg 612) (Real.sqrt_nonneg 612) ((m:ℂ)-s)
  rw [hs] at hp
  rw [show ((2*m:ℕ):ℂ)-2*s=((m:ℂ)-s)+((m:ℂ)-s) by push_cast; ring,
    Complex.cpow_add _ _ hn,←hp]
  have h:=Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤2)
    (by norm_num : (0:ℝ)≤306) ((m:ℂ)-s)
  norm_num only [Complex.ofReal_ofNat] at h
  simpa only [show (2:ℂ)*306=612 by norm_num] using h

theorem reflectionMultiplier_entire (m : ℕ) (ε : ℂ) :
    Differentiable ℂ (reflectionMultiplier m ε) := by
  unfold reflectionMultiplier
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (306:ℂ)≠0)]
  fun_prop

theorem reflectionMultiplier_ne_zero (m : ℕ) {ε : ℂ} (hε : ε≠0) (s : ℂ) :
    reflectionMultiplier m ε s≠0 :=
  mul_ne_zero (neg_ne_zero.mpr hε) (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))

theorem coherent_numerator_reflection (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 34 (2*m) f ε) (s : ℂ) :
    numerator m f s=scaleTwo m f s*reflectionMultiplier m ε s*
      numerator m f (((2*m:ℕ):ℂ)-s) := by
  have hc:=coherent_centers_entire m hm hf ε hε hlaw
  have hp (positive : Bool):=QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection
    (by decide : 0<612) (coefficients (fullCoefficients f (2*m)) (center positive))
    (ε*FinitenessNormalizedTwistProduct.root 34 f 2) (hc positive).2.2 s
  have hpos:=hp true
  have hneg:=hp false
  norm_num only [center,Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat] at hpos hneg
  rw [center_conductor_factor,root_two] at hpos hneg
  unfold numerator scaleTwo reflectionMultiplier
  linear_combination hpos-hneg

/-- The meromorphic odd-third continuation has the coherent conductor306
functional equation. Entireness is established separately by pole exclusion. -/
theorem original_coherent_reflection (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 34 (2*m) f ε) :
    ∃ (B : ℝ) (G : ℂ→ℂ), (∀ s,MeromorphicNFAt G s) ∧
      (∀ s,B<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) ∧
      ∀ s,G s=(-ε)*(306:ℂ)^((m:ℂ)-s)*G (((2*m:ℕ):ℂ)-s) := by
  obtain ⟨B,G,hG,hagree,_hregular,hgerm⟩:=original_continuation m hm hf
  have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
  have hraw (s : ℂ) : numerator m f s/denominator m f s=
      reflectionMultiplier m ε s*
        (numerator m f (((2*m:ℕ):ℂ)-s)/denominator m f (((2*m:ℕ):ℂ)-s)) := by
    rw [coherent_numerator_reflection m hm hf ε hε hlaw s,
      denominator_reflection m hf.toEulerData s,mul_assoc,
      mul_div_mul_left _ _ (scaleTwo_ne_zero m hf.toEulerData s)]
    ring
  have he:=QuantitativeArithmeticQuadraticTwistReflection.normal_form_reflection
    (fun s => numerator m f s/denominator m f s) G (reflectionMultiplier m ε)
    (((2*m:ℕ):ℂ)) hG (fun s => (reflectionMultiplier_entire m ε).analyticAt s)
    (reflectionMultiplier_ne_zero m hε0) hgerm hraw
  exact ⟨B,G,hG,hagree,he⟩

#print axioms denominator_reflection
#print axioms coherent_numerator_reflection
#print axioms original_coherent_reflection
end SmallLevelThirtyFourChiThree
end
end

/-! ## ThirtyFourChiThreeCoherentEntire -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourChiThree
open Complex Filter SmallLevelAdditive
open scoped Topology

theorem original_coherent_entire (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 34 (2*m) f ε) :
    ∃ (B : ℝ) (G : ℂ→ℂ), Differentiable ℂ G ∧ FinitenessOriginalInput.FiniteOrder G ∧
      (∀ s,B<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) ∧
      ∀ s,G s=(-ε)*(306:ℂ)^((m:ℂ)-s)*G (((2*m:ℕ):ℂ)-s) := by
  obtain ⟨BE,E,hE,_hfiniteE,hEF⟩:=original_entire m hm hf
  obtain ⟨B,G,hG,hGF,hFE⟩:=original_coherent_reflection m hm hf ε hε hlaw
  have hent : Differentiable ℂ G := by
    intro s
    apply AnalyticAt.differentiableAt
    exact SmallLevelSimplePoleTaylor.analyticAt_of_model
      (fun s => original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s)
      G E E B BE (s.re-1) s hG hGF
      (fun z _ => (hE.analyticAt z).meromorphicAt) hEF
      (by linarith) (hE.analyticAt s) Filter.EventuallyEq.rfl
  exact ⟨B,G,hent,uniform_finiteOrder hm hf hent B hGF,hGF,hFE⟩

#print axioms original_coherent_entire
end SmallLevelThirtyFourChiThree
end
end

/-! ## ThirtyFourChiThreeFricke -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourChiThree
open Complex FinitenessOriginalFourier FinitenessFourierConstruction

def quadraticFourier (k : ℕ) (f : ℕ→ℂ) (z : ℂ) : ℂ :=
  fourier (fullCoefficients f k) (z+(1/3:ℝ))-
    fourier (fullCoefficients f k) (z+(-1/3:ℝ))

theorem original_quadratic_fricke {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) :
    ∃ ε : ℂ,(ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 34 (2*m) f ε ∧
      ∀ z : ℂ,0<z.im → quadraticFourier (2*m) f z=
        ((-ε)*I^(2*m))/(((Real.sqrt 306:ℂ)*z)^(2*m))*
          quadraticFourier (2*m) f (-1/((306:ℂ)*z)) := by
  obtain ⟨ε,hε,hlaw⟩:=QuantitativeArithmeticCoherentTaylor.original_coherent_law
    (by decide : 0<34) hf
  obtain ⟨B,G,hent,hfinite,hGF,hFE⟩:=original_coherent_entire m hm hf ε hε hlaw
  obtain ⟨σ,_hσ,hgrowth⟩:=hf.growth
  refine ⟨ε,hε,hlaw,?_⟩
  have h:=QuantitativeArithmeticQuadraticTwistInversion.four_translate_fricke
    (k:=2*m) (ε:= -ε) (B:=B) (by decide : 0<306) hf.zero hgrowth
    (1/3) 0 (-1/3) 0 G hent hfinite
    (by
      intro s hs
      rw [hGF s hs]
      simp only [neg_div]
      ring)
    (by rcases hε with rfl|rfl <;> norm_num)
    (by
      have he : ((2*m:ℕ):ℂ)/2=(m:ℂ) := by push_cast; ring
      simpa only [Nat.cast_ofNat,he] using hFE)
  intro z hz
  dsimp only at h
  unfold quadraticFourier
  convert h z hz using 1 <;> ring

#print axioms original_quadratic_fricke
end SmallLevelThirtyFourChiThree
end
end

/-! ## ThirtyFourChiThreeIndividual -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourChiThree
open Complex FinitenessOriginalFourier FinitenessFourierConstruction

/-- The opposite roots of the even and odd third twists exchange the two
individual additive centers, with no division by a Hecke eigenvalue. -/
theorem individual_laws {k : ℕ} {f : ℕ→ℂ} (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 34 k f ε)
    (hquad : ∀ z : ℂ,0<z.im → quadraticFourier k f z=
      ((-ε)*I^k)/(((Real.sqrt 306:ℂ)*z)^k)*quadraticFourier k f (-1/((306:ℂ)*z))) :
    ∀ z : ℂ,0<z.im →
      (fourier (fullCoefficients f k) (z+1/3)=
        (ε*I^k)/(((Real.sqrt 306:ℂ)*z)^k)*
          fourier (fullCoefficients f k) (-1/((306:ℂ)*z)-1/3)) ∧
      (fourier (fullCoefficients f k) (z-1/3)=
        (ε*I^k)/(((Real.sqrt 306:ℂ)*z)^k)*
          fourier (fullCoefficients f k) (-1/((306:ℂ)*z)+1/3)) := by
  intro z hz
  have hr:=hlaw 3 (by decide) z hz
  have hroot : FinitenessNormalizedTwistProduct.root 34 f 3=1 := by
    norm_num [FinitenessNormalizedTwistProduct.root,FinitenessNormalizedTwistLocal.sign]
  rw [show Nat.lcm 34 (3^2)=306 by decide,hroot,one_mul,
    SmallLevelThree.twist_three _ (periodic _),SmallLevelThree.twist_three _ (periodic _)] at hr
  norm_num only [Nat.cast_ofNat] at hr
  have hc:=hquad z hz
  norm_num only [quadraticFourier,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_ofNat,Complex.ofReal_one] at hc
  simp only [sub_eq_add_neg] at hr hc ⊢
  constructor
  · linear_combination (hr+hc)/2
  · linear_combination (hr-hc)/2

#print axioms individual_laws
end SmallLevelThirtyFourChiThree
end
end

/-! ## ThirtyFourGroupKernelData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section
namespace SmallLevelThirtyFourGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups
def kernel : Fin 18 → SL(2,ℤ)
  | 0 => ⟨!![1,1;0,1],by decide⟩
  | 1 => ⟨!![19,1;170,9],by decide⟩
  | 2 => ⟨!![11,-1;34,-3],by decide⟩
  | 3 => ⟨!![37,2;-204,-11],by decide⟩
  | 4 => ⟨!![35,2;-578,-33],by decide⟩
  | 5 => ⟨!![19,-10;-340,179],by decide⟩
  | 6 => ⟨!![13,-3;-238,55],by decide⟩
  | 7 => ⟨!![91,5;-1802,-99],by decide⟩
  | 8 => ⟨!![23,-4;-408,71],by decide⟩
  | 9 => ⟨!![1,0;-34,1],by decide⟩
  | 10 => ⟨!![179,10;340,19],by decide⟩
  | 11 => ⟨!![89,5;-374,-21],by decide⟩
  | 12 => ⟨!![3,1;-34,-11],by decide⟩
  | 13 => ⟨!![71,4;408,23],by decide⟩
  | 14 => ⟨!![307,17;-5508,-305],by decide⟩
  | 15 => ⟨!![25,3;-442,-53],by decide⟩
  | 16 => ⟨!![581,33;-10370,-589],by decide⟩
  | _ => ⟨!![11,2;-204,-37],by decide⟩

end SmallLevelThirtyFourGroup
end
end

/-! ## ThirtyFourPrimeFiveElliptic -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThirtyFourPrimeFive

open Matrix ModularGroup Complex Filter Set
open scoped MatrixGroups Topology

def elliptic : SL(2,ℚ) := ⟨!![-29/5,28/25;-136/5,127/25], by norm_num [det_fin_two]⟩

def fixedPoint : ℂ := ⟨1/5, Real.sqrt 34/170⟩

theorem fixedPoint_positive : 0<fixedPoint.im := by
  change 0<Real.sqrt 34/170
  positivity

theorem fixedPoint_denom : (-136/5:ℂ)*fixedPoint+127/25≠0 := by
  intro h
  have hh := congrArg Complex.im h
  simp [fixedPoint] at hh

theorem fixedPoint_fixed : ((-29/5)*fixedPoint+28/25)/((-136/5)*fixedPoint+127/25)=fixedPoint := by
  apply (div_eq_iff fixedPoint_denom).mpr
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [fixedPoint, Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- The determinant-one square of the prime-five defect matrix
annihilates any positive-weight holomorphic invariant defect. -/
theorem elliptic_defect_zero {F : ℂ → ℂ} {k : ℕ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im}) (hk : 0<k)
    (he : ∀ z : ℂ, 0<z.im →
      F (((-29/5)*z+28/25)/((-136/5)*z+127/25))=((-136/5)*z+127/25)^k*F z) :
    ∀ z : ℂ, 0<z.im → F z=0 := by
  have hnon (m : ℤ) : (-18/25:ℚ)≠m := by
    intro hm
    have hh : (25:ℚ)*m= -18 := by rw [← hm]; norm_num
    have hi : (25:ℤ)*m= -18 := by exact_mod_cast hh
    omega
  have heq : ∀ᶠ z in 𝓝 fixedPoint,
      F (((-29/5)*z+28/25)/((-136/5)*z+127/25))=((-136/5)*z+127/25)^k*F z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds fixedPoint_positive] with z hz
    simpa only [sub_eq_add_neg, neg_div,one_mul] using he z hz
  have hh := SmallLevelAnalyticRigidity.rational_trace_eqOn_zero hF
    (convex_halfSpace_im_gt 0).isPreconnected fixedPoint_positive
    (a:= -29/5) (b:=28/25) (c:= -136/5) (d:=127/25) (t:=(-18/25:ℚ))
    (by norm_num) (by simpa only [sub_eq_add_neg, neg_div,one_mul] using fixedPoint_denom)
    (by simpa only [sub_eq_add_neg, neg_div,one_mul] using fixedPoint_fixed) hk
    (by norm_num) hnon (by simpa only [sub_eq_add_neg, neg_div,one_mul] using heq)
  exact fun z hz => hh hz

#print axioms elliptic_defect_zero
end SmallLevelThirtyFourPrimeFive
end
end

/-! ## ThirtyFourPrimeFiveRigidity -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThirtyFourPrimeFive

open Matrix UpperHalfPlane ModularGroup
open scoped MatrixGroups ModularForm Manifold

def ellipticReal : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ elliptic

theorem ellipticReal_det : (GeneralLinearGroup.det ellipticReal : ℝ)=1 := by
  simp [ellipticReal]

theorem ellipticReal_denom (z : ℍ) : denom ellipticReal z= (-136/5)*(z:ℂ)+127/25 := by
  norm_num [denom, ellipticReal, elliptic, SpecialLinearGroup.toGL,
    SpecialLinearGroup.map_apply_coe]

theorem ellipticReal_point (z : ℍ) :
    ((ellipticReal • z : ℍ):ℂ)=((-29/5)*(z:ℂ)+28/25)/((-136/5)*(z:ℂ)+127/25) := by
  rw [coe_smul_of_det_pos (by rw [ellipticReal_det]; norm_num)]
  norm_num [num, denom, ellipticReal, elliptic, SpecialLinearGroup.toGL,
    SpecialLinearGroup.map_apply_coe]

theorem invariant_zero {k : ℕ} (hk : 0<k) (H : ℍ → ℂ)
    (hhol : MDiff H) (he : H ∣[(k:ℤ)] ellipticReal=H) : H=0 := by
  let F : ℂ → ℂ := H ∘ ofComplex
  have hr (w : ℍ) : H w=F (w:ℂ) := by simp [F]
  have ha : AnalyticOnNhd ℂ F {z : ℂ | 0<z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hhol).analyticOnNhd isOpen_upperHalfPlaneSet
  have htrans (z : ℂ) (hz : 0<z.im) :
      F (((-29/5)*z+28/25)/((-136/5)*z+127/25))=((-136/5)*z+127/25)^k*F z := by
    let w : ℍ := ⟨z,hz⟩
    have hh := congrFun he w
    rw [ModularForm.slash_apply] at hh
    have hs : σ ellipticReal=ContinuousAlgEquiv.refl ℝ ℂ := by
      simp only [σ, ellipticReal_det]; norm_num
    rw [hs, ellipticReal_det, ellipticReal_denom] at hh
    norm_num only [ContinuousAlgEquiv.refl_apply, abs_one, Complex.ofReal_one,
      one_zpow, mul_one, zpow_neg, zpow_natCast] at hh
    rw [hr, hr, ellipticReal_point] at hh
    simp only [← neg_div] at hh
    change F (((-29/5)*z+28/25)/((-136/5)*z+127/25))*(((-136/5)*z+127/25)^k)⁻¹=F z at hh
    have hd : ((-136/5)*z+127/25:ℂ)≠0 := by
      simpa only [ellipticReal_denom] using denom_ne_zero ellipticReal w
    have hx := congrArg (fun v : ℂ => v*((-136/5)*z+127/25)^k) hh
    simp only [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hd), mul_one] at hx
    simpa only [mul_comm] using hx
  funext z
  rw [hr]
  exact elliptic_defect_zero ha hk htrans z z.im_pos


/-- The normalized prime-five defect matrix. Its square has rational
nonintegral trace -18/25 and fixes a point of the upper half-plane. -/
def K : GL (Fin 2) ℝ := SmallLevelThirtyFour.A*SmallLevelNormalized.translation (-(2/5))

theorem K_square : K*K=ellipticReal := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, SmallLevelThirtyFour.A, SmallLevelNormalized.translation,
      ellipticReal, elliptic, SmallLevelNormalized.matrix,
      GeneralLinearGroup.mkOfDetNeZero, SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [SmallLevelThirtyFour.sqrt_norm_ne] <;> nlinarith

#print axioms invariant_zero
#print axioms K_square
end SmallLevelThirtyFourPrimeFive
end
end

/-! ## ThirtyFourPrimeFiveDefect -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourPrimeFive
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm Manifold

theorem K_det : (GeneralLinearGroup.det K : ℝ)=1 := by
  unfold K
  rw [map_mul,Units.val_mul,SmallLevelThirtyFour.A_det,translation_det,mul_one]

/-- Either sign eigenlaw under the prime-five elliptic matrix forces
a positive-weight holomorphic defect to vanish. -/
theorem sign_eigen_zero {k : ℕ} (hk : 0<k) (H : ℍ→ℂ)
    (hhol : MDiff H) (δ : ℂ) (hδ : δ=1 ∨ δ= -1)
    (he : H ∣[(k:ℤ)] K=δ • H) : H=0 := by
  apply invariant_zero hk H hhol
  rw [←K_square,SlashAction.slash_mul,he,det_one_smul _ K_det,he,smul_smul]
  rcases hδ with rfl|rfl <;> simp

def P : GL (Fin 2) ℝ := matrix (4/Real.sqrt 2) (-1/Real.sqrt 2)
    (34/Real.sqrt 2) (-8/Real.sqrt 2) (by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  field_simp [SmallLevelThirtyFour.sqrt_norm_ne]
  nlinarith)

/-- The analytic conclusion of the prime-five defect argument. Its
remaining input is the concrete two-term Ramanujan defect eigenlaw. -/
theorem P_of_defect_eigen {k : ℕ} (hk : 0<k) (F : ℍ→ℂ)
    (hhol : MDiff F) (δ : ℂ) (hδ : δ=1 ∨ δ= -1)
    (he : ((F ∣[(k:ℤ)] P)-δ • F) ∣[(k:ℤ)] K=
      (-δ) • ((F ∣[(k:ℤ)] P)-δ • F)) : F ∣[(k:ℤ)] P=δ • F := by
  have hs : MDiff (δ • F) := by
    rcases hδ with rfl|rfl
    · simpa only [one_smul] using hhol
    · simpa only [neg_one_smul] using hhol.neg
  have hn : -δ=1 ∨ -δ= -1 := by
    rcases hδ with rfl|rfl <;> simp
  exact sub_eq_zero.mp (sign_eigen_zero hk _ ((hhol.slash (k:ℤ) P).sub hs) (-δ) hn he)

#print axioms sign_eigen_zero
#print axioms P_of_defect_eigen
end SmallLevelThirtyFourPrimeFive
end
end

/-! ## ThirtyFourGroupKernelMatrixData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm
open SmallLevelThirtyFourPrimeFive (P)
open SmallLevelThirtyFour (B)

def Y : SL(2,ℤ) := ⟨!![11,-1;34,-3],by decide⟩

def kernelRep : Fin 4→GL (Fin 2) ℝ
  | 0 => 1
  | 1 => E
  | 2 => W
  | _ => E*W

def kernelGenerator : Fin 6→GL (Fin 2) ℝ
  | 0 => translation 1
  | 1 => E
  | 2 => W
  | 3 => P
  | 4 => SpecialLinearGroup.mapGL ℝ Y
  | _ => B

def sourceIndex : Fin 18→Fin 4
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 2
  | 10 => 2
  | 11 => 2
  | 12 => 2
  | 13 => 2
  | 14 => 3
  | 15 => 3
  | 16 => 3
  | _ => 3

def symbolIndex : Fin 18→Fin 6
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 0
  | 5 => 1
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | 9 => 0
  | 10 => 1
  | 11 => 3
  | 12 => 4
  | 13 => 5
  | 14 => 0
  | 15 => 3
  | 16 => 4
  | _ => 5

def targetIndex : Fin 18→Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | 5 => 0
  | 6 => 0
  | 7 => 1
  | 8 => 0
  | 9 => 2
  | 10 => 3
  | 11 => 3
  | 12 => 2
  | 13 => 3
  | 14 => 3
  | 15 => 2
  | 16 => 3
  | _ => 2

def kernelNegative : Fin 18→Bool
  | 0 => false
  | 1 => false
  | 2 => false
  | 3 => false
  | 4 => false
  | 5 => false
  | 6 => true
  | 7 => true
  | 8 => false
  | 9 => false
  | 10 => false
  | 11 => true
  | 12 => true
  | 13 => false
  | 14 => false
  | 15 => true
  | 16 => true
  | _ => true

end SmallLevelThirtyFourGroup
end
end

/-! ## ThirtyFourChiThreeMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourChiThree
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

def crossedMatrix : GL (Fin 2) ℝ := matrix 3 (-1) 34 (-11) (by norm_num)

theorem sqrt_conductor : Real.sqrt 306=3*Real.sqrt 34 := by
  rw [show (306:ℝ)=9*34 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem crossed_branch : fricke 34 (by decide)*crossedMatrix*translation (1/3)=
    translation (-(1/3))*fricke 306 (by decide) := by
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,crossedMatrix,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply,Fin.sum_univ_two,sqrt_conductor] <;>
    field_simp [hn] <;> norm_num [hs] <;> nlinarith [hs]

theorem crossed_conjugate : (fricke 34 (by decide))⁻¹*translation (-(1/3))*
    fricke 306 (by decide)*(translation (1/3))⁻¹=crossedMatrix := by
  calc
    _=(fricke 34 (by decide))⁻¹*(translation (-(1/3))*fricke 306 (by decide))*
        (translation (1/3))⁻¹ := by group
    _=(fricke 34 (by decide))⁻¹*(fricke 34 (by decide)*crossedMatrix*translation (1/3))*
        (translation (1/3))⁻¹ := by rw [crossed_branch]
    _=_ := by group

theorem crossed_Y : crossedMatrix*SpecialLinearGroup.mapGL ℝ SmallLevelThirtyFourGroup.Y=
    (-1:GL (Fin 2) ℝ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [crossedMatrix,SmallLevelThirtyFourGroup.Y,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Fin.sum_univ_two]

theorem Y_of_crossed (m : ℕ) (F : ℍ→ℂ)
    (h : F ∣[((2*m:ℕ):ℤ)] crossedMatrix=F) :
    F ∣[((2*m:ℕ):ℤ)] SmallLevelThirtyFourGroup.Y=F := by
  have hh:=congrArg (fun g : ℍ→ℂ => g ∣[((2*m:ℕ):ℤ)]
    SpecialLinearGroup.mapGL ℝ SmallLevelThirtyFourGroup.Y) h
  rw [←SlashAction.slash_mul,crossed_Y,central_even] at hh
  exact hh.symm

#print axioms crossed_conjugate
#print axioms Y_of_crossed
end SmallLevelThirtyFourChiThree
end
end

/-! ## ThirtyFourGroupGeneratorData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section
namespace SmallLevelThirtyFourGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups
def letter : Fin 37 → SL(2,ℤ)
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
  | 18 => (kernel 0)⁻¹
  | 19 => (kernel 1)⁻¹
  | 20 => (kernel 2)⁻¹
  | 21 => (kernel 3)⁻¹
  | 22 => (kernel 4)⁻¹
  | 23 => (kernel 5)⁻¹
  | 24 => (kernel 6)⁻¹
  | 25 => (kernel 7)⁻¹
  | 26 => (kernel 8)⁻¹
  | 27 => (kernel 9)⁻¹
  | 28 => (kernel 10)⁻¹
  | 29 => (kernel 11)⁻¹
  | 30 => (kernel 12)⁻¹
  | 31 => (kernel 13)⁻¹
  | 32 => (kernel 14)⁻¹
  | 33 => (kernel 15)⁻¹
  | 34 => (kernel 16)⁻¹
  | 35 => (kernel 17)⁻¹
  | _ => -1

def word (w : List (Fin 37)) : SL(2,ℤ) := (w.map letter).prod

theorem word_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 18,kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (w : List (Fin 37)) : word w∈K := by
  have hl (i : Fin 37) : letter i∈K := by
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
    · exact hZ
  exact K.list_prod_mem (fun x hx => by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact hl i)

def repRow (c d : ZMod 34) : SL(2,ℤ) :=
  match c.val*34+d.val with
  | 34 | 102 | 170 | 238 | 306 | 374 | 442 | 510 | 646 | 714 | 782 | 850 | 918 | 986 | 1054 | 1122 => ⟨!![0,-1;1,0],by decide⟩
  | 35 | 105 | 175 | 245 | 315 | 385 | 455 | 525 | 665 | 735 | 805 | 875 | 945 | 1015 | 1085 | 1155 => ⟨!![0,-1;1,1],by decide⟩
  | 67 | 133 | 199 | 265 | 331 | 397 | 463 | 529 | 661 | 727 | 793 | 859 | 925 | 991 | 1057 | 1123 => ⟨!![0,-1;1,-1],by decide⟩
  | 36 | 108 | 180 | 252 | 324 | 396 | 468 | 540 | 650 | 722 | 794 | 866 | 938 | 1010 | 1082 | 1154 => ⟨!![0,-1;1,2],by decide⟩
  | 66 | 130 | 194 | 258 | 322 | 386 | 450 | 514 | 676 | 740 | 804 | 868 | 932 | 996 | 1060 | 1124 => ⟨!![0,-1;1,-2],by decide⟩
  | 101 | 151 | 235 | 285 | 369 | 419 | 503 | 553 | 637 | 687 | 771 | 821 | 905 | 955 | 1039 | 1089 => ⟨!![-1,0;2,-1],by decide⟩
  | 37 | 111 | 185 | 259 | 333 | 407 | 447 | 521 | 669 | 743 | 783 | 857 | 931 | 1005 | 1079 | 1153 => ⟨!![0,-1;1,3],by decide⟩
  | 69 | 155 | 207 | 293 | 345 | 431 | 483 | 569 | 621 | 707 | 759 | 845 | 897 | 983 | 1035 | 1121 => ⟨!![-1,0;-2,-1],by decide⟩
  | 65 | 127 | 189 | 251 | 313 | 375 | 471 | 533 | 657 | 719 | 815 | 877 | 939 | 1001 | 1063 | 1125 => ⟨!![0,-1;1,-3],by decide⟩
  | 99 | 147 | 229 | 277 | 359 | 441 | 489 | 571 | 619 | 701 | 749 | 831 | 913 | 961 | 1043 | 1091 => ⟨!![-1,1;2,-3],by decide⟩
  | 45 | 135 | 191 | 247 | 337 | 393 | 449 | 539 | 651 | 741 | 797 | 853 | 943 | 999 | 1055 | 1145 => ⟨!![-1,0;3,-1],by decide⟩
  | 38 | 114 | 190 | 266 | 308 | 384 | 460 | 536 | 654 | 730 | 806 | 882 | 924 | 1000 | 1076 | 1152 => ⟨!![0,-1;1,4],by decide⟩
  | 71 | 159 | 213 | 301 | 355 | 409 | 497 | 551 | 639 | 693 | 781 | 835 | 889 | 977 | 1031 | 1119 => ⟨!![-1,-1;-2,-3],by decide⟩
  | 57 | 103 | 183 | 263 | 309 | 389 | 469 | 515 | 675 | 721 | 801 | 881 | 927 | 1007 | 1087 | 1133 => ⟨!![-1,0;-3,-1],by decide⟩
  | 64 | 124 | 184 | 244 | 338 | 398 | 458 | 518 | 672 | 732 | 792 | 852 | 946 | 1006 | 1066 | 1126 => ⟨!![0,-1;1,-4],by decide⟩
  | 46 | 104 | 196 | 254 | 312 | 404 | 462 | 520 | 670 | 728 | 786 | 878 | 936 | 994 | 1086 | 1144 => ⟨!![1,1;-3,-2],by decide⟩
  | 97 | 143 | 223 | 303 | 349 | 429 | 509 | 555 | 635 | 681 | 761 | 841 | 887 | 967 | 1047 | 1093 => ⟨!![-1,2;2,-5],by decide⟩
  | 44 | 132 | 186 | 240 | 328 | 382 | 470 | 524 | 666 | 720 | 808 | 862 | 950 | 1004 | 1058 | 1146 => ⟨!![-1,1;3,-4],by decide⟩
  | 93 | 169 | 211 | 287 | 363 | 439 | 481 | 557 | 633 | 709 | 751 | 827 | 903 | 979 | 1021 | 1097 => ⟨!![-1,0;4,-1],by decide⟩
  | 39 | 117 | 195 | 239 | 317 | 395 | 473 | 517 | 673 | 717 | 795 | 873 | 951 | 995 | 1073 | 1151 => ⟨!![0,-1;1,5],by decide⟩
  | 56 | 134 | 178 | 256 | 334 | 378 | 456 | 534 | 656 | 734 | 812 | 856 | 934 | 1012 | 1056 | 1134 => ⟨!![-1,1;-3,2],by decide⟩
  | 73 | 163 | 219 | 275 | 365 | 421 | 477 | 567 | 623 | 713 | 769 | 825 | 915 | 971 | 1027 | 1117 => ⟨!![-1,-2;-2,-5],by decide⟩
  | 58 | 106 | 188 | 270 | 318 | 400 | 448 | 530 | 660 | 742 | 790 | 872 | 920 | 1002 | 1084 | 1132 => ⟨!![-1,-1;-3,-4],by decide⟩
  | 77 | 137 | 231 | 291 | 351 | 411 | 505 | 565 | 625 | 685 | 779 | 839 | 899 | 959 | 1053 | 1113 => ⟨!![-1,0;-4,-1],by decide⟩
  | 63 | 121 | 179 | 271 | 329 | 387 | 445 | 537 | 653 | 745 | 803 | 861 | 919 | 1011 | 1069 | 1127 => ⟨!![0,-1;1,-5],by decide⟩
  | 47 | 107 | 201 | 261 | 321 | 381 | 475 | 535 | 655 | 715 | 809 | 869 | 929 | 989 | 1083 | 1143 => ⟨!![1,2;-3,-5],by decide⟩
  | 48 | 110 | 172 | 268 | 330 | 392 | 454 | 516 | 674 | 736 | 798 | 860 | 922 | 1018 | 1080 | 1142 => ⟨!![2,1;-5,-2],by decide⟩
  | 95 | 139 | 217 | 295 | 373 | 417 | 495 | 573 | 617 | 695 | 773 | 817 | 895 | 973 | 1051 | 1095 => ⟨!![-1,3;2,-7],by decide⟩
  | 43 | 129 | 181 | 267 | 319 | 405 | 457 | 543 | 647 | 733 | 785 | 871 | 923 | 1009 | 1061 | 1147 => ⟨!![-1,2;3,-7],by decide⟩
  | 91 | 165 | 205 | 279 | 353 | 427 | 501 | 575 | 615 | 689 | 763 | 837 | 911 | 985 | 1025 | 1099 => ⟨!![-1,1;4,-5],by decide⟩
  | 61 | 115 | 203 | 257 | 311 | 399 | 453 | 541 | 649 | 737 | 791 | 879 | 933 | 987 | 1075 | 1129 => ⟨!![-1,0;5,-1],by decide⟩
  | 40 | 120 | 200 | 246 | 326 | 406 | 452 | 532 | 658 | 738 | 784 | 864 | 944 | 990 | 1070 | 1150 => ⟨!![0,-1;1,6],by decide⟩
  | 55 | 131 | 173 | 249 | 325 | 401 | 443 | 519 | 671 | 747 | 789 | 865 | 941 | 1017 | 1059 | 1135 => ⟨!![-1,2;-3,5],by decide⟩
  | 54 | 128 | 202 | 242 | 316 | 390 | 464 | 538 | 652 | 726 | 800 | 874 | 948 | 988 | 1062 | 1136 => ⟨!![-2,1;-5,2],by decide⟩
  | 75 | 167 | 225 | 283 | 341 | 433 | 491 | 549 | 641 | 699 | 757 | 849 | 907 | 965 | 1023 | 1115 => ⟨!![-1,-3;-2,-7],by decide⟩
  | 59 | 109 | 193 | 243 | 327 | 377 | 461 | 511 | 679 | 729 | 813 | 863 | 947 | 997 | 1081 | 1131 => ⟨!![-1,-2;-3,-7],by decide⟩
  | 79 | 141 | 237 | 299 | 361 | 423 | 485 | 547 | 643 | 705 | 767 | 829 | 891 | 953 | 1049 | 1111 => ⟨!![-1,-1;-4,-5],by decide⟩
  | 41 | 123 | 171 | 253 | 335 | 383 | 465 | 513 | 677 | 725 | 807 | 855 | 937 | 1019 | 1067 | 1149 => ⟨!![-1,0;-5,-1],by decide⟩
  | 62 | 118 | 174 | 264 | 320 | 376 | 466 | 522 | 668 | 724 | 814 | 870 | 926 | 1016 | 1072 | 1128 => ⟨!![0,-1;1,-6],by decide⟩
  | 49 | 113 | 177 | 241 | 339 | 403 | 467 | 531 | 659 | 723 | 787 | 851 | 949 | 1013 | 1077 | 1141 => ⟨!![2,3;-5,-7],by decide⟩
  | 42 | 126 | 176 | 260 | 310 | 394 | 444 | 528 | 662 | 746 | 796 | 880 | 930 | 1014 | 1064 | 1148 => ⟨!![-1,3;3,-10],by decide⟩
  | 89 | 161 | 233 | 305 | 343 | 415 | 487 | 559 | 631 | 703 | 775 | 847 | 885 | 957 | 1029 | 1101 => ⟨!![-1,2;4,-9],by decide⟩
  | 60 | 112 | 198 | 250 | 336 | 388 | 474 | 526 | 664 | 716 | 802 | 854 | 940 | 992 | 1078 | 1130 => ⟨!![-1,1;5,-6],by decide⟩
  | 53 | 125 | 197 | 269 | 307 | 379 | 451 | 523 | 667 | 739 | 811 | 883 | 921 | 993 | 1065 | 1137 => ⟨!![-2,3;-5,7],by decide⟩
  | 81 | 145 | 209 | 273 | 371 | 435 | 499 | 563 | 627 | 691 | 755 | 819 | 917 | 981 | 1045 | 1109 => ⟨!![-1,-2;-4,-9],by decide⟩
  | 50 | 116 | 182 | 248 | 314 | 380 | 446 | 512 | 678 | 744 | 810 | 876 | 942 | 1008 | 1074 | 1140 => ⟨!![2,5;-5,-12],by decide⟩
  | 87 | 157 | 227 | 297 | 367 | 437 | 507 | 577 | 613 | 683 | 753 | 823 | 893 | 963 | 1033 | 1103 => ⟨!![-1,3;4,-13],by decide⟩
  | 52 | 122 | 192 | 262 | 332 | 402 | 472 | 542 | 648 | 718 | 788 | 858 | 928 | 998 | 1068 | 1138 => ⟨!![-2,5;-5,12],by decide⟩
  | 83 | 149 | 215 | 281 | 347 | 413 | 479 | 545 | 645 | 711 | 777 | 843 | 909 | 975 | 1041 | 1107 => ⟨!![-1,-3;-4,-13],by decide⟩
  | 51 | 119 | 187 | 255 | 323 | 391 | 459 | 527 | 663 | 731 | 799 | 867 | 935 | 1003 | 1071 | 1139 => ⟨!![2,7;-5,-17],by decide⟩
  | 85 | 153 | 221 | 289 | 357 | 425 | 493 | 561 | 629 | 697 | 765 | 833 | 901 | 969 | 1037 | 1105 => ⟨!![-1,4;4,-17],by decide⟩
  | 579 | 581 | 583 | 585 | 587 | 589 | 591 | 593 | 597 | 599 | 601 | 603 | 605 | 607 | 609 | 611 => ⟨!![7,-2;-17,5],by decide⟩
  | 580 | 582 | 584 | 586 | 588 | 590 | 592 | 594 | 596 | 598 | 600 | 602 | 604 | 606 | 608 | 610 => ⟨!![4,1;-17,-4],by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 34) : List (Fin 37) :=
  match c.val*34+d.val with
  | 34 | 102 | 170 | 238 | 306 | 374 | 442 | 510 | 646 | 714 | 782 | 850 | 918 | 986 | 1054 | 1122 => [36]
  | 35 | 105 | 175 | 245 | 315 | 385 | 455 | 525 | 665 | 735 | 805 | 875 | 945 | 1015 | 1085 | 1155 => [18]
  | 67 | 133 | 199 | 265 | 331 | 397 | 463 | 529 | 661 | 727 | 793 | 859 | 925 | 991 | 1057 | 1123 => [0,36]
  | 101 | 151 | 235 | 285 | 369 | 419 | 503 | 553 | 637 | 687 | 771 | 821 | 905 | 955 | 1039 | 1089 => [36]
  | 69 | 155 | 207 | 293 | 345 | 431 | 483 | 569 | 621 | 707 | 759 | 845 | 897 | 983 | 1035 | 1121 => [36]
  | 45 | 135 | 191 | 247 | 337 | 393 | 449 | 539 | 651 | 741 | 797 | 853 | 943 | 999 | 1055 | 1145 => [36]
  | 57 | 103 | 183 | 263 | 309 | 389 | 469 | 515 | 675 | 721 | 801 | 881 | 927 | 1007 | 1087 | 1133 => [36]
  | 46 | 104 | 196 | 254 | 312 | 404 | 462 | 520 | 670 | 728 | 786 | 878 | 936 | 994 | 1086 | 1144 => [36]
  | 44 | 132 | 186 | 240 | 328 | 382 | 470 | 524 | 666 | 720 | 808 | 862 | 950 | 1004 | 1058 | 1146 => [11,5,0]
  | 93 | 169 | 211 | 287 | 363 | 439 | 481 | 557 | 633 | 709 | 751 | 827 | 903 | 979 | 1021 | 1097 => [36]
  | 56 | 134 | 178 | 256 | 334 | 378 | 456 | 534 | 656 | 734 | 812 | 856 | 934 | 1012 | 1056 | 1134 => [36]
  | 58 | 106 | 188 | 270 | 318 | 400 | 448 | 530 | 660 | 742 | 790 | 872 | 920 | 1002 | 1084 | 1132 => [24,32,36,5]
  | 77 | 137 | 231 | 291 | 351 | 411 | 505 | 565 | 625 | 685 | 779 | 839 | 899 | 959 | 1053 | 1113 => [36]
  | 47 | 107 | 201 | 261 | 321 | 381 | 475 | 535 | 655 | 715 | 809 | 869 | 929 | 989 | 1083 | 1143 => [30,4,34,5,0]
  | 48 | 110 | 172 | 268 | 330 | 392 | 454 | 516 | 674 | 736 | 798 | 860 | 922 | 1018 | 1080 | 1142 => [36]
  | 95 | 139 | 217 | 295 | 373 | 417 | 495 | 573 | 617 | 695 | 773 | 817 | 895 | 973 | 1051 | 1095 => [18,10,36,29]
  | 43 | 129 | 181 | 267 | 319 | 405 | 457 | 543 | 647 | 733 | 785 | 871 | 923 | 1009 | 1061 | 1147 => [11,5,0]
  | 91 | 165 | 205 | 279 | 353 | 427 | 501 | 575 | 615 | 689 | 763 | 837 | 911 | 985 | 1025 | 1099 => [3,19]
  | 61 | 115 | 203 | 257 | 311 | 399 | 453 | 541 | 649 | 737 | 791 | 879 | 933 | 987 | 1075 | 1129 => [36]
  | 40 | 120 | 200 | 246 | 326 | 406 | 452 | 532 | 658 | 738 | 784 | 864 | 944 | 990 | 1070 | 1150 => [3,6]
  | 55 | 131 | 173 | 249 | 325 | 401 | 443 | 519 | 671 | 747 | 789 | 865 | 941 | 1017 | 1059 | 1135 => [2,27,7,32,5]
  | 54 | 128 | 202 | 242 | 316 | 390 | 464 | 538 | 652 | 726 | 800 | 874 | 948 | 988 | 1062 | 1136 => [36]
  | 75 | 167 | 225 | 283 | 341 | 433 | 491 | 549 | 641 | 699 | 757 | 849 | 907 | 965 | 1023 | 1115 => [10,14,6]
  | 59 | 109 | 193 | 243 | 327 | 377 | 461 | 511 | 679 | 729 | 813 | 863 | 947 | 997 | 1081 | 1131 => [24,32,5]
  | 79 | 141 | 237 | 299 | 361 | 423 | 485 | 547 | 643 | 705 | 767 | 829 | 891 | 953 | 1049 | 1111 => [24,17]
  | 41 | 123 | 171 | 253 | 335 | 383 | 465 | 513 | 677 | 725 | 807 | 855 | 937 | 1019 | 1067 | 1149 => [36]
  | 62 | 118 | 174 | 264 | 320 | 376 | 466 | 522 | 668 | 724 | 814 | 870 | 926 | 1016 | 1072 | 1128 => [1,17]
  | 49 | 113 | 177 | 241 | 339 | 403 | 467 | 531 | 659 | 723 | 787 | 851 | 949 | 1013 | 1077 | 1141 => [18,10,36,29]
  | 42 | 126 | 176 | 260 | 310 | 394 | 444 | 528 | 662 | 746 | 796 | 880 | 930 | 1014 | 1064 | 1148 => [11,16,29]
  | 89 | 161 | 233 | 305 | 343 | 415 | 487 | 559 | 631 | 703 | 775 | 847 | 885 | 957 | 1029 | 1101 => [11,15,12]
  | 60 | 112 | 198 | 250 | 336 | 388 | 474 | 526 | 664 | 716 | 802 | 854 | 940 | 992 | 1078 | 1130 => [35,6]
  | 53 | 125 | 197 | 269 | 307 | 379 | 451 | 523 | 667 | 739 | 811 | 883 | 921 | 993 | 1065 | 1137 => [10,14,36,6]
  | 81 | 145 | 209 | 273 | 371 | 435 | 499 | 563 | 627 | 691 | 755 | 819 | 917 | 981 | 1045 | 1109 => [13,15]
  | 50 | 116 | 182 | 248 | 314 | 380 | 446 | 512 | 678 | 744 | 810 | 876 | 942 | 1008 | 1074 | 1140 => [18,10,16,29]
  | 87 | 157 | 227 | 297 | 367 | 437 | 507 | 577 | 613 | 683 | 753 | 823 | 893 | 963 | 1033 | 1103 => [11,34,36,5,0]
  | 52 | 122 | 192 | 262 | 332 | 402 | 472 | 542 | 648 | 718 | 788 | 858 | 928 | 998 | 1068 | 1138 => [10,14,25,6]
  | 83 | 149 | 215 | 281 | 347 | 413 | 479 | 545 | 645 | 711 | 777 | 843 | 909 | 975 | 1041 | 1107 => [24,7,36,32,5]
  | 579 | 581 | 583 | 585 | 587 | 589 | 591 | 593 | 597 | 599 | 601 | 603 | 605 | 607 | 609 | 611 => [36]
  | 580 | 582 | 584 | 586 | 588 | 590 | 592 | 594 | 596 | 598 | 600 | 602 | 604 | 606 | 608 | 610 => [36]
  | _ => []

def edgeTRow (c d : ZMod 34) : List (Fin 37) :=
  match c.val*34+d.val with
  | 1 | 3 | 5 | 7 | 9 | 11 | 13 | 15 | 19 | 21 | 23 | 25 | 27 | 29 | 31 | 33 => [0]
  | 101 | 151 | 235 | 285 | 369 | 419 | 503 | 553 | 637 | 687 | 771 | 821 | 905 | 955 | 1039 | 1089 => [18,36]
  | 45 | 135 | 191 | 247 | 337 | 393 | 449 | 539 | 651 | 741 | 797 | 853 | 943 | 999 | 1055 | 1145 => [36]
  | 93 | 169 | 211 | 287 | 363 | 439 | 481 | 557 | 633 | 709 | 751 | 827 | 903 | 979 | 1021 | 1097 => [11,5,36,0]
  | 47 | 107 | 201 | 261 | 321 | 381 | 475 | 535 | 655 | 715 | 809 | 869 | 929 | 989 | 1083 | 1143 => [18,10,16,22,12]
  | 61 | 115 | 203 | 257 | 311 | 399 | 453 | 541 | 649 | 737 | 791 | 879 | 933 | 987 | 1075 | 1129 => [11,8]
  | 40 | 120 | 200 | 246 | 326 | 406 | 452 | 532 | 658 | 738 | 784 | 864 | 944 | 990 | 1070 | 1150 => [35,6]
  | 54 | 128 | 202 | 242 | 316 | 390 | 464 | 538 | 652 | 726 | 800 | 874 | 948 | 988 | 1062 | 1136 => [10,14,25,9,20]
  | 75 | 167 | 225 | 283 | 341 | 433 | 491 | 549 | 641 | 699 | 757 | 849 | 907 | 965 | 1023 | 1115 => [10,14,36,6]
  | 59 | 109 | 193 | 243 | 327 | 377 | 461 | 511 | 679 | 729 | 813 | 863 | 947 | 997 | 1081 | 1131 => [2,1,17]
  | 41 | 123 | 171 | 253 | 335 | 383 | 465 | 513 | 677 | 725 | 807 | 855 | 937 | 1019 | 1067 | 1149 => [13,34,29]
  | 83 | 149 | 215 | 281 | 347 | 413 | 479 | 545 | 645 | 711 | 777 | 843 | 909 | 975 | 1041 | 1107 => [24,29,36]
  | 51 | 119 | 187 | 255 | 323 | 391 | 459 | 527 | 663 | 731 | 799 | 867 | 935 | 1003 | 1071 | 1139 => [18,10,16,22,7,32,5]
  | 579 | 581 | 583 | 585 | 587 | 589 | 591 | 593 | 597 | 599 | 601 | 603 | 605 | 607 | 609 | 611 => [18,10,36,16,29]
  | 580 | 582 | 584 | 586 | 588 | 590 | 592 | 594 | 596 | 598 | 600 | 602 | 604 | 606 | 608 | 610 => [11,4,36,34,5,0]
  | _ => []
def rep (g : SL(2,ZMod 34)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)

theorem row_primitive (g : SL(2,ZMod 34)) :
    ∃ a b : ZMod 34, a*g.1 1 1-b*g.1 1 0=1 := by
  refine ⟨g.1 0 0,g.1 0 1,?_⟩
  exact (det_fin_two g.1).symm.trans g.det_coe



end SmallLevelThirtyFourGroup
end
end

/-! ## ThirtyFourGroupEdgesSFamilyV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SmallLevelThirtyFourGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups















































end SmallLevelThirtyFourGroup
end
end
end

/-! ## ThirtyFourGroupEdgesTFamilyV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SmallLevelThirtyFourGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups















































end SmallLevelThirtyFourGroup
end
end
end

/-! ## ThirtyFourGroupGeneratorRowsS -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section
namespace SmallLevelThirtyFourGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

theorem edgeSRow_checked : ∀ c d : ZMod 34,(∃ a b : ZMod 34,a*d-b*c=1) →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 34,
    Nat.gcd (Nat.gcd c.val d.val) 34 = 1 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

#print axioms edgeSRow_checked

end SmallLevelThirtyFourGroup
end
end

/-! ## ThirtyFourGroupGeneratorRowsT -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section
namespace SmallLevelThirtyFourGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

theorem edgeTRow_checked : ∀ c d : ZMod 34,(∃ a b : ZMod 34,a*d-b*c=1) →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 34,
    Nat.gcd (Nat.gcd c.val d.val) 34 = 1 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

#print axioms edgeTRow_checked

end SmallLevelThirtyFourGroup
end
end

/-! ## ThirtyFourGroupGenerators -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section
namespace SmallLevelThirtyFourGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups
theorem edgeS_checked (g : SL(2,ZMod 34)) :
    rep g*S*(rep (g*reduction 34 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 34 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 34 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 34)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_primitive g)

theorem edgeT_checked (g : SL(2,ZMod 34)) :
    rep g*T*(rep (g*reduction 34 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 34 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 34 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 34)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_primitive g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 34)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 34, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 18, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 34) : γ∈K := by
  apply transversal_mem (reduction 34) rep K
  · intro g
    rw [edgeS_checked]
    exact word_mem K hK hZ _
  · intro g
    rw [edgeT_checked]
    exact word_mem K hK hZ _
  · exact rep_one
  · apply rep_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ

#print axioms edgeSRow_checked
#print axioms edgeTRow_checked
#print axioms gamma0_mem


end SmallLevelThirtyFourGroup
end
end

/-! ## ThirtyFourGroupKernelMatrixFamilyV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
-- Uniform arithmetic script: some concrete cases close before the final steps.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768

namespace SmallLevelThirtyFourGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm
open SmallLevelThirtyFourPrimeFive (P)
open SmallLevelThirtyFour (B)

theorem kernel_relation_00 :
    SpecialLinearGroup.mapGL ℝ (kernel 0)*kernelRep (targetIndex 0)=
      (if kernelNegative 0 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 0)*kernelGenerator (symbolIndex 0) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![1,1;0,1],by decide⟩ : SL(2,ℤ))*1=
    (1:GL (Fin 2) ℝ)*1*(translation 1)
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_00

theorem kernel_relation_01 :
    SpecialLinearGroup.mapGL ℝ (kernel 1)*kernelRep (targetIndex 1)=
      (if kernelNegative 1 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 1)*kernelGenerator (symbolIndex 1) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![19,1;170,9],by decide⟩ : SL(2,ℤ))*E=
    (1:GL (Fin 2) ℝ)*1*P
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_01

theorem kernel_relation_02 :
    SpecialLinearGroup.mapGL ℝ (kernel 2)*kernelRep (targetIndex 2)=
      (if kernelNegative 2 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 2)*kernelGenerator (symbolIndex 2) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![11,-1;34,-3],by decide⟩ : SL(2,ℤ))*1=
    (1:GL (Fin 2) ℝ)*1*(SpecialLinearGroup.mapGL ℝ Y)
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_02

end SmallLevelThirtyFourGroup
end

section
set_option autoImplicit false
-- Uniform arithmetic script: some concrete cases close before the final steps.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768

namespace SmallLevelThirtyFourGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm
open SmallLevelThirtyFourPrimeFive (P)
open SmallLevelThirtyFour (B)

theorem kernel_relation_03 :
    SpecialLinearGroup.mapGL ℝ (kernel 3)*kernelRep (targetIndex 3)=
      (if kernelNegative 3 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 3)*kernelGenerator (symbolIndex 3) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![37,2;-204,-11],by decide⟩ : SL(2,ℤ))*E=
    (1:GL (Fin 2) ℝ)*1*B
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_03

theorem kernel_relation_04 :
    SpecialLinearGroup.mapGL ℝ (kernel 4)*kernelRep (targetIndex 4)=
      (if kernelNegative 4 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 4)*kernelGenerator (symbolIndex 4) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![35,2;-578,-33],by decide⟩ : SL(2,ℤ))*E=
    (1:GL (Fin 2) ℝ)*E*(translation 1)
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_04

theorem kernel_relation_05 :
    SpecialLinearGroup.mapGL ℝ (kernel 5)*kernelRep (targetIndex 5)=
      (if kernelNegative 5 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 5)*kernelGenerator (symbolIndex 5) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![19,-10;-340,179],by decide⟩ : SL(2,ℤ))*1=
    (1:GL (Fin 2) ℝ)*E*E
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_05

end SmallLevelThirtyFourGroup
end

section
set_option autoImplicit false
-- Uniform arithmetic script: some concrete cases close before the final steps.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768

namespace SmallLevelThirtyFourGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm
open SmallLevelThirtyFourPrimeFive (P)
open SmallLevelThirtyFour (B)

theorem kernel_relation_06 :
    SpecialLinearGroup.mapGL ℝ (kernel 6)*kernelRep (targetIndex 6)=
      (if kernelNegative 6 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 6)*kernelGenerator (symbolIndex 6) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![13,-3;-238,55],by decide⟩ : SL(2,ℤ))*1=
    (-1:GL (Fin 2) ℝ)*E*P
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_06

theorem kernel_relation_07 :
    SpecialLinearGroup.mapGL ℝ (kernel 7)*kernelRep (targetIndex 7)=
      (if kernelNegative 7 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 7)*kernelGenerator (symbolIndex 7) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![91,5;-1802,-99],by decide⟩ : SL(2,ℤ))*E=
    (-1:GL (Fin 2) ℝ)*E*(SpecialLinearGroup.mapGL ℝ Y)
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_07

theorem kernel_relation_08 :
    SpecialLinearGroup.mapGL ℝ (kernel 8)*kernelRep (targetIndex 8)=
      (if kernelNegative 8 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 8)*kernelGenerator (symbolIndex 8) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![23,-4;-408,71],by decide⟩ : SL(2,ℤ))*1=
    (1:GL (Fin 2) ℝ)*E*B
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_08

end SmallLevelThirtyFourGroup
end

section
set_option autoImplicit false
-- Uniform arithmetic script: some concrete cases close before the final steps.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768

namespace SmallLevelThirtyFourGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm
open SmallLevelThirtyFourPrimeFive (P)
open SmallLevelThirtyFour (B)

theorem kernel_relation_09 :
    SpecialLinearGroup.mapGL ℝ (kernel 9)*kernelRep (targetIndex 9)=
      (if kernelNegative 9 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 9)*kernelGenerator (symbolIndex 9) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![1,0;-34,1],by decide⟩ : SL(2,ℤ))*W=
    (1:GL (Fin 2) ℝ)*W*(translation 1)
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_09

theorem kernel_relation_10 :
    SpecialLinearGroup.mapGL ℝ (kernel 10)*kernelRep (targetIndex 10)=
      (if kernelNegative 10 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 10)*kernelGenerator (symbolIndex 10) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![179,10;340,19],by decide⟩ : SL(2,ℤ))*(E*W)=
    (1:GL (Fin 2) ℝ)*W*E
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_10

theorem kernel_relation_11 :
    SpecialLinearGroup.mapGL ℝ (kernel 11)*kernelRep (targetIndex 11)=
      (if kernelNegative 11 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 11)*kernelGenerator (symbolIndex 11) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![89,5;-374,-21],by decide⟩ : SL(2,ℤ))*(E*W)=
    (-1:GL (Fin 2) ℝ)*W*P
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_11

end SmallLevelThirtyFourGroup
end

section
set_option autoImplicit false
-- Uniform arithmetic script: some concrete cases close before the final steps.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768

namespace SmallLevelThirtyFourGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm
open SmallLevelThirtyFourPrimeFive (P)
open SmallLevelThirtyFour (B)

theorem kernel_relation_12 :
    SpecialLinearGroup.mapGL ℝ (kernel 12)*kernelRep (targetIndex 12)=
      (if kernelNegative 12 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 12)*kernelGenerator (symbolIndex 12) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![3,1;-34,-11],by decide⟩ : SL(2,ℤ))*W=
    (-1:GL (Fin 2) ℝ)*W*(SpecialLinearGroup.mapGL ℝ Y)
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_12

theorem kernel_relation_13 :
    SpecialLinearGroup.mapGL ℝ (kernel 13)*kernelRep (targetIndex 13)=
      (if kernelNegative 13 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 13)*kernelGenerator (symbolIndex 13) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![71,4;408,23],by decide⟩ : SL(2,ℤ))*(E*W)=
    (1:GL (Fin 2) ℝ)*W*B
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_13

theorem kernel_relation_14 :
    SpecialLinearGroup.mapGL ℝ (kernel 14)*kernelRep (targetIndex 14)=
      (if kernelNegative 14 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 14)*kernelGenerator (symbolIndex 14) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![307,17;-5508,-305],by decide⟩ : SL(2,ℤ))*(E*W)=
    (1:GL (Fin 2) ℝ)*(E*W)*(translation 1)
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_14

end SmallLevelThirtyFourGroup
end

section
set_option autoImplicit false
-- Uniform arithmetic script: some concrete cases close before the final steps.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 32768

namespace SmallLevelThirtyFourGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm
open SmallLevelThirtyFourPrimeFive (P)
open SmallLevelThirtyFour (B)

theorem kernel_relation_15 :
    SpecialLinearGroup.mapGL ℝ (kernel 15)*kernelRep (targetIndex 15)=
      (if kernelNegative 15 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 15)*kernelGenerator (symbolIndex 15) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![25,3;-442,-53],by decide⟩ : SL(2,ℤ))*W=
    (-1:GL (Fin 2) ℝ)*(E*W)*P
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_15

theorem kernel_relation_16 :
    SpecialLinearGroup.mapGL ℝ (kernel 16)*kernelRep (targetIndex 16)=
      (if kernelNegative 16 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 16)*kernelGenerator (symbolIndex 16) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![581,33;-10370,-589],by decide⟩ : SL(2,ℤ))*(E*W)=
    (-1:GL (Fin 2) ℝ)*(E*W)*(SpecialLinearGroup.mapGL ℝ Y)
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_16

theorem kernel_relation_17 :
    SpecialLinearGroup.mapGL ℝ (kernel 17)*kernelRep (targetIndex 17)=
      (if kernelNegative 17 then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex 17)*kernelGenerator (symbolIndex 17) := by
  change SpecialLinearGroup.mapGL ℝ (⟨!![11,2;-204,-37],by decide⟩ : SL(2,ℤ))*W=
    (-1:GL (Fin 2) ℝ)*(E*W)*B
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [E,P,Y,W,B,fricke,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms kernel_relation_17

end SmallLevelThirtyFourGroup
end
end
end

/-! ## ThirtyFourGroupKernelMatrices -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGroup
open Matrix
open scoped MatrixGroups

theorem kernel_relation (i : Fin 18) :
    SpecialLinearGroup.mapGL ℝ (kernel i)*kernelRep (targetIndex i)=
      (if kernelNegative i then (-1:GL (Fin 2) ℝ) else 1)*
        kernelRep (sourceIndex i)*kernelGenerator (symbolIndex i) := by
  fin_cases i
  · exact kernel_relation_00
  · exact kernel_relation_01
  · exact kernel_relation_02
  · exact kernel_relation_03
  · exact kernel_relation_04
  · exact kernel_relation_05
  · exact kernel_relation_06
  · exact kernel_relation_07
  · exact kernel_relation_08
  · exact kernel_relation_09
  · exact kernel_relation_10
  · exact kernel_relation_11
  · exact kernel_relation_12
  · exact kernel_relation_13
  · exact kernel_relation_14
  · exact kernel_relation_15
  · exact kernel_relation_16
  · exact kernel_relation_17

#print axioms kernel_relation
end SmallLevelThirtyFourGroup
end
end

/-! ## ThirtyFourGroupKernelActions -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm
open SmallLevelThirtyFourPrimeFive (P)
open SmallLevelThirtyFour (B)

theorem P_det : (GeneralLinearGroup.det P : ℝ)=1 := matrix_det _ _ _ _ _

def repCharacter (δ η : ℂ) : Fin 4 → ℂ
  | 0 => 1
  | 1 => δ
  | 2 => η
  | _ => δ*η

def generatorCharacter (δ η : ℂ) : Fin 6 → ℂ
  | 0 => 1
  | 1 => δ
  | 2 => η
  | 3 => δ
  | 4 => 1
  | _ => δ

theorem kernelGenerator_det (j : Fin 6) : (GeneralLinearGroup.det (kernelGenerator j):ℝ)=1 := by
  fin_cases j
  · exact translation_det _
  · exact E_det
  · exact fricke_det 34 (by decide)
  · exact P_det
  · simp [kernelGenerator]
  · exact SmallLevelThirtyFour.B_det

theorem rep_eigen {k : ℤ} (F : ℍ→ℂ) (δ η : ℂ)
    (hE : F ∣[k] E=δ • F) (hW : F ∣[k] W=η • F) (j : Fin 4) :
    F ∣[k] kernelRep j=repCharacter δ η j • F := by
  fin_cases j
  · simp [kernelRep,repCharacter]
  · exact hE
  · exact hW
  · change F ∣[k] (E*W)=(δ*η) • F
    rw [SlashAction.slash_mul,hE,det_one_smul _ (show (GeneralLinearGroup.det W:ℝ)=1 from fricke_det _ _),hW,smul_smul]

theorem generator_eigen {k : ℤ} (F : ℍ→ℂ) (δ η : ℂ)
    (hT : F ∣[k] translation 1=F) (hE : F ∣[k] E=δ • F)
    (hW : F ∣[k] W=η • F) (hP : F ∣[k] P=δ • F)
    (hY : F ∣[k] Y=F) (hB : F ∣[k] B=δ • F) (j : Fin 6) :
    F ∣[k] kernelGenerator j=generatorCharacter δ η j • F := by
  fin_cases j
  · change F ∣[k] translation 1=(1:ℂ) • F
    simpa only [one_smul] using hT
  · exact hE
  · exact hW
  · exact hP
  · change F ∣[k] SpecialLinearGroup.mapGL ℝ Y=(1:ℂ) • F
    rw [one_smul]
    change F ∣[k] SpecialLinearGroup.mapGL ℝ Y=F at hY
    exact hY
  · exact hB

theorem character_relation (δ η : ℂ) (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1) (i : Fin 18) :
    repCharacter δ η (sourceIndex i)*generatorCharacter δ η (symbolIndex i)=
      repCharacter δ η (targetIndex i) := by
  rcases hδ with rfl|rfl <;> rcases hη with rfl|rfl <;> fin_cases i <;>
    norm_num [repCharacter,generatorCharacter,sourceIndex,symbolIndex,targetIndex]

/-- Every integral Schreier generator has trivial character. -/
theorem kernel_invariant (m : ℕ) (F : ℍ→ℂ) (δ η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hT : F ∣[((2*m:ℕ):ℤ)] translation 1=F)
    (hE : F ∣[((2*m:ℕ):ℤ)] E=δ • F)
    (hW : F ∣[((2*m:ℕ):ℤ)] W=η • F)
    (hP : F ∣[((2*m:ℕ):ℤ)] P=δ • F)
    (hY : F ∣[((2*m:ℕ):ℤ)] Y=F)
    (hB : F ∣[((2*m:ℕ):ℤ)] B=δ • F) (i : Fin 18) :
    F ∣[((2*m:ℕ):ℤ)] kernel i=F := by
  let k : ℤ:=((2*m:ℕ):ℤ)
  have hc : F ∣[k] (if kernelNegative i then (-1:GL (Fin 2) ℝ) else 1)=F := by
    split_ifs
    · exact central_even F m
    · simp only [SlashAction.slash_one]
  have hh : (F ∣[k] SpecialLinearGroup.mapGL ℝ (kernel i)) ∣[k] kernelRep (targetIndex i)=
      F ∣[k] kernelRep (targetIndex i) := by
    rw [← SlashAction.slash_mul,kernel_relation,SlashAction.slash_mul,SlashAction.slash_mul,hc,
      rep_eigen F δ η hE hW,det_one_smul _ (kernelGenerator_det _),
      generator_eigen F δ η hT hE hW hP hY hB,smul_smul,character_relation δ η hδ hη,
      rep_eigen F δ η hE hW]
  have he:=congrArg (fun G : ℍ→ℂ => G ∣[k] (kernelRep (targetIndex i))⁻¹) hh
  change F ∣[k] SpecialLinearGroup.mapGL ℝ (kernel i)=F
  simpa only [← SlashAction.slash_mul,mul_assoc,mul_inv_cancel,mul_one,SlashAction.slash_one] using he

#print axioms kernel_invariant
end SmallLevelThirtyFourGroup
end
end

/-! ## ThirtyFourGroupModularCriterion -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized SmallLevelOriginal
open scoped MatrixGroups ModularForm
open SmallLevelThirtyFourPrimeFive (P)

/-- Conditional group endgame. The P and denominator-three G laws remain
explicit analytic obligations; this does not assert level34 modularity before these two laws are supplied. -/
theorem modular_of_P_G (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f)
    (hP : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 34 f 2 • fourierFunction (2*m) f)
    (hG : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Y=fourierFunction (2*m) f) :
    IsModular 34 (2*m) f := by
  let F:=fourierFunction (2*m) f
  obtain ⟨η,hη,hW⟩:=original_fricke_sign (by decide : 0<34) m hf
  have hT : F ∣[((2*m:ℕ):ℤ)] translation 1=F := by
    have ht : translation 1=SpecialLinearGroup.mapGL ℝ T := by
      apply Units.ext; ext a b; fin_cases a <;> fin_cases b <;>
        norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero,T,
          SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
    rw [ht]
    exact original_T _ _
  apply modular_of_transformations (by decide) hf
  intro γ hγ
  let K:=slashStabilizer ((2*m:ℕ):ℤ) F
  change γ∈K
  apply gamma0_mem K ?_ (SmallLevelThirtySix.slash_neg_one_even F m) γ hγ
  intro i
  exact kernel_invariant m F (FinitenessNormalizedTwistProduct.root 34 f 2) η
    (FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2) hη hT
    (SmallLevelThirtyFourGroup.original_E hf) hW hP hG
    (SmallLevelSixEigen.thirty_four_B (by omega) hf) i

#print axioms modular_of_P_G
end SmallLevelThirtyFourGroup
end
end

/-! ## ThirtyFourPrimeFiveWords -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourPrimeFive
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized
open scoped MatrixGroups ModularForm
open SmallLevelThirtyFourGroup (E W Y)
open SmallLevelThirtyFour (A B)

theorem Y_inverse : Y⁻¹=(⟨!![-3,1;-34,11],by decide⟩ : SL(2,ℤ)) := by decide

theorem G2_word : E*translation 1*W*SpecialLinearGroup.mapGL ℝ Y⁻¹*W*E*translation 1=
      (-1:GL (Fin 2) ℝ)*SpecialLinearGroup.mapGL ℝ G2 := by
  rw [Y_inverse]
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E,W,Y,P,A,B,G1,Gm1,G2,Gm2,fricke,translation,matrix,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Matrix.vecMul,dotProduct,
      Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms G2_word

theorem Gm2_word : SpecialLinearGroup.mapGL ℝ Gm2*W*SpecialLinearGroup.mapGL ℝ G2*W=
      (-1:GL (Fin 2) ℝ) := by
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E,W,Y,P,A,B,G1,Gm1,G2,Gm2,fricke,translation,matrix,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Matrix.vecMul,dotProduct,
      Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms Gm2_word

theorem G1_factor : B*P=(-1:GL (Fin 2) ℝ)*SpecialLinearGroup.mapGL ℝ G1 := by
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E,W,Y,P,A,B,G1,Gm1,G2,Gm2,fricke,translation,matrix,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Matrix.vecMul,dotProduct,
      Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms G1_factor

theorem Gm1_factor : P*A=(-1:GL (Fin 2) ℝ)*SpecialLinearGroup.mapGL ℝ Gm1 := by
  have hs : (Real.sqrt 34)^2=34 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 34≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hn2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E,W,Y,P,A,B,G1,Gm1,G2,Gm2,fricke,translation,matrix,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Matrix.vecMul,dotProduct,
      Fin.sum_univ_two] <;> field_simp [hn,hn2] <;>
    nlinarith [congrArg (fun x : ℝ => x*(Real.sqrt 34)^2) ht]

#print axioms Gm1_factor

end SmallLevelThirtyFourPrimeFive
end
end

/-! ## ThirtyFourPrimeFiveKnown -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourPrimeFive
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized
open scoped MatrixGroups ModularForm
open SmallLevelThirtyFourGroup (E W Y)

theorem G2_invariant (m : ℕ) (F : ℍ→ℂ) (δ η : ℂ)
    (hδ : δ=1 ∨ δ= -1) (hη : η=1 ∨ η= -1)
    (hT : F ∣[((2*m:ℕ):ℤ)] translation 1=F)
    (hE : F ∣[((2*m:ℕ):ℤ)] E=δ • F)
    (hW : F ∣[((2*m:ℕ):ℤ)] W=η • F)
    (hY : F ∣[((2*m:ℕ):ℤ)] Y=F) : F ∣[((2*m:ℕ):ℤ)] G2=F := by
  have hYi : F ∣[((2*m:ℕ):ℤ)] Y⁻¹=F :=
    (SmallLevelGenerators.slashStabilizer ((2*m:ℕ):ℤ) F).inv_mem hY
  have hc : F ∣[((2*m:ℕ):ℤ)]
      (E*translation 1*W*SpecialLinearGroup.mapGL ℝ Y⁻¹*W*E*translation 1)=F := by
    change F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ Y⁻¹=F at hYi
    rcases hδ with rfl|rfl <;> rcases hη with rfl|rfl <;>
      simp only [SlashAction.slash_mul,hE,hW,hYi,hT,one_smul,neg_one_smul,
        SlashAction.neg_slash,neg_neg]
  rw [G2_word,SlashAction.slash_mul,central_even F m] at hc
  exact hc

theorem Gm2_invariant (m : ℕ) (F : ℍ→ℂ) (η : ℂ)
    (hη : η=1 ∨ η= -1)
    (hW : F ∣[((2*m:ℕ):ℤ)] W=η • F)
    (hG2 : F ∣[((2*m:ℕ):ℤ)] G2=F) : F ∣[((2*m:ℕ):ℤ)] Gm2=F := by
  let C := W*SpecialLinearGroup.mapGL ℝ G2*W
  have hC : F ∣[((2*m:ℕ):ℤ)] C=F := by
    change F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ G2=F at hG2
    rcases hη with rfl|rfl <;>
      simp only [C,SlashAction.slash_mul,hW,hG2,one_smul,neg_one_smul,
        SlashAction.neg_slash,neg_neg]
  have hm : SpecialLinearGroup.mapGL ℝ Gm2*C=(-1:GL (Fin 2) ℝ) := by
    simpa only [C,mul_assoc] using Gm2_word
  have hh : (F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ Gm2) ∣[((2*m:ℕ):ℤ)] C=
      F ∣[((2*m:ℕ):ℤ)] C := by
    rw [←SlashAction.slash_mul,hm,central_even F m,hC]
  have hi := congrArg (fun H : ℍ→ℂ => H ∣[((2*m:ℕ):ℤ)] C⁻¹) hh
  change F ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ Gm2=F
  simpa only [←SlashAction.slash_mul,mul_assoc,mul_inv_cancel,mul_one,SlashAction.slash_one] using hi

#print axioms G2_invariant
#print axioms Gm2_invariant
end SmallLevelThirtyFourPrimeFive
end
end

/-! ## ThirtyFourPrimeFiveTwoTerm -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourPrimeFive
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm Manifold

/-- The surviving two terms of the prime-five Ramanujan relation
annihilate a holomorphic defect in positive weight. -/
theorem two_term_zero {k : ℕ} (hk : 0<k) (H : ℍ→ℂ)
    (hhol : MDiff H) (δ : ℂ) (hδ : δ=1 ∨ δ= -1)
    (he : δ • (H ∣[(k:ℤ)] translation (1/5))+
      (H ∣[(k:ℤ)] (SmallLevelThirtyFour.B⁻¹*translation (-(1/5))))=0) : H=0 := by
  have ht : translation (1/5)*translation (-(1/5))=1 := by
    rw [translation_mul]
    norm_num
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero]
  have hb : SmallLevelThirtyFour.B⁻¹*translation (-(1/5))*translation (-(1/5))=K := by
    rw [SmallLevelThirtyFour.B_inverse,inv_inv,mul_assoc,translation_mul]
    norm_num [K]
  have hh := congrArg (fun F : ℍ→ℂ => F ∣[(k:ℤ)] translation (-(1/5))) he
  simp only [SlashAction.add_slash,det_one_smul _ (translation_det _),
    ←SlashAction.slash_mul,ht,hb,SlashAction.slash_one,SlashAction.zero_slash] at hh
  have hK : H ∣[(k:ℤ)] K=(-δ) • H := by
    rcases hδ with rfl|rfl
    · simpa only [one_smul,neg_one_smul] using eq_neg_of_add_eq_zero_right hh
    · simpa only [neg_one_smul,neg_neg,one_smul] using eq_neg_of_add_eq_zero_right hh
  have hn : -δ=1 ∨ -δ= -1 := by rcases hδ with rfl|rfl <;> simp
  exact sign_eigen_zero hk H hhol (-δ) hn hK

#print axioms two_term_zero
end SmallLevelThirtyFourPrimeFive
end
end

/-! ## ThirtyFourPrimeFivePFromG -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourPrimeFive
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized SmallLevelOriginal SmallLevelGenerators
open scoped MatrixGroups ModularForm Manifold
open SmallLevelThirtyFourGroup (E W Y)
open SmallLevelThirtyFour (A B)

theorem P_of_two_center_relation (m : ℕ) (hm : 0<m) (F : ℍ→ℂ)
    (hhol : MDiff F) (δ : ℂ) (hδ : δ=1 ∨ δ= -1)
    (hA : F ∣[((2*m:ℕ):ℤ)] A=δ • F)
    (hB : F ∣[((2*m:ℕ):ℤ)] B=δ • F)
    (hp : ((F ∣[((2*m:ℕ):ℤ)] G1)-F) ∣[((2*m:ℕ):ℤ)] translation (1/5)+
      ((F ∣[((2*m:ℕ):ℤ)] Gm1)-F) ∣[((2*m:ℕ):ℤ)] translation (-(1/5))=0) :
    F ∣[((2*m:ℕ):ℤ)] P=δ • F := by
  let H := (F ∣[((2*m:ℕ):ℤ)] P)-δ • F
  have hc1 := congrArg (fun M : GL (Fin 2) ℝ => F ∣[((2*m:ℕ):ℤ)] M) G1_factor
  rw [SlashAction.slash_mul,hB,det_one_smul _ SmallLevelThirtyFourGroup.P_det,
    SlashAction.slash_mul,central_even F m] at hc1
  change δ • (F ∣[((2*m:ℕ):ℤ)] P)=F ∣[((2*m:ℕ):ℤ)] G1 at hc1
  have h1 : (F ∣[((2*m:ℕ):ℤ)] G1)-F=δ • H := by
    rw [←hc1]
    rcases hδ with rfl|rfl <;> simp [H,sub_eq_add_neg]
  have hc2 := congrArg (fun M : GL (Fin 2) ℝ => F ∣[((2*m:ℕ):ℤ)] M) Gm1_factor
  rw [SlashAction.slash_mul,SlashAction.slash_mul,central_even F m] at hc2
  change (F ∣[((2*m:ℕ):ℤ)] P) ∣[((2*m:ℕ):ℤ)] A=F ∣[((2*m:ℕ):ℤ)] Gm1 at hc2
  have h2 : (F ∣[((2*m:ℕ):ℤ)] Gm1)-F=H ∣[((2*m:ℕ):ℤ)] A := by
    rw [←hc2]
    dsimp only [H]
    rw [SmallLevelEleven.sub_slash,det_one_smul _ SmallLevelThirtyFour.A_det,hA,smul_smul]
    rcases hδ with rfl|rfl <;> simp
  have hs : MDiff (δ • F) := by
    rcases hδ with rfl|rfl
    · simpa only [one_smul] using hhol
    · simpa only [neg_one_smul] using hhol.neg
  have hz : H=0 := by
    apply two_term_zero (by omega : 0<2*m) H ((hhol.slash _ P).sub hs) δ hδ
    rw [h1,h2,det_one_smul _ (translation_det _),←SlashAction.slash_mul] at hp
    simpa only [SmallLevelThirtyFour.B_inverse,inv_inv] using hp
  exact sub_eq_zero.mp hz

/-- All prime-five work reduces to the denominator-three invariance law.
That law still requires the independent twist pole-removal argument. -/
theorem original_P_of_G (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f)
    (hG : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Y=fourierFunction (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] P=
      FinitenessNormalizedTwistProduct.root 34 f 2 • fourierFunction (2*m) f := by
  let F := fourierFunction (2*m) f
  let δ := FinitenessNormalizedTwistProduct.root 34 f 2
  have hδ := FinitenessNormalizedTwistProduct.root_unit hf.toEulerData 2
  obtain ⟨η,hη,hW⟩ := original_fricke_sign (by decide : 0<34) m hf
  have hT : F ∣[((2*m:ℕ):ℤ)] translation 1=F := by
    have ht : translation 1=SpecialLinearGroup.mapGL ℝ T := by
      apply Units.ext; ext a b; fin_cases a <;> fin_cases b <;>
        norm_num [translation,matrix,GeneralLinearGroup.mkOfDetNeZero,T,
          SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe]
    rw [ht]
    exact original_T _ _
  have h2 := G2_invariant m F δ η hδ hη hT
    (SmallLevelThirtyFourGroup.original_E hf) hW hG
  have hm2 := Gm2_invariant m F η hη hW h2
  have hp := original_defect_sum hf
  change ((F ∣[((2*m:ℕ):ℤ)] G1)-F) ∣[((2*m:ℕ):ℤ)] translation (1/5)+
    ((F ∣[((2*m:ℕ):ℤ)] Gm1)-F) ∣[((2*m:ℕ):ℤ)] translation (-(1/5))+
    ((F ∣[((2*m:ℕ):ℤ)] G2)-F) ∣[((2*m:ℕ):ℤ)] translation (-(2/5))+
    ((F ∣[((2*m:ℕ):ℤ)] Gm2)-F) ∣[((2*m:ℕ):ℤ)] translation (2/5)=0 at hp
  simp only [h2,hm2,sub_self,SlashAction.zero_slash,add_zero] at hp
  exact P_of_two_center_relation m hm F (fourierFunction_holomorphic hf) δ hδ
    (SmallLevelSixEigen.thirty_four_A (by omega) hf)
    (SmallLevelSixEigen.thirty_four_B (by omega) hf) hp

#print axioms P_of_two_center_relation
#print axioms original_P_of_G
end SmallLevelThirtyFourPrimeFive
end
end

/-! ## ThirtyFourModularFromThree -/
section
set_option autoImplicit false
@[expose] public noncomputable section
namespace SmallLevelThirtyFourGroup
open UpperHalfPlane SmallLevelOriginal
open scoped ModularForm

/-- The remaining analytic obligation is the denominator-three law.
This conditional reduction does not assert that pole removal is complete. -/
theorem modular_of_G (m : ℕ) (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f)
    (hG : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Y=fourierFunction (2*m) f) :
    IsModular 34 (2*m) f :=
  modular_of_P_G m hm hf (SmallLevelThirtyFourPrimeFive.original_P_of_G m hm hf hG) hG

#print axioms modular_of_G
end SmallLevelThirtyFourGroup
end
end

/-! ## ThirtyFourOriginalModular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace SmallLevelThirtyFourChiThree
open Complex Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessOriginalFourier FinitenessFourierConstruction
open scoped MatrixGroups ModularForm

theorem original_Y {m : ℕ} (hm : 0<m) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SmallLevelThirtyFourGroup.Y=
      fourierFunction (2*m) f := by
  obtain ⟨ε,_hε,hlaw,hquad⟩:=original_quadratic_fricke hm hf
  have hF : ∀ z : ℂ,0<z.im → fourier (fullCoefficients f (2*m)) z=
      (ε*Complex.I^(2*m))/(((Real.sqrt 34:ℂ)*z)^(2*m))*
        fourier (fullCoefficients f (2*m)) (-1/((34:ℂ)*z)) := by
    intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  have hind:=individual_laws ε hlaw hquad
  have h:=crossed_of_fricke 34 306 (2*m) (by decide) (by decide) (1/3) (-(1/3))
    _ (ε*Complex.I^(2*m)) hF (by
      intro z hz
      simpa only [Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat,
        Complex.ofReal_one,Nat.cast_ofNat,sub_eq_add_neg] using (hind z hz).1)
  rw [crossed_conjugate] at h
  exact Y_of_crossed m _ h

/-- Literal original level34 converse statement. This source is only a
completed formalization after its entire dependency closure is Lean checked. -/
theorem level_thirty_four {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ→ℂ}
    (hf : FinitenessOriginalInput.IsSolution 34 k f) : IsModular 34 k f := by
  obtain ⟨m,hm⟩:=heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  exact SmallLevelThirtyFourGroup.modular_of_G m (by omega) hf (original_Y (by omega) hf)

#print axioms original_Y
#print axioms level_thirty_four
end SmallLevelThirtyFourChiThree
end
end
