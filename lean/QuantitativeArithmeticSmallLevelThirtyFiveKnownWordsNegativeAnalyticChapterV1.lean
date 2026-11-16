module
public meta import SmallLevelCertificateBatchCommandV1
public import QuantitativeArithmeticSmallLevelThirtyFiveKnownWordsOriginalRowsChapterV1

public import QuantitativeArithmeticAnalyticGermTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRowsTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveFullTaylorLaurentV1
public import QuantitativeArithmeticSmallLevelThirtyFiveJetCertificateTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveNegativeRootsV1
public import QuantitativeArithmeticSmallLevelThirtyFivePoleFullRowsV1
public import QuantitativeArithmeticSmallLevelThirtyFivePoleHeckeTwoV1
public import QuantitativeArithmeticSmallLevelThirtyFivePoleWordRowsV1
public import QuantitativeArithmeticSmallLevelThirtyFivePositiveAnalyticShortRowsTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyFiveSignedLaurentV1
public import QuantitativeArithmeticSmallLevelThirtyFiveSignedSourceRowsV1
public import QuantitativeArithmeticSmallLevelThirtyFiveWordWitnessFamilyV4
set_option Elab.async false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelThirtyFiveKnownWords. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveAnalyticClosedSourcesBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Matrix Filter Set FinitenessRamanujanSum FinitenessNormalizedTwistProduct
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

certificate_batch {
theorem analytic_short_source_54 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 63 + (((primeParameter 3 m z)^(2:ℕ)*(u7*primeParameter 7 m z))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 190) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 63, target := -20
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 63=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 63)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 63 0 z*
    (G z) (gridIndex (-20))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 63 0 z=wordCoefficient m (-u5*u7) witnessWord002 63 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 63 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 63 (-2,2,-1,1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_54

theorem analytic_short_source_62 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 105 + (((u5*primeParameter 5 m z)*(u7*primeParameter 7 m z))/((primeParameter 2 m z)^(2:ℕ)))*G z 198) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 105, target := -12
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 105=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 105)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 105 0 z*
    (G z) (gridIndex (-12))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 105 0 z=wordCoefficient m (-u5*u7) witnessWord002 105 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 105 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 105 (-2,0,1,1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_62

theorem analytic_short_source_292 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 111 + ((-1)/((primeParameter 2 m z)^(2:ℕ)))*G z 186) s := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 111, target := -24
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 111=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 111)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 111 0 z*
    (G z) (gridIndex (-24))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 111 0 z=wordCoefficient m (-u5*u7) witnessWord029 111 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 111 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 111 (-2,0,0,0) hr hcompat z]
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_292

theorem analytic_short_source_320 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((-1)/((primeParameter 3 m z)^(2:ℕ)))*G z 30 + (1)*G z 100) s := by
  let r : ClosedWordRow := {
    word := witnessWord030, source := 100, target := 30
    nonaffine := by norm_num [witnessWord030_matrix]
    denominator := by norm_num [integerDen,witnessWord030_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord030_matrix] }
  have hr : rationalRate witnessWord030 100=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord030_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 100)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord030 100 0 z*
    (G z) (gridIndex (30))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord030 100 0 z=wordCoefficient m (-u5*u7) witnessWord030 100 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord030 100 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord030)=
      (-1:ℂ)^(frickeCount witnessWord030)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord030 100 (0,-2,0,0) hr hcompat z]
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_320

theorem analytic_short_source_370 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((-1)*(primeParameter 3 m z)^(2:ℕ))*G z 38 + (1)*G z 156) s := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 156, target := 38
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 156=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 156)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 156 0 z*
    (G z) (gridIndex (38))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 156 0 z=wordCoefficient m (-u5*u7) witnessWord042 156 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 156 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 156 (0,2,0,0) hr hcompat z]
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_370

theorem analytic_short_source_394 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((-1)*(primeParameter 2 m z)^(2:ℕ))/((primeParameter 3 m z)^(2:ℕ)))*G z 27 + (1)*G z 178) s := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 178, target := 27
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 178=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 178)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 178 0 z*
    (G z) (gridIndex (27))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 178 0 z=wordCoefficient m (-u5*u7) witnessWord042 178 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 178 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 178 (2,-2,0,0) hr hcompat z]
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_394

theorem analytic_short_source_2858 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((1)/((u7*primeParameter 7 m z)))*G z 0 + ((1)/((u7*primeParameter 7 m z)))*G z 42 + (1)*G z 48 + ((1)/((u7*primeParameter 7 m z)))*G z 84 + (1)*G z 90 + ((1)/((u7*primeParameter 7 m z)))*G z 126 + (1)*G z 132 + (1)*G z 174) s := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((6:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    5 (by decide) (by decide) (6) 252 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = ((1)/((u7*primeParameter 7 m z)))*G z 0 + ((1)/((u7*primeParameter 7 m z)))*G z 42 + (1)*G z 48 + ((1)/((u7*primeParameter 7 m z)))*G z 84 + (1)*G z 90 + ((1)/((u7*primeParameter 7 m z)))*G z 126 + (1)*G z 132 + (1)*G z 174
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (6) (0,0,0,-1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2858

theorem analytic_short_source_2870 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 21 + (1)*G z 54 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 63 + (1)*G z 96 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 105 + (1)*G z 138 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 147 + (1)*G z 180) s := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((12:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    5 (by decide) (by decide) (12) 252 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 21 + (1)*G z 54 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 63 + (1)*G z 96 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 105 + (1)*G z 138 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 147 + (1)*G z 180
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (12) (2,0,0,-1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2870

theorem analytic_short_source_2942 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((1)/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 0 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 30 + (1)*G z 33 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 60 + (1)*G z 63 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 90 + (1)*G z 93 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 120 + (1)*G z 123 + (1)*G z 153 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 180 + (1)*G z 183) s := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((3:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    7 (by decide) (by decide) (3) 180 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = ((1)/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 0 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 30 + (1)*G z 33 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 60 + (1)*G z 63 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 90 + (1)*G z 93 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 120 + (1)*G z 123 + (1)*G z 153 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 180 + (1)*G z 183
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (3) (-2,0,-1,0) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2942

theorem analytic_short_source_2952 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 6 + (1)*G z 25 + (1)*G z 55 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 66 + (1)*G z 85 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 96 + (1)*G z 115 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 126 + (1)*G z 145 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 156 + (1)*G z 175 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 186) s := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((-5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    7 (by decide) (by decide) (-5) 180 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 6 + (1)*G z 25 + (1)*G z 55 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 66 + (1)*G z 85 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 96 + (1)*G z 115 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 126 + (1)*G z 145 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 156 + (1)*G z 175 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 186
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (-5) (-2,-2,1,0) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2952

theorem analytic_short_source_2954 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((1)/((u5*primeParameter 5 m z)))*G z 0 + ((1)/((u5*primeParameter 5 m z)))*G z 30 + (1)*G z 36 + ((1)/((u5*primeParameter 5 m z)))*G z 60 + (1)*G z 66 + ((1)/((u5*primeParameter 5 m z)))*G z 90 + (1)*G z 96 + ((1)/((u5*primeParameter 5 m z)))*G z 120 + (1)*G z 126 + ((1)/((u5*primeParameter 5 m z)))*G z 150 + (1)*G z 156 + (1)*G z 186) s := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((6:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    7 (by decide) (by decide) (6) 180 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = ((1)/((u5*primeParameter 5 m z)))*G z 0 + ((1)/((u5*primeParameter 5 m z)))*G z 30 + (1)*G z 36 + ((1)/((u5*primeParameter 5 m z)))*G z 60 + (1)*G z 66 + ((1)/((u5*primeParameter 5 m z)))*G z 90 + (1)*G z 96 + ((1)/((u5*primeParameter 5 m z)))*G z 120 + (1)*G z 126 + ((1)/((u5*primeParameter 5 m z)))*G z 150 + (1)*G z 156 + (1)*G z 186
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (6) (0,0,-1,0) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2954

theorem analytic_short_source_2958 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 10 + (1)*G z 39 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 40 + (1)*G z 69 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 70 + (1)*G z 99 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 100 + (1)*G z 129 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 130 + (1)*G z 159 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 160 + (1)*G z 189) s := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((9:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    7 (by decide) (by decide) (9) 180 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 10 + (1)*G z 39 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 40 + (1)*G z 69 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 70 + (1)*G z 99 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 100 + (1)*G z 129 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 130 + (1)*G z 159 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 160 + (1)*G z 189
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (9) (-2,2,-1,0) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2958

theorem analytic_short_source_2964 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 20 + (((u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 48 + (1)*G z 50 + (((u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 78 + (1)*G z 80 + (((u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 108 + (1)*G z 110 + (((u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 138 + (1)*G z 140 + (((u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 168 + (1)*G z 170 + (((u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 198) s := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((-10:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    7 (by decide) (by decide) (-10) 180 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 20 + (((u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 48 + (1)*G z 50 + (((u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 78 + (1)*G z 80 + (((u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 108 + (1)*G z 110 + (((u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 138 + (1)*G z 140 + (((u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 168 + (1)*G z 170 + (((u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 198
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (-10) (0,-2,1,0) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2964

theorem analytic_short_source_2968 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 18 + (((primeParameter 2 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 45 + (1)*G z 48 + (((primeParameter 2 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 75 + (1)*G z 78 + (((primeParameter 2 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 105 + (1)*G z 108 + (((primeParameter 2 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 135 + (1)*G z 138 + (((primeParameter 2 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 165 + (1)*G z 168 + (((primeParameter 2 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 195) s := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((-12:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    7 (by decide) (by decide) (-12) 180 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 18 + (((primeParameter 2 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 45 + (1)*G z 48 + (((primeParameter 2 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 75 + (1)*G z 78 + (((primeParameter 2 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 105 + (1)*G z 108 + (((primeParameter 2 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 135 + (1)*G z 138 + (((primeParameter 2 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 165 + (1)*G z 168 + (((primeParameter 2 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 195
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (-12) (2,0,-1,0) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2968

theorem analytic_short_source_2978 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 21 + (1)*G z 50 + (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 51 + (1)*G z 80 + (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 81 + (1)*G z 110 + (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 111 + (1)*G z 140 + (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 141 + (1)*G z 170 + (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 171 + (1)*G z 200) s := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((20:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    7 (by decide) (by decide) (20) 180 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 21 + (1)*G z 50 + (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 51 + (1)*G z 80 + (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 81 + (1)*G z 110 + (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 111 + (1)*G z 140 + (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 141 + (1)*G z 170 + (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 171 + (1)*G z 200
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (20) (2,-2,1,0) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2978

theorem analytic_short_source_3046 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 10 + (1)*G z 24 + (((primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 40 + (1)*G z 54 + (((primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 70 + (1)*G z 84 + (((primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 130 + (1)*G z 144 + (((primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 160 + (1)*G z 174 + (((primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 190 + (1)*G z 204) s := by
  have hroot : root 35 f 14=u7 := by simp [root_signed_14,h5,h7]
  have hr : (Nat.lcm 35 (14^2):ℚ)*((9:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 14*ε*I^(2*m)= -u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    14 (by decide) (by decide) (9) 45 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (((primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 10 + (1)*G z 24 + (((primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 40 + (1)*G z 54 + (((primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 70 + (1)*G z 84 + (((primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 130 + (1)*G z 144 + (((primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 160 + (1)*G z 174 + (((primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)))*G z 190 + (1)*G z 204
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 14 (9) (0,2,-1,0) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3046

theorem analytic_short_source_3158 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 5 + (1)*G z 25 + (1)*G z 55 + (1)*G z 65 + (1)*G z 85 + (1)*G z 95 + (1)*G z 115 + (1)*G z 125 + (1)*G z 145 + (1)*G z 155 + (1)*G z 185 + (1)*G z 205) s := by
  have hh := analytic_full_entire hm hf BG G hG hGF s 42 (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 5 + (1)*G z 25 + (1)*G z 55 + (1)*G z 65 + (1)*G z 85 + (1)*G z 95 + (1)*G z 115 + (1)*G z 125 + (1)*G z 145 + (1)*G z 155 + (1)*G z 185 + (1)*G z 205
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3158

theorem analytic_short_source_3174 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (2)*G z 0 + (2)*G z 6 + (1)*G z 12 + (1)*G z 24 + (2)*G z 30 + (2)*G z 36 + (1)*G z 42 + (1)*G z 48 + (2)*G z 54 + (1)*G z 60 + (1)*G z 66 + (1)*G z 72 + (1)*G z 78 + (2)*G z 84 + (2)*G z 90 + (2)*G z 96 + (1)*G z 102 + (1)*G z 108 + (2)*G z 114 + (2)*G z 120 + (2)*G z 126 + (1)*G z 132 + (1)*G z 138 + (1)*G z 144 + (1)*G z 150 + (2)*G z 156 + (1)*G z 162 + (1)*G z 168 + (2)*G z 174 + (2)*G z 180 + (1)*G z 186 + (1)*G z 198 + (2)*G z 204) s := by
  have hroot : root 35 f 70=u5*u7 := by simp [root_signed_70,h5,h7]
  have hr : (Nat.lcm 35 (70^2):ℚ)*((3:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 70*ε*I^(2*m)= -u5^(0:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    70 (by decide) (by decide) (3) 9 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (2)*G z 0 + (2)*G z 6 + (1)*G z 12 + (1)*G z 24 + (2)*G z 30 + (2)*G z 36 + (1)*G z 42 + (1)*G z 48 + (2)*G z 54 + (1)*G z 60 + (1)*G z 66 + (1)*G z 72 + (1)*G z 78 + (2)*G z 84 + (2)*G z 90 + (2)*G z 96 + (1)*G z 102 + (1)*G z 108 + (2)*G z 114 + (2)*G z 120 + (2)*G z 126 + (1)*G z 132 + (1)*G z 138 + (1)*G z 144 + (1)*G z 150 + (2)*G z 156 + (1)*G z 162 + (1)*G z 168 + (2)*G z 174 + (2)*G z 180 + (1)*G z 186 + (1)*G z 198 + (2)*G z 204
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 70 (3) (0,0,0,0) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3174

theorem analytic_short_source_3256 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 27 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 54 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 108 + (1)*G z 132) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 27
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 27 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 54 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 108 + (1)*G z 132
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3256

theorem analytic_short_source_3274 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 36 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 72 + (1)*G z 141 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 144) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 36
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 36 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 72 + (1)*G z 141 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 144
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3274

theorem analytic_short_source_3298 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 48 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 96 + (1)*G z 153 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 192) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 48
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 48 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 96 + (1)*G z 153 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 192
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3298

theorem analytic_short_source_3340 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 66 + (1)*G z 69 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 138 + (1)*G z 174) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 69
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 66 + (1)*G z 69 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 138 + (1)*G z 174
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3340

theorem analytic_short_source_3376 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 87 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 138 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 174 + (1)*G z 192) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 87
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 87 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 138 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 174 + (1)*G z 192
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3376

theorem analytic_short_source_3488 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 38 + (1)*G z 108 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 114 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 132 + (1)*G z 178) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 3 (by decide) (by decide) 38
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 38 + (1)*G z 108 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 114 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 132 + (1)*G z 178
  have hp : (3:ℂ)^((m:ℂ)-z)=(primeParameter 3 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3488

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveAnalyticFourthSourcesBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Matrix Filter Set FinitenessRamanujanSum FinitenessNormalizedTwistProduct
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

certificate_batch {
theorem analytic_short_source_0 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 0 + ((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)*(u7*primeParameter 7 m z))*G z 207) s := by
  let r : ClosedWordRow := {
    word := witnessWord000, source := 0, target := -3
    nonaffine := by norm_num [witnessWord000_matrix]
    denominator := by norm_num [integerDen,witnessWord000_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord000_matrix] }
  have hr : rationalRate witnessWord000 0=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord000_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 0)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord000 0 0 z*
    (G z) (gridIndex (-3))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord000 0 0 z=wordCoefficient m (-u5*u7) witnessWord000 0 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord000 0 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord000)=
      (-1:ℂ)^(frickeCount witnessWord000)*u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord000_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord000 0 (2,0,1,1) hr hcompat z]
  norm_num [witnessWord000_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_0

theorem analytic_short_source_2 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 0 + ((u5*primeParameter 5 m z)*(u7*primeParameter 7 m z))*G z 204) s := by
  let r : ClosedWordRow := {
    word := witnessWord001, source := 0, target := -6
    nonaffine := by norm_num [witnessWord001_matrix]
    denominator := by norm_num [integerDen,witnessWord001_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord001_matrix] }
  have hr : rationalRate witnessWord001 0=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord001_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 0)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord001 0 0 z*
    (G z) (gridIndex (-6))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord001 0 0 z=wordCoefficient m (-u5*u7) witnessWord001 0 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord001 0 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord001)=
      (-1:ℂ)^(frickeCount witnessWord001)*u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord001_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord001 0 (0,0,1,1) hr hcompat z]
  norm_num [witnessWord001_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2

theorem analytic_short_source_4 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 42 + (((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)*(u7*primeParameter 7 m z))/((u5*primeParameter 5 m z)))*G z 205) s := by
  let r : ClosedWordRow := {
    word := witnessWord001, source := 42, target := -5
    nonaffine := by norm_num [witnessWord001_matrix]
    denominator := by norm_num [integerDen,witnessWord001_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord001_matrix] }
  have hr : rationalRate witnessWord001 42=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord001_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 42)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord001 42 0 z*
    (G z) (gridIndex (-5))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord001 42 0 z=wordCoefficient m (-u5*u7) witnessWord001 42 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord001 42 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord001)=
      (-1:ℂ)^(frickeCount witnessWord001)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord001_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord001 42 (2,2,-1,1) hr hcompat z]
  norm_num [witnessWord001_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_4

theorem analytic_short_source_8 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 0) s := by
  have h := analytic_full_entire hm hf BG G hG hGF s 1 (by decide) (by decide)
  simpa [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex] using h

#print axioms analytic_short_source_8

theorem analytic_short_source_12 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((1)/((primeParameter 3 m z)^(2:ℕ)*(u5*primeParameter 5 m z)*(u7*primeParameter 7 m z)))*G z 0 + (1)*G z 2) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 2, target := -630
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 2)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 2 0 z*
    (G z) (gridIndex (-630))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 2 0 z=wordCoefficient m (-u5*u7) witnessWord002 2 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 2 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 2 (0,-2,-1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_12

theorem analytic_short_source_16 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 4 + (((primeParameter 2 m z)^(2:ℕ))/((primeParameter 3 m z)^(2:ℕ)*(u5*primeParameter 5 m z)*(u7*primeParameter 7 m z)))*G z 105) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 4, target := -315
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 4=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 4)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 4 0 z*
    (G z) (gridIndex (-315))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 4 0 z=wordCoefficient m (-u5*u7) witnessWord002 4 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 4 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 4 (2,-2,-1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_16

theorem analytic_short_source_18 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 5 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 168) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 5, target := -252
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 5=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 5)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 5 0 z*
    (G z) (gridIndex (-252))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 5 0 z=wordCoefficient m (-u5*u7) witnessWord002 5 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 5 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 5 (-2,-2,1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_18

theorem analytic_short_source_20 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((1)/((u5*primeParameter 5 m z)*(u7*primeParameter 7 m z)))*G z 0 + (1)*G z 6) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 6, target := -210
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 6=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 6)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 6 0 z*
    (G z) (gridIndex (-210))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 6 0 z=wordCoefficient m (-u5*u7) witnessWord002 6 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 6 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 6 (0,0,-1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_20

theorem analytic_short_source_28 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 12 + (((primeParameter 2 m z)^(2:ℕ))/((u5*primeParameter 5 m z)*(u7*primeParameter 7 m z)))*G z 105) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 12, target := -105
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 12=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 12)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 12 0 z*
    (G z) (gridIndex (-105))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 12 0 z=wordCoefficient m (-u5*u7) witnessWord002 12 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 12 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 12 (2,0,-1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_28

theorem analytic_short_source_34 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 18 + (((primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)*(u7*primeParameter 7 m z)))*G z 140) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 18, target := -70
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 18=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 18)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 18 0 z*
    (G z) (gridIndex (-70))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 18 0 z=wordCoefficient m (-u5*u7) witnessWord002 18 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 18 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 18 (0,2,-1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_34

theorem analytic_short_source_36 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 20 + (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 147) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 20, target := -63
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 20=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 20)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 20 0 z*
    (G z) (gridIndex (-63))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 20 0 z=wordCoefficient m (-u5*u7) witnessWord002 20 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 20 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 20 (2,-2,1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_36

theorem analytic_short_source_44 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 35 + (((u5*primeParameter 5 m z)*(u7*primeParameter 7 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 174) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 35, target := -36
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 35=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 35)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 35 0 z*
    (G z) (gridIndex (-36))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 35 0 z=wordCoefficient m (-u5*u7) witnessWord002 35 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 35 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 35 (-2,-2,1,1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_44

theorem analytic_short_source_46 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 36 + (((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ))/((u5*primeParameter 5 m z)*(u7*primeParameter 7 m z)))*G z 175) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 36, target := -35
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 36=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 36)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 36 0 z*
    (G z) (gridIndex (-35))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 36 0 z=wordCoefficient m (-u5*u7) witnessWord002 36 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 36 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 36 (2,2,-1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_46

theorem analytic_short_source_56 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 70 + (((u5*primeParameter 5 m z)*(u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 192) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 70, target := -18
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 70=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 70)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 70 0 z*
    (G z) (gridIndex (-18))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 70 0 z=wordCoefficient m (-u5*u7) witnessWord002 70 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 70 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 70 (0,-2,1,1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_56

theorem analytic_short_source_66 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 140 + (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)*(u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 201) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 140, target := -9
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 140=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 140)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 140 0 z*
    (G z) (gridIndex (-9))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 140 0 z=wordCoefficient m (-u5*u7) witnessWord002 140 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 140 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 140 (2,-2,1,1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_66

theorem analytic_short_source_128 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((1)/((primeParameter 3 m z)^(2:ℕ)*(u5*primeParameter 5 m z)*(u7*primeParameter 7 m z)))*G z 0 + (1)*G z 208) s := by
  let r : ClosedWordRow := {
    word := witnessWord003, source := 208, target := 630
    nonaffine := by norm_num [witnessWord003_matrix]
    denominator := by norm_num [integerDen,witnessWord003_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord003_matrix] }
  have hr : rationalRate witnessWord003 208=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord003_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 208)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord003 208 0 z*
    (G z) (gridIndex (630))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord003 208 0 z=wordCoefficient m (-u5*u7) witnessWord003 208 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord003 208 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord003)=
      (-1:ℂ)^(frickeCount witnessWord003)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord003_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord003 208 (0,-2,-1,-1) hr hcompat z]
  norm_num [witnessWord003_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_128

theorem analytic_short_source_150 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((-1)*(primeParameter 3 m z)^(2:ℕ))*G z 8 + (1)*G z 186) s := by
  let r : ClosedWordRow := {
    word := witnessWord009, source := 186, target := 8
    nonaffine := by norm_num [witnessWord009_matrix]
    denominator := by norm_num [integerDen,witnessWord009_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord009_matrix] }
  have hr : rationalRate witnessWord009 186=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord009_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 186)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord009 186 0 z*
    (G z) (gridIndex (8))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord009 186 0 z=wordCoefficient m (-u5*u7) witnessWord009 186 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord009 186 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord009)=
      (-1:ℂ)^(frickeCount witnessWord009)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord009_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord009 186 (0,2,0,0) hr hcompat z]
  norm_num [witnessWord009_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_150

theorem analytic_short_source_162 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((-1)/((primeParameter 3 m z)^(2:ℕ)))*G z 24 + (1)*G z 202) s := by
  let r : ClosedWordRow := {
    word := witnessWord009, source := 202, target := 24
    nonaffine := by norm_num [witnessWord009_matrix]
    denominator := by norm_num [integerDen,witnessWord009_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord009_matrix] }
  have hr : rationalRate witnessWord009 202=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord009_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 202)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord009 202 0 z*
    (G z) (gridIndex (24))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord009 202 0 z=wordCoefficient m (-u5*u7) witnessWord009 202 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord009 202 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord009)=
      (-1:ℂ)^(frickeCount witnessWord009)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord009_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord009 202 (0,-2,0,0) hr hcompat z]
  norm_num [witnessWord009_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_162

theorem analytic_short_source_246 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 102 + ((-1)*(primeParameter 3 m z)^(2:ℕ))*G z 208) s := by
  let r : ClosedWordRow := {
    word := witnessWord027, source := 102, target := -2
    nonaffine := by norm_num [witnessWord027_matrix]
    denominator := by norm_num [integerDen,witnessWord027_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord027_matrix] }
  have hr : rationalRate witnessWord027 102=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord027_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 102)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord027 102 0 z*
    (G z) (gridIndex (-2))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord027 102 0 z=wordCoefficient m (-u5*u7) witnessWord027 102 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord027 102 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord027)=
      (-1:ℂ)^(frickeCount witnessWord027)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord027_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord027 102 (0,2,0,0) hr hcompat z]
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_246

theorem analytic_short_source_248 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((-1)/((primeParameter 2 m z)^(2:ℕ)))*G z 0 + (1)*G z 105) s := by
  let r : ClosedWordRow := {
    word := witnessWord027, source := 105, target := 0
    nonaffine := by norm_num [witnessWord027_matrix]
    denominator := by norm_num [integerDen,witnessWord027_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord027_matrix] }
  have hr : rationalRate witnessWord027 105=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord027_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 105)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord027 105 0 z*
    (G z) (gridIndex (0))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord027 105 0 z=wordCoefficient m (-u5*u7) witnessWord027 105 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord027 105 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord027)=
      (-1:ℂ)^(frickeCount witnessWord027)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord027_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord027 105 (-2,0,0,0) hr hcompat z]
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_248

theorem analytic_short_source_252 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 108 + ((-1)*(primeParameter 2 m z)^(2:ℕ))*G z 207) s := by
  let r : ClosedWordRow := {
    word := witnessWord027, source := 108, target := -3
    nonaffine := by norm_num [witnessWord027_matrix]
    denominator := by norm_num [integerDen,witnessWord027_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord027_matrix] }
  have hr : rationalRate witnessWord027 108=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord027_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 108)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord027 108 0 z*
    (G z) (gridIndex (-3))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord027 108 0 z=wordCoefficient m (-u5*u7) witnessWord027 108 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord027 108 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord027)=
      (-1:ℂ)^(frickeCount witnessWord027)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord027_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord027 108 (2,0,0,0) hr hcompat z]
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_252

theorem analytic_short_source_262 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 107 + ((-1)/((primeParameter 2 m z)^(2:ℕ)))*G z 202) s := by
  let r : ClosedWordRow := {
    word := witnessWord028, source := 107, target := -8
    nonaffine := by norm_num [witnessWord028_matrix]
    denominator := by norm_num [integerDen,witnessWord028_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord028_matrix] }
  have hr : rationalRate witnessWord028 107=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord028_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 107)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord028 107 0 z*
    (G z) (gridIndex (-8))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord028 107 0 z=wordCoefficient m (-u5*u7) witnessWord028 107 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord028 107 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord028)=
      (-1:ℂ)^(frickeCount witnessWord028)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord028_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord028 107 (-2,0,0,0) hr hcompat z]
  norm_num [witnessWord028_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_262

theorem analytic_short_source_266 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 110 + ((-1)*(primeParameter 2 m z)^(2:ℕ))*G z 205) s := by
  let r : ClosedWordRow := {
    word := witnessWord028, source := 110, target := -5
    nonaffine := by norm_num [witnessWord028_matrix]
    denominator := by norm_num [integerDen,witnessWord028_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord028_matrix] }
  have hr : rationalRate witnessWord028 110=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord028_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 110)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord028 110 0 z*
    (G z) (gridIndex (-5))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord028 110 0 z=wordCoefficient m (-u5*u7) witnessWord028 110 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord028 110 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord028)=
      (-1:ℂ)^(frickeCount witnessWord028)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord028_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord028 110 (2,0,0,0) hr hcompat z]
  norm_num [witnessWord028_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_266

theorem analytic_short_source_272 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 96 + ((-1)*(primeParameter 2 m z)^(2:ℕ))*G z 201) s := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 96, target := -9
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 96=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 96)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 96 0 z*
    (G z) (gridIndex (-9))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 96 0 z=wordCoefficient m (-u5*u7) witnessWord029 96 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 96 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 96 (2,0,0,0) hr hcompat z]
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_272

theorem analytic_short_source_274 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 99 + (((-1)*(primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)))*G z 202) s := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 99, target := -8
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 99=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 99)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 99 0 z*
    (G z) (gridIndex (-8))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 99 0 z=wordCoefficient m (-u5*u7) witnessWord029 99 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 99 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 99 (-2,2,0,0) hr hcompat z]
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_274

theorem analytic_short_source_288 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 109 + ((-1)/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 162) s := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 109, target := -48
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 109=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 109)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 109 0 z*
    (G z) (gridIndex (-48))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 109 0 z=wordCoefficient m (-u5*u7) witnessWord029 109 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 109 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 109 (-2,-2,0,0) hr hcompat z]
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_288

theorem analytic_short_source_296 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 114 + (-1)*G z 192) s := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 114, target := -18
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 114=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 114)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 114 0 z*
    (G z) (gridIndex (-18))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 114 0 z=wordCoefficient m (-u5*u7) witnessWord029 114 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 114 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 114 (0,0,0,0) hr hcompat z]
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_296

theorem analytic_short_source_312 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((-1)*(primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)))*G z 16 + (1)*G z 93) s := by
  let r : ClosedWordRow := {
    word := witnessWord030, source := 93, target := 16
    nonaffine := by norm_num [witnessWord030_matrix]
    denominator := by norm_num [integerDen,witnessWord030_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord030_matrix] }
  have hr : rationalRate witnessWord030 93=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord030_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 93)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord030 93 0 z*
    (G z) (gridIndex (16))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord030 93 0 z=wordCoefficient m (-u5*u7) witnessWord030 93 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord030 93 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord030)=
      (-1:ℂ)^(frickeCount witnessWord030)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord030 93 (-2,2,0,0) hr hcompat z]
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_312

theorem analytic_short_source_326 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 103 + ((-1)/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 186) s := by
  let r : ClosedWordRow := {
    word := witnessWord030, source := 103, target := -24
    nonaffine := by norm_num [witnessWord030_matrix]
    denominator := by norm_num [integerDen,witnessWord030_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord030_matrix] }
  have hr : rationalRate witnessWord030 103=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord030_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 103)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord030 103 0 z*
    (G z) (gridIndex (-24))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord030 103 0 z=wordCoefficient m (-u5*u7) witnessWord030 103 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord030 103 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord030)=
      (-1:ℂ)^(frickeCount witnessWord030)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord030 103 (-2,-2,0,0) hr hcompat z]
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_326

theorem analytic_short_source_360 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 174 + (-1)*G z 204) s := by
  let r : ClosedWordRow := {
    word := witnessWord041, source := 174, target := -6
    nonaffine := by norm_num [witnessWord041_matrix]
    denominator := by norm_num [integerDen,witnessWord041_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord041_matrix] }
  have hr : rationalRate witnessWord041 174=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord041_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 174)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord041 174 0 z*
    (G z) (gridIndex (-6))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord041 174 0 z=wordCoefficient m (-u5*u7) witnessWord041 174 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord041 174 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord041)=
      (-1:ℂ)^(frickeCount witnessWord041)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord041 174 (0,0,0,0) hr hcompat z]
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_360

theorem analytic_short_source_362 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((-1)/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 0 + (1)*G z 175) s := by
  let r : ClosedWordRow := {
    word := witnessWord041, source := 175, target := 0
    nonaffine := by norm_num [witnessWord041_matrix]
    denominator := by norm_num [integerDen,witnessWord041_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord041_matrix] }
  have hr : rationalRate witnessWord041 175=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord041_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 175)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord041 175 0 z*
    (G z) (gridIndex (0))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord041 175 0 z=wordCoefficient m (-u5*u7) witnessWord041 175 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord041 175 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord041)=
      (-1:ℂ)^(frickeCount witnessWord041)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord041 175 (-2,-2,0,0) hr hcompat z]
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_362

theorem analytic_short_source_366 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 177 + (((-1)*(primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)))*G z 202) s := by
  let r : ClosedWordRow := {
    word := witnessWord041, source := 177, target := -8
    nonaffine := by norm_num [witnessWord041_matrix]
    denominator := by norm_num [integerDen,witnessWord041_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord041_matrix] }
  have hr : rationalRate witnessWord041 177=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord041_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 177)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord041 177 0 z*
    (G z) (gridIndex (-8))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord041 177 0 z=wordCoefficient m (-u5*u7) witnessWord041 177 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord041 177 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord041)=
      (-1:ℂ)^(frickeCount witnessWord041)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord041 177 (-2,2,0,0) hr hcompat z]
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_366

theorem analytic_short_source_372 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((-1)*(primeParameter 2 m z)^(2:ℕ))*G z 39 + (1)*G z 162) s := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 162, target := 39
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 162=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 162)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 162 0 z*
    (G z) (gridIndex (39))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 162 0 z=wordCoefficient m (-u5*u7) witnessWord042 162 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 162 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 162 (2,0,0,0) hr hcompat z]
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_372

theorem analytic_short_source_378 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((-1)*(primeParameter 2 m z)^(2:ℕ))/((primeParameter 3 m z)^(2:ℕ)))*G z 45 + (1)*G z 170) s := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 170, target := 45
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 170=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 170)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 170 0 z*
    (G z) (gridIndex (45))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 170 0 z=wordCoefficient m (-u5*u7) witnessWord042 170 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 170 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 170 (2,-2,0,0) hr hcompat z]
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_378

theorem analytic_short_source_380 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((-1)/((primeParameter 2 m z)^(2:ℕ)))*G z 48 + (1)*G z 171) s := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 171, target := 48
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 171=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 171)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 171 0 z*
    (G z) (gridIndex (48))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 171 0 z=wordCoefficient m (-u5*u7) witnessWord042 171 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 171 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 171 (-2,0,0,0) hr hcompat z]
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_380

theorem analytic_short_source_382 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((-1)/((primeParameter 3 m z)^(2:ℕ)))*G z 54 + (1)*G z 172) s := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 172, target := 54
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 172=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 172)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 172 0 z*
    (G z) (gridIndex (54))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 172 0 z=wordCoefficient m (-u5*u7) witnessWord042 172 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 172 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 172 (0,-2,0,0) hr hcompat z]
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_382

theorem analytic_short_source_384 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((-1)/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 72 + (1)*G z 173) s := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 173, target := 72
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 173=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 173)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 173 0 z*
    (G z) (gridIndex (72))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 173 0 z=wordCoefficient m (-u5*u7) witnessWord042 173 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 173 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 173 (-2,-2,0,0) hr hcompat z]
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_384

theorem analytic_short_source_398 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((-1)*(primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)))*G z 32 + (1)*G z 183) s := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 183, target := 32
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 183=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 183)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 183 0 z*
    (G z) (gridIndex (32))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 183 0 z=wordCoefficient m (-u5*u7) witnessWord042 183 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 183 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 183 (-2,2,0,0) hr hcompat z]
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_398

theorem analytic_short_source_400 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((-1)*(primeParameter 2 m z)^(2:ℕ))*G z 33 + (1)*G z 186) s := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 186, target := 33
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 186=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 186)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 186 0 z*
    (G z) (gridIndex (33))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 186 0 z=wordCoefficient m (-u5*u7) witnessWord042 186 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 186 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 186 (2,0,0,0) hr hcompat z]
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_400

theorem analytic_short_source_2790 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 70 + (1)*G z 140) s := by
  have hh := analytic_full_entire hm hf BG G hG hGF s 3 (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 70 + (1)*G z 140
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2790

theorem analytic_short_source_2806 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 65 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 98 + (1)*G z 135 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 168) s := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= -u5^(1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    3 (by decide) (by decide) (-5) 140 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 65 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 98 + (1)*G z 135 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 168
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (-5) (-2,0,1,-1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2806

theorem analytic_short_source_2808 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((u7*primeParameter 7 m z))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 50 + (1)*G z 77 + (((u7*primeParameter 7 m z))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 120 + (1)*G z 147) s := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((7:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= -u5^(-1:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    3 (by decide) (by decide) (7) 140 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (((u7*primeParameter 7 m z))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 50 + (1)*G z 77 + (((u7*primeParameter 7 m z))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 120 + (1)*G z 147
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (7) (-2,0,-1,1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2808

theorem analytic_short_source_2814 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 60 + (((u5*primeParameter 5 m z))/((u7*primeParameter 7 m z)))*G z 84 + (1)*G z 130 + (((u5*primeParameter 5 m z))/((u7*primeParameter 7 m z)))*G z 154) s := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-10:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= -u5^(1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    3 (by decide) (by decide) (-10) 140 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 60 + (((u5*primeParameter 5 m z))/((u7*primeParameter 7 m z)))*G z 84 + (1)*G z 130 + (((u5*primeParameter 5 m z))/((u7*primeParameter 7 m z)))*G z 154
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (-10) (0,0,1,-1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2814

theorem analytic_short_source_2850 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 0 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 42 + (1)*G z 45 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 84 + (1)*G z 87 + (1)*G z 129 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 168 + (1)*G z 171) s := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((3:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    5 (by decide) (by decide) (3) 252 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 0 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 42 + (1)*G z 45 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 84 + (1)*G z 87 + (1)*G z 129 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 168 + (1)*G z 171
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (3) (-2,0,0,-1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2850

theorem analytic_short_source_2852 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 0 + (1)*G z 39 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 42 + (1)*G z 81 + (1)*G z 123 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 126 + (1)*G z 165 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 168) s := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-3:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    5 (by decide) (by decide) (-3) 252 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 0 + (1)*G z 39 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 42 + (1)*G z 81 + (1)*G z 123 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 126 + (1)*G z 165 + ((1)/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 168
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (-3) (-2,0,0,-1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2852

theorem analytic_short_source_2860 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => ((1)/((u7*primeParameter 7 m z)))*G z 0 + (1)*G z 36 + (1)*G z 78 + ((1)/((u7*primeParameter 7 m z)))*G z 84 + (1)*G z 120 + ((1)/((u7*primeParameter 7 m z)))*G z 126 + (1)*G z 162 + ((1)/((u7*primeParameter 7 m z)))*G z 168) s := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-6:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    5 (by decide) (by decide) (-6) 252 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = ((1)/((u7*primeParameter 7 m z)))*G z 0 + (1)*G z 36 + (1)*G z 78 + ((1)/((u7*primeParameter 7 m z)))*G z 84 + (1)*G z 120 + ((1)/((u7*primeParameter 7 m z)))*G z 126 + (1)*G z 162 + ((1)/((u7*primeParameter 7 m z)))*G z 168
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (-6) (0,0,0,-1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2860

theorem analytic_short_source_2866 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 14 + (1)*G z 51 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 56 + (1)*G z 93 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 98 + (1)*G z 135 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 140 + (1)*G z 177) s := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((9:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    5 (by decide) (by decide) (9) 252 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 14 + (1)*G z 51 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 56 + (1)*G z 93 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 98 + (1)*G z 135 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 140 + (1)*G z 177
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (9) (-2,2,0,-1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2866

theorem analytic_short_source_2868 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 33 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 70 + (1)*G z 75 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 112 + (1)*G z 117 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 154 + (1)*G z 159 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 196) s := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-9:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    5 (by decide) (by decide) (-9) 252 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 33 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 70 + (1)*G z 75 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 112 + (1)*G z 117 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 154 + (1)*G z 159 + (((primeParameter 3 m z)^(2:ℕ))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 196
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (-9) (-2,2,0,-1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2868

theorem analytic_short_source_2872 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 30 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 63 + (1)*G z 72 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 105 + (1)*G z 114 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 147 + (1)*G z 156 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 189) s := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-12:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    5 (by decide) (by decide) (-12) 252 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 30 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 63 + (1)*G z 72 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 105 + (1)*G z 114 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 147 + (1)*G z 156 + (((primeParameter 2 m z)^(2:ℕ))/((u7*primeParameter 7 m z)))*G z 189
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (-12) (2,0,0,-1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2872

theorem analytic_short_source_2874 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 24 + (1)*G z 56 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 66 + (1)*G z 98 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 108 + (1)*G z 140 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 150 + (1)*G z 182) s := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((14:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    5 (by decide) (by decide) (14) 252 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 24 + (1)*G z 56 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 66 + (1)*G z 98 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 108 + (1)*G z 140 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 150 + (1)*G z 182
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (14) (0,-2,0,1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2874

theorem analytic_short_source_2876 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 28 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 60 + (1)*G z 70 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 102 + (1)*G z 112 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 144 + (1)*G z 154 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 186) s := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-14:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    5 (by decide) (by decide) (-14) 252 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 28 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 60 + (1)*G z 70 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 102 + (1)*G z 112 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 144 + (1)*G z 154 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)))*G z 186
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (-14) (0,-2,0,1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2876

theorem analytic_short_source_2950 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 24 + (1)*G z 35 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 54 + (1)*G z 65 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 84 + (1)*G z 95 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 114 + (1)*G z 125 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 144 + (1)*G z 155 + (1)*G z 185 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 204) s := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    7 (by decide) (by decide) (5) 180 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 24 + (1)*G z 35 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 54 + (1)*G z 65 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 84 + (1)*G z 95 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 114 + (1)*G z 125 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 144 + (1)*G z 155 + (1)*G z 185 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)))*G z 204
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (5) (-2,-2,1,0) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2950

theorem analytic_short_source_3006 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 21 + (1)*G z 63 + (1)*G z 147 + (1)*G z 189) s := by
  have hh := analytic_full_entire hm hf BG G hG hGF s 10 (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 21 + (1)*G z 63 + (1)*G z 147 + (1)*G z 189
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3006

theorem analytic_short_source_3026 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (1)*G z 0 + ((u7*primeParameter 7 m z))*G z 24 + (1)*G z 42 + ((u7*primeParameter 7 m z))*G z 66 + (1)*G z 126 + ((u7*primeParameter 7 m z))*G z 150 + (1)*G z 168 + ((u7*primeParameter 7 m z))*G z 192) s := by
  have hroot : root 35 f 10=u5 := by simp [root_signed_10,h5,h7]
  have hr : (Nat.lcm 35 (10^2):ℚ)*((-21:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 10*ε*I^(2*m)= -u5^(0:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    10 (by decide) (by decide) (-21) 63 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 0 + ((u7*primeParameter 7 m z))*G z 24 + (1)*G z 42 + ((u7*primeParameter 7 m z))*G z 66 + (1)*G z 126 + ((u7*primeParameter 7 m z))*G z 150 + (1)*G z 168 + ((u7*primeParameter 7 m z))*G z 192
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 10 (-21) (0,0,0,1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3026

theorem analytic_short_source_3032 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 15 + (1)*G z 45 + (1)*G z 75 + (1)*G z 135 + (1)*G z 165 + (1)*G z 195) s := by
  have hh := analytic_full_entire hm hf BG G hG hGF s 14 (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 15 + (1)*G z 45 + (1)*G z 75 + (1)*G z 135 + (1)*G z 165 + (1)*G z 195
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3032

theorem analytic_short_source_3084 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 10 + (1)*G z 20 + (1)*G z 40 + (1)*G z 50 + (1)*G z 80 + (1)*G z 100 + (1)*G z 110 + (1)*G z 130 + (1)*G z 160 + (1)*G z 170 + (1)*G z 190 + (1)*G z 200) s := by
  have hh := analytic_full_entire hm hf BG G hG hGF s 21 (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 10 + (1)*G z 20 + (1)*G z 40 + (1)*G z 50 + (1)*G z 80 + (1)*G z 100 + (1)*G z 110 + (1)*G z 130 + (1)*G z 160 + (1)*G z 170 + (1)*G z 190 + (1)*G z 200
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3084

theorem analytic_short_source_3206 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 2 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 4 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 8 + (1)*G z 107) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 2
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 2 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 4 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 8 + (1)*G z 107
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3206

theorem analytic_short_source_3210 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 4 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 8 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 16 + (1)*G z 109) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 4
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 4 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 8 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 16 + (1)*G z 109
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3210

theorem analytic_short_source_3212 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 5 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 10 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 20 + (1)*G z 110) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 5
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 5 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 10 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 20 + (1)*G z 110
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3212

theorem analytic_short_source_3226 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 12 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 24 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 48 + (1)*G z 117) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 12
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 12 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 24 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 48 + (1)*G z 117
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3226

theorem analytic_short_source_3238 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 18 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 36 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 72 + (1)*G z 123) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 18
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 18 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 36 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 72 + (1)*G z 123
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3238

theorem analytic_short_source_3242 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 20 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 40 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 80 + (1)*G z 125) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 20
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 20 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 40 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 80 + (1)*G z 125
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3242

theorem analytic_short_source_3250 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 24 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 48 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 96 + (1)*G z 129) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 24
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 24 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 48 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 96 + (1)*G z 129
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3250

theorem analytic_short_source_3262 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 30 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 60 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 120 + (1)*G z 135) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 30
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 30 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 60 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 120 + (1)*G z 135
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3262

theorem analytic_short_source_3302 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 50 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 100 + (1)*G z 155 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 200) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 50
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 50 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 100 + (1)*G z 155 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 200
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3302

theorem analytic_short_source_3304 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 51 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 102 + (1)*G z 156 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 204) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 51
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 51 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 102 + (1)*G z 156 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 204
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3304

theorem analytic_short_source_3310 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 6 + (1)*G z 54 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 108 + (1)*G z 159) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 54
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 6 + (1)*G z 54 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 108 + (1)*G z 159
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3310

theorem analytic_short_source_3358 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 78 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 102 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 156 + (1)*G z 183) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 78
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 78 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 102 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 156 + (1)*G z 183
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3358

theorem analytic_short_source_3362 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 80 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 110 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 160 + (1)*G z 185) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 80
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 80 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 110 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 160 + (1)*G z 185
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3362

theorem analytic_short_source_3364 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 81 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 114 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 162 + (1)*G z 186) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 81
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 81 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 114 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 162 + (1)*G z 186
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3364

theorem analytic_short_source_3392 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 95 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 170 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 190 + (1)*G z 200) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 95
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 95 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 170 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 190 + (1)*G z 200
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3392

theorem analytic_short_source_3426 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 7 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 21 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 63 + (1)*G z 77 + (1)*G z 147) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 3 (by decide) (by decide) 7
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 7 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 21 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 63 + (1)*G z 77 + (1)*G z 147
  have hp : (3:ℂ)^((m:ℂ)-z)=(primeParameter 3 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3426

theorem analytic_short_source_3476 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 32 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 78 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 96 + (1)*G z 102 + (1)*G z 172) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 3 (by decide) (by decide) 32
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 32 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 78 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 96 + (1)*G z 102 + (1)*G z 172
  have hp : (3:ℂ)^((m:ℂ)-z)=(primeParameter 3 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3476

theorem analytic_short_source_3478 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 33 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 87 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 99 + (1)*G z 103 + (1)*G z 173) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 3 (by decide) (by decide) 33
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 33 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 87 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 99 + (1)*G z 103 + (1)*G z 173
  have hp : (3:ℂ)^((m:ℂ)-z)=(primeParameter 3 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3478

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

