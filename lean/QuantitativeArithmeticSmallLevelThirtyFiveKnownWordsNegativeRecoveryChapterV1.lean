module
public meta import SmallLevelCertificateBatchCommandV1
public import QuantitativeArithmeticSmallLevelThirtyFiveKnownWordsNegativeAnalyticChapterV1

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

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortSourcesBundleV4 -/
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
open Complex Matrix Filter Set FinitenessRamanujanSum
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology
open Complex Matrix Filter Set FinitenessRamanujanSum FinitenessNormalizedTwistProduct

certificate_batch {
theorem analytic_short_source_22 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 7 + (((u7*primeParameter 7 m z))/((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 30) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 7, target := -180
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 7=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 7)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 7 0 z*
    (G z) (gridIndex (-180))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 7 0 z=wordCoefficient m (-u5*u7) witnessWord002 7 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 7 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 7 (-2,-2,-1,1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_22

theorem analytic_short_source_26 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 10 + (((u5*primeParameter 5 m z))/((primeParameter 3 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 84) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 10, target := -126
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 10=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 10)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 10 0 z*
    (G z) (gridIndex (-126))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 10 0 z=wordCoefficient m (-u5*u7) witnessWord002 10 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 10 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 10 (0,-2,1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_26

theorem analytic_short_source_30 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 14 + (((u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 120) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 14, target := -90
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 14=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 14)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 14 0 z*
    (G z) (gridIndex (-90))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 14 0 z=wordCoefficient m (-u5*u7) witnessWord002 14 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 14 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 14 (0,-2,-1,1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_30

theorem analytic_short_source_32 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 15 + (((u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 126) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 15, target := -84
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 15=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 15)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 15 0 z*
    (G z) (gridIndex (-84))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 15 0 z=wordCoefficient m (-u5*u7) witnessWord002 15 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 15 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 15 (-2,0,1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_32

theorem analytic_short_source_38 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 21 + (((u7*primeParameter 7 m z))/((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 150) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 21, target := -60
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 21=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 21)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 21 0 z*
    (G z) (gridIndex (-60))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 21 0 z=wordCoefficient m (-u5*u7) witnessWord002 21 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 21 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 21 (-2,0,-1,1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_38

theorem analytic_short_source_40 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 28 + (((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z))/((primeParameter 3 m z)^(2:ℕ)*(u5*primeParameter 5 m z)))*G z 165) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 28, target := -45
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 28=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 28)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 28 0 z*
    (G z) (gridIndex (-45))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 28 0 z=wordCoefficient m (-u5*u7) witnessWord002 28 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 28 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 28 (2,-2,-1,1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_40

theorem analytic_short_source_42 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 30 + (((u5*primeParameter 5 m z))/((u7*primeParameter 7 m z)))*G z 168) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 30, target := -42
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 30=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 30)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 30 0 z*
    (G z) (gridIndex (-42))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 30 0 z=wordCoefficient m (-u5*u7) witnessWord002 30 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 30 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 30 (0,0,1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_42

theorem analytic_short_source_48 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 42 + (((u7*primeParameter 7 m z))/((u5*primeParameter 5 m z)))*G z 180) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 42, target := -30
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 42=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 42)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 42 0 z*
    (G z) (gridIndex (-30))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 42 0 z=wordCoefficient m (-u5*u7) witnessWord002 42 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 42 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 42 (0,0,-1,1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_48

theorem analytic_short_source_50 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 45 + (((primeParameter 3 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z)))*G z 182) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 45, target := -28
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 45=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 45)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 45 0 z*
    (G z) (gridIndex (-28))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 45 0 z=wordCoefficient m (-u5*u7) witnessWord002 45 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 45 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 45 (-2,2,1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_50

theorem analytic_short_source_52 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 60 + (((primeParameter 2 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((u7*primeParameter 7 m z)))*G z 189) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 60, target := -21
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 60=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 60)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 60 0 z*
    (G z) (gridIndex (-21))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 60 0 z=wordCoefficient m (-u5*u7) witnessWord002 60 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 60 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 60 (2,0,1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_52

theorem analytic_short_source_58 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 84 + (((primeParameter 2 m z)^(2:ℕ)*(u7*primeParameter 7 m z))/((u5*primeParameter 5 m z)))*G z 195) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 84, target := -15
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 84=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 84)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 84 0 z*
    (G z) (gridIndex (-15))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 84 0 z=wordCoefficient m (-u5*u7) witnessWord002 84 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 84 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 84 (2,0,-1,1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_58

theorem analytic_short_source_60 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 90 + (((primeParameter 3 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((u7*primeParameter 7 m z)))*G z 196) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 90, target := -14
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 90=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 90)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 90 0 z*
    (G z) (gridIndex (-14))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 90 0 z=wordCoefficient m (-u5*u7) witnessWord002 90 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 90 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 90 (0,2,1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_60

theorem analytic_short_source_64 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 126 + (((primeParameter 3 m z)^(2:ℕ)*(u7*primeParameter 7 m z))/((u5*primeParameter 5 m z)))*G z 200) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 126, target := -10
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 126=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 126)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 126 0 z*
    (G z) (gridIndex (-10))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 126 0 z=wordCoefficient m (-u5*u7) witnessWord002 126 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 126 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 126 (0,2,-1,1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_64

theorem analytic_short_source_68 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 180 + (((primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ)*(u5*primeParameter 5 m z))/((u7*primeParameter 7 m z)))*G z 203) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 180, target := -7
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 180=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 180)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 180 0 z*
    (G z) (gridIndex (-7))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 180 0 z=wordCoefficient m (-u5*u7) witnessWord002 180 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 180 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 180 (2,2,1,-1) hr hcompat z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_68

theorem analytic_short_source_270 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 90 + ((-1)*(primeParameter 3 m z)^(2:ℕ))*G z 200) s := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 90, target := -10
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 90=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 90)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 90 0 z*
    (G z) (gridIndex (-10))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 90 0 z=wordCoefficient m (-u5*u7) witnessWord029 90 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 90 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 90 (0,2,0,0) hr hcompat z]
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_270

theorem analytic_short_source_294 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 112 + (((-1)*(primeParameter 2 m z)^(2:ℕ))/((primeParameter 3 m z)^(2:ℕ)))*G z 189) s := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 112, target := -21
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 112=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 112)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 112 0 z*
    (G z) (gridIndex (-21))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 112 0 z=wordCoefficient m (-u5*u7) witnessWord029 112 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 112 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 112 (2,-2,0,0) hr hcompat z]
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_294

theorem analytic_short_source_300 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 120 + ((-1)*(primeParameter 2 m z)^(2:ℕ))*G z 195) s := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 120, target := -15
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 120=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 120)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 120 0 z*
    (G z) (gridIndex (-15))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 120 0 z=wordCoefficient m (-u5*u7) witnessWord029 120 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 120 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 120 (2,0,0,0) hr hcompat z]
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_300

theorem analytic_short_source_316 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (((-1)*(primeParameter 2 m z)^(2:ℕ))/((primeParameter 3 m z)^(2:ℕ)))*G z 21 + (1)*G z 98) s := by
  let r : ClosedWordRow := {
    word := witnessWord030, source := 98, target := 21
    nonaffine := by norm_num [witnessWord030_matrix]
    denominator := by norm_num [integerDen,witnessWord030_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord030_matrix] }
  have hr : rationalRate witnessWord030 98=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord030_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 98)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord030 98 0 z*
    (G z) (gridIndex (21))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord030 98 0 z=wordCoefficient m (-u5*u7) witnessWord030 98 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord030 98 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord030)=
      (-1:ℂ)^(frickeCount witnessWord030)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord030 98 (2,-2,0,0) hr hcompat z]
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_316

theorem analytic_short_source_358 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun z => (1)*G z 168 + ((-1)*(primeParameter 2 m z)^(2:ℕ)*(primeParameter 3 m z)^(2:ℕ))*G z 203) s := by
  let r : ClosedWordRow := {
    word := witnessWord041, source := 168, target := -7
    nonaffine := by norm_num [witnessWord041_matrix]
    denominator := by norm_num [integerDen,witnessWord041_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord041_matrix] }
  have hr : rationalRate witnessWord041 168=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord041_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change (G z) (gridIndex 168)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord041 168 0 z*
    (G z) (gridIndex (-7))= _
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord041 168 0 z=wordCoefficient m (-u5*u7) witnessWord041 168 0 z :=
    (wordCoefficient_rational m (-u5*u7) witnessWord041 168 0 z).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord041)=
      (-1:ℂ)^(frickeCount witnessWord041)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord041 168 (2,2,0,0) hr hcompat z]
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_358

theorem analytic_short_source_2812 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => (((u5*primeParameter 5 m z))/((u7*primeParameter 7 m z)))*G z 56 + (1)*G z 80 + (((u5*primeParameter 5 m z))/((u7*primeParameter 7 m z)))*G z 126 + (1)*G z 150) s := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((10:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= -u5^(1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hh := analytic_full_taylor hf ε hlaw BG G hG hGF s hshift
    3 (by decide) (by decide) (10) 140 (by decide) (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (((u5*primeParameter 5 m z))/((u7*primeParameter 7 m z)))*G z 56 + (1)*G z 80 + (((u5*primeParameter 5 m z))/((u7*primeParameter 7 m z)))*G z 126 + (1)*G z 150
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (10) (0,0,1,-1) hr hcompat z
  dsimp only
  rw [hc]
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals simp_all
  all_goals ring

#print axioms analytic_short_source_2812

theorem analytic_short_source_2840 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 42 + (1)*G z 84 + (1)*G z 126 + (1)*G z 168) s := by
  have hh := analytic_full_entire hm hf BG G hG hGF s 5 (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 42 + (1)*G z 84 + (1)*G z 126 + (1)*G z 168
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2840

theorem analytic_short_source_2932 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 30 + (1)*G z 60 + (1)*G z 90 + (1)*G z 120 + (1)*G z 150 + (1)*G z 180) s := by
  have hh := analytic_full_entire hm hf BG G hG hGF s 7 (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 30 + (1)*G z 60 + (1)*G z 90 + (1)*G z 120 + (1)*G z 150 + (1)*G z 180
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_2932

theorem analytic_short_source_3058 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 14 + (1)*G z 28 + (1)*G z 56 + (1)*G z 98 + (1)*G z 112 + (1)*G z 154 + (1)*G z 182 + (1)*G z 196) s := by
  have hh := analytic_full_entire hm hf BG G hG hGF s 15 (by decide) (by decide)
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 14 + (1)*G z 28 + (1)*G z 56 + (1)*G z 98 + (1)*G z 112 + (1)*G z 154 + (1)*G z 182 + (1)*G z 196
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3058

theorem analytic_short_source_3216 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 7 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 14 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 28 + (1)*G z 112) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 7
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 7 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 14 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 28 + (1)*G z 112
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3216

theorem analytic_short_source_3232 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 15 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 30 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 60 + (1)*G z 120) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 15
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 15 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 30 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 60 + (1)*G z 120
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3232

theorem analytic_short_source_3292 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 45 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 90 + (1)*G z 150 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 180) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 2 (by decide) (by decide) 45
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 45 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m z)))*G z 90 + (1)*G z 150 + ((1)/((primeParameter 2 m z)^(2:ℕ)))*G z 180
  have hp : (2:ℂ)^((m:ℂ)-z)=(primeParameter 2 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3292

theorem analytic_short_source_3432 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 10 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 30 + (1)*G z 80 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 90 + (1)*G z 150) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 3 (by decide) (by decide) 10
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 10 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 30 + (1)*G z 80 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 90 + (1)*G z 150
  have hp : (3:ℂ)^((m:ℂ)-z)=(primeParameter 3 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3432

theorem analytic_short_source_3440 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 14 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 42 + (1)*G z 84 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 126 + (1)*G z 154) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 3 (by decide) (by decide) 14
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 14 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 42 + (1)*G z 84 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 126 + (1)*G z 154
  have hp : (3:ℂ)^((m:ℂ)-z)=(primeParameter 3 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3440

theorem analytic_short_source_3468 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) :
    HasAnalyticGerm (fun z => (1)*G z 28 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 42 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 84 + (1)*G z 98 + (1)*G z 168) s := by
  have hh := analytic_full_hecke hm hf BG G hG hGF s 3 (by decide) (by decide) 28
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro z
  change _ = (1)*G z 28 + ((1)/((primeParameter 3 m z)^(2:ℕ)))*G z 42 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m z)))*G z 84 + (1)*G z 98 + (1)*G z 168
  have hp : (3:ℂ)^((m:ℂ)-z)=(primeParameter 3 m z)⁻¹ := by
    rw [show (m:ℂ)-z= -(z-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp]
  all_goals field_simp [primeParameter_ne_zero 2 m (by decide) z, primeParameter_ne_zero 3 m (by decide) z, primeParameter_ne_zero 5 m (by decide) z, primeParameter_ne_zero 7 m (by decide) z]
  all_goals try simp_all
  all_goals ring

#print axioms analytic_short_source_3468

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridRecoveryNegativeSourcesBundleV4 -/
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
open Complex Matrix Filter Set FinitenessNormalizedTwistProduct
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open FinitenessRamanujanSum
open scoped Topology

certificate_batch {
theorem actual_signed_negative_source_6 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 105 + (((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)))*v 206 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord001, source := 105, target := -4
    nonaffine := by norm_num [witnessWord001_matrix]
    denominator := by norm_num [integerDen,witnessWord001_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord001_matrix] }
  have hr : rationalRate witnessWord001 105=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord001_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 105)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord001 105 0 s*v (gridIndex (-4))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord001 105 0 s=wordCoefficient m (-u5*u7) witnessWord001 105 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord001 105 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord001)=(-1:ℂ)^(frickeCount witnessWord001)*u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord001_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord001 105 (-2,2,1,1) hr hcompat s] at hh
  norm_num [witnessWord001_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_6


theorem actual_signed_negative_source_10 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 1 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord002, source := 1, target := -1260
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 1=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 1)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 1 0 s*v (gridIndex (-1260))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 1 0 s=wordCoefficient m (-u5*u7) witnessWord002 1 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 1 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=(-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 1 (-2,-2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_10


theorem actual_signed_negative_source_14 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 3 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord002, source := 3, target := -420
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 3=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 3)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 3 0 s*v (gridIndex (-420))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 3 0 s=wordCoefficient m (-u5*u7) witnessWord002 3 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 3 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=(-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 3 (-2,0,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_14


theorem actual_signed_negative_source_24 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 9 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 70 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord002, source := 9, target := -140
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 9=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 9)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 9 0 s*v (gridIndex (-140))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 9 0 s=wordCoefficient m (-u5*u7) witnessWord002 9 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 9 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=(-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 9 (-2,2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_24


theorem actual_signed_negative_source_130 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 209 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord003, source := 209, target := 1260
    nonaffine := by norm_num [witnessWord003_matrix]
    denominator := by norm_num [integerDen,witnessWord003_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord003_matrix] }
  have hr : rationalRate witnessWord003 209=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord003_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 209)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord003 209 0 s*v (gridIndex (1260))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord003 209 0 s=wordCoefficient m (-u5*u7) witnessWord003 209 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord003 209 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord003)=(-1:ℂ)^(frickeCount witnessWord003)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord003_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord003 209 (-2,-2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord003_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_130


theorem actual_signed_negative_source_250 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 106 + ((-1)/((primeParameter 3 m s)^(2:ℕ)))*v 204 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord027, source := 106, target := -6
    nonaffine := by norm_num [witnessWord027_matrix]
    denominator := by norm_num [integerDen,witnessWord027_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord027_matrix] }
  have hr : rationalRate witnessWord027 106=(2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord027_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 106)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord027 106 0 s*v (gridIndex (-6))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord027 106 0 s=wordCoefficient m (-u5*u7) witnessWord027 106 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord027 106 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord027)=(-1:ℂ)^(frickeCount witnessWord027)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord027_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord027 106 (0,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_250

theorem actual_signed_negative_source_256 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 104 + (-1)*v 208 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord028, source := 104, target := -2
    nonaffine := by norm_num [witnessWord028_matrix]
    denominator := by norm_num [integerDen,witnessWord028_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord028_matrix] }
  have hr : rationalRate witnessWord028 104=(2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord028_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 104)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord028 104 0 s*v (gridIndex (-2))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord028 104 0 s=wordCoefficient m (-u5*u7) witnessWord028 104 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord028 104 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord028)=(-1:ℂ)^(frickeCount witnessWord028)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord028_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord028 104 (0,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord028_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_256


theorem actual_signed_negative_source_306 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)*(primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ))*v 13 + (1)*v 66 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord030, source := 66, target := 13
    nonaffine := by norm_num [witnessWord030_matrix]
    denominator := by norm_num [integerDen,witnessWord030_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord030_matrix] }
  have hr : rationalRate witnessWord030 66=(2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord030_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 66)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord030 66 0 s*v (gridIndex (13))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord030 66 0 s=wordCoefficient m (-u5*u7) witnessWord030 66 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord030 66 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord030)=(-1:ℂ)^(frickeCount witnessWord030)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord030 66 (2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_306


theorem actual_signed_negative_source_322 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 48 + (1)*v 101 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord030, source := 101, target := 48
    nonaffine := by norm_num [witnessWord030_matrix]
    denominator := by norm_num [integerDen,witnessWord030_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord030_matrix] }
  have hr : rationalRate witnessWord030 101=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord030_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 101)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord030 101 0 s*v (gridIndex (48))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord030 101 0 s=wordCoefficient m (-u5*u7) witnessWord030 101 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord030 101 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord030)=(-1:ℂ)^(frickeCount witnessWord030)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord030 101 (-2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_322


theorem actual_signed_negative_source_402 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)*(primeParameter 3 m s)^(2:ℕ))*v 34 + (1)*v 192 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord042, source := 192, target := 34
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 192=(2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 192)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 192 0 s*v (gridIndex (34))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 192 0 s=wordCoefficient m (-u5*u7) witnessWord042 192 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 192 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=(-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 192 (0,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_402


theorem actual_signed_negative_source_2792 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 71 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 140 + (1)*v 141 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=-u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (1) (-2,0,-1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (1) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2792


theorem actual_signed_negative_source_2794 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 69 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 70 + (1)*v 139 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=-u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (-1) (-2,0,-1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-1) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2794

theorem actual_signed_negative_source_2810 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 63 + (((u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 90 + (1)*v 133 + (((u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 160 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-7:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=-u5^(-1:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (-7) (-2,0,-1,1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-7) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2810


theorem actual_signed_negative_source_2842 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 42 + (1)*v 43 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 84 + (1)*v 85 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 126 + (1)*v 127 + (1)*v 169 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)=-u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (1) (-2,-2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (1) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2842


theorem actual_signed_negative_source_2934 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 0 + (1)*v 31 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 60 + (1)*v 61 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 90 + (1)*v 91 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 120 + (1)*v 121 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 150 + (1)*v 151 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 180 + (1)*v 181 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)=-u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (1) (-2,-2,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (1) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2934


theorem actual_signed_negative_source_2938 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 0 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 30 + (1)*v 32 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 60 + (1)*v 62 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 90 + (1)*v 92 + (1)*v 122 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 150 + (1)*v 152 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 180 + (1)*v 182 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)=-u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (2) (0,-2,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (2) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2938


theorem actual_signed_negative_source_3034 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 0 + (1)*v 16 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 30 + (1)*v 46 + (1)*v 76 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 90 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 120 + (1)*v 136 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 150 + (1)*v 166 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 180 + (1)*v 196 = 0 := by
  have hroot : root 35 f 14=u7 := by simp [root_signed_14,h5,h7]
  have hr : (Nat.lcm 35 (14^2):ℚ)*((1:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 14*ε*I^(2*m)=-u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 14 (1) (0,-2,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    14 (by decide) (by decide) (1) 45 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_3034


theorem actual_signed_negative_source_3066 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((u7*primeParameter 7 m s)))*v 0 + (1)*v 12 + (1)*v 26 + ((1)/((u7*primeParameter 7 m s)))*v 28 + ((1)/((u7*primeParameter 7 m s)))*v 42 + (1)*v 54 + ((1)/((u7*primeParameter 7 m s)))*v 70 + (1)*v 96 + (1)*v 110 + ((1)/((u7*primeParameter 7 m s)))*v 112 + ((1)/((u7*primeParameter 7 m s)))*v 126 + (1)*v 152 + ((1)/((u7*primeParameter 7 m s)))*v 168 + (1)*v 180 + (1)*v 194 + ((1)/((u7*primeParameter 7 m s)))*v 196 = 0 := by
  have hroot : root 35 f 15=u5 := by simp [root_signed_15,h5,h7]
  have hr : (Nat.lcm 35 (15^2):ℚ)*((-2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 15*ε*I^(2*m)=-u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 15 (-2) (0,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    15 (by decide) (by decide) (-2) 28 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_3066

theorem actual_negative_source_3110 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 7 + (1)*v 49 + (1)*v 77 + (1)*v 91 + (1)*v 119 + (1)*v 133 + (1)*v 161 + (1)*v 203 = 0 := by
  have hh := pole_full_entire hm hf BG G hG hGF s v hv 30 (by decide) (by decide)
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex] at hh
  linear_combination hh

#print axioms actual_negative_source_3110


theorem actual_signed_negative_source_3122 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 0 + (1)*v 7 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 12 + (1)*v 13 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 18 + (1)*v 19 + (1)*v 25 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 30 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 36 + (1)*v 37 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 42 + (1)*v 49 + (1)*v 55 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 60 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 66 + (1)*v 67 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 72 + (1)*v 73 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 78 + (1)*v 79 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 96 + (1)*v 97 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 102 + (1)*v 103 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 108 + (1)*v 109 + (1)*v 115 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 120 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 126 + (1)*v 133 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 138 + (1)*v 139 + (1)*v 145 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 150 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 156 + (1)*v 157 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 162 + (1)*v 163 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 168 + (1)*v 175 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 180 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 186 + (1)*v 187 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 192 + (1)*v 193 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 198 + (1)*v 199 + (1)*v 205 = 0 := by
  have hroot : root 35 f 35=u5*u7 := by simp [root_signed_35,h5,h7]
  have hr : (Nat.lcm 35 (35^2):ℚ)*((1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 35*ε*I^(2*m)=-u5^(0:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 35 (1) (-2,-2,0,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    35 (by decide) (by decide) (1) 36 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_3122


theorem actual_negative_source_3224 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 11 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 22 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 44 + (1)*v 116 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 11
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3224


theorem actual_negative_source_3228 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 13 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 26 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 52 + (1)*v 118 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 13
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3228


theorem actual_negative_source_3234 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 16 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 32 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 64 + (1)*v 121 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 16
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3234


theorem actual_negative_source_3236 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 17 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 34 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 68 + (1)*v 122 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 17
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3236

theorem actual_negative_source_3240 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 19 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 38 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 76 + (1)*v 124 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 19
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3240


theorem actual_negative_source_3246 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 22 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 44 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 88 + (1)*v 127 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 22
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3246


theorem actual_negative_source_3248 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 23 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 46 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 92 + (1)*v 128 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 23
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3248


theorem actual_negative_source_3254 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 26 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 52 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 104 + (1)*v 131 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 26
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3254


theorem actual_negative_source_3264 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 31 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 62 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 124 + (1)*v 136 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 31
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3264


theorem actual_negative_source_3278 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 38 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 76 + (1)*v 143 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 152 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 38
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3278

theorem actual_negative_source_3288 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 43 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 86 + (1)*v 148 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 172 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 43
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3288


theorem actual_negative_source_3296 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 47 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 94 + (1)*v 152 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 188 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 47
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3296


theorem actual_negative_source_3300 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 49 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 98 + (1)*v 154 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 196 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 49
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3300


theorem actual_negative_source_3306 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 52 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 104 + (1)*v 157 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 208 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 52
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3306


theorem actual_negative_source_3308 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 2 + (1)*v 53 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 106 + (1)*v 158 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 53
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3308


theorem actual_negative_source_3314 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 14 + (1)*v 56 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 112 + (1)*v 161 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 56
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3314

theorem actual_negative_source_3318 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 22 + (1)*v 58 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 116 + (1)*v 163 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 58
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3318


theorem actual_negative_source_3324 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 34 + (1)*v 61 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 122 + (1)*v 166 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 61
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3324


theorem actual_negative_source_3330 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 46 + (1)*v 64 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 128 + (1)*v 169 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 64
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3330


theorem actual_negative_source_3336 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 58 + (1)*v 67 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 134 + (1)*v 172 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 67
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3336


theorem actual_negative_source_3354 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 76 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 94 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 152 + (1)*v 181 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 76
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3354


theorem actual_negative_source_3360 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 79 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 106 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 158 + (1)*v 184 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 79
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3360

theorem actual_negative_source_3374 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 86 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 134 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 172 + (1)*v 191 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 86
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3374


theorem actual_negative_source_3378 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 88 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 142 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 176 + (1)*v 193 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 88
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3378


theorem actual_negative_source_3390 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 94 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 166 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 188 + (1)*v 199 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 94
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3390


theorem actual_negative_source_3396 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 97 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 178 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 194 + (1)*v 202 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 97
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3396


theorem actual_negative_source_3446 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 17 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 51 + (1)*v 87 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 153 + (1)*v 157 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 17
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3446


theorem actual_negative_source_3450 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 19 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 57 + (1)*v 89 + (1)*v 159 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 171 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 19
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3450

theorem actual_negative_source_3540 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 64 + (1)*v 134 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 156 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 192 + (1)*v 204 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 64
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3540

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveOriginalAnalyticRowBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRows
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

certificate_batch {
theorem analytic_signed_negative_row0 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced0 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced0 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_34 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_372 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2790 hm hf BG G hG hGF s
  · exact analytic_short_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2852 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3006 hm hf BG G hG hGF s
  · exact analytic_short_source_3032 hm hf BG G hG hGF s
  · exact analytic_short_source_3058 hm hf BG G hG hGF s
  · exact analytic_short_source_3084 hm hf BG G hG hGF s
  · exact analytic_short_source_3206 hm hf BG G hG hGF s
  · exact analytic_short_source_3210 hm hf BG G hG hGF s
  · exact analytic_short_source_3212 hm hf BG G hG hGF s
  · exact analytic_short_source_3216 hm hf BG G hG hGF s
  · exact analytic_short_source_3226 hm hf BG G hG hGF s
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3238 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3250 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3304 hm hf BG G hG hGF s
  · exact analytic_short_source_3310 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3364 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s
  · exact analytic_short_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row0

theorem analytic_signed_negative_row104 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced104 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced104 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_62 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2790 hm hf BG G hG hGF s
  · exact analytic_short_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2858 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2860 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3006 hm hf BG G hG hGF s
  · exact analytic_short_source_3058 hm hf BG G hG hGF s
  · exact analytic_short_source_3084 hm hf BG G hG hGF s
  · exact analytic_short_source_3174 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3206 hm hf BG G hG hGF s
  · exact analytic_short_source_3212 hm hf BG G hG hGF s
  · exact analytic_short_source_3216 hm hf BG G hG hGF s
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3376 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s
  · exact analytic_short_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row104

theorem analytic_signed_negative_row13 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced13 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced13 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2790 hm hf BG G hG hGF s
  · exact analytic_short_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2952 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3006 hm hf BG G hG hGF s
  · exact analytic_short_source_3032 hm hf BG G hG hGF s
  · exact analytic_short_source_3058 hm hf BG G hG hGF s
  · exact analytic_short_source_3084 hm hf BG G hG hGF s
  · exact analytic_short_source_3158 hm hf BG G hG hGF s
  · exact analytic_short_source_3206 hm hf BG G hG hGF s
  · exact analytic_short_source_3212 hm hf BG G hG hGF s
  · exact analytic_short_source_3216 hm hf BG G hG hGF s
  · exact analytic_short_source_3226 hm hf BG G hG hGF s
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3250 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3310 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s
  · exact analytic_short_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row13

theorem analytic_signed_negative_row14 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced14 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced14 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2790 hm hf BG G hG hGF s
  · exact analytic_short_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2954 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3006 hm hf BG G hG hGF s
  · exact analytic_short_source_3032 hm hf BG G hG hGF s
  · exact analytic_short_source_3058 hm hf BG G hG hGF s
  · exact analytic_short_source_3084 hm hf BG G hG hGF s
  · exact analytic_short_source_3206 hm hf BG G hG hGF s
  · exact analytic_short_source_3212 hm hf BG G hG hGF s
  · exact analytic_short_source_3216 hm hf BG G hG hGF s
  · exact analytic_short_source_3226 hm hf BG G hG hGF s
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3250 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3310 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s
  · exact analytic_short_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row14

theorem analytic_signed_negative_row163 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced163 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced163 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_382 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_398 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2790 hm hf BG G hG hGF s
  · exact analytic_short_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2860 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3006 hm hf BG G hG hGF s
  · exact analytic_short_source_3032 hm hf BG G hG hGF s
  · exact analytic_short_source_3058 hm hf BG G hG hGF s
  · exact analytic_short_source_3084 hm hf BG G hG hGF s
  · exact analytic_short_source_3206 hm hf BG G hG hGF s
  · exact analytic_short_source_3210 hm hf BG G hG hGF s
  · exact analytic_short_source_3212 hm hf BG G hG hGF s
  · exact analytic_short_source_3216 hm hf BG G hG hGF s
  · exact analytic_short_source_3226 hm hf BG G hG hGF s
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3250 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3304 hm hf BG G hG hGF s
  · exact analytic_short_source_3310 hm hf BG G hG hGF s
  · exact analytic_short_source_3358 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s
  · exact analytic_short_source_3476 hm hf BG G hG hGF s
  · exact analytic_short_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row163

theorem analytic_signed_negative_row164 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced164 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced164 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_370 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_394 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2790 hm hf BG G hG hGF s
  · exact analytic_short_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2858 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3006 hm hf BG G hG hGF s
  · exact analytic_short_source_3032 hm hf BG G hG hGF s
  · exact analytic_short_source_3058 hm hf BG G hG hGF s
  · exact analytic_short_source_3084 hm hf BG G hG hGF s
  · exact analytic_short_source_3206 hm hf BG G hG hGF s
  · exact analytic_short_source_3212 hm hf BG G hG hGF s
  · exact analytic_short_source_3216 hm hf BG G hG hGF s
  · exact analytic_short_source_3226 hm hf BG G hG hGF s
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3250 hm hf BG G hG hGF s
  · exact analytic_short_source_3256 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3310 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s
  · exact analytic_short_source_3478 hm hf BG G hG hGF s
  · exact analytic_short_source_3488 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row164

theorem analytic_signed_negative_row16 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced16 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced16 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_54 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_372 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2790 hm hf BG G hG hGF s
  · exact analytic_short_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2958 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3006 hm hf BG G hG hGF s
  · exact analytic_short_source_3032 hm hf BG G hG hGF s
  · exact analytic_short_source_3058 hm hf BG G hG hGF s
  · exact analytic_short_source_3084 hm hf BG G hG hGF s
  · exact analytic_short_source_3206 hm hf BG G hG hGF s
  · exact analytic_short_source_3210 hm hf BG G hG hGF s
  · exact analytic_short_source_3212 hm hf BG G hG hGF s
  · exact analytic_short_source_3216 hm hf BG G hG hGF s
  · exact analytic_short_source_3226 hm hf BG G hG hGF s
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3250 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3304 hm hf BG G hG hGF s
  · exact analytic_short_source_3310 hm hf BG G hG hGF s
  · exact analytic_short_source_3340 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3376 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s
  · exact analytic_short_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row16

theorem analytic_signed_negative_row19 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced19 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced19 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_62 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2790 hm hf BG G hG hGF s
  · exact analytic_short_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2860 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2964 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3006 hm hf BG G hG hGF s
  · exact analytic_short_source_3032 hm hf BG G hG hGF s
  · exact analytic_short_source_3058 hm hf BG G hG hGF s
  · exact analytic_short_source_3084 hm hf BG G hG hGF s
  · exact analytic_short_source_3206 hm hf BG G hG hGF s
  · exact analytic_short_source_3210 hm hf BG G hG hGF s
  · exact analytic_short_source_3212 hm hf BG G hG hGF s
  · exact analytic_short_source_3216 hm hf BG G hG hGF s
  · exact analytic_short_source_3226 hm hf BG G hG hGF s
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3250 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3304 hm hf BG G hG hGF s
  · exact analytic_short_source_3310 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3376 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s
  · exact analytic_short_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row19

theorem analytic_signed_negative_row21 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced21 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced21 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_34 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2790 hm hf BG G hG hGF s
  · exact analytic_short_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2860 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2968 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3006 hm hf BG G hG hGF s
  · exact analytic_short_source_3032 hm hf BG G hG hGF s
  · exact analytic_short_source_3058 hm hf BG G hG hGF s
  · exact analytic_short_source_3084 hm hf BG G hG hGF s
  · exact analytic_short_source_3206 hm hf BG G hG hGF s
  · exact analytic_short_source_3210 hm hf BG G hG hGF s
  · exact analytic_short_source_3212 hm hf BG G hG hGF s
  · exact analytic_short_source_3216 hm hf BG G hG hGF s
  · exact analytic_short_source_3226 hm hf BG G hG hGF s
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3250 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3304 hm hf BG G hG hGF s
  · exact analytic_short_source_3310 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3376 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s
  · exact analytic_short_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row21

theorem analytic_signed_negative_row26 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced26 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced26 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_292 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2790 hm hf BG G hG hGF s
  · exact analytic_short_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2978 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3006 hm hf BG G hG hGF s
  · exact analytic_short_source_3032 hm hf BG G hG hGF s
  · exact analytic_short_source_3058 hm hf BG G hG hGF s
  · exact analytic_short_source_3084 hm hf BG G hG hGF s
  · exact analytic_short_source_3206 hm hf BG G hG hGF s
  · exact analytic_short_source_3210 hm hf BG G hG hGF s
  · exact analytic_short_source_3212 hm hf BG G hG hGF s
  · exact analytic_short_source_3216 hm hf BG G hG hGF s
  · exact analytic_short_source_3226 hm hf BG G hG hGF s
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3250 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3274 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3304 hm hf BG G hG hGF s
  · exact analytic_short_source_3310 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3364 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s
  · exact analytic_short_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row26

theorem analytic_signed_negative_row3 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced3 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced3 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2870 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3006 hm hf BG G hG hGF s
  · exact analytic_short_source_3032 hm hf BG G hG hGF s
  · exact analytic_short_source_3058 hm hf BG G hG hGF s
  · exact analytic_short_source_3084 hm hf BG G hG hGF s
  · exact analytic_short_source_3206 hm hf BG G hG hGF s
  · exact analytic_short_source_3212 hm hf BG G hG hGF s
  · exact analytic_short_source_3216 hm hf BG G hG hGF s
  · exact analytic_short_source_3226 hm hf BG G hG hGF s
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3250 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3310 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3376 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row3

theorem analytic_signed_negative_row45 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced45 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced45 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2790 hm hf BG G hG hGF s
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_3026 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row45

theorem analytic_signed_negative_row53 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced53 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced53 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_320 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3006 hm hf BG G hG hGF s
  · exact analytic_short_source_3046 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3058 hm hf BG G hG hGF s
  · exact analytic_short_source_3084 hm hf BG G hG hGF s
  · exact analytic_short_source_3212 hm hf BG G hG hGF s
  · exact analytic_short_source_3216 hm hf BG G hG hGF s
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row53

theorem analytic_signed_negative_row9 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced9 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced9 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s))
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G
  intro i
  fin_cases i
  · exact analytic_short_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_34 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_short_source_2790 hm hf BG G hG hGF s
  · exact analytic_short_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2840 hm hf BG G hG hGF s
  · exact analytic_short_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2860 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2932 hm hf BG G hG hGF s
  · exact analytic_short_source_2942 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_short_source_3006 hm hf BG G hG hGF s
  · exact analytic_short_source_3032 hm hf BG G hG hGF s
  · exact analytic_short_source_3058 hm hf BG G hG hGF s
  · exact analytic_short_source_3084 hm hf BG G hG hGF s
  · exact analytic_short_source_3206 hm hf BG G hG hGF s
  · exact analytic_short_source_3210 hm hf BG G hG hGF s
  · exact analytic_short_source_3212 hm hf BG G hG hGF s
  · exact analytic_short_source_3216 hm hf BG G hG hGF s
  · exact analytic_short_source_3226 hm hf BG G hG hGF s
  · exact analytic_short_source_3232 hm hf BG G hG hGF s
  · exact analytic_short_source_3238 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3250 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3298 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3304 hm hf BG G hG hGF s
  · exact analytic_short_source_3310 hm hf BG G hG hGF s
  · exact analytic_short_source_3358 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s
  · exact analytic_short_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_row9

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

