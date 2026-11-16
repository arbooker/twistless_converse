module
public meta import SmallLevelCertificateBatchCommandV1
public import QuantitativeArithmeticSmallLevelThirtyFiveKnownWordsPositiveSourcesChapterV1

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

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveOriginalPositiveAnalyticRowBundleV4 -/
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
open QuantitativeArithmeticSmallLevelThirtyFivePositiveAnalyticShortRows
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

certificate_batch {
theorem analytic_signed_positive_row0 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
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
  · exact analytic_positive_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_34 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_372 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2790 hm hf BG G hG hGF s
  · exact analytic_positive_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2840 hm hf BG G hG hGF s
  · exact analytic_positive_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2852 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2932 hm hf BG G hG hGF s
  · exact analytic_positive_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_3006 hm hf BG G hG hGF s
  · exact analytic_positive_source_3032 hm hf BG G hG hGF s
  · exact analytic_positive_source_3058 hm hf BG G hG hGF s
  · exact analytic_positive_source_3084 hm hf BG G hG hGF s
  · exact analytic_positive_source_3206 hm hf BG G hG hGF s
  · exact analytic_positive_source_3210 hm hf BG G hG hGF s
  · exact analytic_positive_source_3212 hm hf BG G hG hGF s
  · exact analytic_positive_source_3216 hm hf BG G hG hGF s
  · exact analytic_positive_source_3226 hm hf BG G hG hGF s
  · exact analytic_positive_source_3232 hm hf BG G hG hGF s
  · exact analytic_positive_source_3238 hm hf BG G hG hGF s
  · exact analytic_positive_source_3242 hm hf BG G hG hGF s
  · exact analytic_positive_source_3250 hm hf BG G hG hGF s
  · exact analytic_positive_source_3262 hm hf BG G hG hGF s
  · exact analytic_positive_source_3292 hm hf BG G hG hGF s
  · exact analytic_positive_source_3302 hm hf BG G hG hGF s
  · exact analytic_positive_source_3304 hm hf BG G hG hGF s
  · exact analytic_positive_source_3310 hm hf BG G hG hGF s
  · exact analytic_positive_source_3362 hm hf BG G hG hGF s
  · exact analytic_positive_source_3364 hm hf BG G hG hGF s
  · exact analytic_positive_source_3392 hm hf BG G hG hGF s
  · exact analytic_positive_source_3426 hm hf BG G hG hGF s
  · exact analytic_positive_source_3432 hm hf BG G hG hGF s
  · exact analytic_positive_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_positive_row0

theorem analytic_signed_positive_row13 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
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
  · exact analytic_positive_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2790 hm hf BG G hG hGF s
  · exact analytic_positive_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2840 hm hf BG G hG hGF s
  · exact analytic_positive_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2932 hm hf BG G hG hGF s
  · exact analytic_positive_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2952 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_3006 hm hf BG G hG hGF s
  · exact analytic_positive_source_3032 hm hf BG G hG hGF s
  · exact analytic_positive_source_3058 hm hf BG G hG hGF s
  · exact analytic_positive_source_3084 hm hf BG G hG hGF s
  · exact analytic_positive_source_3158 hm hf BG G hG hGF s
  · exact analytic_positive_source_3206 hm hf BG G hG hGF s
  · exact analytic_positive_source_3212 hm hf BG G hG hGF s
  · exact analytic_positive_source_3216 hm hf BG G hG hGF s
  · exact analytic_positive_source_3226 hm hf BG G hG hGF s
  · exact analytic_positive_source_3232 hm hf BG G hG hGF s
  · exact analytic_positive_source_3242 hm hf BG G hG hGF s
  · exact analytic_positive_source_3250 hm hf BG G hG hGF s
  · exact analytic_positive_source_3262 hm hf BG G hG hGF s
  · exact analytic_positive_source_3292 hm hf BG G hG hGF s
  · exact analytic_positive_source_3302 hm hf BG G hG hGF s
  · exact analytic_positive_source_3310 hm hf BG G hG hGF s
  · exact analytic_positive_source_3362 hm hf BG G hG hGF s
  · exact analytic_positive_source_3392 hm hf BG G hG hGF s
  · exact analytic_positive_source_3426 hm hf BG G hG hGF s
  · exact analytic_positive_source_3432 hm hf BG G hG hGF s
  · exact analytic_positive_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_positive_row13

theorem analytic_signed_positive_row14 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
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
  · exact analytic_positive_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2790 hm hf BG G hG hGF s
  · exact analytic_positive_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2840 hm hf BG G hG hGF s
  · exact analytic_positive_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2932 hm hf BG G hG hGF s
  · exact analytic_positive_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2954 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_3006 hm hf BG G hG hGF s
  · exact analytic_positive_source_3032 hm hf BG G hG hGF s
  · exact analytic_positive_source_3058 hm hf BG G hG hGF s
  · exact analytic_positive_source_3084 hm hf BG G hG hGF s
  · exact analytic_positive_source_3206 hm hf BG G hG hGF s
  · exact analytic_positive_source_3212 hm hf BG G hG hGF s
  · exact analytic_positive_source_3216 hm hf BG G hG hGF s
  · exact analytic_positive_source_3226 hm hf BG G hG hGF s
  · exact analytic_positive_source_3232 hm hf BG G hG hGF s
  · exact analytic_positive_source_3242 hm hf BG G hG hGF s
  · exact analytic_positive_source_3250 hm hf BG G hG hGF s
  · exact analytic_positive_source_3262 hm hf BG G hG hGF s
  · exact analytic_positive_source_3292 hm hf BG G hG hGF s
  · exact analytic_positive_source_3302 hm hf BG G hG hGF s
  · exact analytic_positive_source_3310 hm hf BG G hG hGF s
  · exact analytic_positive_source_3362 hm hf BG G hG hGF s
  · exact analytic_positive_source_3392 hm hf BG G hG hGF s
  · exact analytic_positive_source_3426 hm hf BG G hG hGF s
  · exact analytic_positive_source_3432 hm hf BG G hG hGF s
  · exact analytic_positive_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_positive_row14

theorem analytic_signed_positive_row150 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced150 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced150 (primeParameter 2 m) (primeParameter 3 m)
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
  · exact analytic_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2840 hm hf BG G hG hGF s
  · exact analytic_positive_source_2932 hm hf BG G hG hGF s
  · exact analytic_positive_source_3058 hm hf BG G hG hGF s
  · exact analytic_positive_source_3216 hm hf BG G hG hGF s
  · exact analytic_positive_source_3292 hm hf BG G hG hGF s
  · exact analytic_positive_source_3432 hm hf BG G hG hGF s
  · exact analytic_positive_source_3440 hm hf BG G hG hGF s

#print axioms analytic_signed_positive_row150

theorem analytic_signed_positive_row159 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced159 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced159 (primeParameter 2 m) (primeParameter 3 m)
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
  · exact analytic_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2840 hm hf BG G hG hGF s
  · exact analytic_positive_source_2932 hm hf BG G hG hGF s
  · exact analytic_positive_source_3216 hm hf BG G hG hGF s
  · exact analytic_positive_source_3232 hm hf BG G hG hGF s
  · exact analytic_positive_source_3468 hm hf BG G hG hGF s

#print axioms analytic_signed_positive_row159

theorem analytic_signed_positive_row163 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
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
  · exact analytic_positive_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_382 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_398 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2790 hm hf BG G hG hGF s
  · exact analytic_positive_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2840 hm hf BG G hG hGF s
  · exact analytic_positive_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2860 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2932 hm hf BG G hG hGF s
  · exact analytic_positive_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_3006 hm hf BG G hG hGF s
  · exact analytic_positive_source_3032 hm hf BG G hG hGF s
  · exact analytic_positive_source_3058 hm hf BG G hG hGF s
  · exact analytic_positive_source_3084 hm hf BG G hG hGF s
  · exact analytic_positive_source_3206 hm hf BG G hG hGF s
  · exact analytic_positive_source_3210 hm hf BG G hG hGF s
  · exact analytic_positive_source_3212 hm hf BG G hG hGF s
  · exact analytic_positive_source_3216 hm hf BG G hG hGF s
  · exact analytic_positive_source_3226 hm hf BG G hG hGF s
  · exact analytic_positive_source_3232 hm hf BG G hG hGF s
  · exact analytic_positive_source_3242 hm hf BG G hG hGF s
  · exact analytic_positive_source_3250 hm hf BG G hG hGF s
  · exact analytic_positive_source_3262 hm hf BG G hG hGF s
  · exact analytic_positive_source_3292 hm hf BG G hG hGF s
  · exact analytic_positive_source_3302 hm hf BG G hG hGF s
  · exact analytic_positive_source_3304 hm hf BG G hG hGF s
  · exact analytic_positive_source_3310 hm hf BG G hG hGF s
  · exact analytic_positive_source_3358 hm hf BG G hG hGF s
  · exact analytic_positive_source_3362 hm hf BG G hG hGF s
  · exact analytic_positive_source_3392 hm hf BG G hG hGF s
  · exact analytic_positive_source_3426 hm hf BG G hG hGF s
  · exact analytic_positive_source_3432 hm hf BG G hG hGF s
  · exact analytic_positive_source_3476 hm hf BG G hG hGF s
  · exact analytic_positive_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_positive_row163

theorem analytic_signed_positive_row164 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
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
  · exact analytic_positive_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_370 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_394 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2790 hm hf BG G hG hGF s
  · exact analytic_positive_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2840 hm hf BG G hG hGF s
  · exact analytic_positive_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2858 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2932 hm hf BG G hG hGF s
  · exact analytic_positive_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_3006 hm hf BG G hG hGF s
  · exact analytic_positive_source_3032 hm hf BG G hG hGF s
  · exact analytic_positive_source_3058 hm hf BG G hG hGF s
  · exact analytic_positive_source_3084 hm hf BG G hG hGF s
  · exact analytic_positive_source_3206 hm hf BG G hG hGF s
  · exact analytic_positive_source_3212 hm hf BG G hG hGF s
  · exact analytic_positive_source_3216 hm hf BG G hG hGF s
  · exact analytic_positive_source_3226 hm hf BG G hG hGF s
  · exact analytic_positive_source_3232 hm hf BG G hG hGF s
  · exact analytic_positive_source_3242 hm hf BG G hG hGF s
  · exact analytic_positive_source_3250 hm hf BG G hG hGF s
  · exact analytic_positive_source_3256 hm hf BG G hG hGF s
  · exact analytic_positive_source_3262 hm hf BG G hG hGF s
  · exact analytic_positive_source_3292 hm hf BG G hG hGF s
  · exact analytic_positive_source_3302 hm hf BG G hG hGF s
  · exact analytic_positive_source_3310 hm hf BG G hG hGF s
  · exact analytic_positive_source_3362 hm hf BG G hG hGF s
  · exact analytic_positive_source_3392 hm hf BG G hG hGF s
  · exact analytic_positive_source_3426 hm hf BG G hG hGF s
  · exact analytic_positive_source_3432 hm hf BG G hG hGF s
  · exact analytic_positive_source_3478 hm hf BG G hG hGF s
  · exact analytic_positive_source_3488 hm hf BG G hG hGF s

#print axioms analytic_signed_positive_row164

theorem analytic_signed_positive_row16 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
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
  · exact analytic_positive_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_54 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_372 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2790 hm hf BG G hG hGF s
  · exact analytic_positive_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2840 hm hf BG G hG hGF s
  · exact analytic_positive_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2932 hm hf BG G hG hGF s
  · exact analytic_positive_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2958 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_3006 hm hf BG G hG hGF s
  · exact analytic_positive_source_3032 hm hf BG G hG hGF s
  · exact analytic_positive_source_3058 hm hf BG G hG hGF s
  · exact analytic_positive_source_3084 hm hf BG G hG hGF s
  · exact analytic_positive_source_3206 hm hf BG G hG hGF s
  · exact analytic_positive_source_3210 hm hf BG G hG hGF s
  · exact analytic_positive_source_3212 hm hf BG G hG hGF s
  · exact analytic_positive_source_3216 hm hf BG G hG hGF s
  · exact analytic_positive_source_3226 hm hf BG G hG hGF s
  · exact analytic_positive_source_3232 hm hf BG G hG hGF s
  · exact analytic_positive_source_3242 hm hf BG G hG hGF s
  · exact analytic_positive_source_3250 hm hf BG G hG hGF s
  · exact analytic_positive_source_3262 hm hf BG G hG hGF s
  · exact analytic_positive_source_3292 hm hf BG G hG hGF s
  · exact analytic_positive_source_3302 hm hf BG G hG hGF s
  · exact analytic_positive_source_3304 hm hf BG G hG hGF s
  · exact analytic_positive_source_3310 hm hf BG G hG hGF s
  · exact analytic_positive_source_3340 hm hf BG G hG hGF s
  · exact analytic_positive_source_3362 hm hf BG G hG hGF s
  · exact analytic_positive_source_3376 hm hf BG G hG hGF s
  · exact analytic_positive_source_3392 hm hf BG G hG hGF s
  · exact analytic_positive_source_3426 hm hf BG G hG hGF s
  · exact analytic_positive_source_3432 hm hf BG G hG hGF s
  · exact analytic_positive_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_positive_row16

theorem analytic_signed_positive_row18 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun t => reduced18 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reduced18 (primeParameter 2 m) (primeParameter 3 m)
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
  · exact analytic_positive_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2790 hm hf BG G hG hGF s
  · exact analytic_positive_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2840 hm hf BG G hG hGF s
  · exact analytic_positive_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2858 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2932 hm hf BG G hG hGF s
  · exact analytic_positive_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2962 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_3006 hm hf BG G hG hGF s
  · exact analytic_positive_source_3032 hm hf BG G hG hGF s
  · exact analytic_positive_source_3058 hm hf BG G hG hGF s
  · exact analytic_positive_source_3084 hm hf BG G hG hGF s
  · exact analytic_positive_source_3206 hm hf BG G hG hGF s
  · exact analytic_positive_source_3210 hm hf BG G hG hGF s
  · exact analytic_positive_source_3212 hm hf BG G hG hGF s
  · exact analytic_positive_source_3216 hm hf BG G hG hGF s
  · exact analytic_positive_source_3226 hm hf BG G hG hGF s
  · exact analytic_positive_source_3232 hm hf BG G hG hGF s
  · exact analytic_positive_source_3242 hm hf BG G hG hGF s
  · exact analytic_positive_source_3250 hm hf BG G hG hGF s
  · exact analytic_positive_source_3262 hm hf BG G hG hGF s
  · exact analytic_positive_source_3292 hm hf BG G hG hGF s
  · exact analytic_positive_source_3302 hm hf BG G hG hGF s
  · exact analytic_positive_source_3304 hm hf BG G hG hGF s
  · exact analytic_positive_source_3310 hm hf BG G hG hGF s
  · exact analytic_positive_source_3362 hm hf BG G hG hGF s
  · exact analytic_positive_source_3392 hm hf BG G hG hGF s
  · exact analytic_positive_source_3426 hm hf BG G hG hGF s
  · exact analytic_positive_source_3432 hm hf BG G hG hGF s
  · exact analytic_positive_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_positive_row18

theorem analytic_signed_positive_row19 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
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
  · exact analytic_positive_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_62 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2790 hm hf BG G hG hGF s
  · exact analytic_positive_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2840 hm hf BG G hG hGF s
  · exact analytic_positive_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2860 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2932 hm hf BG G hG hGF s
  · exact analytic_positive_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2964 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_3006 hm hf BG G hG hGF s
  · exact analytic_positive_source_3032 hm hf BG G hG hGF s
  · exact analytic_positive_source_3058 hm hf BG G hG hGF s
  · exact analytic_positive_source_3084 hm hf BG G hG hGF s
  · exact analytic_positive_source_3206 hm hf BG G hG hGF s
  · exact analytic_positive_source_3210 hm hf BG G hG hGF s
  · exact analytic_positive_source_3212 hm hf BG G hG hGF s
  · exact analytic_positive_source_3216 hm hf BG G hG hGF s
  · exact analytic_positive_source_3226 hm hf BG G hG hGF s
  · exact analytic_positive_source_3232 hm hf BG G hG hGF s
  · exact analytic_positive_source_3242 hm hf BG G hG hGF s
  · exact analytic_positive_source_3250 hm hf BG G hG hGF s
  · exact analytic_positive_source_3262 hm hf BG G hG hGF s
  · exact analytic_positive_source_3292 hm hf BG G hG hGF s
  · exact analytic_positive_source_3302 hm hf BG G hG hGF s
  · exact analytic_positive_source_3304 hm hf BG G hG hGF s
  · exact analytic_positive_source_3310 hm hf BG G hG hGF s
  · exact analytic_positive_source_3362 hm hf BG G hG hGF s
  · exact analytic_positive_source_3376 hm hf BG G hG hGF s
  · exact analytic_positive_source_3392 hm hf BG G hG hGF s
  · exact analytic_positive_source_3426 hm hf BG G hG hGF s
  · exact analytic_positive_source_3432 hm hf BG G hG hGF s
  · exact analytic_positive_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_positive_row19

theorem analytic_signed_positive_row3 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
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
  · exact analytic_positive_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2840 hm hf BG G hG hGF s
  · exact analytic_positive_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2870 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2932 hm hf BG G hG hGF s
  · exact analytic_positive_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_3006 hm hf BG G hG hGF s
  · exact analytic_positive_source_3032 hm hf BG G hG hGF s
  · exact analytic_positive_source_3058 hm hf BG G hG hGF s
  · exact analytic_positive_source_3084 hm hf BG G hG hGF s
  · exact analytic_positive_source_3206 hm hf BG G hG hGF s
  · exact analytic_positive_source_3212 hm hf BG G hG hGF s
  · exact analytic_positive_source_3216 hm hf BG G hG hGF s
  · exact analytic_positive_source_3226 hm hf BG G hG hGF s
  · exact analytic_positive_source_3232 hm hf BG G hG hGF s
  · exact analytic_positive_source_3242 hm hf BG G hG hGF s
  · exact analytic_positive_source_3250 hm hf BG G hG hGF s
  · exact analytic_positive_source_3262 hm hf BG G hG hGF s
  · exact analytic_positive_source_3292 hm hf BG G hG hGF s
  · exact analytic_positive_source_3302 hm hf BG G hG hGF s
  · exact analytic_positive_source_3310 hm hf BG G hG hGF s
  · exact analytic_positive_source_3362 hm hf BG G hG hGF s
  · exact analytic_positive_source_3376 hm hf BG G hG hGF s
  · exact analytic_positive_source_3392 hm hf BG G hG hGF s
  · exact analytic_positive_source_3426 hm hf BG G hG hGF s
  · exact analytic_positive_source_3432 hm hf BG G hG hGF s

#print axioms analytic_signed_positive_row3

theorem analytic_signed_positive_row45 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
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
  · exact analytic_positive_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2790 hm hf BG G hG hGF s
  · exact analytic_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2840 hm hf BG G hG hGF s
  · exact analytic_positive_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2932 hm hf BG G hG hGF s
  · exact analytic_positive_source_3026 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_3232 hm hf BG G hG hGF s
  · exact analytic_positive_source_3292 hm hf BG G hG hGF s
  · exact analytic_positive_source_3432 hm hf BG G hG hGF s

#print axioms analytic_signed_positive_row45

theorem analytic_signed_positive_row53 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
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
  · exact analytic_positive_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_320 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s hshift
  · exact analytic_positive_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_2840 hm hf BG G hG hGF s
  · exact analytic_positive_source_2932 hm hf BG G hG hGF s
  · exact analytic_positive_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_3006 hm hf BG G hG hGF s
  · exact analytic_positive_source_3046 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  · exact analytic_positive_source_3058 hm hf BG G hG hGF s
  · exact analytic_positive_source_3084 hm hf BG G hG hGF s
  · exact analytic_positive_source_3212 hm hf BG G hG hGF s
  · exact analytic_positive_source_3216 hm hf BG G hG hGF s
  · exact analytic_positive_source_3232 hm hf BG G hG hGF s
  · exact analytic_positive_source_3242 hm hf BG G hG hGF s
  · exact analytic_positive_source_3262 hm hf BG G hG hGF s
  · exact analytic_positive_source_3302 hm hf BG G hG hGF s
  · exact analytic_positive_source_3362 hm hf BG G hG hGF s
  · exact analytic_positive_source_3392 hm hf BG G hG hGF s
  · exact analytic_positive_source_3426 hm hf BG G hG hGF s
  · exact analytic_positive_source_3432 hm hf BG G hG hGF s

#print axioms analytic_signed_positive_row53

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFivePositiveActualRowsBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
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
theorem actual_positive_source_0 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 0 + ((-1)*(primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))*v 207 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord000, source := 0, target := -3
    nonaffine := by norm_num [witnessWord000_matrix]
    denominator := by norm_num [integerDen,witnessWord000_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord000_matrix] }
  have hr : rationalRate witnessWord000 0=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord000_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 0)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord000 0 0 s*
    v (gridIndex (-3))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord000 0 0 s=wordCoefficient m (u5*u7) witnessWord000 0 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord000 0 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord000)=
      u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord000_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord000 0 (2,0,1,1) hr hcompat s] at hh
  norm_num [witnessWord000_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_0

theorem actual_positive_source_2 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 0 + ((-1)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))*v 204 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord001, source := 0, target := -6
    nonaffine := by norm_num [witnessWord001_matrix]
    denominator := by norm_num [integerDen,witnessWord001_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord001_matrix] }
  have hr : rationalRate witnessWord001 0=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord001_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 0)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord001 0 0 s*
    v (gridIndex (-6))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord001 0 0 s=wordCoefficient m (u5*u7) witnessWord001 0 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord001 0 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord001)=
      u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord001_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord001 0 (0,0,1,1) hr hcompat s] at hh
  norm_num [witnessWord001_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2

theorem actual_positive_source_4 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 42 + (((-1)*(primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s))/((u5*primeParameter 5 m s)))*v 205 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord001, source := 42, target := -5
    nonaffine := by norm_num [witnessWord001_matrix]
    denominator := by norm_num [integerDen,witnessWord001_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord001_matrix] }
  have hr : rationalRate witnessWord001 42=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord001_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 42)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord001 42 0 s*
    v (gridIndex (-5))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord001 42 0 s=wordCoefficient m (u5*u7) witnessWord001 42 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord001 42 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord001)=
      u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord001_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord001 42 (2,2,-1,1) hr hcompat s] at hh
  norm_num [witnessWord001_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_4

theorem actual_positive_source_8 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 0 = 0 := by
  have hh := coordinate_zero_of_germ hv 0
    (source_zero_and_six_germs hm hf BG G hG hGF s).1
  simpa only [one_mul] using hh


#print axioms actual_positive_source_8

theorem actual_positive_source_12 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 2 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 2, target := -630
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 2)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 2 0 s*
    v (gridIndex (-630))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 2 0 s=wordCoefficient m (u5*u7) witnessWord002 2 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 2 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 2 (0,-2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_12

theorem actual_positive_source_16 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 4 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 105 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 4, target := -315
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 4=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 4)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 4 0 s*
    v (gridIndex (-315))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 4 0 s=wordCoefficient m (u5*u7) witnessWord002 4 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 4 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 4 (2,-2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_16

theorem actual_positive_source_18 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 5 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 5, target := -252
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 5=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 5)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 5 0 s*
    v (gridIndex (-252))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 5 0 s=wordCoefficient m (u5*u7) witnessWord002 5 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 5 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 5 (-2,-2,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_18

theorem actual_positive_source_20 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 6 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 6, target := -210
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 6=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 6)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 6 0 s*
    v (gridIndex (-210))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 6 0 s=wordCoefficient m (u5*u7) witnessWord002 6 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 6 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 6 (0,0,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_20

theorem actual_positive_source_22 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 7 + (((-1)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 30 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 7, target := -180
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 7=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 7)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 7 0 s*
    v (gridIndex (-180))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 7 0 s=wordCoefficient m (u5*u7) witnessWord002 7 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 7 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 7 (-2,-2,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_22

theorem actual_positive_source_26 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 10 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 84 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 10, target := -126
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 10=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 10)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 10 0 s*
    v (gridIndex (-126))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 10 0 s=wordCoefficient m (u5*u7) witnessWord002 10 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 10 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 10 (0,-2,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_26

theorem actual_positive_source_28 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 12 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 105 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 12, target := -105
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 12=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 12)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 12 0 s*
    v (gridIndex (-105))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 12 0 s=wordCoefficient m (u5*u7) witnessWord002 12 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 12 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 12 (2,0,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_28

theorem actual_positive_source_30 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 14 + (((-1)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 120 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 14, target := -90
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 14=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 14)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 14 0 s*
    v (gridIndex (-90))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 14 0 s=wordCoefficient m (u5*u7) witnessWord002 14 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 14 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 14 (0,-2,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_30

theorem actual_positive_source_32 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 15 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 126 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 15, target := -84
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 15=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 15)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 15 0 s*
    v (gridIndex (-84))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 15 0 s=wordCoefficient m (u5*u7) witnessWord002 15 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 15 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 15 (-2,0,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_32

theorem actual_positive_source_34 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 18 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 140 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 18, target := -70
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 18=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 18)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 18 0 s*
    v (gridIndex (-70))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 18 0 s=wordCoefficient m (u5*u7) witnessWord002 18 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 18 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 18 (0,2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_34

theorem actual_positive_source_36 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 20 + (((-1)*(primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 147 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 20, target := -63
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 20=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 20)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 20 0 s*
    v (gridIndex (-63))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 20 0 s=wordCoefficient m (u5*u7) witnessWord002 20 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 20 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 20 (2,-2,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_36

theorem actual_positive_source_38 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 21 + (((-1)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 150 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 21, target := -60
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 21=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 21)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 21 0 s*
    v (gridIndex (-60))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 21 0 s=wordCoefficient m (u5*u7) witnessWord002 21 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 21 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 21 (-2,0,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_38

theorem actual_positive_source_40 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 28 + (((-1)*(primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 165 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 28, target := -45
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 28=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 28)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 28 0 s*
    v (gridIndex (-45))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 28 0 s=wordCoefficient m (u5*u7) witnessWord002 28 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 28 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 28 (2,-2,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_40

theorem actual_positive_source_42 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 30 + (((-1)*(u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 168 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 30, target := -42
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 30=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 30)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 30 0 s*
    v (gridIndex (-42))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 30 0 s=wordCoefficient m (u5*u7) witnessWord002 30 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 30 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 30 (0,0,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_42

theorem actual_positive_source_44 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 35 + (((-1)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 174 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 35, target := -36
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 35=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 35)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 35 0 s*
    v (gridIndex (-36))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 35 0 s=wordCoefficient m (u5*u7) witnessWord002 35 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 35 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 35 (-2,-2,1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_44

theorem actual_positive_source_46 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 36 + (((-1)*(primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 175 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 36, target := -35
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 36=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 36)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 36 0 s*
    v (gridIndex (-35))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 36 0 s=wordCoefficient m (u5*u7) witnessWord002 36 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 36 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 36 (2,2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_46

theorem actual_positive_source_48 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 42 + (((-1)*(u7*primeParameter 7 m s))/((u5*primeParameter 5 m s)))*v 180 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 42, target := -30
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 42=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 42)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 42 0 s*
    v (gridIndex (-30))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 42 0 s=wordCoefficient m (u5*u7) witnessWord002 42 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 42 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 42 (0,0,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_48

theorem actual_positive_source_50 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 45 + (((-1)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 182 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 45, target := -28
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 45=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 45)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 45 0 s*
    v (gridIndex (-28))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 45 0 s=wordCoefficient m (u5*u7) witnessWord002 45 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 45 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 45 (-2,2,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_50

theorem actual_positive_source_52 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 60 + (((-1)*(primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 189 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 60, target := -21
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 60=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 60)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 60 0 s*
    v (gridIndex (-21))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 60 0 s=wordCoefficient m (u5*u7) witnessWord002 60 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 60 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 60 (2,0,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_52

theorem actual_positive_source_54 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 63 + (((-1)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 190 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 63, target := -20
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 63=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 63)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 63 0 s*
    v (gridIndex (-20))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 63 0 s=wordCoefficient m (u5*u7) witnessWord002 63 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 63 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 63 (-2,2,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_54

theorem actual_positive_source_56 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 70 + (((-1)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 192 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 70, target := -18
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 70=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 70)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 70 0 s*
    v (gridIndex (-18))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 70 0 s=wordCoefficient m (u5*u7) witnessWord002 70 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 70 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 70 (0,-2,1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_56

theorem actual_positive_source_58 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 84 + (((-1)*(primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s))/((u5*primeParameter 5 m s)))*v 195 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 84, target := -15
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 84=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 84)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 84 0 s*
    v (gridIndex (-15))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 84 0 s=wordCoefficient m (u5*u7) witnessWord002 84 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 84 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 84 (2,0,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_58

theorem actual_positive_source_60 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 90 + (((-1)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 196 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 90, target := -14
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 90=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 90)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 90 0 s*
    v (gridIndex (-14))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 90 0 s=wordCoefficient m (u5*u7) witnessWord002 90 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 90 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 90 (0,2,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_60

theorem actual_positive_source_62 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 105 + (((-1)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)))*v 198 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 105, target := -12
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 105=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 105)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 105 0 s*
    v (gridIndex (-12))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 105 0 s=wordCoefficient m (u5*u7) witnessWord002 105 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 105 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 105 (-2,0,1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_62

theorem actual_positive_source_64 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 126 + (((-1)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s))/((u5*primeParameter 5 m s)))*v 200 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 126, target := -10
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 126=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 126)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 126 0 s*
    v (gridIndex (-10))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 126 0 s=wordCoefficient m (u5*u7) witnessWord002 126 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 126 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 126 (0,2,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_64

theorem actual_positive_source_66 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 140 + (((-1)*(primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 201 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 140, target := -9
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 140=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 140)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 140 0 s*
    v (gridIndex (-9))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 140 0 s=wordCoefficient m (u5*u7) witnessWord002 140 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 140 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 140 (2,-2,1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_66

theorem actual_positive_source_68 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 180 + (((-1)*(primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 203 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 180, target := -7
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 180=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 180)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 180 0 s*
    v (gridIndex (-7))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 180 0 s=wordCoefficient m (u5*u7) witnessWord002 180 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 180 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=
      u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 180 (2,2,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_68

theorem actual_positive_source_128 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 208 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord003, source := 208, target := 630
    nonaffine := by norm_num [witnessWord003_matrix]
    denominator := by norm_num [integerDen,witnessWord003_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord003_matrix] }
  have hr : rationalRate witnessWord003 208=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord003_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 208)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord003 208 0 s*
    v (gridIndex (630))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord003 208 0 s=wordCoefficient m (u5*u7) witnessWord003 208 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord003 208 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord003)=
      u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord003_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord003 208 (0,-2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord003_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_128

theorem actual_positive_source_150 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)*(primeParameter 3 m s)^(2:ℕ))*v 8 + (1)*v 186 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord009, source := 186, target := 8
    nonaffine := by norm_num [witnessWord009_matrix]
    denominator := by norm_num [integerDen,witnessWord009_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord009_matrix] }
  have hr : rationalRate witnessWord009 186=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord009_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 186)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord009 186 0 s*
    v (gridIndex (8))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord009 186 0 s=wordCoefficient m (u5*u7) witnessWord009 186 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord009 186 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord009)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord009_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord009 186 (0,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord009_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_150

theorem actual_positive_source_162 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 3 m s)^(2:ℕ)))*v 24 + (1)*v 202 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord009, source := 202, target := 24
    nonaffine := by norm_num [witnessWord009_matrix]
    denominator := by norm_num [integerDen,witnessWord009_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord009_matrix] }
  have hr : rationalRate witnessWord009 202=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord009_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 202)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord009 202 0 s*
    v (gridIndex (24))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord009 202 0 s=wordCoefficient m (u5*u7) witnessWord009 202 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord009 202 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord009)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord009_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord009 202 (0,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord009_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_162

theorem actual_positive_source_246 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 102 + ((-1)*(primeParameter 3 m s)^(2:ℕ))*v 208 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord027, source := 102, target := -2
    nonaffine := by norm_num [witnessWord027_matrix]
    denominator := by norm_num [integerDen,witnessWord027_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord027_matrix] }
  have hr : rationalRate witnessWord027 102=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord027_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 102)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord027 102 0 s*
    v (gridIndex (-2))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord027 102 0 s=wordCoefficient m (u5*u7) witnessWord027 102 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord027 102 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord027)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord027_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord027 102 (0,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_246

theorem actual_positive_source_248 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)))*v 0 + (1)*v 105 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord027, source := 105, target := 0
    nonaffine := by norm_num [witnessWord027_matrix]
    denominator := by norm_num [integerDen,witnessWord027_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord027_matrix] }
  have hr : rationalRate witnessWord027 105=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord027_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 105)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord027 105 0 s*
    v (gridIndex (0))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord027 105 0 s=wordCoefficient m (u5*u7) witnessWord027 105 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord027 105 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord027)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord027_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord027 105 (-2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_248

theorem actual_positive_source_252 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 108 + ((-1)*(primeParameter 2 m s)^(2:ℕ))*v 207 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord027, source := 108, target := -3
    nonaffine := by norm_num [witnessWord027_matrix]
    denominator := by norm_num [integerDen,witnessWord027_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord027_matrix] }
  have hr : rationalRate witnessWord027 108=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord027_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 108)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord027 108 0 s*
    v (gridIndex (-3))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord027 108 0 s=wordCoefficient m (u5*u7) witnessWord027 108 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord027 108 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord027)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord027_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord027 108 (2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_252

theorem actual_positive_source_262 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 107 + ((-1)/((primeParameter 2 m s)^(2:ℕ)))*v 202 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord028, source := 107, target := -8
    nonaffine := by norm_num [witnessWord028_matrix]
    denominator := by norm_num [integerDen,witnessWord028_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord028_matrix] }
  have hr : rationalRate witnessWord028 107=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord028_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 107)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord028 107 0 s*
    v (gridIndex (-8))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord028 107 0 s=wordCoefficient m (u5*u7) witnessWord028 107 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord028 107 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord028)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord028_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord028 107 (-2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord028_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_262

theorem actual_positive_source_266 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 110 + ((-1)*(primeParameter 2 m s)^(2:ℕ))*v 205 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord028, source := 110, target := -5
    nonaffine := by norm_num [witnessWord028_matrix]
    denominator := by norm_num [integerDen,witnessWord028_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord028_matrix] }
  have hr : rationalRate witnessWord028 110=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord028_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 110)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord028 110 0 s*
    v (gridIndex (-5))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord028 110 0 s=wordCoefficient m (u5*u7) witnessWord028 110 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord028 110 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord028)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord028_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord028 110 (2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord028_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_266

theorem actual_positive_source_270 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 90 + ((-1)*(primeParameter 3 m s)^(2:ℕ))*v 200 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 90, target := -10
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 90=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 90)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 90 0 s*
    v (gridIndex (-10))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord029 90 0 s=wordCoefficient m (u5*u7) witnessWord029 90 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord029 90 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord029)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord029 90 (0,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_270

theorem actual_positive_source_272 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 96 + ((-1)*(primeParameter 2 m s)^(2:ℕ))*v 201 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 96, target := -9
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 96=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 96)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 96 0 s*
    v (gridIndex (-9))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord029 96 0 s=wordCoefficient m (u5*u7) witnessWord029 96 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord029 96 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord029)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord029 96 (2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_272

theorem actual_positive_source_274 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 99 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)))*v 202 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 99, target := -8
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 99=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 99)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 99 0 s*
    v (gridIndex (-8))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord029 99 0 s=wordCoefficient m (u5*u7) witnessWord029 99 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord029 99 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord029)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord029 99 (-2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_274

theorem actual_positive_source_288 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 109 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 162 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 109, target := -48
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 109=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 109)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 109 0 s*
    v (gridIndex (-48))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord029 109 0 s=wordCoefficient m (u5*u7) witnessWord029 109 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord029 109 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord029)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord029 109 (-2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_288

theorem actual_positive_source_294 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 112 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)))*v 189 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 112, target := -21
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 112=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 112)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 112 0 s*
    v (gridIndex (-21))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord029 112 0 s=wordCoefficient m (u5*u7) witnessWord029 112 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord029 112 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord029)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord029 112 (2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_294

theorem actual_positive_source_296 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 114 + (-1)*v 192 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 114, target := -18
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 114=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 114)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 114 0 s*
    v (gridIndex (-18))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord029 114 0 s=wordCoefficient m (u5*u7) witnessWord029 114 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord029 114 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord029)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord029 114 (0,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_296

theorem actual_positive_source_298 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 117 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)))*v 194 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 117, target := -16
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 117=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 117)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 117 0 s*
    v (gridIndex (-16))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord029 117 0 s=wordCoefficient m (u5*u7) witnessWord029 117 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord029 117 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord029)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord029 117 (-2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_298

theorem actual_positive_source_300 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 120 + ((-1)*(primeParameter 2 m s)^(2:ℕ))*v 195 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 120, target := -15
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 120=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 120)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 120 0 s*
    v (gridIndex (-15))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord029 120 0 s=wordCoefficient m (u5*u7) witnessWord029 120 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord029 120 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord029)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord029 120 (2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_300

theorem actual_positive_source_312 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)))*v 16 + (1)*v 93 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord030, source := 93, target := 16
    nonaffine := by norm_num [witnessWord030_matrix]
    denominator := by norm_num [integerDen,witnessWord030_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord030_matrix] }
  have hr : rationalRate witnessWord030 93=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord030_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 93)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord030 93 0 s*
    v (gridIndex (16))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord030 93 0 s=wordCoefficient m (u5*u7) witnessWord030 93 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord030 93 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord030)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord030 93 (-2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_312

theorem actual_positive_source_316 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)))*v 21 + (1)*v 98 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord030, source := 98, target := 21
    nonaffine := by norm_num [witnessWord030_matrix]
    denominator := by norm_num [integerDen,witnessWord030_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord030_matrix] }
  have hr : rationalRate witnessWord030 98=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord030_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 98)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord030 98 0 s*
    v (gridIndex (21))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord030 98 0 s=wordCoefficient m (u5*u7) witnessWord030 98 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord030 98 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord030)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord030 98 (2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_316

theorem actual_positive_source_320 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 3 m s)^(2:ℕ)))*v 30 + (1)*v 100 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord030, source := 100, target := 30
    nonaffine := by norm_num [witnessWord030_matrix]
    denominator := by norm_num [integerDen,witnessWord030_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord030_matrix] }
  have hr : rationalRate witnessWord030 100=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord030_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 100)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord030 100 0 s*
    v (gridIndex (30))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord030 100 0 s=wordCoefficient m (u5*u7) witnessWord030 100 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord030 100 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord030)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord030 100 (0,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_320

theorem actual_positive_source_326 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 103 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 186 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord030, source := 103, target := -24
    nonaffine := by norm_num [witnessWord030_matrix]
    denominator := by norm_num [integerDen,witnessWord030_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord030_matrix] }
  have hr : rationalRate witnessWord030 103=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord030_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 103)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord030 103 0 s*
    v (gridIndex (-24))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord030 103 0 s=wordCoefficient m (u5*u7) witnessWord030 103 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord030 103 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord030)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord030 103 (-2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_326

theorem actual_positive_source_358 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 168 + ((-1)*(primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ))*v 203 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord041, source := 168, target := -7
    nonaffine := by norm_num [witnessWord041_matrix]
    denominator := by norm_num [integerDen,witnessWord041_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord041_matrix] }
  have hr : rationalRate witnessWord041 168=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord041_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 168)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord041 168 0 s*
    v (gridIndex (-7))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord041 168 0 s=wordCoefficient m (u5*u7) witnessWord041 168 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord041 168 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord041)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord041 168 (2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_358

theorem actual_positive_source_360 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 174 + (-1)*v 204 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord041, source := 174, target := -6
    nonaffine := by norm_num [witnessWord041_matrix]
    denominator := by norm_num [integerDen,witnessWord041_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord041_matrix] }
  have hr : rationalRate witnessWord041 174=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord041_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 174)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord041 174 0 s*
    v (gridIndex (-6))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord041 174 0 s=wordCoefficient m (u5*u7) witnessWord041 174 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord041 174 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord041)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord041 174 (0,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_360

theorem actual_positive_source_362 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 0 + (1)*v 175 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord041, source := 175, target := 0
    nonaffine := by norm_num [witnessWord041_matrix]
    denominator := by norm_num [integerDen,witnessWord041_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord041_matrix] }
  have hr : rationalRate witnessWord041 175=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord041_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 175)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord041 175 0 s*
    v (gridIndex (0))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord041 175 0 s=wordCoefficient m (u5*u7) witnessWord041 175 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord041 175 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord041)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord041 175 (-2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_362

theorem actual_positive_source_366 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 177 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)))*v 202 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord041, source := 177, target := -8
    nonaffine := by norm_num [witnessWord041_matrix]
    denominator := by norm_num [integerDen,witnessWord041_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord041_matrix] }
  have hr : rationalRate witnessWord041 177=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord041_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 177)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord041 177 0 s*
    v (gridIndex (-8))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord041 177 0 s=wordCoefficient m (u5*u7) witnessWord041 177 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord041 177 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord041)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord041 177 (-2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_366

theorem actual_positive_source_370 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)*(primeParameter 3 m s)^(2:ℕ))*v 38 + (1)*v 156 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 156, target := 38
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 156=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 156)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 156 0 s*
    v (gridIndex (38))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord042 156 0 s=wordCoefficient m (u5*u7) witnessWord042 156 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord042 156 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord042)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord042 156 (0,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_370

theorem actual_positive_source_372 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)*(primeParameter 2 m s)^(2:ℕ))*v 39 + (1)*v 162 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 162, target := 39
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 162=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 162)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 162 0 s*
    v (gridIndex (39))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord042 162 0 s=wordCoefficient m (u5*u7) witnessWord042 162 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord042 162 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord042)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord042 162 (2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_372

theorem actual_positive_source_374 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)))*v 40 + (1)*v 165 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 165, target := 40
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 165=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 165)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 165 0 s*
    v (gridIndex (40))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord042 165 0 s=wordCoefficient m (u5*u7) witnessWord042 165 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord042 165 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord042)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord042 165 (-2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_374

theorem actual_positive_source_378 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)))*v 45 + (1)*v 170 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 170, target := 45
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 170=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 170)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 170 0 s*
    v (gridIndex (45))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord042 170 0 s=wordCoefficient m (u5*u7) witnessWord042 170 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord042 170 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord042)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord042 170 (2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_378

theorem actual_positive_source_380 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)))*v 48 + (1)*v 171 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 171, target := 48
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 171=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 171)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 171 0 s*
    v (gridIndex (48))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord042 171 0 s=wordCoefficient m (u5*u7) witnessWord042 171 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord042 171 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord042)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord042 171 (-2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_380

theorem actual_positive_source_382 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 3 m s)^(2:ℕ)))*v 54 + (1)*v 172 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 172, target := 54
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 172=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 172)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 172 0 s*
    v (gridIndex (54))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord042 172 0 s=wordCoefficient m (u5*u7) witnessWord042 172 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord042 172 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord042)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord042 172 (0,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_382

theorem actual_positive_source_384 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 72 + (1)*v 173 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 173, target := 72
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 173=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 173)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 173 0 s*
    v (gridIndex (72))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord042 173 0 s=wordCoefficient m (u5*u7) witnessWord042 173 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord042 173 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord042)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord042 173 (-2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_384

theorem actual_positive_source_394 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)))*v 27 + (1)*v 178 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 178, target := 27
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 178=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 178)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 178 0 s*
    v (gridIndex (27))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord042 178 0 s=wordCoefficient m (u5*u7) witnessWord042 178 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord042 178 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord042)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord042 178 (2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_394

theorem actual_positive_source_398 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)))*v 32 + (1)*v 183 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 183, target := 32
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 183=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 183)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 183 0 s*
    v (gridIndex (32))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord042 183 0 s=wordCoefficient m (u5*u7) witnessWord042 183 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord042 183 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord042)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord042 183 (-2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_398

theorem actual_positive_source_400 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)*(primeParameter 2 m s)^(2:ℕ))*v 33 + (1)*v 186 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord042, source := 186, target := 33
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 186=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 186)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 186 0 s*
    v (gridIndex (33))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord042 186 0 s=wordCoefficient m (u5*u7) witnessWord042 186 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord042 186 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord042)=
      u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord042 186 (2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_400

theorem actual_positive_source_2804 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 42 + (1)*v 75 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 112 + (1)*v 145 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= u5^(1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 3 (5) (-2,0,1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (5) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2804

theorem actual_positive_source_2806 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 65 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 98 + (1)*v 135 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= u5^(1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 3 (-5) (-2,0,1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-5) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2806

theorem actual_positive_source_2808 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 50 + (1)*v 77 + (((-1)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 120 + (1)*v 147 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((7:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= u5^(-1:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 3 (7) (-2,0,-1,1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (7) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2808

theorem actual_positive_source_2812 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 56 + (1)*v 80 + (((-1)*(u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 126 + (1)*v 150 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((10:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= u5^(1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 3 (10) (0,0,1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (10) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2812

theorem actual_positive_source_2814 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 60 + (((-1)*(u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 84 + (1)*v 130 + (((-1)*(u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 154 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-10:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= u5^(1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 3 (-10) (0,0,1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-10) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2814

theorem actual_positive_source_2850 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 42 + (1)*v 45 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 84 + (1)*v 87 + (1)*v 129 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 + (1)*v 171 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((3:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (3) (-2,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (3) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2850

theorem actual_positive_source_2852 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 39 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 42 + (1)*v 81 + (1)*v 123 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 126 + (1)*v 165 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-3:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (-3) (-2,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-3) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2852

theorem actual_positive_source_2858 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((u7*primeParameter 7 m s)))*v 0 + ((-1)/((u7*primeParameter 7 m s)))*v 42 + (1)*v 48 + ((-1)/((u7*primeParameter 7 m s)))*v 84 + (1)*v 90 + ((-1)/((u7*primeParameter 7 m s)))*v 126 + (1)*v 132 + (1)*v 174 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((6:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (6) (0,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (6) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2858

theorem actual_positive_source_2860 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((u7*primeParameter 7 m s)))*v 0 + (1)*v 36 + (1)*v 78 + ((-1)/((u7*primeParameter 7 m s)))*v 84 + (1)*v 120 + ((-1)/((u7*primeParameter 7 m s)))*v 126 + (1)*v 162 + ((-1)/((u7*primeParameter 7 m s)))*v 168 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-6:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (-6) (0,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-6) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2860

theorem actual_positive_source_2866 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 14 + (1)*v 51 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 56 + (1)*v 93 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 98 + (1)*v 135 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 140 + (1)*v 177 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((9:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (9) (-2,2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (9) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2866

theorem actual_positive_source_2868 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 33 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 70 + (1)*v 75 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 112 + (1)*v 117 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 154 + (1)*v 159 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 196 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-9:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (-9) (-2,2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-9) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2868

theorem actual_positive_source_2870 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 21 + (1)*v 54 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 63 + (1)*v 96 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 105 + (1)*v 138 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 147 + (1)*v 180 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((12:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (12) (2,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (12) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2870

theorem actual_positive_source_2872 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 30 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 63 + (1)*v 72 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 105 + (1)*v 114 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 147 + (1)*v 156 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 189 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-12:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (-12) (2,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-12) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2872

theorem actual_positive_source_2874 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 24 + (1)*v 56 + (((-1)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 66 + (1)*v 98 + (((-1)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 108 + (1)*v 140 + (((-1)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 150 + (1)*v 182 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((14:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= u5^(0:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (14) (0,-2,0,1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (14) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2874

theorem actual_positive_source_2876 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 28 + (((-1)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 60 + (1)*v 70 + (((-1)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 102 + (1)*v 112 + (((-1)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 144 + (1)*v 154 + (((-1)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 186 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-14:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= u5^(0:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (-14) (0,-2,0,1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-14) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2876

theorem actual_positive_source_2950 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 24 + (1)*v 35 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 54 + (1)*v 65 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 84 + (1)*v 95 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 114 + (1)*v 125 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 204 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= u5^(1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 7 (5) (-2,-2,1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (5) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2950

theorem actual_positive_source_2952 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 6 + (1)*v 25 + (1)*v 55 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 66 + (1)*v 85 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 96 + (1)*v 115 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 126 + (1)*v 145 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 156 + (1)*v 175 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 186 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((-5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= u5^(1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 7 (-5) (-2,-2,1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (-5) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2952

theorem actual_positive_source_2954 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((u5*primeParameter 5 m s)))*v 0 + ((-1)/((u5*primeParameter 5 m s)))*v 30 + (1)*v 36 + ((-1)/((u5*primeParameter 5 m s)))*v 60 + (1)*v 66 + ((-1)/((u5*primeParameter 5 m s)))*v 90 + (1)*v 96 + ((-1)/((u5*primeParameter 5 m s)))*v 120 + (1)*v 126 + ((-1)/((u5*primeParameter 5 m s)))*v 150 + (1)*v 156 + (1)*v 186 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((6:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 7 (6) (0,0,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (6) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2954

theorem actual_positive_source_2958 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 10 + (1)*v 39 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 40 + (1)*v 69 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 70 + (1)*v 99 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 100 + (1)*v 129 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 130 + (1)*v 159 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 160 + (1)*v 189 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((9:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 7 (9) (-2,2,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (9) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2958

theorem actual_positive_source_2962 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 12 + (1)*v 40 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 42 + (1)*v 70 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 72 + (1)*v 100 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 102 + (1)*v 130 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 132 + (1)*v 160 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 162 + (1)*v 190 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((10:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= u5^(1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 7 (10) (0,-2,1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (10) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2962

theorem actual_positive_source_2964 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 20 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 48 + (1)*v 50 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 78 + (1)*v 80 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 108 + (1)*v 110 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 138 + (1)*v 140 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 168 + (1)*v 170 + (((-1)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 198 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((-10:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= u5^(1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 7 (-10) (0,-2,1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (-10) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_2964

theorem actual_positive_source_3026 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 0 + ((-1)*(u7*primeParameter 7 m s))*v 24 + (1)*v 42 + ((-1)*(u7*primeParameter 7 m s))*v 66 + (1)*v 126 + ((-1)*(u7*primeParameter 7 m s))*v 150 + (1)*v 168 + ((-1)*(u7*primeParameter 7 m s))*v 192 = 0 := by
  have hroot : root 35 f 10=u5 := by simp [root_signed_10,h5,h7]
  have hr : (Nat.lcm 35 (10^2):ℚ)*((-21:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 10*ε*I^(2*m)= u5^(0:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 10 (-21) (0,0,0,1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    10 (by decide) (by decide) (-21) 63 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_3026

theorem actual_positive_source_3046 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 10 + (1)*v 24 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 40 + (1)*v 54 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 70 + (1)*v 84 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 130 + (1)*v 144 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 160 + (1)*v 174 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 190 + (1)*v 204 = 0 := by
  have hroot : root 35 f 14=u7 := by simp [root_signed_14,h5,h7]
  have hr : (Nat.lcm 35 (14^2):ℚ)*((9:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 14*ε*I^(2*m)= u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 14 (9) (0,2,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    14 (by decide) (by decide) (9) 45 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh


#print axioms actual_positive_source_3046

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

