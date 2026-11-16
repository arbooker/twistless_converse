module
public meta import SmallLevelCertificateBatchCommandV1

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

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveActualRowsAFBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set FinitenessNormalizedTwistProduct
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open FinitenessRamanujanSum
open scoped Topology

certificate_batch {
theorem actual_negative_source_2804 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 42 + (1)*v 75 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 112 + (1)*v 145 = 0 := by
  have hroot : root 35 f 3=1 := by exact root_three f
  have hr : (Nat.lcm 35 (3^2):ℚ)*((5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 3 hroot (5) (-2,0,1,-1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (5) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2804

theorem actual_negative_source_2806 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 65 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 98 + (1)*v 135 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 168 = 0 := by
  have hroot : root 35 f 3=1 := by exact root_three f
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 3 hroot (-5) (-2,0,1,-1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-5) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2806

theorem actual_negative_source_2808 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 50 + (1)*v 77 + (((primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 120 + (1)*v 147 = 0 := by
  have hroot : root 35 f 3=1 := by exact root_three f
  have hr : (Nat.lcm 35 (3^2):ℚ)*((7:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 3 hroot (7) (-2,0,-1,1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (7) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2808

theorem actual_negative_source_2812 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 5 m s))/((primeParameter 7 m s)))*v 56 + (1)*v 80 + (((primeParameter 5 m s))/((primeParameter 7 m s)))*v 126 + (1)*v 150 = 0 := by
  have hroot : root 35 f 3=1 := by exact root_three f
  have hr : (Nat.lcm 35 (3^2):ℚ)*((10:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 3 hroot (10) (0,0,1,-1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (10) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2812

theorem actual_negative_source_2814 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 60 + (((primeParameter 5 m s))/((primeParameter 7 m s)))*v 84 + (1)*v 130 + (((primeParameter 5 m s))/((primeParameter 7 m s)))*v 154 = 0 := by
  have hroot : root 35 f 3=1 := by exact root_three f
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-10:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 3 hroot (-10) (0,0,1,-1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-10) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2814

theorem actual_negative_source_2850 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 0 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 42 + (1)*v 45 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 84 + (1)*v 87 + (1)*v 129 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 168 + (1)*v 171 = 0 := by
  have hroot : root 35 f 5=1 := by rw [root_five,h5]; norm_num
  have hr : (Nat.lcm 35 (5^2):ℚ)*((3:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 5 hroot (3) (-2,0,0,-1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (3) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2850

theorem actual_negative_source_2852 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 0 + (1)*v 39 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 42 + (1)*v 81 + (1)*v 123 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 126 + (1)*v 165 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 168 = 0 := by
  have hroot : root 35 f 5=1 := by rw [root_five,h5]; norm_num
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-3:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 5 hroot (-3) (-2,0,0,-1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-3) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2852

theorem actual_negative_source_2860 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 7 m s)))*v 0 + (1)*v 36 + (1)*v 78 + ((1)/((primeParameter 7 m s)))*v 84 + (1)*v 120 + ((1)/((primeParameter 7 m s)))*v 126 + (1)*v 162 + ((1)/((primeParameter 7 m s)))*v 168 = 0 := by
  have hroot : root 35 f 5=1 := by rw [root_five,h5]; norm_num
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-6:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 5 hroot (-6) (0,0,0,-1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-6) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2860

theorem actual_negative_source_2866 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 14 + (1)*v 51 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 56 + (1)*v 93 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 98 + (1)*v 135 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 140 + (1)*v 177 = 0 := by
  have hroot : root 35 f 5=1 := by rw [root_five,h5]; norm_num
  have hr : (Nat.lcm 35 (5^2):ℚ)*((9:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 5 hroot (9) (-2,2,0,-1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (9) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2866

theorem actual_negative_source_2868 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 33 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 70 + (1)*v 75 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 112 + (1)*v 117 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 154 + (1)*v 159 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 196 = 0 := by
  have hroot : root 35 f 5=1 := by rw [root_five,h5]; norm_num
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-9:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 5 hroot (-9) (-2,2,0,-1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-9) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2868

theorem actual_negative_source_2870 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 7 m s)))*v 21 + (1)*v 54 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 7 m s)))*v 63 + (1)*v 96 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 7 m s)))*v 105 + (1)*v 138 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 7 m s)))*v 147 + (1)*v 180 = 0 := by
  have hroot : root 35 f 5=1 := by rw [root_five,h5]; norm_num
  have hr : (Nat.lcm 35 (5^2):ℚ)*((12:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 5 hroot (12) (2,0,0,-1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (12) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2870

theorem actual_negative_source_2872 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 30 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 7 m s)))*v 63 + (1)*v 72 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 7 m s)))*v 105 + (1)*v 114 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 7 m s)))*v 147 + (1)*v 156 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 7 m s)))*v 189 = 0 := by
  have hroot : root 35 f 5=1 := by rw [root_five,h5]; norm_num
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-12:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 5 hroot (-12) (2,0,0,-1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-12) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2872

theorem actual_negative_source_2874 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 24 + (1)*v 56 + (((primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 66 + (1)*v 98 + (((primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 108 + (1)*v 140 + (((primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 150 + (1)*v 182 = 0 := by
  have hroot : root 35 f 5=1 := by rw [root_five,h5]; norm_num
  have hr : (Nat.lcm 35 (5^2):ℚ)*((14:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 5 hroot (14) (0,-2,0,1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (14) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2874

theorem actual_negative_source_2876 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 28 + (((primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 60 + (1)*v 70 + (((primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 102 + (1)*v 112 + (((primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 144 + (1)*v 154 + (((primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 186 = 0 := by
  have hroot : root 35 f 5=1 := by rw [root_five,h5]; norm_num
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-14:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 5 hroot (-14) (0,-2,0,1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-14) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2876

theorem actual_negative_source_2942 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 0 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 30 + (1)*v 33 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 60 + (1)*v 63 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 90 + (1)*v 93 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 120 + (1)*v 123 + (1)*v 153 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 180 + (1)*v 183 = 0 := by
  have hroot : root 35 f 7=1 := by rw [root_seven,h7]; norm_num
  have hr : (Nat.lcm 35 (7^2):ℚ)*((3:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 7 hroot (3) (-2,0,-1,0) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (3) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2942

theorem actual_negative_source_2950 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 24 + (1)*v 35 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 54 + (1)*v 65 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 84 + (1)*v 95 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 114 + (1)*v 125 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 204 = 0 := by
  have hroot : root 35 f 7=1 := by rw [root_seven,h7]; norm_num
  have hr : (Nat.lcm 35 (7^2):ℚ)*((5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 7 hroot (5) (-2,-2,1,0) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (5) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2950

theorem actual_negative_source_2952 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 6 + (1)*v 25 + (1)*v 55 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 66 + (1)*v 85 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 96 + (1)*v 115 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 126 + (1)*v 145 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 156 + (1)*v 175 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 186 = 0 := by
  have hroot : root 35 f 7=1 := by rw [root_seven,h7]; norm_num
  have hr : (Nat.lcm 35 (7^2):ℚ)*((-5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 7 hroot (-5) (-2,-2,1,0) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (-5) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2952

theorem actual_negative_source_2954 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 5 m s)))*v 0 + ((1)/((primeParameter 5 m s)))*v 30 + (1)*v 36 + ((1)/((primeParameter 5 m s)))*v 60 + (1)*v 66 + ((1)/((primeParameter 5 m s)))*v 90 + (1)*v 96 + ((1)/((primeParameter 5 m s)))*v 120 + (1)*v 126 + ((1)/((primeParameter 5 m s)))*v 150 + (1)*v 156 + (1)*v 186 = 0 := by
  have hroot : root 35 f 7=1 := by rw [root_seven,h7]; norm_num
  have hr : (Nat.lcm 35 (7^2):ℚ)*((6:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 7 hroot (6) (0,0,-1,0) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (6) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2954

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveActualRowsAGBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Matrix Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open scoped Topology

certificate_batch {
theorem actual_negative_source_0 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 0 + ((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)*(primeParameter 7 m s))*v 207 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord000 0 0 s=wordCoefficient m (-1) witnessWord000 0 0 s :=
    (wordCoefficient_rational m (-1) witnessWord000 0 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord000 0 (2,0,1,1) hr s] at hh
  norm_num [witnessWord000_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_0

theorem actual_negative_source_2 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 0 + ((primeParameter 5 m s)*(primeParameter 7 m s))*v 204 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord001 0 0 s=wordCoefficient m (-1) witnessWord001 0 0 s :=
    (wordCoefficient_rational m (-1) witnessWord001 0 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord001 0 (0,0,1,1) hr s] at hh
  norm_num [witnessWord001_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2

theorem actual_negative_source_4 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 42 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(primeParameter 7 m s))/((primeParameter 5 m s)))*v 205 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord001 42 0 s=wordCoefficient m (-1) witnessWord001 42 0 s :=
    (wordCoefficient_rational m (-1) witnessWord001 42 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord001 42 (2,2,-1,1) hr s] at hh
  norm_num [witnessWord001_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_4

theorem actual_negative_source_8 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 0 = 0 := by
  have hh := coordinate_zero_of_germ hv 0
    (source_zero_and_six_germs hm hf BG G hG hGF s).1
  simpa only [one_mul] using hh

#print axioms actual_negative_source_8

theorem actual_negative_source_12 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 3 m s)^(2:ℕ)*(primeParameter 5 m s)*(primeParameter 7 m s)))*v 0 + (1)*v 2 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 2 0 s=wordCoefficient m (-1) witnessWord002 2 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 2 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 2 (0,-2,-1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_12

theorem actual_negative_source_16 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 4 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(primeParameter 5 m s)*(primeParameter 7 m s)))*v 105 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 4 0 s=wordCoefficient m (-1) witnessWord002 4 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 4 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 4 (2,-2,-1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_16

theorem actual_negative_source_18 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 5 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 168 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 5 0 s=wordCoefficient m (-1) witnessWord002 5 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 5 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 5 (-2,-2,1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_18

theorem actual_negative_source_20 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 5 m s)*(primeParameter 7 m s)))*v 0 + (1)*v 6 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 6 0 s=wordCoefficient m (-1) witnessWord002 6 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 6 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 6 (0,0,-1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_20

theorem actual_negative_source_22 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 7 + (((primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 30 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 7 0 s=wordCoefficient m (-1) witnessWord002 7 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 7 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 7 (-2,-2,-1,1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_22

theorem actual_negative_source_26 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 10 + (((primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 84 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 10 0 s=wordCoefficient m (-1) witnessWord002 10 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 10 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 10 (0,-2,1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_26

theorem actual_negative_source_28 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 12 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 5 m s)*(primeParameter 7 m s)))*v 105 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 12 0 s=wordCoefficient m (-1) witnessWord002 12 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 12 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 12 (2,0,-1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_28

theorem actual_negative_source_30 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 14 + (((primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 120 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 14 0 s=wordCoefficient m (-1) witnessWord002 14 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 14 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 14 (0,-2,-1,1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_30

theorem actual_negative_source_32 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 15 + (((primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 126 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 15 0 s=wordCoefficient m (-1) witnessWord002 15 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 15 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 15 (-2,0,1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_32

theorem actual_negative_source_34 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 18 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 5 m s)*(primeParameter 7 m s)))*v 140 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 18 0 s=wordCoefficient m (-1) witnessWord002 18 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 18 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 18 (0,2,-1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_34

theorem actual_negative_source_36 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 20 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 147 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 20 0 s=wordCoefficient m (-1) witnessWord002 20 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 20 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 20 (2,-2,1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_36

theorem actual_negative_source_38 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 21 + (((primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 150 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 21 0 s=wordCoefficient m (-1) witnessWord002 21 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 21 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 21 (-2,0,-1,1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_38

theorem actual_negative_source_40 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 28 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 165 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 28 0 s=wordCoefficient m (-1) witnessWord002 28 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 28 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 28 (2,-2,-1,1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_40

theorem actual_negative_source_42 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 30 + (((primeParameter 5 m s))/((primeParameter 7 m s)))*v 168 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 30 0 s=wordCoefficient m (-1) witnessWord002 30 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 30 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 30 (0,0,1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_42

theorem actual_negative_source_44 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 35 + (((primeParameter 5 m s)*(primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 174 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 35 0 s=wordCoefficient m (-1) witnessWord002 35 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 35 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 35 (-2,-2,1,1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_44

theorem actual_negative_source_46 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 36 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 5 m s)*(primeParameter 7 m s)))*v 175 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 36 0 s=wordCoefficient m (-1) witnessWord002 36 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 36 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 36 (2,2,-1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_46

theorem actual_negative_source_48 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 42 + (((primeParameter 7 m s))/((primeParameter 5 m s)))*v 180 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 42 0 s=wordCoefficient m (-1) witnessWord002 42 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 42 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 42 (0,0,-1,1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_48

theorem actual_negative_source_50 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 45 + (((primeParameter 3 m s)^(2:ℕ)*(primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s)))*v 182 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 45 0 s=wordCoefficient m (-1) witnessWord002 45 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 45 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 45 (-2,2,1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_50

theorem actual_negative_source_52 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 60 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s))/((primeParameter 7 m s)))*v 189 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 60 0 s=wordCoefficient m (-1) witnessWord002 60 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 60 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 60 (2,0,1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_52

theorem actual_negative_source_54 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 63 + (((primeParameter 3 m s)^(2:ℕ)*(primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 190 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 63 0 s=wordCoefficient m (-1) witnessWord002 63 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 63 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 63 (-2,2,-1,1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_54

theorem actual_negative_source_56 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 70 + (((primeParameter 5 m s)*(primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 192 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 70 0 s=wordCoefficient m (-1) witnessWord002 70 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 70 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 70 (0,-2,1,1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_56

theorem actual_negative_source_58 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 84 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 7 m s))/((primeParameter 5 m s)))*v 195 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 84 0 s=wordCoefficient m (-1) witnessWord002 84 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 84 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 84 (2,0,-1,1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_58

theorem actual_negative_source_60 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 90 + (((primeParameter 3 m s)^(2:ℕ)*(primeParameter 5 m s))/((primeParameter 7 m s)))*v 196 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 90 0 s=wordCoefficient m (-1) witnessWord002 90 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 90 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 90 (0,2,1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_60

theorem actual_negative_source_64 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 126 + (((primeParameter 3 m s)^(2:ℕ)*(primeParameter 7 m s))/((primeParameter 5 m s)))*v 200 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 126 0 s=wordCoefficient m (-1) witnessWord002 126 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 126 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 126 (0,2,-1,1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_64

theorem actual_negative_source_66 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 140 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)*(primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 201 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 140 0 s=wordCoefficient m (-1) witnessWord002 140 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 140 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 140 (2,-2,1,1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_66

theorem actual_negative_source_68 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 180 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(primeParameter 5 m s))/((primeParameter 7 m s)))*v 203 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 180 0 s=wordCoefficient m (-1) witnessWord002 180 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 180 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 180 (2,2,1,-1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_68

theorem actual_negative_source_128 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 3 m s)^(2:ℕ)*(primeParameter 5 m s)*(primeParameter 7 m s)))*v 0 + (1)*v 208 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord003 208 0 s=wordCoefficient m (-1) witnessWord003 208 0 s :=
    (wordCoefficient_rational m (-1) witnessWord003 208 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord003 208 (0,-2,-1,-1) hr s] at hh
  norm_num [witnessWord003_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_128

theorem actual_negative_source_150 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord009 186 0 s=wordCoefficient m (-1) witnessWord009 186 0 s :=
    (wordCoefficient_rational m (-1) witnessWord009 186 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord009 186 (0,2,0,0) hr s] at hh
  norm_num [witnessWord009_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_150

theorem actual_negative_source_162 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord009 202 0 s=wordCoefficient m (-1) witnessWord009 202 0 s :=
    (wordCoefficient_rational m (-1) witnessWord009 202 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord009 202 (0,-2,0,0) hr s] at hh
  norm_num [witnessWord009_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_162

theorem actual_negative_source_246 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord027 102 0 s=wordCoefficient m (-1) witnessWord027 102 0 s :=
    (wordCoefficient_rational m (-1) witnessWord027 102 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord027 102 (0,2,0,0) hr s] at hh
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_246

theorem actual_negative_source_248 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord027 105 0 s=wordCoefficient m (-1) witnessWord027 105 0 s :=
    (wordCoefficient_rational m (-1) witnessWord027 105 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord027 105 (-2,0,0,0) hr s] at hh
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_248

theorem actual_negative_source_252 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord027 108 0 s=wordCoefficient m (-1) witnessWord027 108 0 s :=
    (wordCoefficient_rational m (-1) witnessWord027 108 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord027 108 (2,0,0,0) hr s] at hh
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_252

theorem actual_negative_source_262 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord028 107 0 s=wordCoefficient m (-1) witnessWord028 107 0 s :=
    (wordCoefficient_rational m (-1) witnessWord028 107 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord028 107 (-2,0,0,0) hr s] at hh
  norm_num [witnessWord028_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_262

theorem actual_negative_source_266 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord028 110 0 s=wordCoefficient m (-1) witnessWord028 110 0 s :=
    (wordCoefficient_rational m (-1) witnessWord028 110 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord028 110 (2,0,0,0) hr s] at hh
  norm_num [witnessWord028_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_266

theorem actual_negative_source_270 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord029 90 0 s=wordCoefficient m (-1) witnessWord029 90 0 s :=
    (wordCoefficient_rational m (-1) witnessWord029 90 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord029 90 (0,2,0,0) hr s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_270

theorem actual_negative_source_272 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord029 96 0 s=wordCoefficient m (-1) witnessWord029 96 0 s :=
    (wordCoefficient_rational m (-1) witnessWord029 96 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord029 96 (2,0,0,0) hr s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_272

theorem actual_negative_source_274 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord029 99 0 s=wordCoefficient m (-1) witnessWord029 99 0 s :=
    (wordCoefficient_rational m (-1) witnessWord029 99 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord029 99 (-2,2,0,0) hr s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_274

theorem actual_negative_source_288 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord029 109 0 s=wordCoefficient m (-1) witnessWord029 109 0 s :=
    (wordCoefficient_rational m (-1) witnessWord029 109 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord029 109 (-2,-2,0,0) hr s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_288

theorem actual_negative_source_294 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord029 112 0 s=wordCoefficient m (-1) witnessWord029 112 0 s :=
    (wordCoefficient_rational m (-1) witnessWord029 112 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord029 112 (2,-2,0,0) hr s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_294

theorem actual_negative_source_296 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord029 114 0 s=wordCoefficient m (-1) witnessWord029 114 0 s :=
    (wordCoefficient_rational m (-1) witnessWord029 114 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord029 114 (0,0,0,0) hr s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_296

theorem actual_negative_source_298 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord029 117 0 s=wordCoefficient m (-1) witnessWord029 117 0 s :=
    (wordCoefficient_rational m (-1) witnessWord029 117 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord029 117 (-2,2,0,0) hr s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_298

theorem actual_negative_source_300 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord029 120 0 s=wordCoefficient m (-1) witnessWord029 120 0 s :=
    (wordCoefficient_rational m (-1) witnessWord029 120 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord029 120 (2,0,0,0) hr s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_300

theorem actual_negative_source_312 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord030 93 0 s=wordCoefficient m (-1) witnessWord030 93 0 s :=
    (wordCoefficient_rational m (-1) witnessWord030 93 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord030 93 (-2,2,0,0) hr s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_312

theorem actual_negative_source_316 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord030 98 0 s=wordCoefficient m (-1) witnessWord030 98 0 s :=
    (wordCoefficient_rational m (-1) witnessWord030 98 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord030 98 (2,-2,0,0) hr s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_316

theorem actual_negative_source_320 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord030 100 0 s=wordCoefficient m (-1) witnessWord030 100 0 s :=
    (wordCoefficient_rational m (-1) witnessWord030 100 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord030 100 (0,-2,0,0) hr s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_320

theorem actual_negative_source_326 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord030 103 0 s=wordCoefficient m (-1) witnessWord030 103 0 s :=
    (wordCoefficient_rational m (-1) witnessWord030 103 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord030 103 (-2,-2,0,0) hr s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_326

theorem actual_negative_source_358 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord041 168 0 s=wordCoefficient m (-1) witnessWord041 168 0 s :=
    (wordCoefficient_rational m (-1) witnessWord041 168 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord041 168 (2,2,0,0) hr s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_358

theorem actual_negative_source_360 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord041 174 0 s=wordCoefficient m (-1) witnessWord041 174 0 s :=
    (wordCoefficient_rational m (-1) witnessWord041 174 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord041 174 (0,0,0,0) hr s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_360

theorem actual_negative_source_362 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord041 175 0 s=wordCoefficient m (-1) witnessWord041 175 0 s :=
    (wordCoefficient_rational m (-1) witnessWord041 175 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord041 175 (-2,-2,0,0) hr s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_362

theorem actual_negative_source_366 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord041 177 0 s=wordCoefficient m (-1) witnessWord041 177 0 s :=
    (wordCoefficient_rational m (-1) witnessWord041 177 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord041 177 (-2,2,0,0) hr s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_366

theorem actual_negative_source_372 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord042 162 0 s=wordCoefficient m (-1) witnessWord042 162 0 s :=
    (wordCoefficient_rational m (-1) witnessWord042 162 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord042 162 (2,0,0,0) hr s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_372

theorem actual_negative_source_374 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord042 165 0 s=wordCoefficient m (-1) witnessWord042 165 0 s :=
    (wordCoefficient_rational m (-1) witnessWord042 165 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord042 165 (-2,2,0,0) hr s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_374

theorem actual_negative_source_378 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord042 170 0 s=wordCoefficient m (-1) witnessWord042 170 0 s :=
    (wordCoefficient_rational m (-1) witnessWord042 170 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord042 170 (2,-2,0,0) hr s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_378

theorem actual_negative_source_380 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord042 171 0 s=wordCoefficient m (-1) witnessWord042 171 0 s :=
    (wordCoefficient_rational m (-1) witnessWord042 171 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord042 171 (-2,0,0,0) hr s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_380

theorem actual_negative_source_384 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord042 173 0 s=wordCoefficient m (-1) witnessWord042 173 0 s :=
    (wordCoefficient_rational m (-1) witnessWord042 173 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord042 173 (-2,-2,0,0) hr s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_384

theorem actual_negative_source_398 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord042 183 0 s=wordCoefficient m (-1) witnessWord042 183 0 s :=
    (wordCoefficient_rational m (-1) witnessWord042 183 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord042 183 (-2,2,0,0) hr s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_398

theorem actual_negative_source_400 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord042 186 0 s=wordCoefficient m (-1) witnessWord042 186 0 s :=
    (wordCoefficient_rational m (-1) witnessWord042 186 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord042 186 (2,0,0,0) hr s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_400

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveActualRowsARHBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open FinitenessRamanujanSum
open scoped Topology

certificate_batch {
theorem actual_negative_source_2790 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 70 + (1)*v 140 = 0 := by
  have hh := pole_full_entire hm hf BG G hG hGF s v hv 3 (by decide) (by decide)
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex] at hh
  linear_combination hh

#print axioms actual_negative_source_2790

theorem actual_negative_source_2840 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 42 + (1)*v 84 + (1)*v 126 + (1)*v 168 = 0 := by
  have hh := pole_full_entire hm hf BG G hG hGF s v hv 5 (by decide) (by decide)
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex] at hh
  linear_combination hh

#print axioms actual_negative_source_2840

theorem actual_negative_source_2932 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 30 + (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + (1)*v 180 = 0 := by
  have hh := pole_full_entire hm hf BG G hG hGF s v hv 7 (by decide) (by decide)
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex] at hh
  linear_combination hh

#print axioms actual_negative_source_2932

theorem actual_negative_source_3006 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 21 + (1)*v 63 + (1)*v 147 + (1)*v 189 = 0 := by
  have hh := pole_full_entire hm hf BG G hG hGF s v hv 10 (by decide) (by decide)
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex] at hh
  linear_combination hh

#print axioms actual_negative_source_3006

theorem actual_negative_source_3032 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 15 + (1)*v 45 + (1)*v 75 + (1)*v 135 + (1)*v 165 + (1)*v 195 = 0 := by
  have hh := pole_full_entire hm hf BG G hG hGF s v hv 14 (by decide) (by decide)
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex] at hh
  linear_combination hh

#print axioms actual_negative_source_3032

theorem actual_negative_source_3058 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 14 + (1)*v 28 + (1)*v 56 + (1)*v 98 + (1)*v 112 + (1)*v 154 + (1)*v 182 + (1)*v 196 = 0 := by
  have hh := pole_full_entire hm hf BG G hG hGF s v hv 15 (by decide) (by decide)
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex] at hh
  linear_combination hh

#print axioms actual_negative_source_3058

theorem actual_negative_source_3084 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 10 + (1)*v 20 + (1)*v 40 + (1)*v 50 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + (1)*v 160 + (1)*v 170 + (1)*v 190 + (1)*v 200 = 0 := by
  have hh := pole_full_entire hm hf BG G hG hGF s v hv 21 (by decide) (by decide)
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex] at hh
  linear_combination hh

#print axioms actual_negative_source_3084

theorem actual_negative_source_3158 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 5 + (1)*v 25 + (1)*v 55 + (1)*v 65 + (1)*v 85 + (1)*v 95 + (1)*v 115 + (1)*v 125 + (1)*v 145 + (1)*v 155 + (1)*v 185 + (1)*v 205 = 0 := by
  have hh := pole_full_entire hm hf BG G hG hGF s v hv 42 (by decide) (by decide)
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex] at hh
  linear_combination hh

#print axioms actual_negative_source_3158

theorem actual_negative_source_3206 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 2 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 4 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 8 + (1)*v 107 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 2
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3206

theorem actual_negative_source_3210 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 4 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 8 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 16 + (1)*v 109 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 4
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3210

theorem actual_negative_source_3212 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 5 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 10 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 20 + (1)*v 110 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 5
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3212

theorem actual_negative_source_3216 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 7 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 14 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 28 + (1)*v 112 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 7
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3216

theorem actual_negative_source_3222 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 10 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 20 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 40 + (1)*v 115 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 10
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3222

theorem actual_negative_source_3226 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 12 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 24 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 48 + (1)*v 117 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 12
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3226

theorem actual_negative_source_3232 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 15 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 30 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 60 + (1)*v 120 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 15
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3232

theorem actual_negative_source_3238 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 18 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 36 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 72 + (1)*v 123 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 18
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3238

theorem actual_negative_source_3242 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 20 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 40 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 80 + (1)*v 125 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 20
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3242

theorem actual_negative_source_3250 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 24 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 48 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 96 + (1)*v 129 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 24
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3250

theorem actual_negative_source_3252 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 25 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 50 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 100 + (1)*v 130 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 25
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3252

theorem actual_negative_source_3262 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 30 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 60 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 120 + (1)*v 135 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 30
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3262

theorem actual_negative_source_3292 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 45 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 90 + (1)*v 150 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 180 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 45
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3292

theorem actual_negative_source_3298 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 48 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 96 + (1)*v 153 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 192 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 48
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3298

theorem actual_negative_source_3302 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 50 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 100 + (1)*v 155 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 200 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 50
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3302

theorem actual_negative_source_3304 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 51 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 102 + (1)*v 156 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 204 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 51
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3304

theorem actual_negative_source_3310 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 6 + (1)*v 54 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 108 + (1)*v 159 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 54
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3310

theorem actual_negative_source_3312 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 10 + (1)*v 55 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 110 + (1)*v 160 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 55
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3312

theorem actual_negative_source_3358 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 78 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 102 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 156 + (1)*v 183 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 78
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3358

theorem actual_negative_source_3362 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 80 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 110 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 160 + (1)*v 185 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 80
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3362

theorem actual_negative_source_3364 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 81 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 114 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 162 + (1)*v 186 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 81
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3364

theorem actual_negative_source_3376 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 87 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 138 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 174 + (1)*v 192 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 87
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3376

theorem actual_negative_source_3392 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 95 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 170 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 190 + (1)*v 200 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 95
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3392

theorem actual_negative_source_3426 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 7 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 21 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 7
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3426

theorem actual_negative_source_3432 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 10 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 30 + (1)*v 80 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 90 + (1)*v 150 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 10
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3432

theorem actual_negative_source_3478 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 33 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 87 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 99 + (1)*v 103 + (1)*v 173 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 33
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3478

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveActualRowsBFBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set FinitenessNormalizedTwistProduct
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open FinitenessRamanujanSum
open scoped Topology

certificate_batch {
theorem actual_negative_source_2858 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 7 m s)))*v 0 + ((1)/((primeParameter 7 m s)))*v 42 + (1)*v 48 + ((1)/((primeParameter 7 m s)))*v 84 + (1)*v 90 + ((1)/((primeParameter 7 m s)))*v 126 + (1)*v 132 + (1)*v 174 = 0 := by
  have hroot : root 35 f 5=1 := by exact all_roots_one_of_negative_bad_signs h5 h7 5
  have hr : (Nat.lcm 35 (5^2):ℚ)*((6:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 5 hroot (6) (0,0,0,-1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (6) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2858

theorem actual_negative_source_2958 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 10 + (1)*v 39 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 40 + (1)*v 69 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 70 + (1)*v 99 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 100 + (1)*v 129 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 130 + (1)*v 159 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s)))*v 160 + (1)*v 189 = 0 := by
  have hroot : root 35 f 7=1 := by exact all_roots_one_of_negative_bad_signs h5 h7 7
  have hr : (Nat.lcm 35 (7^2):ℚ)*((9:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 7 hroot (9) (-2,2,-1,0) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (9) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2958

theorem actual_negative_source_2964 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 20 + (((primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 48 + (1)*v 50 + (((primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 78 + (1)*v 80 + (((primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 108 + (1)*v 110 + (((primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 138 + (1)*v 140 + (((primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 168 + (1)*v 170 + (((primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 198 = 0 := by
  have hroot : root 35 f 7=1 := by exact all_roots_one_of_negative_bad_signs h5 h7 7
  have hr : (Nat.lcm 35 (7^2):ℚ)*((-10:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 7 hroot (-10) (0,-2,1,0) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (-10) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2964

theorem actual_negative_source_2968 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 18 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 5 m s)))*v 45 + (1)*v 48 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 5 m s)))*v 75 + (1)*v 78 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 5 m s)))*v 105 + (1)*v 108 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 5 m s)))*v 135 + (1)*v 138 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 5 m s)))*v 165 + (1)*v 168 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 5 m s)))*v 195 = 0 := by
  have hroot : root 35 f 7=1 := by exact all_roots_one_of_negative_bad_signs h5 h7 7
  have hr : (Nat.lcm 35 (7^2):ℚ)*((-12:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 7 hroot (-12) (2,0,-1,0) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (-12) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2968

theorem actual_negative_source_2978 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 21 + (1)*v 50 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 51 + (1)*v 80 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 81 + (1)*v 110 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 111 + (1)*v 140 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 141 + (1)*v 170 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 171 + (1)*v 200 = 0 := by
  have hroot : root 35 f 7=1 := by exact all_roots_one_of_negative_bad_signs h5 h7 7
  have hr : (Nat.lcm 35 (7^2):ℚ)*((20:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 7 hroot (20) (2,-2,1,0) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (20) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_2978

theorem actual_negative_source_3026 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 0 + ((primeParameter 7 m s))*v 24 + (1)*v 42 + ((primeParameter 7 m s))*v 66 + (1)*v 126 + ((primeParameter 7 m s))*v 150 + (1)*v 168 + ((primeParameter 7 m s))*v 192 = 0 := by
  have hroot : root 35 f 10=1 := by exact all_roots_one_of_negative_bad_signs h5 h7 10
  have hr : (Nat.lcm 35 (10^2):ℚ)*((-21:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 10 hroot (-21) (0,0,0,1) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    10 (by decide) (by decide) (-21) 63 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3026

theorem actual_negative_source_3046 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 5 m s)))*v 10 + (1)*v 24 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 5 m s)))*v 40 + (1)*v 54 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 5 m s)))*v 70 + (1)*v 84 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 5 m s)))*v 130 + (1)*v 144 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 5 m s)))*v 160 + (1)*v 174 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 5 m s)))*v 190 + (1)*v 204 = 0 := by
  have hroot : root 35 f 14=1 := by exact all_roots_one_of_negative_bad_signs h5 h7 14
  have hr : (Nat.lcm 35 (14^2):ℚ)*((9:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 14 hroot (9) (0,2,-1,0) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    14 (by decide) (by decide) (9) 45 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3046

theorem actual_negative_source_3174 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (2)*v 0 + (2)*v 6 + (1)*v 12 + (1)*v 24 + (2)*v 30 + (2)*v 36 + (1)*v 42 + (1)*v 48 + (2)*v 54 + (1)*v 60 + (1)*v 66 + (1)*v 72 + (1)*v 78 + (2)*v 84 + (2)*v 90 + (2)*v 96 + (1)*v 102 + (1)*v 108 + (2)*v 114 + (2)*v 120 + (2)*v 126 + (1)*v 132 + (1)*v 138 + (1)*v 144 + (1)*v 150 + (2)*v 156 + (1)*v 162 + (1)*v 168 + (2)*v 174 + (2)*v 180 + (1)*v 186 + (1)*v 198 + (2)*v 204 = 0 := by
  have hroot : root 35 f 70=1 := by exact all_roots_one_of_negative_bad_signs h5 h7 70
  have hr : (Nat.lcm 35 (70^2):ℚ)*((3:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hc := fullTaylorCoefficient_negative_laurent m f ε hphase 70 hroot (3) (0,0,0,0) hr s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    70 (by decide) (by decide) (3) 9 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3174

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveActualRowsBRHBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open FinitenessRamanujanSum
open scoped Topology

certificate_batch {
theorem actual_negative_source_3256 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 27 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 54 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 108 + (1)*v 132 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 27
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3256

theorem actual_negative_source_3274 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 36 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 72 + (1)*v 141 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 144 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 36
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3274

theorem actual_negative_source_3340 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 66 + (1)*v 69 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 138 + (1)*v 174 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 69
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3340

theorem actual_negative_source_3440 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 14 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 42 + (1)*v 84 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 126 + (1)*v 154 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 14
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3440

theorem actual_negative_source_3468 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 28 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 42 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 84 + (1)*v 98 + (1)*v 168 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 28
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3468

theorem actual_negative_source_3476 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 32 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 78 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 96 + (1)*v 102 + (1)*v 172 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 32
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3476

theorem actual_negative_source_3488 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 38 + (1)*v 108 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 114 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 132 + (1)*v 178 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 38
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3488

}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

