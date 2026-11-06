module
public import QuantitativeArithmeticSmallLevelThirtyFiveFullTaylorLaurentV1
public import QuantitativeArithmeticSmallLevelThirtyFiveSignedLaurentV1
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

theorem actual_signed_negative_source_2804 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 42 + (1)*v 75 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 112 + (1)*v 145 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= -u5^(1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (5) (-2,0,1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (5) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2804

theorem actual_signed_negative_source_2806 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 65 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 98 + (1)*v 135 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= -u5^(1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (-5) (-2,0,1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-5) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2806

theorem actual_signed_negative_source_2808 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 50 + (1)*v 77 + (((u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 120 + (1)*v 147 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((7:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= -u5^(-1:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (7) (-2,0,-1,1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (7) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2808

theorem actual_signed_negative_source_2812 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 56 + (1)*v 80 + (((u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 126 + (1)*v 150 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((10:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= -u5^(1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (10) (0,0,1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (10) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2812

theorem actual_signed_negative_source_2814 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 60 + (((u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 84 + (1)*v 130 + (((u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 154 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-10:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)= -u5^(1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (-10) (0,0,1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-10) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2814

theorem actual_signed_negative_source_2850 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 42 + (1)*v 45 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 84 + (1)*v 87 + (1)*v 129 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 + (1)*v 171 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((3:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (3) (-2,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (3) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2850

theorem actual_signed_negative_source_2852 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 39 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 42 + (1)*v 81 + (1)*v 123 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 126 + (1)*v 165 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-3:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (-3) (-2,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-3) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2852

theorem actual_signed_negative_source_2860 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((u7*primeParameter 7 m s)))*v 0 + (1)*v 36 + (1)*v 78 + ((1)/((u7*primeParameter 7 m s)))*v 84 + (1)*v 120 + ((1)/((u7*primeParameter 7 m s)))*v 126 + (1)*v 162 + ((1)/((u7*primeParameter 7 m s)))*v 168 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-6:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (-6) (0,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-6) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2860

theorem actual_signed_negative_source_2866 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 14 + (1)*v 51 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 56 + (1)*v 93 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 98 + (1)*v 135 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 140 + (1)*v 177 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((9:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (9) (-2,2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (9) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2866

theorem actual_signed_negative_source_2868 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 33 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 70 + (1)*v 75 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 112 + (1)*v 117 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 154 + (1)*v 159 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 196 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-9:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (-9) (-2,2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-9) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2868

theorem actual_signed_negative_source_2870 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 21 + (1)*v 54 + (((primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 63 + (1)*v 96 + (((primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 105 + (1)*v 138 + (((primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 147 + (1)*v 180 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((12:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (12) (2,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (12) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2870

theorem actual_signed_negative_source_2872 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 30 + (((primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 63 + (1)*v 72 + (((primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 105 + (1)*v 114 + (((primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 147 + (1)*v 156 + (((primeParameter 2 m s)^(2:ℕ))/((u7*primeParameter 7 m s)))*v 189 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-12:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (-12) (2,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-12) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2872

theorem actual_signed_negative_source_2874 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 24 + (1)*v 56 + (((u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 66 + (1)*v 98 + (((u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 108 + (1)*v 140 + (((u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 150 + (1)*v 182 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((14:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (14) (0,-2,0,1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (14) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2874

theorem actual_signed_negative_source_2876 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 28 + (((u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 60 + (1)*v 70 + (((u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 102 + (1)*v 112 + (((u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 144 + (1)*v 154 + (((u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 186 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-14:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (-14) (0,-2,0,1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-14) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2876

theorem actual_signed_negative_source_2942 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 0 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 30 + (1)*v 33 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 60 + (1)*v 63 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 90 + (1)*v 93 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 120 + (1)*v 123 + (1)*v 153 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 180 + (1)*v 183 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((3:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (3) (-2,0,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (3) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2942

theorem actual_signed_negative_source_2950 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 24 + (1)*v 35 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 54 + (1)*v 65 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 84 + (1)*v 95 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 114 + (1)*v 125 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 204 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (5) (-2,-2,1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (5) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2950

theorem actual_signed_negative_source_2952 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 6 + (1)*v 25 + (1)*v 55 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 66 + (1)*v 85 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 96 + (1)*v 115 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 126 + (1)*v 145 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 156 + (1)*v 175 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 186 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((-5:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (-5) (-2,-2,1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (-5) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2952

theorem actual_signed_negative_source_2954 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((u5*primeParameter 5 m s)))*v 0 + ((1)/((u5*primeParameter 5 m s)))*v 30 + (1)*v 36 + ((1)/((u5*primeParameter 5 m s)))*v 60 + (1)*v 66 + ((1)/((u5*primeParameter 5 m s)))*v 90 + (1)*v 96 + ((1)/((u5*primeParameter 5 m s)))*v 120 + (1)*v 126 + ((1)/((u5*primeParameter 5 m s)))*v 150 + (1)*v 156 + (1)*v 186 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((6:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (6) (0,0,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (6) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2954

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
