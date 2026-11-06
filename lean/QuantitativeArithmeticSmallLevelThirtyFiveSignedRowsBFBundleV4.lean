module
public import QuantitativeArithmeticSmallLevelThirtyFiveNegativeRootsV1
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

theorem actual_signed_negative_source_2858 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((u7*primeParameter 7 m s)))*v 0 + ((1)/((u7*primeParameter 7 m s)))*v 42 + (1)*v 48 + ((1)/((u7*primeParameter 7 m s)))*v 84 + (1)*v 90 + ((1)/((u7*primeParameter 7 m s)))*v 126 + (1)*v 132 + (1)*v 174 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((6:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)= -u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (6) (0,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (6) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2858

theorem actual_signed_negative_source_2958 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 10 + (1)*v 39 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 40 + (1)*v 69 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 70 + (1)*v 99 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 100 + (1)*v 129 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 130 + (1)*v 159 + (((primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 160 + (1)*v 189 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((9:ℚ)/210)^2=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (9) (-2,2,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (9) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2958

theorem actual_signed_negative_source_2964 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 20 + (((u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 48 + (1)*v 50 + (((u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 78 + (1)*v 80 + (((u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 108 + (1)*v 110 + (((u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 138 + (1)*v 140 + (((u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 168 + (1)*v 170 + (((u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 198 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((-10:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (-10) (0,-2,1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (-10) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2964

theorem actual_signed_negative_source_2968 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 18 + (((primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 45 + (1)*v 48 + (((primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 75 + (1)*v 78 + (((primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 105 + (1)*v 108 + (((primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 135 + (1)*v 138 + (((primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 165 + (1)*v 168 + (((primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 195 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((-12:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (-12) (2,0,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (-12) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2968

theorem actual_signed_negative_source_2978 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 21 + (1)*v 50 + (((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 51 + (1)*v 80 + (((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 81 + (1)*v 110 + (((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 111 + (1)*v 140 + (((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 141 + (1)*v 170 + (((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 171 + (1)*v 200 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((20:ℚ)/210)^2=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)= -u5^(1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (20) (2,-2,1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (20) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2978

theorem actual_signed_negative_source_3026 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 0 + ((u7*primeParameter 7 m s))*v 24 + (1)*v 42 + ((u7*primeParameter 7 m s))*v 66 + (1)*v 126 + ((u7*primeParameter 7 m s))*v 150 + (1)*v 168 + ((u7*primeParameter 7 m s))*v 192 = 0 := by
  have hroot : root 35 f 10=u5 := by simp [root_signed_10,h5,h7]
  have hr : (Nat.lcm 35 (10^2):ℚ)*((-21:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 10*ε*I^(2*m)= -u5^(0:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 10 (-21) (0,0,0,1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    10 (by decide) (by decide) (-21) 63 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_3026

theorem actual_signed_negative_source_3046 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 10 + (1)*v 24 + (((primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 40 + (1)*v 54 + (((primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 70 + (1)*v 84 + (((primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 130 + (1)*v 144 + (((primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 160 + (1)*v 174 + (((primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)))*v 190 + (1)*v 204 = 0 := by
  have hroot : root 35 f 14=u7 := by simp [root_signed_14,h5,h7]
  have hr : (Nat.lcm 35 (14^2):ℚ)*((9:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 14*ε*I^(2*m)= -u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 14 (9) (0,2,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    14 (by decide) (by decide) (9) 45 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_3046

theorem actual_signed_negative_source_3174 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (2)*v 0 + (2)*v 6 + (1)*v 12 + (1)*v 24 + (2)*v 30 + (2)*v 36 + (1)*v 42 + (1)*v 48 + (2)*v 54 + (1)*v 60 + (1)*v 66 + (1)*v 72 + (1)*v 78 + (2)*v 84 + (2)*v 90 + (2)*v 96 + (1)*v 102 + (1)*v 108 + (2)*v 114 + (2)*v 120 + (2)*v 126 + (1)*v 132 + (1)*v 138 + (1)*v 144 + (1)*v 150 + (2)*v 156 + (1)*v 162 + (1)*v 168 + (2)*v 174 + (2)*v 180 + (1)*v 186 + (1)*v 198 + (2)*v 204 = 0 := by
  have hroot : root 35 f 70=u5*u7 := by simp [root_signed_70,h5,h7]
  have hr : (Nat.lcm 35 (70^2):ℚ)*((3:ℚ)/210)^2=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 70*ε*I^(2*m)= -u5^(0:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc, hphase, hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 70 (3) (0,0,0,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    70 (by decide) (by decide) (3) 9 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s, primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_3174

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
