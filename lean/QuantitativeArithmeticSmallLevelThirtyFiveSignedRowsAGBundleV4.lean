module
public import QuantitativeArithmeticSmallLevelThirtyFivePoleFullRowsV1
public import QuantitativeArithmeticSmallLevelThirtyFiveSignedLaurentV1
public import QuantitativeArithmeticSmallLevelThirtyFiveWordWitnessFamilyV4
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

theorem actual_signed_negative_source_0 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 0 + ((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))*v 207 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord000 0 0 s=wordCoefficient m (-u5*u7) witnessWord000 0 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord000 0 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord000)=
      (-1:ℂ)^(frickeCount witnessWord000)*u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord000_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord000 0 (2,0,1,1) hr hcompat s] at hh
  norm_num [witnessWord000_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_0

theorem actual_signed_negative_source_2 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 0 + ((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))*v 204 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord001 0 0 s=wordCoefficient m (-u5*u7) witnessWord001 0 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord001 0 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord001)=
      (-1:ℂ)^(frickeCount witnessWord001)*u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord001_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord001 0 (0,0,1,1) hr hcompat s] at hh
  norm_num [witnessWord001_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2

theorem actual_signed_negative_source_4 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 42 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s))/((u5*primeParameter 5 m s)))*v 205 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord001 42 0 s=wordCoefficient m (-u5*u7) witnessWord001 42 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord001 42 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord001)=
      (-1:ℂ)^(frickeCount witnessWord001)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord001_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord001 42 (2,2,-1,1) hr hcompat s] at hh
  norm_num [witnessWord001_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_4

theorem actual_signed_negative_source_8 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 0 = 0 := by
  have hh := coordinate_zero_of_germ hv 0
    (source_zero_and_six_germs hm hf BG G hG hGF s).1
  simpa only [one_mul] using hh

#print axioms actual_signed_negative_source_8

theorem actual_signed_negative_source_12 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 2 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 2 0 s=wordCoefficient m (-u5*u7) witnessWord002 2 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 2 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 2 (0,-2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_12

theorem actual_signed_negative_source_16 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 4 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 105 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 4 0 s=wordCoefficient m (-u5*u7) witnessWord002 4 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 4 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 4 (2,-2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_16

theorem actual_signed_negative_source_18 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 5 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 5 0 s=wordCoefficient m (-u5*u7) witnessWord002 5 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 5 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 5 (-2,-2,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_18

theorem actual_signed_negative_source_20 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    ((1)/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 6 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 6 0 s=wordCoefficient m (-u5*u7) witnessWord002 6 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 6 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 6 (0,0,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_20

theorem actual_signed_negative_source_22 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 7 + (((u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 30 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 7 0 s=wordCoefficient m (-u5*u7) witnessWord002 7 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 7 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 7 (-2,-2,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_22

theorem actual_signed_negative_source_26 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 10 + (((u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 84 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 10 0 s=wordCoefficient m (-u5*u7) witnessWord002 10 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 10 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 10 (0,-2,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_26

theorem actual_signed_negative_source_28 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 12 + (((primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 105 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 12 0 s=wordCoefficient m (-u5*u7) witnessWord002 12 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 12 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 12 (2,0,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_28

theorem actual_signed_negative_source_30 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 14 + (((u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 120 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 14 0 s=wordCoefficient m (-u5*u7) witnessWord002 14 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 14 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 14 (0,-2,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_30

theorem actual_signed_negative_source_32 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 15 + (((u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 126 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 15 0 s=wordCoefficient m (-u5*u7) witnessWord002 15 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 15 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 15 (-2,0,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_32

theorem actual_signed_negative_source_34 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 18 + (((primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 140 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 18 0 s=wordCoefficient m (-u5*u7) witnessWord002 18 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 18 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 18 (0,2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_34

theorem actual_signed_negative_source_36 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 20 + (((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 147 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 20 0 s=wordCoefficient m (-u5*u7) witnessWord002 20 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 20 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 20 (2,-2,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_36

theorem actual_signed_negative_source_38 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 21 + (((u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 150 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 21 0 s=wordCoefficient m (-u5*u7) witnessWord002 21 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 21 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 21 (-2,0,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_38

theorem actual_signed_negative_source_40 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 28 + (((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 165 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 28 0 s=wordCoefficient m (-u5*u7) witnessWord002 28 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 28 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 28 (2,-2,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_40

theorem actual_signed_negative_source_42 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 30 + (((u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 168 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 30 0 s=wordCoefficient m (-u5*u7) witnessWord002 30 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 30 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 30 (0,0,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_42

theorem actual_signed_negative_source_44 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 35 + (((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 174 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 35 0 s=wordCoefficient m (-u5*u7) witnessWord002 35 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 35 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 35 (-2,-2,1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_44

theorem actual_signed_negative_source_46 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 36 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 175 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 36 0 s=wordCoefficient m (-u5*u7) witnessWord002 36 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 36 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 36 (2,2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_46

theorem actual_signed_negative_source_48 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 42 + (((u7*primeParameter 7 m s))/((u5*primeParameter 5 m s)))*v 180 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 42 0 s=wordCoefficient m (-u5*u7) witnessWord002 42 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 42 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 42 (0,0,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_48

theorem actual_signed_negative_source_50 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 45 + (((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 182 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 45 0 s=wordCoefficient m (-u5*u7) witnessWord002 45 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 45 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 45 (-2,2,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_50

theorem actual_signed_negative_source_52 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 60 + (((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 189 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 60 0 s=wordCoefficient m (-u5*u7) witnessWord002 60 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 60 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 60 (2,0,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_52

theorem actual_signed_negative_source_54 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 63 + (((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 190 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 63 0 s=wordCoefficient m (-u5*u7) witnessWord002 63 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 63 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 63 (-2,2,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_54

theorem actual_signed_negative_source_56 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 70 + (((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 192 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 70 0 s=wordCoefficient m (-u5*u7) witnessWord002 70 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 70 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 70 (0,-2,1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_56

theorem actual_signed_negative_source_58 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 84 + (((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s))/((u5*primeParameter 5 m s)))*v 195 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 84 0 s=wordCoefficient m (-u5*u7) witnessWord002 84 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 84 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 84 (2,0,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_58

theorem actual_signed_negative_source_60 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 90 + (((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 196 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 90 0 s=wordCoefficient m (-u5*u7) witnessWord002 90 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 90 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 90 (0,2,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_60

theorem actual_signed_negative_source_64 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 126 + (((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s))/((u5*primeParameter 5 m s)))*v 200 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 126 0 s=wordCoefficient m (-u5*u7) witnessWord002 126 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 126 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(-1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 126 (0,2,-1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_64

theorem actual_signed_negative_source_66 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 140 + (((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))/((primeParameter 3 m s)^(2:ℕ)))*v 201 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 140 0 s=wordCoefficient m (-u5*u7) witnessWord002 140 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 140 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 140 (2,-2,1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_66

theorem actual_signed_negative_source_68 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 180 + (((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s))/((u7*primeParameter 7 m s)))*v 203 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 180 0 s=wordCoefficient m (-u5*u7) witnessWord002 180 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 180 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 180 (2,2,1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_68

theorem actual_signed_negative_source_128 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    ((1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 208 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord003 208 0 s=wordCoefficient m (-u5*u7) witnessWord003 208 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord003 208 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord003)=
      (-1:ℂ)^(frickeCount witnessWord003)*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord003_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord003 208 (0,-2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord003_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_128

theorem actual_signed_negative_source_150 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord009 186 0 s=wordCoefficient m (-u5*u7) witnessWord009 186 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord009 186 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord009)=
      (-1:ℂ)^(frickeCount witnessWord009)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord009_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord009 186 (0,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord009_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_150

theorem actual_signed_negative_source_162 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord009 202 0 s=wordCoefficient m (-u5*u7) witnessWord009 202 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord009 202 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord009)=
      (-1:ℂ)^(frickeCount witnessWord009)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord009_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord009 202 (0,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord009_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_162

theorem actual_signed_negative_source_246 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord027 102 0 s=wordCoefficient m (-u5*u7) witnessWord027 102 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord027 102 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord027)=
      (-1:ℂ)^(frickeCount witnessWord027)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord027_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord027 102 (0,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_246

theorem actual_signed_negative_source_248 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord027 105 0 s=wordCoefficient m (-u5*u7) witnessWord027 105 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord027 105 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord027)=
      (-1:ℂ)^(frickeCount witnessWord027)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord027_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord027 105 (-2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_248

theorem actual_signed_negative_source_252 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord027 108 0 s=wordCoefficient m (-u5*u7) witnessWord027 108 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord027 108 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord027)=
      (-1:ℂ)^(frickeCount witnessWord027)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord027_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord027 108 (2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_252

theorem actual_signed_negative_source_262 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord028 107 0 s=wordCoefficient m (-u5*u7) witnessWord028 107 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord028 107 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord028)=
      (-1:ℂ)^(frickeCount witnessWord028)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord028_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord028 107 (-2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord028_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_262

theorem actual_signed_negative_source_266 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord028 110 0 s=wordCoefficient m (-u5*u7) witnessWord028 110 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord028 110 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord028)=
      (-1:ℂ)^(frickeCount witnessWord028)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord028_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord028 110 (2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord028_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_266

theorem actual_signed_negative_source_270 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 90 0 s=wordCoefficient m (-u5*u7) witnessWord029 90 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 90 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 90 (0,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_270

theorem actual_signed_negative_source_272 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 96 0 s=wordCoefficient m (-u5*u7) witnessWord029 96 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 96 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 96 (2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_272

theorem actual_signed_negative_source_274 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 99 0 s=wordCoefficient m (-u5*u7) witnessWord029 99 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 99 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 99 (-2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_274

theorem actual_signed_negative_source_288 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 109 0 s=wordCoefficient m (-u5*u7) witnessWord029 109 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 109 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 109 (-2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_288

theorem actual_signed_negative_source_294 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 112 0 s=wordCoefficient m (-u5*u7) witnessWord029 112 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 112 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 112 (2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_294

theorem actual_signed_negative_source_296 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 114 0 s=wordCoefficient m (-u5*u7) witnessWord029 114 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 114 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 114 (0,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_296

theorem actual_signed_negative_source_298 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 117 0 s=wordCoefficient m (-u5*u7) witnessWord029 117 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 117 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 117 (-2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_298

theorem actual_signed_negative_source_300 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 120 0 s=wordCoefficient m (-u5*u7) witnessWord029 120 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 120 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 120 (2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_300

theorem actual_signed_negative_source_312 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord030 93 0 s=wordCoefficient m (-u5*u7) witnessWord030 93 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord030 93 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord030)=
      (-1:ℂ)^(frickeCount witnessWord030)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord030 93 (-2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_312

theorem actual_signed_negative_source_316 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord030 98 0 s=wordCoefficient m (-u5*u7) witnessWord030 98 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord030 98 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord030)=
      (-1:ℂ)^(frickeCount witnessWord030)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord030 98 (2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_316

theorem actual_signed_negative_source_320 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord030 100 0 s=wordCoefficient m (-u5*u7) witnessWord030 100 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord030 100 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord030)=
      (-1:ℂ)^(frickeCount witnessWord030)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord030 100 (0,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_320

theorem actual_signed_negative_source_326 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord030 103 0 s=wordCoefficient m (-u5*u7) witnessWord030 103 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord030 103 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord030)=
      (-1:ℂ)^(frickeCount witnessWord030)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord030 103 (-2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_326

theorem actual_signed_negative_source_358 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord041 168 0 s=wordCoefficient m (-u5*u7) witnessWord041 168 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord041 168 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord041)=
      (-1:ℂ)^(frickeCount witnessWord041)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord041 168 (2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_358

theorem actual_signed_negative_source_360 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord041 174 0 s=wordCoefficient m (-u5*u7) witnessWord041 174 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord041 174 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord041)=
      (-1:ℂ)^(frickeCount witnessWord041)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord041 174 (0,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_360

theorem actual_signed_negative_source_362 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord041 175 0 s=wordCoefficient m (-u5*u7) witnessWord041 175 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord041 175 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord041)=
      (-1:ℂ)^(frickeCount witnessWord041)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord041 175 (-2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_362

theorem actual_signed_negative_source_366 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord041 177 0 s=wordCoefficient m (-u5*u7) witnessWord041 177 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord041 177 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord041)=
      (-1:ℂ)^(frickeCount witnessWord041)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord041 177 (-2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_366

theorem actual_signed_negative_source_372 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 162 0 s=wordCoefficient m (-u5*u7) witnessWord042 162 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 162 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 162 (2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_372

theorem actual_signed_negative_source_374 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 165 0 s=wordCoefficient m (-u5*u7) witnessWord042 165 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 165 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 165 (-2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_374

theorem actual_signed_negative_source_378 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 170 0 s=wordCoefficient m (-u5*u7) witnessWord042 170 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 170 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 170 (2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_378

theorem actual_signed_negative_source_380 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 171 0 s=wordCoefficient m (-u5*u7) witnessWord042 171 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 171 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 171 (-2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_380

theorem actual_signed_negative_source_384 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 173 0 s=wordCoefficient m (-u5*u7) witnessWord042 173 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 173 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 173 (-2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_384

theorem actual_signed_negative_source_398 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 183 0 s=wordCoefficient m (-u5*u7) witnessWord042 183 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 183 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 183 (-2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_398

theorem actual_signed_negative_source_400 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 186 0 s=wordCoefficient m (-u5*u7) witnessWord042 186 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 186 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 186 (2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_400

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
