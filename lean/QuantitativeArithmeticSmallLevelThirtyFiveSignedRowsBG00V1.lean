module
public import QuantitativeArithmeticSmallLevelThirtyFivePoleFullRowsV1
public import QuantitativeArithmeticSmallLevelThirtyFiveWordWitnessFamilyV4
public import QuantitativeArithmeticSmallLevelThirtyFiveSignedLaurentV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Matrix Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open scoped Topology

theorem actual_signed_negative_source_62 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 105 + (((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)))*v 198 = 0 := by
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord002 105 0 s=wordCoefficient m (-u5*u7) witnessWord002 105 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord002 105 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord002)=
      (-1:ℂ)^(frickeCount witnessWord002)*u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord002 105 (-2,0,1,1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_62

theorem actual_signed_negative_source_292 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 111 + ((-1)/((primeParameter 2 m s)^(2:ℕ)))*v 186 = 0 := by
  let r : ClosedWordRow := {
    word := witnessWord029, source := 111, target := -24
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 111=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift r
  change v (gridIndex 111)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 111 0 s*
    v (gridIndex (-24))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 111 0 s=wordCoefficient m (-u5*u7) witnessWord029 111 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 111 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=
      (-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 111 (-2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_292

theorem actual_signed_negative_source_370 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 156 0 s=wordCoefficient m (-u5*u7) witnessWord042 156 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 156 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 156 (0,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_370

theorem actual_signed_negative_source_382 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 172 0 s=wordCoefficient m (-u5*u7) witnessWord042 172 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 172 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 172 (0,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_382

theorem actual_signed_negative_source_394 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 178 0 s=wordCoefficient m (-u5*u7) witnessWord042 178 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 178 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=
      (-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;>
      norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 178 (2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_394
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
