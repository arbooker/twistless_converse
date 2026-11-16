module
public meta import SmallLevelCertificateBatchCommandV1
public import QuantitativeArithmeticSmallLevelThirtyFiveKnownWordsSourceRowsChapterV1

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

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveActualRowsBG00V1 -/
section
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

certificate_batch {
theorem actual_negative_source_62 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 105 + (((primeParameter 5 m s)*(primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)))*v 198 = 0 := by
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
  have hc : rationalWordCoefficient m (-1) witnessWord002 105 0 s=wordCoefficient m (-1) witnessWord002 105 0 s :=
    (wordCoefficient_rational m (-1) witnessWord002 105 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord002 105 (-2,0,1,1) hr s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_62

theorem actual_negative_source_292 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord029 111 0 s=wordCoefficient m (-1) witnessWord029 111 0 s :=
    (wordCoefficient_rational m (-1) witnessWord029 111 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord029 111 (-2,0,0,0) hr s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_292

theorem actual_negative_source_370 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord042 156 0 s=wordCoefficient m (-1) witnessWord042 156 0 s :=
    (wordCoefficient_rational m (-1) witnessWord042 156 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord042 156 (0,2,0,0) hr s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_370

theorem actual_negative_source_382 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord042 172 0 s=wordCoefficient m (-1) witnessWord042 172 0 s :=
    (wordCoefficient_rational m (-1) witnessWord042 172 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord042 172 (0,-2,0,0) hr s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_382

theorem actual_negative_source_394 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
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
  have hc : rationalWordCoefficient m (-1) witnessWord042 178 0 s=wordCoefficient m (-1) witnessWord042 178 0 s :=
    (wordCoefficient_rational m (-1) witnessWord042 178 0 s).symm
  rw [hphase,hc,word_leading_laurent m (-1) witnessWord042 178 (2,-2,0,0) hr s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s, primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s, primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_394
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveAnalyticWordRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open scoped Topology

certificate_batch {
/-- Closed word relations hold modulo an analytic germ once the positive
Taylor translates are regular. This controls every negative Laurent term. -/
theorem analytic_word_constraint {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (r : ClosedWordRow) :
    HasAnalyticGerm (fun z => G z (gridIndex r.source)-
      rationalWordCoefficient m (ε*I^(2*m)) r.word r.source 0 z*
        G z (gridIndex r.target)) x := by
  obtain ⟨B,H,hrow⟩ := integer_word_grid_germs hm hf ε hε hlaw BG G hG hGF
    r.word r.nonaffine r.source r.target r.denominator r.closed
  have he := leading_taylor_germ G x hG hshift B (wordLeadingRow m (ε*I^(2*m)) r)
    (wordShiftRow m (ε*I^(2*m)) r) H
    (fun n j => wordShiftRow_analytic m (ε*I^(2*m)) r n x j)
    (fun n hn => (hrow n).1 x hn)
    (fun n hn => by
      simpa only [wordLeadingRow_apply,wordShiftRow_apply] using (hrow n).2 x hn)
  simpa only [wordLeadingRow_apply] using he

/-- The denominator-three Ramanujan sum gives an analytic germ of the sum
of the two primitive additive coordinates. -/
theorem analytic_ramanujan_three {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z) (x : ℂ) :
    HasAnalyticGerm (fun z => G z 70+G z 140) x := by
  obtain ⟨hE,he⟩ := original_full_entire_germs hm hf BG G hG hGF
    (q:=3) (by decide) (by decide)
  exact ⟨_,hE x,by simpa only [sampleSum_three] using he x⟩

/-- The quadratic-three difference and coordinate 192 have the same
principal part up to an explicit nonvanishing analytic multiplier. -/
theorem analytic_chi3_coordinate_relation {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    HasAnalyticGerm (fun z => G z 70-G z 140-
      (2*(ε*I^(2*m))*primeParameter 5 m z*primeParameter 7 m z/
        (primeParameter 3 m z)^(2:ℕ))*G z 192) s := by
  let r : ClosedWordRow := {
    word := witnessWord002, source := 70, target := -18
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 70=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := analytic_word_constraint hm hf ε hε hlaw BG G hG hGF s hshift r
  have hR := analytic_ramanujan_three hm hf BG G hG hGF s
  have he := (hh.mul_analytic (C:=fun _ => (2:ℂ)) analyticAt_const).sub hR
  apply he.congr
  apply Filter.Eventually.of_forall
  intro z
  change 2*(G z (gridIndex 70)-
    rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 70 0 z*G z (gridIndex (-18)))-
    (G z 70+G z 140)=_
  have hc : rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 70 0 z=
      wordCoefficient m (ε*I^(2*m)) witnessWord002 70 0 z :=
    (wordCoefficient_rational m (ε*I^(2*m)) witnessWord002 70 0 z).symm
  rw [hc,
    word_leading_laurent m (ε*I^(2*m)) witnessWord002 70 (0,-2,1,1) hr z]
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv]
  ring

#print axioms analytic_word_constraint
#print axioms analytic_ramanujan_three
#print axioms analytic_chi3_coordinate_relation
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveAnalyticFullRowsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open scoped Topology

certificate_batch {
/-- Closed Ramanujan Taylor rows are analytic germs after the positive
Taylor translates have been proved regular. -/
theorem analytic_full_taylor {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n))
    (q : ℕ) (hq : 0<q) (hqQ : q∣210) (t d : ℤ) (ht : t≠0)
    (hd : (Nat.lcm 35 (q^2):ℤ)*d=(210:ℤ)^2) (htd : t∣d) :
    HasAnalyticGerm (fun z => sampleSum q t (G z)-
      fullTaylorCoefficient (2*m) f ε q t 0 z*sampleSum q (-(d/t)) (G z)) x := by
  obtain ⟨B,hrow⟩ := full_taylor_germs_of_law hf ε hlaw BG G hG hGF q hq hqQ t d ht hd htd
  have hC (n : ℕ) (i : Fin 210) : AnalyticAt ℂ (fun z => ramanujanShiftRow m f ε q t (-(d/t)) n z i) x :=
    (fullTaylorCoefficient_analytic (2*m) f ε hq ht (n+1) x).mul analyticAt_const
  have hh := leading_taylor_germ G x hG hshift B (ramanujanLeadingRow m f ε q t (-(d/t)))
    (ramanujanShiftRow m f ε q t (-(d/t))) (fullTaylorError (2*m) f ε q t)
    hC (fun n hn => (hrow n).1 x hn)
    (fun n hn => by simpa only [ramanujanLeadingRow_apply,ramanujanShiftRow_apply] using (hrow n).2 x hn)
  simpa only [ramanujanLeadingRow_apply] using hh

theorem analytic_full_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (q : ℕ) (hq : 0<q) (hqQ : q∣210) :
    HasAnalyticGerm (fun z => sampleSum q 0 (G z)) x := by
  obtain ⟨hH,he⟩ := original_full_entire_germs hm hf BG G hG hGF hq hqQ
  exact ⟨_,hH x,he x⟩

theorem analytic_full_hecke {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (p : ℕ) (hp : p.Prime) (hpQ : p∣210) (t : ℤ) :
    HasAnalyticGerm (fun z => fullHeckeRow m f p t z (G z)) x :=
  ⟨_,analyticAt_const,original_full_hecke_germs hm hf BG G hG hGF hp hpQ t x⟩

#print axioms analytic_full_taylor
#print axioms analytic_full_entire
#print axioms analytic_full_hecke
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFivePositiveSignedLaurentV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex SmallLevelTaylor FinitenessNormalizedTwistProduct
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan

certificate_batch {
theorem word_leading_positive_signed_laurent (m : ℕ) (χ u v : ℂ) (w : Word) (t : ℤ)
    (e : ℤ×ℤ×ℤ×ℤ)
    (hr : rationalRate w t=(2:ℚ)^e.1*(3:ℚ)^e.2.1*(5:ℚ)^e.2.2.1*(7:ℚ)^e.2.2.2)
    (hsign : χ^(frickeCount w)=u^e.2.2.1*v^e.2.2.2)
    (s : ℂ) :
    wordCoefficient m χ w t 0 s=fourPrimeMonomial e
      (primeParameter 2 m s) (primeParameter 3 m s)
      (u*primeParameter 5 m s) (v*primeParameter 7 m s) := by
  rw [word_leading_laurent m χ w t e hr,hsign,fourPrimeMonomial_sign]

theorem fullTaylorCoefficient_positive_signed_laurent (m : ℕ) (f : ℕ → ℂ) (ε u v : ℂ)
    (q : ℕ) (t : ℤ) (e : ℤ×ℤ×ℤ×ℤ)
    (hr : (Nat.lcm 35 (q^2):ℚ)*((t:ℚ)/210)^2=
      (2:ℚ)^e.1*(3:ℚ)^e.2.1*(5:ℚ)^e.2.2.1*(7:ℚ)^e.2.2.2)
    (hsign : root 35 f q*ε*I^(2*m)= u^e.2.2.1*v^e.2.2.2) (s : ℂ) :
    fullTaylorCoefficient (2*m) f ε q t 0 s=
      fourPrimeMonomial e (primeParameter 2 m s) (primeParameter 3 m s)
        (u*primeParameter 5 m s) (v*primeParameter 7 m s) := by
  have hex : s-((2*m:ℕ):ℂ)/2=s-(m:ℂ) := by push_cast; ring
  have hc : (((Nat.lcm 35 (q^2):ℝ)*((t:ℝ)/210)^2:ℝ):ℂ)=
      (((Nat.lcm 35 (q^2):ℚ)*((t:ℚ)/210)^2:ℚ):ℂ) := by push_cast; rfl
  simp only [fullTaylorCoefficient,taylorRowScalar,hsign,
    pow_zero,Ring.choose_zero_right,mul_one,hex,hc]
  rw [rational_four_prime_power _ e hr,fourPrimeMonomial_sign]
  simp only [primeParameter,Nat.cast_ofNat]

#print axioms word_leading_positive_signed_laurent
#print axioms fullTaylorCoefficient_positive_signed_laurent
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveGridRecoveryRootsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Matrix Filter Set FinitenessNormalizedTwistProduct
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open FinitenessRamanujanSum
open scoped Topology
certificate_batch {
theorem root_signed_35 (f : ℕ → ℂ) : root 35 f 35=badFive f*badSeven f := by
  have hp : (35:ℕ).primeFactors={7,5} := by
    rw [show (35:ℕ)=7*5 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    rw [(by decide : Nat.Prime 7).primeFactors,(by decide : Nat.Prime 5).primeFactors]
    decide
  have hv2 : (35:ℕ).factorization 7=1 := by
    rw [show (35:ℕ)=7*5 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 7).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬7∣5)]
  have hv5 : (35:ℕ).factorization 5=1 := by
    rw [show (35:ℕ)=5*7 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 5).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬5∣7)]
  norm_num [root,hp,hv2,hv5,FinitenessNormalizedTwistLocal.sign,badFive,badSeven]
  ring


#print axioms root_signed_35
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveLastPairRootsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Matrix Filter Set FinitenessNormalizedTwistProduct
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open FinitenessRamanujanSum
open scoped Topology
certificate_batch {
theorem root_signed_15 (f : ℕ → ℂ) : root 35 f 15=-badFive f := by
  have hp : (15:ℕ).primeFactors={3,5} := by
    rw [show (15:ℕ)=3*5 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    rw [(by decide : Nat.Prime 3).primeFactors,(by decide : Nat.Prime 5).primeFactors]
    decide
  have hv2 : (15:ℕ).factorization 3=1 := by
    rw [show (15:ℕ)=3*5 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 3).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬3∣5)]
  have hv5 : (15:ℕ).factorization 5=1 := by
    rw [show (15:ℕ)=5*3 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 5).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬5∣3)]
  norm_num [root,hp,hv2,hv5,FinitenessNormalizedTwistLocal.sign,badFive,badSeven]
  ring

#print axioms root_signed_15

theorem root_signed_21 (f : ℕ → ℂ) : root 35 f 21=-badSeven f := by
  have hp : (21:ℕ).primeFactors={3,7} := by
    rw [show (21:ℕ)=3*7 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    rw [(by decide : Nat.Prime 3).primeFactors,(by decide : Nat.Prime 7).primeFactors]
    decide
  have hv2 : (21:ℕ).factorization 3=1 := by
    rw [show (21:ℕ)=3*7 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 3).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬3∣7)]
  have hv7 : (21:ℕ).factorization 7=1 := by
    rw [show (21:ℕ)=7*3 by decide,Nat.factorization_mul (by decide) (by decide)]
    simp [(by decide : Nat.Prime 7).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬7∣3)]
  norm_num [root,hp,hv2,hv7,FinitenessNormalizedTwistLocal.sign,badFive,badSeven]
  ring

#print axioms root_signed_21
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFivePoleChiThreeV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set Matrix
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic

def frickeThirdRow : ClosedWordRow where
  word := .generator 4
  source := 70
  target := -18
  nonaffine := by norm_num [integerRaw,integerSeed]
  denominator := by norm_num [integerDen,integerRaw,integerSeed]
  closed := by norm_num [integerDen,integerNumer,integerRaw,integerSeed]

certificate_batch {
theorem frickeThird_rate : rationalRate (.generator 4) 70=
    (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
  norm_num [rationalRate,integerDen,integerRaw,integerSeed,Matrix.det_fin_two]

theorem frickeThird_negative_coefficient (m : ℕ) (s : ℂ) :
    rationalWordCoefficient m (-1) (.generator 4) 70 0 s=
      -(primeParameter 5 m s*primeParameter 7 m s/(primeParameter 3 m s)^2) := by
  calc
    _ = wordCoefficient m (-1) (.generator 4) 70 0 s :=
      (wordCoefficient_rational m (-1) (.generator 4) 70 0 s).symm
    _ = (-1:ℂ)^(frickeCount (.generator 4))*fourPrimeMonomial (0,-2,1,1)
        (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s) :=
      word_leading_laurent m (-1) (.generator 4) 70 (0,-2,1,1) frickeThird_rate s
    _ = _ := by
      norm_num [frickeCount,fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
      ring

/-- The first reduced chi_3 coordinate identity holds for the genuine
principal part of the original continued grid. This is a pole constraint,
not yet an exclusion of poles. -/
theorem pole_negative_chi3_relation {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (x : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G x v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (x+n)) :
    v 70-v 140=(-2*primeParameter 5 m x*primeParameter 7 m x/
      (primeParameter 3 m x)^2)*v 192 := by
  have hw := pole_word_constraint hm hf ε hε hlaw BG G hG hGF x v hv hshift frickeThirdRow
  have hr := pole_ramanujan_three hm hf BG G hG hGF x v hv
  change v (gridIndex 70)-rationalWordCoefficient m (ε*I^(2*m)) (.generator 4) 70 0 x*
    v (gridIndex (-18))=0 at hw
  rw [hphase,frickeThird_negative_coefficient] at hw
  norm_num [gridIndex] at hw
  linear_combination 2*hw-hr

#print axioms frickeThird_rate
#print axioms pole_negative_chi3_relation
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveOriginalNegativeRow118V1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Matrix Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open scoped Topology

def row118Word0 : ClosedWordRow where
  word := (.generator 4)
  source := 9
  target := -140
  nonaffine := by norm_num [integerRaw,integerSeed]
  denominator := by norm_num [integerDen,integerRaw,integerSeed]
  closed := by norm_num [integerDen,integerNumer,integerRaw,integerSeed]

certificate_batch {
theorem row118Coefficient0 (m : ℕ) (s : ℂ) :
    rationalWordCoefficient m (-1) (.generator 4) 9 0 s=-((primeParameter 3 m s)^2/((primeParameter 2 m s)^2*primeParameter 5 m s*primeParameter 7 m s)) := by
  have hr : rationalRate (.generator 4) 9=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,integerRaw,integerSeed,Matrix.det_fin_two]
  calc
    _ = wordCoefficient m (-1) (.generator 4) 9 0 s :=
      (wordCoefficient_rational m (-1) (.generator 4) 9 0 s).symm
    _ = (-1:ℂ)^(frickeCount (.generator 4))*fourPrimeMonomial (-2,2,-1,-1)
        (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s) :=
      word_leading_laurent m (-1) (.generator 4) 9 (-2,2,-1,-1) hr s
    _ = _ := by
      norm_num [frickeCount,witnessWord041_count,fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
      ring

def row118Word1 : ClosedWordRow where
  word := (.generator 4)
  source := 18
  target := -70
  nonaffine := by norm_num [integerRaw,integerSeed]
  denominator := by norm_num [integerDen,integerRaw,integerSeed]
  closed := by norm_num [integerDen,integerNumer,integerRaw,integerSeed]

theorem row118Coefficient1 (m : ℕ) (s : ℂ) :
    rationalWordCoefficient m (-1) (.generator 4) 18 0 s=-((primeParameter 3 m s)^2/(primeParameter 5 m s*primeParameter 7 m s)) := by
  have hr : rationalRate (.generator 4) 18=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,integerRaw,integerSeed,Matrix.det_fin_two]
  calc
    _ = wordCoefficient m (-1) (.generator 4) 18 0 s :=
      (wordCoefficient_rational m (-1) (.generator 4) 18 0 s).symm
    _ = (-1:ℂ)^(frickeCount (.generator 4))*fourPrimeMonomial (0,2,-1,-1)
        (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s) :=
      word_leading_laurent m (-1) (.generator 4) 18 (0,2,-1,-1) hr s
    _ = _ := by
      norm_num [frickeCount,witnessWord041_count,fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
      ring

def row118Word2 : ClosedWordRow where
  word := (.generator 4)
  source := 36
  target := -35
  nonaffine := by norm_num [integerRaw,integerSeed]
  denominator := by norm_num [integerDen,integerRaw,integerSeed]
  closed := by norm_num [integerDen,integerNumer,integerRaw,integerSeed]

theorem row118Coefficient2 (m : ℕ) (s : ℂ) :
    rationalWordCoefficient m (-1) (.generator 4) 36 0 s=-((primeParameter 2 m s)^2*(primeParameter 3 m s)^2/(primeParameter 5 m s*primeParameter 7 m s)) := by
  have hr : rationalRate (.generator 4) 36=
      (2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,integerRaw,integerSeed,Matrix.det_fin_two]
  calc
    _ = wordCoefficient m (-1) (.generator 4) 36 0 s :=
      (wordCoefficient_rational m (-1) (.generator 4) 36 0 s).symm
    _ = (-1:ℂ)^(frickeCount (.generator 4))*fourPrimeMonomial (2,2,-1,-1)
        (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s) :=
      word_leading_laurent m (-1) (.generator 4) 36 (2,2,-1,-1) hr s
    _ = _ := by
      norm_num [frickeCount,witnessWord041_count,fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
      ring

def row118Word3 : ClosedWordRow where
  word := (.generator 4)
  source := 70
  target := -18
  nonaffine := by norm_num [integerRaw,integerSeed]
  denominator := by norm_num [integerDen,integerRaw,integerSeed]
  closed := by norm_num [integerDen,integerNumer,integerRaw,integerSeed]

theorem row118Coefficient3 (m : ℕ) (s : ℂ) :
    rationalWordCoefficient m (-1) (.generator 4) 70 0 s=-(primeParameter 5 m s*primeParameter 7 m s/(primeParameter 3 m s)^2) := by
  have hr : rationalRate (.generator 4) 70=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,integerRaw,integerSeed,Matrix.det_fin_two]
  calc
    _ = wordCoefficient m (-1) (.generator 4) 70 0 s :=
      (wordCoefficient_rational m (-1) (.generator 4) 70 0 s).symm
    _ = (-1:ℂ)^(frickeCount (.generator 4))*fourPrimeMonomial (0,-2,1,1)
        (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s) :=
      word_leading_laurent m (-1) (.generator 4) 70 (0,-2,1,1) hr s
    _ = _ := by
      norm_num [frickeCount,witnessWord041_count,fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
      ring

def row118Word4 : ClosedWordRow where
  word := (.generator 2)
  source := 114
  target := -18
  nonaffine := by norm_num [integerRaw,integerSeed]
  denominator := by norm_num [integerDen,integerRaw,integerSeed]
  closed := by norm_num [integerDen,integerNumer,integerRaw,integerSeed]

theorem row118Coefficient4 (m : ℕ) (s : ℂ) :
    rationalWordCoefficient m (-1) (.generator 2) 114 0 s=1 := by
  have hr : rationalRate (.generator 2) 114=
      (2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,integerRaw,integerSeed,Matrix.det_fin_two]
  calc
    _ = wordCoefficient m (-1) (.generator 2) 114 0 s :=
      (wordCoefficient_rational m (-1) (.generator 2) 114 0 s).symm
    _ = (-1:ℂ)^(frickeCount (.generator 2))*fourPrimeMonomial (0,0,0,0)
        (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s) :=
      word_leading_laurent m (-1) (.generator 2) 114 (0,0,0,0) hr s
    _ = _ := by
      norm_num [frickeCount,witnessWord041_count,fourPrimeMonomial,zpow_neg,div_eq_mul_inv]

def row118Word5 : ClosedWordRow where
  word := witnessWord041
  source := 175
  target := 0
  nonaffine := by norm_num [witnessWord041_matrix]
  denominator := by norm_num [integerDen,witnessWord041_matrix]
  closed := by norm_num [integerDen,integerNumer,witnessWord041_matrix]

theorem row118Coefficient5 (m : ℕ) (s : ℂ) :
    rationalWordCoefficient m (-1) witnessWord041 175 0 s=1/((primeParameter 2 m s)^2*(primeParameter 3 m s)^2) := by
  have hr : rationalRate witnessWord041 175=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord041_matrix,Matrix.det_fin_two]
  calc
    _ = wordCoefficient m (-1) witnessWord041 175 0 s :=
      (wordCoefficient_rational m (-1) witnessWord041 175 0 s).symm
    _ = (-1:ℂ)^(frickeCount witnessWord041)*fourPrimeMonomial (-2,-2,0,0)
        (primeParameter 2 m s) (primeParameter 3 m s)
        (primeParameter 5 m s) (primeParameter 7 m s) :=
      word_leading_laurent m (-1) witnessWord041 175 (-2,-2,0,0) hr s
    _ = _ := by
      norm_num [frickeCount,witnessWord041_count,fourPrimeMonomial,zpow_neg,div_eq_mul_inv]
      ring

/-- A reduced polynomial constraint, now derived from the actual twists.
No reduced-row hypothesis and no nonzero Hecke eigenvalue is assumed. -/
theorem original_negative_row118 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1+primeParameter 2 m s*((Real.sqrt 2:ℂ)*f 2)+(primeParameter 2 m s)^2)/
      (primeParameter 2 m s)^2)*v 192=0 := by
  have h0 := coordinate_zero_of_germ hv 0 (source_zero_and_six_germs hm hf BG G hG hGF s).1
  have h1 := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift row118Word0
  change v (gridIndex 9)-rationalWordCoefficient m (ε*I^(2*m)) (.generator 4) 9 0 s*
    v (gridIndex (-140))=0 at h1
  rw [hphase,row118Coefficient0] at h1
  norm_num [gridIndex] at h1
  have h2 := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift row118Word1
  change v (gridIndex 18)-rationalWordCoefficient m (ε*I^(2*m)) (.generator 4) 18 0 s*
    v (gridIndex (-70))=0 at h2
  rw [hphase,row118Coefficient1] at h2
  norm_num [gridIndex] at h2
  have h3 := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift row118Word2
  change v (gridIndex 36)-rationalWordCoefficient m (ε*I^(2*m)) (.generator 4) 36 0 s*
    v (gridIndex (-35))=0 at h3
  rw [hphase,row118Coefficient2] at h3
  norm_num [gridIndex] at h3
  have h4 := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift row118Word3
  change v (gridIndex 70)-rationalWordCoefficient m (ε*I^(2*m)) (.generator 4) 70 0 s*
    v (gridIndex (-18))=0 at h4
  rw [hphase,row118Coefficient3] at h4
  norm_num [gridIndex] at h4
  have h5 := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift row118Word4
  change v (gridIndex 114)-rationalWordCoefficient m (ε*I^(2*m)) (.generator 2) 114 0 s*
    v (gridIndex (-18))=0 at h5
  rw [hphase,row118Coefficient4] at h5
  norm_num [gridIndex] at h5
  have h6 := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift row118Word5
  change v (gridIndex 175)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord041 175 0 s*
    v (gridIndex (0))=0 at h6
  rw [hphase,row118Coefficient5] at h6
  norm_num [gridIndex] at h6
  have hr := pole_ramanujan_three hm hf BG G hG hGF s v hv
  have hh := pole_hecke_two hm hf BG G hG hGF s v hv 9
  norm_num [gridIndex] at hh
  apply QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate.negative_row118
    (primeParameter 2 m s) (primeParameter 3 m s)
    (primeParameter 5 m s) (primeParameter 7 m s) ((Real.sqrt 2:ℂ)*f 2) 0
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (primeParameter_ne_zero 5 m (by decide) s) (primeParameter_ne_zero 7 m (by decide) s)
    v v
  · simpa using h0
  · simpa only [one_mul,sub_neg_eq_add] using h1
  · simpa only [one_mul,sub_neg_eq_add] using h2
  · simpa only [one_mul,sub_neg_eq_add] using h3
  · simpa only [one_mul,sub_neg_eq_add] using h4
  · linear_combination h5
  · linear_combination h6
  · simpa only [one_mul] using hr
  · simp only [one_mul,neg_mul,neg_div,one_div,inv_pow] at *
    linear_combination hh

#print axioms original_negative_row118
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveOriginalNegativeRowsAV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

/-- Exactly the five selected reduced equations, with their full coefficients. -/
def negativeRowsAConclusion (x y z w a b : ℂ) (v : Fin 210 → ℂ) : Prop :=
((1 + (-1)*y*b + (-1)*y^(2:ℕ) + (-2)*x^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ)*y*b + x^(2:ℕ)*y^(2:ℕ) + (-2)*x^(3:ℕ)*a + x^(3:ℕ)*y*a*b + x^(3:ℕ)*y^(2:ℕ)*a + x^(4:ℕ) + x^(4:ℕ)*a^(2:ℕ) + (3)*x^(5:ℕ)*a + x^(5:ℕ)*a^(3:ℕ) + (2)*x^(6:ℕ)*a^(2:ℕ))/(x^(2:ℕ)))*v 24 + ((-4 + (4)*z + (2)*y*b + (4)*y^(2:ℕ) + (-6)*x*a + (2)*x*y*a*b + (4)*x*y^(2:ℕ)*a + (7)*x^(2:ℕ) + (-4)*x^(2:ℕ)*a^(2:ℕ) + (-4)*x^(2:ℕ)*z*a^(2:ℕ) + (-3)*x^(2:ℕ)*y*b + (-5)*x^(2:ℕ)*y^(2:ℕ) + (18)*x^(3:ℕ)*a + (-5)*x^(3:ℕ)*z*a + (-2)*x^(3:ℕ)*z*a^(3:ℕ) + (-2)*x^(3:ℕ)*y*a*b + (-8)*x^(3:ℕ)*y^(2:ℕ)*a + (-2)*x^(4:ℕ) + (14)*x^(4:ℕ)*a^(2:ℕ) + (-1)*x^(4:ℕ)*z + (-2)*x^(4:ℕ)*z*a^(2:ℕ) + (3)*x^(4:ℕ)*y*b + (2)*x^(4:ℕ)*y*a^(2:ℕ)*b + (2)*x^(4:ℕ)*y^(2:ℕ) + (-4)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-10)*x^(5:ℕ)*a + (3)*x^(5:ℕ)*a^(3:ℕ) + (2)*x^(5:ℕ)*z*a^(3:ℕ) + (4)*x^(5:ℕ)*y*a*b + x^(5:ℕ)*y*a^(3:ℕ)*b + (5)*x^(5:ℕ)*y^(2:ℕ)*a + (-1)*x^(5:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (3)*x^(6:ℕ) + (-14)*x^(6:ℕ)*a^(2:ℕ) + (2)*x^(6:ℕ)*z*a^(2:ℕ) + x^(6:ℕ)*z*a^(4:ℕ) + (-1)*x^(6:ℕ)*y*b + (-2)*x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*y^(2:ℕ) + (5)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (6)*x^(7:ℕ)*a + (-6)*x^(7:ℕ)*a^(3:ℕ) + x^(7:ℕ)*z*a^(3:ℕ) + (-3)*x^(7:ℕ)*y*a*b + (-4)*x^(7:ℕ)*y*a^(3:ℕ)*b + (3)*x^(7:ℕ)*y^(2:ℕ)*a + (3)*x^(7:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-2)*x^(8:ℕ) + (6)*x^(8:ℕ)*a^(2:ℕ) + (-3)*x^(8:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(8:ℕ)*y*a^(4:ℕ)*b + (3)*x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(8:ℕ)*y^(2:ℕ)*a^(4:ℕ) + (-4)*x^(9:ℕ)*a + (4)*x^(9:ℕ)*a^(3:ℕ) + (-1)*x^(9:ℕ)*y*a^(3:ℕ)*b + x^(9:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-2)*x^(10:ℕ)*a^(2:ℕ) + x^(10:ℕ)*a^(4:ℕ))/(x^(2:ℕ)*w))*v 42 + ((-2 + (2)*z + (2)*y^(2:ℕ) + (-2)*x*z*a + (2)*x*y^(2:ℕ)*a + (5)*x^(2:ℕ) + (-1)*x^(2:ℕ)*w + (-2)*x^(2:ℕ)*z*a^(2:ℕ) + (-2)*x^(2:ℕ)*y^(2:ℕ) + (7)*x^(3:ℕ)*a + (-1)*x^(3:ℕ)*w*a + x^(3:ℕ)*z*a + x^(3:ℕ)*y*a*b + (-3)*x^(3:ℕ)*y^(2:ℕ)*a + (-4)*x^(4:ℕ) + x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ)*w + (-1)*x^(4:ℕ)*z + (4)*x^(4:ℕ)*z*a^(2:ℕ) + x^(4:ℕ)*y*b + x^(4:ℕ)*y*a^(2:ℕ)*b + (2)*x^(4:ℕ)*y^(2:ℕ) + (-1)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-11)*x^(5:ℕ)*a + (-1)*x^(5:ℕ)*a^(3:ℕ) + (2)*x^(5:ℕ)*w*a + x^(5:ℕ)*z*a + x^(5:ℕ)*z*a^(3:ℕ) + (-1)*x^(5:ℕ)*y*a*b + (4)*x^(5:ℕ)*y^(2:ℕ)*a + (3)*x^(6:ℕ) + (-8)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ)*w*a^(2:ℕ) + (-1)*x^(6:ℕ)*z*a^(2:ℕ) + (-2)*x^(6:ℕ)*y*b + (-3)*x^(6:ℕ)*y*a^(2:ℕ)*b + (2)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (8)*x^(7:ℕ)*a + (-1)*x^(7:ℕ)*z*a + (-1)*x^(7:ℕ)*z*a^(3:ℕ) + (-2)*x^(7:ℕ)*y*a*b + (-1)*x^(7:ℕ)*y*a^(3:ℕ)*b + (-2)*x^(7:ℕ)*y^(2:ℕ)*a + (-2)*x^(8:ℕ) + (8)*x^(8:ℕ)*a^(2:ℕ) + x^(8:ℕ)*a^(4:ℕ) + (-1)*x^(8:ℕ)*z*a^(2:ℕ) + x^(8:ℕ)*y*b + x^(8:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(8:ℕ)*y^(2:ℕ) + (-3)*x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-5)*x^(9:ℕ)*a + (3)*x^(9:ℕ)*a^(3:ℕ) + (2)*x^(9:ℕ)*y*a*b + x^(9:ℕ)*y*a^(3:ℕ)*b + (-2)*x^(9:ℕ)*y^(2:ℕ)*a + (-1)*x^(9:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-4)*x^(10:ℕ)*a^(2:ℕ) + x^(10:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(10:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1)*x^(11:ℕ)*a^(3:ℕ))/(x^(2:ℕ)*w))*v 84 + ((-2 + (2)*z + (2)*x*z*a + (2)*x^(2:ℕ) + (-2)*x^(2:ℕ)*z + x^(3:ℕ)*a + (-3)*x^(3:ℕ)*z*a + x^(4:ℕ) + x^(4:ℕ)*z + (-1)*x^(4:ℕ)*z*a^(2:ℕ) + (2)*x^(5:ℕ)*a + (2)*x^(5:ℕ)*z*a + x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ)*z*a^(2:ℕ))/(x^(2:ℕ)))*v 192 = 0 ∧
      (-3 + x^(2:ℕ) + x^(2:ℕ)*a^(2:ℕ) + (2)*x^(3:ℕ)*a)*v 24 + ((3 + (-6)*z + (-3)*y*b + (-5)*y^(2:ℕ) + (9)*x*a + (-3)*x*z*a + x*y*a*b + (-3)*x*y^(2:ℕ)*a + (-2)*x^(2:ℕ) + (3)*x^(2:ℕ)*a^(2:ℕ) + (-1)*x^(2:ℕ)*z + x^(2:ℕ)*z*a^(2:ℕ) + (3)*x^(2:ℕ)*y*b + x^(2:ℕ)*y*a^(2:ℕ)*b + (2)*x^(2:ℕ)*y^(2:ℕ) + (-1)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-8)*x^(3:ℕ)*a + x^(3:ℕ)*z*a + x^(3:ℕ)*z*a^(3:ℕ) + x^(3:ℕ)*y*a*b + (3)*x^(3:ℕ)*y^(2:ℕ)*a + (3)*x^(4:ℕ) + (-6)*x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ)*z*a^(2:ℕ) + (-1)*x^(4:ℕ)*y*b + (-3)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*y^(2:ℕ) + (2)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (3)*x^(5:ℕ)*a + (-2)*x^(5:ℕ)*y*a*b + (-1)*x^(5:ℕ)*y*a^(3:ℕ)*b + (2)*x^(5:ℕ)*y^(2:ℕ)*a + x^(5:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-2)*x^(6:ℕ) + (3)*x^(6:ℕ)*a^(2:ℕ) + (-1)*x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2)*x^(7:ℕ)*a + x^(7:ℕ)*a^(3:ℕ))/(w))*v 42 + ((1 + (-1)*w + (-2)*z + (-2)*y^(2:ℕ) + (2)*x*a + x*z*a + x*y*a*b + (-1)*x*y^(2:ℕ)*a + (-2)*x^(2:ℕ) + (-1)*x^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ)*w + x^(2:ℕ)*z + x^(2:ℕ)*z*a^(2:ℕ) + x^(2:ℕ)*y*b + (2)*x^(2:ℕ)*y^(2:ℕ) + (-7)*x^(3:ℕ)*a + x^(3:ℕ)*w*a + (-2)*x^(3:ℕ)*y*a*b + (2)*x^(3:ℕ)*y^(2:ℕ)*a + (3)*x^(4:ℕ) + (-1)*x^(4:ℕ)*a^(2:ℕ) + (-1)*x^(4:ℕ)*z*a^(2:ℕ) + (-2)*x^(4:ℕ)*y*b + (-1)*x^(4:ℕ)*y*a^(2:ℕ)*b + (5)*x^(5:ℕ)*a + x^(5:ℕ)*a^(3:ℕ) + (-1)*x^(5:ℕ)*z*a + (-2)*x^(5:ℕ)*y^(2:ℕ)*a + (-2)*x^(6:ℕ) + (3)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ)*y*b + x^(6:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(6:ℕ)*y^(2:ℕ) + (-1)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-3)*x^(7:ℕ)*a + x^(7:ℕ)*y*a*b + (-1)*x^(7:ℕ)*y^(2:ℕ)*a + (-1)*x^(8:ℕ)*a^(2:ℕ))/(w))*v 84 + (-1 + (-2)*z + (-1)*x*z*a + x^(2:ℕ)*z + x^(3:ℕ)*a + x^(3:ℕ)*z*a)*v 192 = 0 ∧
      ((-2 + (-1)*y*b + (-1)*y^(2:ℕ) + (-1)*x*y*a*b + (-1)*x*y^(2:ℕ)*a + x^(2:ℕ) + (-1)*x^(2:ℕ)*a^(2:ℕ) + (-1)*x^(2:ℕ)*y*b + (-1)*x^(2:ℕ)*y^(2:ℕ) + (-5)*x^(3:ℕ)*a + (-1)*x^(3:ℕ)*a^(3:ℕ) + (-3)*x^(4:ℕ) + (-3)*x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y*b + x^(4:ℕ)*y^(2:ℕ) + (-2)*x^(5:ℕ)*a + x^(6:ℕ) + x^(6:ℕ)*a^(2:ℕ) + (2)*x^(7:ℕ)*a)/(x^(2:ℕ)))*v 24 + ((-6 + w + (3)*z + (-11)*x*a + (8)*x*z*a + (2)*x*y*a*b + (4)*x*y^(2:ℕ)*a + (-8)*x^(2:ℕ) + (-9)*x^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ)*w + (8)*x^(2:ℕ)*z + (2)*x^(2:ℕ)*z*a^(2:ℕ) + x^(2:ℕ)*y*b + x^(2:ℕ)*y*a^(2:ℕ)*b + (3)*x^(2:ℕ)*y^(2:ℕ) + (2)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-3)*x^(3:ℕ)*a + (-3)*x^(3:ℕ)*a^(3:ℕ) + (-2)*x^(3:ℕ)*z*a^(3:ℕ) + (-1)*x^(3:ℕ)*y*a*b + (-5)*x^(3:ℕ)*y^(2:ℕ)*a + (7)*x^(4:ℕ) + (8)*x^(4:ℕ)*a^(2:ℕ) + (-3)*x^(4:ℕ)*z + (-5)*x^(4:ℕ)*z*a^(2:ℕ) + (-1)*x^(4:ℕ)*z*a^(4:ℕ) + (-4)*x^(4:ℕ)*y*b + (3)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-9)*x^(4:ℕ)*y^(2:ℕ) + (-6)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (13)*x^(5:ℕ)*a + (5)*x^(5:ℕ)*a^(3:ℕ) + (-4)*x^(5:ℕ)*z*a + (-2)*x^(5:ℕ)*z*a^(3:ℕ) + (4)*x^(5:ℕ)*y*a*b + (4)*x^(5:ℕ)*y*a^(3:ℕ)*b + (-10)*x^(5:ℕ)*y^(2:ℕ)*a + (-3)*x^(5:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-1)*x^(6:ℕ) + (2)*x^(6:ℕ)*a^(2:ℕ) + (-1)*x^(6:ℕ)*z + (4)*x^(6:ℕ)*y*b + (7)*x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*y*a^(4:ℕ)*b + x^(6:ℕ)*y^(2:ℕ) + (-6)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1)*x^(6:ℕ)*y^(2:ℕ)*a^(4:ℕ) + (-7)*x^(7:ℕ)*a + (-4)*x^(7:ℕ)*a^(3:ℕ) + x^(7:ℕ)*z*a + x^(7:ℕ)*z*a^(3:ℕ) + (3)*x^(7:ℕ)*y*a*b + (2)*x^(7:ℕ)*y*a^(3:ℕ)*b + x^(7:ℕ)*y^(2:ℕ)*a + (-2)*x^(7:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (5)*x^(8:ℕ) + (-7)*x^(8:ℕ)*a^(2:ℕ) + (-1)*x^(8:ℕ)*a^(4:ℕ) + x^(8:ℕ)*z*a^(2:ℕ) + (-1)*x^(8:ℕ)*y*b + (-2)*x^(8:ℕ)*y*a^(2:ℕ)*b + x^(8:ℕ)*y^(2:ℕ) + x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (5)*x^(9:ℕ)*a + (-1)*x^(9:ℕ)*a^(3:ℕ) + (-2)*x^(9:ℕ)*y*a*b + (-1)*x^(9:ℕ)*y*a^(3:ℕ)*b + (2)*x^(9:ℕ)*y^(2:ℕ)*a + x^(9:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-2)*x^(10:ℕ) + (3)*x^(10:ℕ)*a^(2:ℕ) + (-1)*x^(10:ℕ)*y*a^(2:ℕ)*b + x^(10:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2)*x^(11:ℕ)*a + x^(11:ℕ)*a^(3:ℕ))/(x^(2:ℕ)*w))*v 42 + ((-2 + (-2)*x*a + (-1)*x*w*a + x*z*a + (2)*x*y^(2:ℕ)*a + (-1)*x^(2:ℕ)*w + (2)*x^(2:ℕ)*z + (-2)*x^(2:ℕ)*z*a^(2:ℕ) + (2)*x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (7)*x^(3:ℕ)*a + (-2)*x^(3:ℕ)*w*a + (-4)*x^(3:ℕ)*z*a + (-1)*x^(3:ℕ)*z*a^(3:ℕ) + x^(3:ℕ)*y*a*b + (-1)*x^(3:ℕ)*y^(2:ℕ)*a + (7)*x^(4:ℕ) + (5)*x^(4:ℕ)*a^(2:ℕ) + (-2)*x^(4:ℕ)*w + (-1)*x^(4:ℕ)*w*a^(2:ℕ) + (-2)*x^(4:ℕ)*z + x^(4:ℕ)*y*b + (2)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-2)*x^(4:ℕ)*y^(2:ℕ) + (-1)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(5:ℕ)*a + (-1)*x^(5:ℕ)*w*a + (4)*x^(5:ℕ)*z*a + x^(5:ℕ)*z*a^(3:ℕ) + (3)*x^(5:ℕ)*y*a*b + x^(5:ℕ)*y*a^(3:ℕ)*b + x^(5:ℕ)*y^(2:ℕ)*a + (-3)*x^(6:ℕ) + (-7)*x^(6:ℕ)*a^(2:ℕ) + (-1)*x^(6:ℕ)*a^(4:ℕ) + x^(6:ℕ)*w + x^(6:ℕ)*z + (3)*x^(6:ℕ)*z*a^(2:ℕ) + x^(6:ℕ)*y*b + (4)*x^(6:ℕ)*y^(2:ℕ) + (3)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-6)*x^(7:ℕ)*a + (-4)*x^(7:ℕ)*a^(3:ℕ) + x^(7:ℕ)*w*a + x^(7:ℕ)*z*a + (-4)*x^(7:ℕ)*y*a*b + (-1)*x^(7:ℕ)*y*a^(3:ℕ)*b + (6)*x^(7:ℕ)*y^(2:ℕ)*a + x^(7:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (5)*x^(8:ℕ) + (-1)*x^(8:ℕ)*z*a^(2:ℕ) + (-3)*x^(8:ℕ)*y*b + (-3)*x^(8:ℕ)*y*a^(2:ℕ)*b + x^(8:ℕ)*y^(2:ℕ) + (2)*x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (8)*x^(9:ℕ)*a + (2)*x^(9:ℕ)*a^(3:ℕ) + (-1)*x^(9:ℕ)*z*a + (-1)*x^(9:ℕ)*y*a*b + (-1)*x^(9:ℕ)*y^(2:ℕ)*a + (-2)*x^(10:ℕ) + (4)*x^(10:ℕ)*a^(2:ℕ) + x^(10:ℕ)*y*b + x^(10:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(10:ℕ)*y^(2:ℕ) + (-1)*x^(10:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-3)*x^(11:ℕ)*a + x^(11:ℕ)*y*a*b + (-1)*x^(11:ℕ)*y^(2:ℕ)*a + (-1)*x^(12:ℕ)*a^(2:ℕ))/(x^(2:ℕ)*w))*v 84 + ((-2 + (-3)*x*a + (2)*x*z*a + (-2)*x^(2:ℕ) + (2)*x^(2:ℕ)*z + x^(2:ℕ)*z*a^(2:ℕ) + (-2)*x^(3:ℕ)*a + (-1)*x^(3:ℕ)*z*a + (-1)*x^(4:ℕ)*a^(2:ℕ) + (-3)*x^(4:ℕ)*z + (-1)*x^(4:ℕ)*z*a^(2:ℕ) + (-1)*x^(5:ℕ)*a + (-2)*x^(5:ℕ)*z*a + x^(6:ℕ) + x^(6:ℕ)*z + x^(7:ℕ)*a + x^(7:ℕ)*z*a)/(x^(2:ℕ)))*v 192 = 0 ∧
      (((-2)*z + (-1)*y*z*b + (-1)*y^(2:ℕ)*z + (-1)*x^(2:ℕ)*z + (-1)*x^(2:ℕ)*z*a^(2:ℕ) + (-2)*x^(3:ℕ)*z*a)/(x^(2:ℕ)*y^(2:ℕ)))*v 24 + (((-5)*z + (-2)*z*w + (2)*z^(2:ℕ) + (-1)*y*z*b + (-1)*y^(2:ℕ)*z + (-1)*x*z*a + x*z^(2:ℕ)*a + (3)*x*y*z*a*b + x*y^(2:ℕ)*z*a + (-3)*x^(2:ℕ)*z*a^(2:ℕ) + x^(2:ℕ)*z^(2:ℕ) + (-1)*x^(2:ℕ)*z^(2:ℕ)*a^(2:ℕ) + (-1)*x^(2:ℕ)*y*z*b + x^(2:ℕ)*y*z*a^(2:ℕ)*b + (-4)*x^(2:ℕ)*y^(2:ℕ)*z + (-1)*x^(2:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (4)*x^(3:ℕ)*z*a + (-1)*x^(3:ℕ)*z^(2:ℕ)*a + (-1)*x^(3:ℕ)*z^(2:ℕ)*a^(3:ℕ) + x^(3:ℕ)*y*z*a*b + (-5)*x^(3:ℕ)*y^(2:ℕ)*z*a + x^(4:ℕ)*z + (4)*x^(4:ℕ)*z*a^(2:ℕ) + (-1)*x^(4:ℕ)*z^(2:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y*z*b + (3)*x^(4:ℕ)*y*z*a^(2:ℕ)*b + (-1)*x^(4:ℕ)*y^(2:ℕ)*z + (-2)*x^(4:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (-3)*x^(5:ℕ)*z*a + (2)*x^(5:ℕ)*y*z*a*b + x^(5:ℕ)*y*z*a^(3:ℕ)*b + (-2)*x^(5:ℕ)*y^(2:ℕ)*z*a + (-1)*x^(5:ℕ)*y^(2:ℕ)*z*a^(3:ℕ) + (2)*x^(6:ℕ)*z + (-3)*x^(6:ℕ)*z*a^(2:ℕ) + x^(6:ℕ)*y*z*a^(2:ℕ)*b + (-1)*x^(6:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (2)*x^(7:ℕ)*z*a + (-1)*x^(7:ℕ)*z*a^(3:ℕ))/(x^(2:ℕ)*y^(2:ℕ)*w))*v 42 + (((-1)*z + (-1)*z*w + (2)*x*z*a + (-1)*x*z^(2:ℕ)*a + x*y*z*a*b + x*y^(2:ℕ)*z*a + (2)*x^(2:ℕ)*z + (-1)*x^(2:ℕ)*z*a^(2:ℕ) + (-1)*x^(2:ℕ)*z*w + x^(2:ℕ)*z^(2:ℕ) + (-1)*x^(2:ℕ)*z^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ)*y*z*b + x^(3:ℕ)*z*a + (-1)*x^(3:ℕ)*z*w*a + x^(4:ℕ)*z + x^(4:ℕ)*z*a^(2:ℕ) + x^(4:ℕ)*z^(2:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y*z*a^(2:ℕ)*b + (2)*x^(4:ℕ)*y^(2:ℕ)*z + (-3)*x^(5:ℕ)*z*a + (-1)*x^(5:ℕ)*z*a^(3:ℕ) + x^(5:ℕ)*z^(2:ℕ)*a + (2)*x^(5:ℕ)*y^(2:ℕ)*z*a + (2)*x^(6:ℕ)*z + (-3)*x^(6:ℕ)*z*a^(2:ℕ) + (-1)*x^(6:ℕ)*y*z*b + (-1)*x^(6:ℕ)*y*z*a^(2:ℕ)*b + x^(6:ℕ)*y^(2:ℕ)*z + x^(6:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (3)*x^(7:ℕ)*z*a + (-1)*x^(7:ℕ)*y*z*a*b + x^(7:ℕ)*y^(2:ℕ)*z*a + x^(8:ℕ)*z*a^(2:ℕ))/(x^(2:ℕ)*y^(2:ℕ)*w))*v 84 + (((-3)*z + x*z^(2:ℕ)*a + (-1)*x^(2:ℕ)*z + (-1)*x^(2:ℕ)*z^(2:ℕ) + (-1)*x^(3:ℕ)*z*a + (-1)*x^(3:ℕ)*z^(2:ℕ)*a)/(x^(2:ℕ)*y^(2:ℕ)))*v 192 = 0 ∧
      (-2 + (-1)*y*b + (-1)*y^(2:ℕ) + (-1)*x^(2:ℕ) + (-1)*x^(2:ℕ)*a^(2:ℕ) + (-2)*x^(3:ℕ)*a)*v 24 + ((-4 + (-2)*w + (2)*z + (-3)*x*a + x*z*a + x*y*a*b + (2)*x*y^(2:ℕ)*a + (-1)*x^(2:ℕ) + (-3)*x^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ)*z + (-1)*x^(2:ℕ)*z*a^(2:ℕ) + (-2)*x^(2:ℕ)*y*b + (-3)*x^(2:ℕ)*y^(2:ℕ) + (5)*x^(3:ℕ)*a + (-1)*x^(3:ℕ)*z*a + (-1)*x^(3:ℕ)*z*a^(3:ℕ) + (-4)*x^(3:ℕ)*y^(2:ℕ)*a + (-1)*x^(4:ℕ) + (5)*x^(4:ℕ)*a^(2:ℕ) + (-1)*x^(4:ℕ)*z*a^(2:ℕ) + x^(4:ℕ)*y*b + (3)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(4:ℕ)*y^(2:ℕ) + (-2)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-3)*x^(5:ℕ)*a + (2)*x^(5:ℕ)*y*a*b + x^(5:ℕ)*y*a^(3:ℕ)*b + (-2)*x^(5:ℕ)*y^(2:ℕ)*a + (-1)*x^(5:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (2)*x^(6:ℕ) + (-3)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (2)*x^(7:ℕ)*a + (-1)*x^(7:ℕ)*a^(3:ℕ))/(w))*v 42 + ((-1 + (-1)*w + x*a + (-1)*x*z*a + x*y^(2:ℕ)*a + x^(2:ℕ) + (-1)*x^(2:ℕ)*w + x^(2:ℕ)*z + (-1)*x^(2:ℕ)*z*a^(2:ℕ) + (-1)*x^(2:ℕ)*y^(2:ℕ) + (4)*x^(3:ℕ)*a + (-1)*x^(3:ℕ)*w*a + x^(3:ℕ)*y*a*b + (-1)*x^(3:ℕ)*y^(2:ℕ)*a + x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ)*z*a^(2:ℕ) + x^(4:ℕ)*y*b + x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*y^(2:ℕ) + (-4)*x^(5:ℕ)*a + (-1)*x^(5:ℕ)*a^(3:ℕ) + x^(5:ℕ)*z*a + (2)*x^(5:ℕ)*y^(2:ℕ)*a + (2)*x^(6:ℕ) + (-3)*x^(6:ℕ)*a^(2:ℕ) + (-1)*x^(6:ℕ)*y*b + (-1)*x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*y^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (3)*x^(7:ℕ)*a + (-1)*x^(7:ℕ)*y*a*b + x^(7:ℕ)*y^(2:ℕ)*a + x^(8:ℕ)*a^(2:ℕ))/(w))*v 84 + (-3 + x*z*a + (-1)*x^(2:ℕ) + (-1)*x^(2:ℕ)*z + (-1)*x^(3:ℕ)*a + (-1)*x^(3:ℕ)*z*a)*v 192 = 0

certificate_batch {
/-- The five reduced equations hold for the actual principal-part vector
of the original continued system. No algebraic source row is assumed. -/
theorem original_negative_rows_a {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    negativeRowsAConclusion (primeParameter 2 m s) (primeParameter 3 m s)
      (primeParameter 5 m s) (primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v := by
  apply QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate.negative_rows_a
    (primeParameter 2 m s) (primeParameter 3 m s)
    (primeParameter 5 m s) (primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3)
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (primeParameter_ne_zero 5 m (by decide) s) (primeParameter_ne_zero 7 m (by decide) s) v v
  · exact actual_negative_source_0 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_2 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_4 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_8 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_12 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_16 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_18 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_20 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_22 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_26 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_28 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_30 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_32 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_34 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_36 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_38 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_40 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_42 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_44 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_46 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_48 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_50 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_52 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_54 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_56 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_58 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_60 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_64 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_66 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_68 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_128 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_150 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_162 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_246 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_248 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_252 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_262 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_266 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_270 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_272 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_274 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_288 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_294 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_296 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_298 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_300 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_312 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_316 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_320 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_326 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_358 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_360 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_362 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_366 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_372 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_374 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_378 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_380 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_384 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_398 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_400 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_2790 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_2804 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2806 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2808 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2812 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2814 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2840 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_2850 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2852 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2860 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2866 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2868 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2870 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2872 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2874 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2876 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2932 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_2942 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2950 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2952 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2954 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_3006 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3032 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3058 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3084 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3158 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3206 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3210 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3212 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3216 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3222 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3226 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3232 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3238 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3242 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3250 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3252 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3262 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3292 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3298 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3302 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3304 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3310 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3312 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3358 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3362 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3364 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3376 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3392 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3426 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3432 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3478 hm hf BG G hG hGF s v hv

#print axioms original_negative_rows_a
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveOriginalNegativeRowsBV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

/-- Exactly the eleven selected reduced equations, with their full coefficients. -/
def negativeRowsBConclusion (x y z w a b : ℂ) (v : Fin 210 → ℂ) : Prop :=
((3 + (-3)*x*a + x^(2:ℕ) + x^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ)*y*b + x^(2:ℕ)*y^(2:ℕ) + (3)*x^(3:ℕ)*a + x^(3:ℕ)*a^(3:ℕ) + x^(4:ℕ) + (3)*x^(4:ℕ)*a^(2:ℕ) + (2)*x^(5:ℕ)*a)/(x^(2:ℕ)))*v 24 + ((-3 + (2)*w + (2)*z + y*b + (6)*y^(2:ℕ) + x*w*a + (-8)*x*z*a + (-3)*x*y*a*b + (-3)*x*y^(2:ℕ)*a + (8)*x^(2:ℕ) + (8)*x^(2:ℕ)*a^(2:ℕ) + (-1)*x^(2:ℕ)*z + (-3)*x^(2:ℕ)*z*a^(2:ℕ) + x^(2:ℕ)*y*b + (-1)*x^(2:ℕ)*y*a^(2:ℕ)*b + x^(2:ℕ)*y^(2:ℕ) + (-2)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(3:ℕ)*a + (3)*x^(3:ℕ)*a^(3:ℕ) + (-1)*x^(3:ℕ)*z*a + (2)*x^(3:ℕ)*z*a^(3:ℕ) + x^(3:ℕ)*y*a*b + (5)*x^(3:ℕ)*y^(2:ℕ)*a + (-8)*x^(4:ℕ)*a^(2:ℕ) + (-1)*x^(4:ℕ)*z + (3)*x^(4:ℕ)*z*a^(2:ℕ) + x^(4:ℕ)*z*a^(4:ℕ) + x^(4:ℕ)*y*b + (-3)*x^(4:ℕ)*y*a^(2:ℕ)*b + (4)*x^(4:ℕ)*y^(2:ℕ) + (6)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2)*x^(5:ℕ)*a + (-5)*x^(5:ℕ)*a^(3:ℕ) + x^(5:ℕ)*z*a + (2)*x^(5:ℕ)*z*a^(3:ℕ) + (-3)*x^(5:ℕ)*y*a*b + (-4)*x^(5:ℕ)*y*a^(3:ℕ)*b + (7)*x^(5:ℕ)*y^(2:ℕ)*a + (3)*x^(5:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-1)*x^(6:ℕ) + x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ)*z*a^(2:ℕ) + (-1)*x^(6:ℕ)*y*b + (-6)*x^(6:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(6:ℕ)*y*a^(4:ℕ)*b + x^(6:ℕ)*y^(2:ℕ) + (5)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ)*a^(4:ℕ) + (-1)*x^(7:ℕ)*a + (4)*x^(7:ℕ)*a^(3:ℕ) + (-2)*x^(7:ℕ)*y*a*b + (-2)*x^(7:ℕ)*y*a^(3:ℕ)*b + (2)*x^(7:ℕ)*y^(2:ℕ)*a + (2)*x^(7:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-2)*x^(8:ℕ) + x^(8:ℕ)*a^(2:ℕ) + x^(8:ℕ)*a^(4:ℕ) + (-1)*x^(8:ℕ)*y*a^(2:ℕ)*b + x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2)*x^(9:ℕ)*a + x^(9:ℕ)*a^(3:ℕ))/(x^(2:ℕ)*w))*v 42 + ((-2 + w + (2)*z + (-1)*y*b + (2)*y^(2:ℕ) + (-3)*x*z*a + (-2)*x*y^(2:ℕ)*a + (5)*x^(2:ℕ) + (-1)*x^(2:ℕ)*z + (2)*x^(2:ℕ)*z*a^(2:ℕ) + x^(2:ℕ)*y*b + (-1)*x^(2:ℕ)*y^(2:ℕ) + (-1)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-6)*x^(3:ℕ)*a + (2)*x^(3:ℕ)*w*a + (3)*x^(3:ℕ)*z*a + x^(3:ℕ)*z*a^(3:ℕ) + (-1)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*y^(2:ℕ)*a + (-4)*x^(4:ℕ) + (-5)*x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ)*w + x^(4:ℕ)*w*a^(2:ℕ) + (-1)*x^(4:ℕ)*z + (-1)*x^(4:ℕ)*y*b + (-2)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(5:ℕ)*a + x^(5:ℕ)*w*a + (-1)*x^(5:ℕ)*z*a + (-1)*x^(5:ℕ)*z*a^(3:ℕ) + (-2)*x^(5:ℕ)*y*a*b + (-1)*x^(5:ℕ)*y*a^(3:ℕ)*b + (-2)*x^(5:ℕ)*y^(2:ℕ)*a + (-1)*x^(6:ℕ) + (6)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ)*a^(4:ℕ) + (-2)*x^(6:ℕ)*z*a^(2:ℕ) + (-2)*x^(6:ℕ)*y^(2:ℕ) + (-3)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1)*x^(7:ℕ)*a + (4)*x^(7:ℕ)*a^(3:ℕ) + (-1)*x^(7:ℕ)*z*a + (2)*x^(7:ℕ)*y*a*b + x^(7:ℕ)*y*a^(3:ℕ)*b + (-4)*x^(7:ℕ)*y^(2:ℕ)*a + (-1)*x^(7:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-2)*x^(8:ℕ) + (-1)*x^(8:ℕ)*a^(2:ℕ) + x^(8:ℕ)*y*b + (2)*x^(8:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(8:ℕ)*y^(2:ℕ) + (-2)*x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-3)*x^(9:ℕ)*a + (-1)*x^(9:ℕ)*a^(3:ℕ) + x^(9:ℕ)*y*a*b + (-1)*x^(9:ℕ)*y^(2:ℕ)*a + (-1)*x^(10:ℕ)*a^(2:ℕ))/(x^(2:ℕ)*w))*v 84 + ((1 + (-1)*w + (2)*z + x*a + (-2)*x*z*a + (3)*x^(2:ℕ) + (-1)*x^(2:ℕ)*z*a^(2:ℕ) + x^(3:ℕ)*a + x^(3:ℕ)*z*a + x^(4:ℕ) + x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ)*z + x^(4:ℕ)*z*a^(2:ℕ) + x^(5:ℕ)*a + x^(5:ℕ)*z*a)/(x^(2:ℕ)))*v 192 = 0 ∧
      (((-3)*z + (2)*x*z*a + (3)*x^(2:ℕ)*z + x^(2:ℕ)*z*a^(2:ℕ) + (-1)*x^(2:ℕ)*y*z*b + (-1)*x^(2:ℕ)*y^(2:ℕ)*z + (2)*x^(3:ℕ)*z*a + (-1)*x^(4:ℕ)*z + (-1)*x^(4:ℕ)*z*a^(2:ℕ) + (-2)*x^(5:ℕ)*z*a)/(y^(2:ℕ)))*v 24 + (((8)*z + z*w + (-7)*z^(2:ℕ) + (-2)*y*z*b + (-8)*y^(2:ℕ)*z + (11)*x*z*a + (-3)*x*y^(2:ℕ)*z*a + (-8)*x^(2:ℕ)*z + (3)*x^(2:ℕ)*z*a^(2:ℕ) + (3)*x^(2:ℕ)*z^(2:ℕ) + (3)*x^(2:ℕ)*z^(2:ℕ)*a^(2:ℕ) + (5)*x^(2:ℕ)*y*z*b + (8)*x^(2:ℕ)*y^(2:ℕ)*z + (-18)*x^(3:ℕ)*z*a + (4)*x^(3:ℕ)*z^(2:ℕ)*a + x^(3:ℕ)*z^(2:ℕ)*a^(3:ℕ) + (-1)*x^(3:ℕ)*y*z*a*b + (7)*x^(3:ℕ)*y^(2:ℕ)*z*a + (3)*x^(4:ℕ)*z + (-8)*x^(4:ℕ)*z*a^(2:ℕ) + x^(4:ℕ)*z^(2:ℕ) + (-4)*x^(4:ℕ)*y*z*b + (-4)*x^(4:ℕ)*y*z*a^(2:ℕ)*b + (-1)*x^(4:ℕ)*y^(2:ℕ)*z + (3)*x^(4:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (11)*x^(5:ℕ)*z*a + (-1)*x^(5:ℕ)*z^(2:ℕ)*a + (-1)*x^(5:ℕ)*z^(2:ℕ)*a^(3:ℕ) + (-3)*x^(5:ℕ)*y*z*a*b + (-1)*x^(5:ℕ)*y*z*a^(3:ℕ)*b + (-1)*x^(5:ℕ)*y^(2:ℕ)*z*a + x^(5:ℕ)*y^(2:ℕ)*z*a^(3:ℕ) + (-5)*x^(6:ℕ)*z + (9)*x^(6:ℕ)*z*a^(2:ℕ) + (-1)*x^(6:ℕ)*z^(2:ℕ)*a^(2:ℕ) + x^(6:ℕ)*y*z*b + (2)*x^(6:ℕ)*y*z*a^(2:ℕ)*b + (-1)*x^(6:ℕ)*y^(2:ℕ)*z + (-1)*x^(6:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (-5)*x^(7:ℕ)*z*a + x^(7:ℕ)*z*a^(3:ℕ) + (2)*x^(7:ℕ)*y*z*a*b + x^(7:ℕ)*y*z*a^(3:ℕ)*b + (-2)*x^(7:ℕ)*y^(2:ℕ)*z*a + (-1)*x^(7:ℕ)*y^(2:ℕ)*z*a^(3:ℕ) + (2)*x^(8:ℕ)*z + (-3)*x^(8:ℕ)*z*a^(2:ℕ) + x^(8:ℕ)*y*z*a^(2:ℕ)*b + (-1)*x^(8:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (2)*x^(9:ℕ)*z*a + (-1)*x^(9:ℕ)*z*a^(3:ℕ))/(y^(2:ℕ)*w))*v 42 + ((z + (-2)*z^(2:ℕ) + y*z*b + (-3)*y^(2:ℕ)*z + (-1)*x*z*a + (3)*x*z^(2:ℕ)*a + (-1)*x*y^(2:ℕ)*z*a + (-8)*x^(2:ℕ)*z + (2)*x^(2:ℕ)*z*w + (2)*x^(2:ℕ)*z^(2:ℕ) + x^(2:ℕ)*z^(2:ℕ)*a^(2:ℕ) + (-1)*x^(2:ℕ)*y*z*b + (4)*x^(2:ℕ)*y^(2:ℕ)*z + (-6)*x^(3:ℕ)*z*a + x^(3:ℕ)*z*w*a + (-3)*x^(3:ℕ)*z^(2:ℕ)*a + (-2)*x^(3:ℕ)*y*z*a*b + (2)*x^(3:ℕ)*y^(2:ℕ)*z*a + (6)*x^(4:ℕ)*z + (-1)*x^(4:ℕ)*z*w + (-1)*x^(4:ℕ)*z^(2:ℕ) + (-2)*x^(4:ℕ)*z^(2:ℕ)*a^(2:ℕ) + (-2)*x^(4:ℕ)*y*z*b + (-1)*x^(4:ℕ)*y*z*a^(2:ℕ)*b + (-3)*x^(4:ℕ)*y^(2:ℕ)*z + (11)*x^(5:ℕ)*z*a + x^(5:ℕ)*z*a^(3:ℕ) + (-1)*x^(5:ℕ)*z*w*a + (-1)*x^(5:ℕ)*z^(2:ℕ)*a + (2)*x^(5:ℕ)*y*z*a*b + (-4)*x^(5:ℕ)*y^(2:ℕ)*z*a + (-5)*x^(6:ℕ)*z + (4)*x^(6:ℕ)*z*a^(2:ℕ) + x^(6:ℕ)*z^(2:ℕ)*a^(2:ℕ) + (3)*x^(6:ℕ)*y*z*b + (2)*x^(6:ℕ)*y*z*a^(2:ℕ)*b + (-1)*x^(6:ℕ)*y^(2:ℕ)*z + (-1)*x^(6:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (-8)*x^(7:ℕ)*z*a + (-1)*x^(7:ℕ)*z*a^(3:ℕ) + x^(7:ℕ)*z^(2:ℕ)*a + x^(7:ℕ)*y*z*a*b + x^(7:ℕ)*y^(2:ℕ)*z*a + (2)*x^(8:ℕ)*z + (-4)*x^(8:ℕ)*z*a^(2:ℕ) + (-1)*x^(8:ℕ)*y*z*b + (-1)*x^(8:ℕ)*y*z*a^(2:ℕ)*b + x^(8:ℕ)*y^(2:ℕ)*z + x^(8:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (3)*x^(9:ℕ)*z*a + (-1)*x^(9:ℕ)*y*z*a*b + x^(9:ℕ)*y^(2:ℕ)*z*a + x^(10:ℕ)*z*a^(2:ℕ))/(y^(2:ℕ)*w))*v 84 + ((z + z*w + (-3)*z^(2:ℕ) + (-1)*x*z^(2:ℕ)*a + (-1)*x^(2:ℕ)*z + (3)*x^(2:ℕ)*z^(2:ℕ) + x^(3:ℕ)*z*a + (2)*x^(3:ℕ)*z^(2:ℕ)*a + (-1)*x^(4:ℕ)*z + (-1)*x^(4:ℕ)*z^(2:ℕ) + (-1)*x^(5:ℕ)*z*a + (-1)*x^(5:ℕ)*z^(2:ℕ)*a)/(y^(2:ℕ)))*v 192 = 0 ∧
      (-3 + (2)*x*a + (3)*x^(2:ℕ) + x^(2:ℕ)*a^(2:ℕ) + (-1)*x^(2:ℕ)*y*b + (-1)*x^(2:ℕ)*y^(2:ℕ) + (2)*x^(3:ℕ)*a + (-1)*x^(4:ℕ) + (-1)*x^(4:ℕ)*a^(2:ℕ) + (-2)*x^(5:ℕ)*a)*v 24 + ((5 + w + (-7)*z + (-3)*y*b + (-6)*y^(2:ℕ) + (9)*x*a + (-1)*x*y*a*b + (-2)*x*y^(2:ℕ)*a + (-8)*x^(2:ℕ) + (3)*x^(2:ℕ)*a^(2:ℕ) + (3)*x^(2:ℕ)*z + (3)*x^(2:ℕ)*z*a^(2:ℕ) + (5)*x^(2:ℕ)*y*b + (8)*x^(2:ℕ)*y^(2:ℕ) + (-17)*x^(3:ℕ)*a + (4)*x^(3:ℕ)*z*a + x^(3:ℕ)*z*a^(3:ℕ) + (-1)*x^(3:ℕ)*y*a*b + (7)*x^(3:ℕ)*y^(2:ℕ)*a + (3)*x^(4:ℕ) + (-8)*x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ)*z + (-4)*x^(4:ℕ)*y*b + (-4)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(4:ℕ)*y^(2:ℕ) + (3)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (11)*x^(5:ℕ)*a + (-1)*x^(5:ℕ)*z*a + (-1)*x^(5:ℕ)*z*a^(3:ℕ) + (-3)*x^(5:ℕ)*y*a*b + (-1)*x^(5:ℕ)*y*a^(3:ℕ)*b + (-1)*x^(5:ℕ)*y^(2:ℕ)*a + x^(5:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-5)*x^(6:ℕ) + (9)*x^(6:ℕ)*a^(2:ℕ) + (-1)*x^(6:ℕ)*z*a^(2:ℕ) + x^(6:ℕ)*y*b + (2)*x^(6:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(6:ℕ)*y^(2:ℕ) + (-1)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-5)*x^(7:ℕ)*a + x^(7:ℕ)*a^(3:ℕ) + (2)*x^(7:ℕ)*y*a*b + x^(7:ℕ)*y*a^(3:ℕ)*b + (-2)*x^(7:ℕ)*y^(2:ℕ)*a + (-1)*x^(7:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (2)*x^(8:ℕ) + (-3)*x^(8:ℕ)*a^(2:ℕ) + x^(8:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (2)*x^(9:ℕ)*a + (-1)*x^(9:ℕ)*a^(3:ℕ))/(w))*v 42 + (((-2)*z + (-3)*y^(2:ℕ) + (3)*x*z*a + (-1)*x*y^(2:ℕ)*a + (-7)*x^(2:ℕ) + (2)*x^(2:ℕ)*w + (2)*x^(2:ℕ)*z + x^(2:ℕ)*z*a^(2:ℕ) + (3)*x^(2:ℕ)*y^(2:ℕ) + (-6)*x^(3:ℕ)*a + x^(3:ℕ)*w*a + (-3)*x^(3:ℕ)*z*a + (-2)*x^(3:ℕ)*y*a*b + (2)*x^(3:ℕ)*y^(2:ℕ)*a + (5)*x^(4:ℕ) + (-1)*x^(4:ℕ)*w + (-1)*x^(4:ℕ)*z + (-2)*x^(4:ℕ)*z*a^(2:ℕ) + (-2)*x^(4:ℕ)*y*b + (-1)*x^(4:ℕ)*y*a^(2:ℕ)*b + (-3)*x^(4:ℕ)*y^(2:ℕ) + (11)*x^(5:ℕ)*a + x^(5:ℕ)*a^(3:ℕ) + (-1)*x^(5:ℕ)*w*a + (-1)*x^(5:ℕ)*z*a + (2)*x^(5:ℕ)*y*a*b + (-4)*x^(5:ℕ)*y^(2:ℕ)*a + (-5)*x^(6:ℕ) + (4)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ)*z*a^(2:ℕ) + (3)*x^(6:ℕ)*y*b + (2)*x^(6:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(6:ℕ)*y^(2:ℕ) + (-1)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-8)*x^(7:ℕ)*a + (-1)*x^(7:ℕ)*a^(3:ℕ) + x^(7:ℕ)*z*a + x^(7:ℕ)*y*a*b + x^(7:ℕ)*y^(2:ℕ)*a + (2)*x^(8:ℕ) + (-4)*x^(8:ℕ)*a^(2:ℕ) + (-1)*x^(8:ℕ)*y*b + (-1)*x^(8:ℕ)*y*a^(2:ℕ)*b + x^(8:ℕ)*y^(2:ℕ) + x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (3)*x^(9:ℕ)*a + (-1)*x^(9:ℕ)*y*a*b + x^(9:ℕ)*y^(2:ℕ)*a + x^(10:ℕ)*a^(2:ℕ))/(w))*v 84 + ((-3)*z + (-1)*x*z*a + (-1)*x^(2:ℕ) + (3)*x^(2:ℕ)*z + x^(3:ℕ)*a + (2)*x^(3:ℕ)*z*a + (-1)*x^(4:ℕ) + (-1)*x^(4:ℕ)*z + (-1)*x^(5:ℕ)*a + (-1)*x^(5:ℕ)*z*a)*v 192 = 0 ∧
      (((-3)*z + (2)*x*z*a + x*y*z*a*b + x*y^(2:ℕ)*z*a + (3)*x^(2:ℕ)*z + (-1)*x^(2:ℕ)*z*a^(2:ℕ) + x^(2:ℕ)*y*z*b + x^(2:ℕ)*y^(2:ℕ)*z + x^(3:ℕ)*z*a + x^(3:ℕ)*z*a^(3:ℕ) + x^(3:ℕ)*y*z*a*b + x^(3:ℕ)*y^(2:ℕ)*z*a + x^(4:ℕ)*z + (3)*x^(4:ℕ)*z*a^(2:ℕ) + (3)*x^(5:ℕ)*z*a + x^(5:ℕ)*z*a^(3:ℕ) + (2)*x^(6:ℕ)*z*a^(2:ℕ))/(y^(2:ℕ)))*v 24 + (((7)*z + (-2)*z*w + (-6)*z^(2:ℕ) + (-1)*y*z*b + (-6)*y^(2:ℕ)*z + (12)*x*z*a + (-1)*x*z*w*a + (-4)*x*z^(2:ℕ)*a + x*y*z*a*b + (-1)*x*y^(2:ℕ)*z*a + (2)*x^(2:ℕ)*z + (4)*x^(2:ℕ)*z*a^(2:ℕ) + (-3)*x^(2:ℕ)*z^(2:ℕ) + (-3)*x^(2:ℕ)*z^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ)*y*z*b + (-1)*x^(2:ℕ)*y*z*a^(2:ℕ)*b + x^(2:ℕ)*y^(2:ℕ)*z + (-2)*x^(2:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (4)*x^(3:ℕ)*z*a + (3)*x^(3:ℕ)*z*a^(3:ℕ) + (-5)*x^(3:ℕ)*z^(2:ℕ)*a + (-2)*x^(3:ℕ)*y*z*a*b + (3)*x^(4:ℕ)*z*a^(2:ℕ) + (-1)*x^(4:ℕ)*z^(2:ℕ) + x^(4:ℕ)*z^(2:ℕ)*a^(4:ℕ) + x^(4:ℕ)*y*z*b + (-2)*x^(4:ℕ)*y*z*a^(2:ℕ)*b + (4)*x^(4:ℕ)*y^(2:ℕ)*z + (3)*x^(4:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (-4)*x^(5:ℕ)*z*a + (-2)*x^(5:ℕ)*z*a^(3:ℕ) + (3)*x^(5:ℕ)*z^(2:ℕ)*a^(3:ℕ) + (-3)*x^(5:ℕ)*y*z*a^(3:ℕ)*b + (9)*x^(5:ℕ)*y^(2:ℕ)*z*a + (2)*x^(5:ℕ)*y^(2:ℕ)*z*a^(3:ℕ) + (-1)*x^(6:ℕ)*z + (-7)*x^(6:ℕ)*z*a^(2:ℕ) + (2)*x^(6:ℕ)*z^(2:ℕ)*a^(2:ℕ) + x^(6:ℕ)*z^(2:ℕ)*a^(4:ℕ) + (-1)*x^(6:ℕ)*y*z*b + (-5)*x^(6:ℕ)*y*z*a^(2:ℕ)*b + (-1)*x^(6:ℕ)*y*z*a^(4:ℕ)*b + x^(6:ℕ)*y^(2:ℕ)*z + (8)*x^(6:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ)*z*a^(4:ℕ) + (2)*x^(7:ℕ)*z*a + (-2)*x^(7:ℕ)*z*a^(3:ℕ) + x^(7:ℕ)*z^(2:ℕ)*a^(3:ℕ) + (-3)*x^(7:ℕ)*y*z*a*b + (-5)*x^(7:ℕ)*y*z*a^(3:ℕ)*b + (3)*x^(7:ℕ)*y^(2:ℕ)*z*a + (4)*x^(7:ℕ)*y^(2:ℕ)*z*a^(3:ℕ) + (-2)*x^(8:ℕ)*z + (4)*x^(8:ℕ)*z*a^(2:ℕ) + x^(8:ℕ)*z*a^(4:ℕ) + (-3)*x^(8:ℕ)*y*z*a^(2:ℕ)*b + (-1)*x^(8:ℕ)*y*z*a^(4:ℕ)*b + (3)*x^(8:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + x^(8:ℕ)*y^(2:ℕ)*z*a^(4:ℕ) + (-4)*x^(9:ℕ)*z*a + (4)*x^(9:ℕ)*z*a^(3:ℕ) + (-1)*x^(9:ℕ)*y*z*a^(3:ℕ)*b + x^(9:ℕ)*y^(2:ℕ)*z*a^(3:ℕ) + (-2)*x^(10:ℕ)*z*a^(2:ℕ) + x^(10:ℕ)*z*a^(4:ℕ))/(y^(2:ℕ)*w))*v 42 + (((2)*z + (-1)*z*w + (-2)*z^(2:ℕ) + y*z*b + (-2)*y^(2:ℕ)*z + (2)*x*z*a + x*z^(2:ℕ)*a + (-3)*x^(2:ℕ)*z + (2)*x^(2:ℕ)*z*w + x^(2:ℕ)*z^(2:ℕ) + (-1)*x^(2:ℕ)*y*z*b + x^(2:ℕ)*y^(2:ℕ)*z + (-1)*x^(2:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (-1)*x^(3:ℕ)*z*a + x^(3:ℕ)*z*w*a + (-1)*x^(3:ℕ)*z^(2:ℕ)*a + x^(3:ℕ)*z^(2:ℕ)*a^(3:ℕ) + (-1)*x^(3:ℕ)*y*z*a*b + (-1)*x^(3:ℕ)*y^(2:ℕ)*z*a + (-3)*x^(4:ℕ)*z*a^(2:ℕ) + x^(4:ℕ)*z*w + x^(4:ℕ)*z*w*a^(2:ℕ) + (-1)*x^(4:ℕ)*z^(2:ℕ) + (3)*x^(4:ℕ)*z^(2:ℕ)*a^(2:ℕ) + (-1)*x^(4:ℕ)*y*z*b + (-1)*x^(4:ℕ)*y*z*a^(2:ℕ)*b + (-3)*x^(5:ℕ)*z*a + (-1)*x^(5:ℕ)*z*a^(3:ℕ) + (2)*x^(5:ℕ)*z*w*a + (-1)*x^(5:ℕ)*y*z*a*b + (-1)*x^(5:ℕ)*y*z*a^(3:ℕ)*b + (-1)*x^(6:ℕ)*z + (-1)*x^(6:ℕ)*z*a^(2:ℕ) + x^(6:ℕ)*z*a^(4:ℕ) + x^(6:ℕ)*z*w*a^(2:ℕ) + (-2)*x^(6:ℕ)*z^(2:ℕ)*a^(2:ℕ) + (-2)*x^(6:ℕ)*y*z*a^(2:ℕ)*b + (-2)*x^(6:ℕ)*y^(2:ℕ)*z + (-1)*x^(6:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (2)*x^(7:ℕ)*z*a + (3)*x^(7:ℕ)*z*a^(3:ℕ) + (-1)*x^(7:ℕ)*z^(2:ℕ)*a + (-1)*x^(7:ℕ)*z^(2:ℕ)*a^(3:ℕ) + (-4)*x^(7:ℕ)*y^(2:ℕ)*z*a + (-1)*x^(7:ℕ)*y^(2:ℕ)*z*a^(3:ℕ) + (-2)*x^(8:ℕ)*z + (4)*x^(8:ℕ)*z*a^(2:ℕ) + x^(8:ℕ)*z*a^(4:ℕ) + (-1)*x^(8:ℕ)*z^(2:ℕ)*a^(2:ℕ) + x^(8:ℕ)*y*z*b + (2)*x^(8:ℕ)*y*z*a^(2:ℕ)*b + (-1)*x^(8:ℕ)*y^(2:ℕ)*z + (-4)*x^(8:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (-5)*x^(9:ℕ)*z*a + (2)*x^(9:ℕ)*z*a^(3:ℕ) + (2)*x^(9:ℕ)*y*z*a*b + x^(9:ℕ)*y*z*a^(3:ℕ)*b + (-2)*x^(9:ℕ)*y^(2:ℕ)*z*a + (-1)*x^(9:ℕ)*y^(2:ℕ)*z*a^(3:ℕ) + (-4)*x^(10:ℕ)*z*a^(2:ℕ) + x^(10:ℕ)*y*z*a^(2:ℕ)*b + (-1)*x^(10:ℕ)*y^(2:ℕ)*z*a^(2:ℕ) + (-1)*x^(11:ℕ)*z*a^(3:ℕ))/(y^(2:ℕ)*w))*v 84 + (((-1)*z + z*w + (-2)*z^(2:ℕ) + x*z*a + (3)*x^(2:ℕ)*z + (-1)*x^(2:ℕ)*z^(2:ℕ)*a^(2:ℕ) + (3)*x^(3:ℕ)*z*a + (-1)*x^(3:ℕ)*z^(2:ℕ)*a + x^(4:ℕ)*z + x^(4:ℕ)*z*a^(2:ℕ) + x^(4:ℕ)*z^(2:ℕ) + (2)*x^(5:ℕ)*z*a + (2)*x^(5:ℕ)*z^(2:ℕ)*a + x^(6:ℕ)*z*a^(2:ℕ) + x^(6:ℕ)*z^(2:ℕ)*a^(2:ℕ))/(y^(2:ℕ)))*v 192 = 0 ∧
      (1 + (-1)*y*b + (-2)*y^(2:ℕ) + (3)*x*a + (-2)*x^(2:ℕ) + (-1)*x^(3:ℕ)*a)*v 42 + ((-1)*y^(2:ℕ) + x*a + (-2)*x^(2:ℕ) + x^(4:ℕ))*v 84 + (w + (-1)*z*w)*v 192 = 0 ∧
      ((-4 + (-2)*y*b + y^(2:ℕ) + x*y*a*b + x^(2:ℕ) + x^(2:ℕ)*y*b + x^(2:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(2:ℕ)*y^(2:ℕ) + (-1)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(3:ℕ)*y*a*b + (-1)*x^(3:ℕ)*y^(2:ℕ)*a + (2)*x^(4:ℕ) + (-1)*x^(4:ℕ)*a^(2:ℕ))/(w))*v 42 + ((-1 + (-1)*y*b + (2)*x*a + x*y*a*b + (2)*x^(2:ℕ) + (-1)*x^(2:ℕ)*a^(2:ℕ) + (2)*x^(2:ℕ)*y*b + (-3)*x^(3:ℕ)*a + (-1)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*y^(2:ℕ)*a + (-1)*x^(4:ℕ)*y*b + x^(4:ℕ)*y^(2:ℕ) + x^(5:ℕ)*a)/(w))*v 84 + (-1 + (-1)*w)*v 192 = 0 ∧
      (-5 + (-1)*y*b + (-1)*y^(2:ℕ))*v 24 + ((-2 + (-2)*w + (-4)*z + (-4)*y*b + (-6)*y^(2:ℕ) + (8)*x*a + (-2)*x*z*a + (4)*x*y*a*b + (-2)*x*y^(2:ℕ)*a + (-2)*x^(2:ℕ) + (2)*x^(2:ℕ)*y*b + (2)*x^(2:ℕ)*y*a^(2:ℕ)*b + (-2)*x^(2:ℕ)*y^(2:ℕ) + (-2)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-4)*x^(3:ℕ)*a + (2)*x^(3:ℕ)*y*a*b + (-2)*x^(3:ℕ)*y^(2:ℕ)*a + (4)*x^(4:ℕ) + (-2)*x^(4:ℕ)*a^(2:ℕ))/(w))*v 42 + (((-2)*w + (-2)*z + (-2)*y^(2:ℕ) + (4)*x*a + (2)*x*y*a*b + (-2)*x^(2:ℕ)*a^(2:ℕ) + (2)*x^(2:ℕ)*z + (2)*x^(2:ℕ)*y*b + (2)*x^(2:ℕ)*y^(2:ℕ) + (-6)*x^(3:ℕ)*a + (-2)*x^(3:ℕ)*y*a*b + (2)*x^(3:ℕ)*y^(2:ℕ)*a + (4)*x^(4:ℕ) + (-2)*x^(4:ℕ)*y*b + (2)*x^(4:ℕ)*y^(2:ℕ) + (2)*x^(5:ℕ)*a)/(w))*v 84 + (-4 + (-2)*z + (-1)*x^(2:ℕ))*v 192 = 0 ∧
      (((-2)*y*b + (-2)*y^(2:ℕ) + (2)*x*a)/(y^(2:ℕ)))*v 42 = 0 ∧
      ((-2 + y^(2:ℕ) + (-1)*x*a + (-2)*x^(2:ℕ) + (-1)*x^(3:ℕ)*a)/(y^(2:ℕ)))*v 42 + ((-1 + (-1)*y*b + x*a + x^(4:ℕ))/(y^(2:ℕ)))*v 84 = 0 ∧
      ((-3 + x*a + (-1)*x*y*a*b + (-1)*x*y^(2:ℕ)*a + x^(2:ℕ) + (-1)*x^(2:ℕ)*y*b + (-1)*x^(2:ℕ)*y^(2:ℕ) + (-2)*x^(3:ℕ)*a + (-1)*x^(3:ℕ)*a^(3:ℕ) + (-1)*x^(4:ℕ) + (-3)*x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y*b + x^(4:ℕ)*y^(2:ℕ) + (-2)*x^(5:ℕ)*a + x^(6:ℕ) + x^(6:ℕ)*a^(2:ℕ) + (2)*x^(7:ℕ)*a)/(y^(2:ℕ)))*v 24 + ((2 + (-2)*z + (-3)*y*b + (-5)*y^(2:ℕ) + (5)*x*z*a + (3)*x*y*a*b + x*y^(2:ℕ)*a + (-8)*x^(2:ℕ) + (-6)*x^(2:ℕ)*a^(2:ℕ) + (3)*x^(2:ℕ)*z + (3)*x^(2:ℕ)*z*a^(2:ℕ) + (3)*x^(2:ℕ)*y*b + (2)*x^(2:ℕ)*y*a^(2:ℕ)*b + (3)*x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-8)*x^(3:ℕ)*a + (-3)*x^(3:ℕ)*a^(3:ℕ) + x^(3:ℕ)*z*a + (-1)*x^(3:ℕ)*z*a^(3:ℕ) + (-2)*x^(3:ℕ)*y^(2:ℕ)*a + (9)*x^(4:ℕ) + (2)*x^(4:ℕ)*a^(2:ℕ) + (-2)*x^(4:ℕ)*z + (-3)*x^(4:ℕ)*z*a^(2:ℕ) + (-1)*x^(4:ℕ)*z*a^(4:ℕ) + (-3)*x^(4:ℕ)*y*b + (-5)*x^(4:ℕ)*y^(2:ℕ) + (-4)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (11)*x^(5:ℕ)*a + (5)*x^(5:ℕ)*a^(3:ℕ) + (-3)*x^(5:ℕ)*z*a + (-2)*x^(5:ℕ)*z*a^(3:ℕ) + (3)*x^(5:ℕ)*y*a^(3:ℕ)*b + (-7)*x^(5:ℕ)*y^(2:ℕ)*a + (-2)*x^(5:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-2)*x^(6:ℕ) + (5)*x^(6:ℕ)*a^(2:ℕ) + (-1)*x^(6:ℕ)*z + (3)*x^(6:ℕ)*y*b + (5)*x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*y*a^(4:ℕ)*b + (2)*x^(6:ℕ)*y^(2:ℕ) + (-4)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1)*x^(6:ℕ)*y^(2:ℕ)*a^(4:ℕ) + (-7)*x^(7:ℕ)*a + (-3)*x^(7:ℕ)*a^(3:ℕ) + x^(7:ℕ)*z*a + x^(7:ℕ)*z*a^(3:ℕ) + (2)*x^(7:ℕ)*y*a*b + (2)*x^(7:ℕ)*y*a^(3:ℕ)*b + (2)*x^(7:ℕ)*y^(2:ℕ)*a + (-2)*x^(7:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (3)*x^(8:ℕ) + (-6)*x^(8:ℕ)*a^(2:ℕ) + (-1)*x^(8:ℕ)*a^(4:ℕ) + x^(8:ℕ)*z*a^(2:ℕ) + (-1)*x^(8:ℕ)*y*b + (-2)*x^(8:ℕ)*y*a^(2:ℕ)*b + x^(8:ℕ)*y^(2:ℕ) + x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (5)*x^(9:ℕ)*a + (-1)*x^(9:ℕ)*a^(3:ℕ) + (-2)*x^(9:ℕ)*y*a*b + (-1)*x^(9:ℕ)*y*a^(3:ℕ)*b + (2)*x^(9:ℕ)*y^(2:ℕ)*a + x^(9:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-2)*x^(10:ℕ) + (3)*x^(10:ℕ)*a^(2:ℕ) + (-1)*x^(10:ℕ)*y*a^(2:ℕ)*b + x^(10:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2)*x^(11:ℕ)*a + x^(11:ℕ)*a^(3:ℕ))/(y^(2:ℕ)*w))*v 42 + ((1 + (-1)*w + (-1)*z + (-2)*y^(2:ℕ) + (2)*x*z*a + x*y*a*b + x*y^(2:ℕ)*a + (-4)*x^(2:ℕ) + (-1)*x^(2:ℕ)*a^(2:ℕ) + (2)*x^(2:ℕ)*z + (-1)*x^(2:ℕ)*z*a^(2:ℕ) + x^(2:ℕ)*y*b + (3)*x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1)*x^(3:ℕ)*w*a + (-3)*x^(3:ℕ)*z*a + (-1)*x^(3:ℕ)*z*a^(3:ℕ) + (-1)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*y^(2:ℕ)*a + (8)*x^(4:ℕ) + (4)*x^(4:ℕ)*a^(2:ℕ) + (-1)*x^(4:ℕ)*w + (-1)*x^(4:ℕ)*w*a^(2:ℕ) + (-1)*x^(4:ℕ)*z + (-1)*x^(4:ℕ)*z*a^(2:ℕ) + (-1)*x^(4:ℕ)*y*b + x^(4:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(4:ℕ)*y^(2:ℕ) + (-1)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (4)*x^(5:ℕ)*a + x^(5:ℕ)*a^(3:ℕ) + (-1)*x^(5:ℕ)*w*a + (2)*x^(5:ℕ)*z*a + x^(5:ℕ)*z*a^(3:ℕ) + (2)*x^(5:ℕ)*y*a*b + x^(5:ℕ)*y*a^(3:ℕ)*b + (-1)*x^(5:ℕ)*y^(2:ℕ)*a + (-4)*x^(6:ℕ) + (-3)*x^(6:ℕ)*a^(2:ℕ) + (-1)*x^(6:ℕ)*a^(4:ℕ) + x^(6:ℕ)*w + (3)*x^(6:ℕ)*z*a^(2:ℕ) + x^(6:ℕ)*y*b + x^(6:ℕ)*y*a^(2:ℕ)*b + (2)*x^(6:ℕ)*y^(2:ℕ) + (2)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-6)*x^(7:ℕ)*a + (-4)*x^(7:ℕ)*a^(3:ℕ) + x^(7:ℕ)*w*a + x^(7:ℕ)*z*a + (-2)*x^(7:ℕ)*y*a*b + (-1)*x^(7:ℕ)*y*a^(3:ℕ)*b + (4)*x^(7:ℕ)*y^(2:ℕ)*a + x^(7:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (3)*x^(8:ℕ) + (-1)*x^(8:ℕ)*a^(2:ℕ) + (-1)*x^(8:ℕ)*z*a^(2:ℕ) + (-2)*x^(8:ℕ)*y*b + (-3)*x^(8:ℕ)*y*a^(2:ℕ)*b + (2)*x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (7)*x^(9:ℕ)*a + (2)*x^(9:ℕ)*a^(3:ℕ) + (-1)*x^(9:ℕ)*z*a + (-1)*x^(9:ℕ)*y*a*b + (-1)*x^(9:ℕ)*y^(2:ℕ)*a + (-2)*x^(10:ℕ) + (4)*x^(10:ℕ)*a^(2:ℕ) + x^(10:ℕ)*y*b + x^(10:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(10:ℕ)*y^(2:ℕ) + (-1)*x^(10:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-3)*x^(11:ℕ)*a + x^(11:ℕ)*y*a*b + (-1)*x^(11:ℕ)*y^(2:ℕ)*a + (-1)*x^(12:ℕ)*a^(2:ℕ))/(y^(2:ℕ)*w))*v 84 + ((-1 + (-2)*z + y*b + (-2)*x*a + x*z*a + (-2)*x^(2:ℕ) + (2)*x^(2:ℕ)*z + x^(2:ℕ)*z*a^(2:ℕ) + (-1)*x^(3:ℕ)*a + x^(4:ℕ) + (-1)*x^(4:ℕ)*a^(2:ℕ) + (-2)*x^(4:ℕ)*z + (-1)*x^(4:ℕ)*z*a^(2:ℕ) + (-1)*x^(5:ℕ)*a + (-2)*x^(5:ℕ)*z*a + x^(6:ℕ) + x^(6:ℕ)*z + x^(7:ℕ)*a + x^(7:ℕ)*z*a)/(y^(2:ℕ)))*v 192 = 0 ∧
      ((1 + (-1)*y*b + (-1)*y^(2:ℕ) + (-3)*x*a + (-4)*x^(2:ℕ) + (-1)*x^(2:ℕ)*a^(2:ℕ) + (-1)*x^(3:ℕ)*a + (2)*x^(4:ℕ))/(y^(2:ℕ)))*v 24 + ((-7 + (6)*z + (2)*y*b + (4)*y^(2:ℕ) + (-8)*x*a + (-1)*x*y*a*b + (-1)*x*y^(2:ℕ)*a + (3)*x^(2:ℕ) + (2)*x^(2:ℕ)*a^(2:ℕ) + (-2)*x^(2:ℕ)*z + (-3)*x^(2:ℕ)*z*a^(2:ℕ) + (-5)*x^(2:ℕ)*y*b + (2)*x^(2:ℕ)*y*a^(2:ℕ)*b + (-8)*x^(2:ℕ)*y^(2:ℕ) + (-1)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (13)*x^(3:ℕ)*a + (-2)*x^(3:ℕ)*z*a + (-1)*x^(3:ℕ)*z*a^(3:ℕ) + (3)*x^(3:ℕ)*y*a*b + x^(3:ℕ)*y*a^(3:ℕ)*b + (-6)*x^(3:ℕ)*y^(2:ℕ)*a + (-1)*x^(3:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-3)*x^(4:ℕ) + (3)*x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ)*z + (4)*x^(4:ℕ)*y*b + (5)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*y^(2:ℕ) + (-4)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-8)*x^(5:ℕ)*a + (-1)*x^(5:ℕ)*a^(3:ℕ) + x^(5:ℕ)*z*a + x^(5:ℕ)*y*a*b + x^(5:ℕ)*y*a^(3:ℕ)*b + (-2)*x^(5:ℕ)*y^(2:ℕ)*a + (-1)*x^(5:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (5)*x^(6:ℕ) + (-4)*x^(6:ℕ)*a^(2:ℕ) + (-1)*x^(6:ℕ)*y*b + x^(6:ℕ)*y^(2:ℕ) + (4)*x^(7:ℕ)*a + (-1)*x^(7:ℕ)*a^(3:ℕ) + (-1)*x^(7:ℕ)*y*a*b + x^(7:ℕ)*y^(2:ℕ)*a + (-2)*x^(8:ℕ) + x^(8:ℕ)*a^(2:ℕ))/(y^(2:ℕ)*w))*v 42 + ((-2 + z + (2)*y^(2:ℕ) + x*a + (-1)*x*w*a + (-3)*x*z*a + (5)*x^(2:ℕ) + (2)*x^(2:ℕ)*a^(2:ℕ) + (-2)*x^(2:ℕ)*w + (-1)*x^(2:ℕ)*z + (-1)*x^(2:ℕ)*z*a^(2:ℕ) + x^(2:ℕ)*y*a^(2:ℕ)*b + (-3)*x^(2:ℕ)*y^(2:ℕ) + (5)*x^(3:ℕ)*a + (-1)*x^(3:ℕ)*a^(3:ℕ) + (-1)*x^(3:ℕ)*w*a + (3)*x^(3:ℕ)*z*a + (3)*x^(3:ℕ)*y*a*b + (-4)*x^(4:ℕ) + (-3)*x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ)*w + (2)*x^(4:ℕ)*z + x^(4:ℕ)*z*a^(2:ℕ) + (2)*x^(4:ℕ)*y*b + (3)*x^(4:ℕ)*y^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-7)*x^(5:ℕ)*a + (-1)*x^(5:ℕ)*a^(3:ℕ) + (-3)*x^(5:ℕ)*y*a*b + (4)*x^(5:ℕ)*y^(2:ℕ)*a + (5)*x^(6:ℕ) + (-1)*x^(6:ℕ)*a^(2:ℕ) + (-1)*x^(6:ℕ)*z + (-3)*x^(6:ℕ)*y*b + (-1)*x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*y^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (7)*x^(7:ℕ)*a + (-2)*x^(8:ℕ) + x^(8:ℕ)*a^(2:ℕ) + x^(8:ℕ)*y*b + (-1)*x^(8:ℕ)*y^(2:ℕ) + (-1)*x^(9:ℕ)*a)/(y^(2:ℕ)*w))*v 84 + ((-2 + (2)*z + (-1)*y*b + (-1)*x*a + (-2)*x^(2:ℕ) + (-3)*x^(2:ℕ)*z + (-1)*x^(3:ℕ)*a + (-1)*x^(3:ℕ)*z*a + x^(4:ℕ) + x^(4:ℕ)*z)/(y^(2:ℕ)))*v 192 = 0

certificate_batch {
/-- The eleven reduced equations hold for the actual principal-part vector
of the original continued system. No algebraic source row is assumed. -/
theorem original_negative_rows_b {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hphase : ε*I^(2*m)= -1) (h5 : badFive f= -1) (h7 : badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    negativeRowsBConclusion (primeParameter 2 m s) (primeParameter 3 m s)
      (primeParameter 5 m s) (primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v := by
  apply QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate.negative_rows_b
    (primeParameter 2 m s) (primeParameter 3 m s)
    (primeParameter 5 m s) (primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3)
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (primeParameter_ne_zero 5 m (by decide) s) (primeParameter_ne_zero 7 m (by decide) s) v v
  · exact actual_negative_source_0 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_2 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_4 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_8 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_12 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_16 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_18 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_20 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_22 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_26 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_28 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_30 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_32 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_34 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_36 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_38 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_40 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_42 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_44 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_46 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_48 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_50 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_52 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_54 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_56 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_58 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_60 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_62 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_64 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_66 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_68 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_128 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_150 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_162 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_246 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_248 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_252 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_262 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_266 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_270 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_272 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_274 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_288 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_292 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_294 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_296 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_298 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_300 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_312 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_316 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_320 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_326 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_358 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_360 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_362 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_366 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_370 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_372 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_374 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_378 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_380 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_382 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_384 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_394 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_398 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_400 hm hf ε hε hlaw hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_2790 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_2806 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2808 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2812 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2814 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2840 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_2850 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2858 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2860 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2866 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2868 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2872 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2874 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2876 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2932 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_2950 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2958 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2964 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2968 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2978 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_3006 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3026 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_3032 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3046 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_3058 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3084 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3174 hm hf ε hlaw hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_3206 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3210 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3212 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3216 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3226 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3232 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3242 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3250 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3256 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3262 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3274 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3292 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3302 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3304 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3310 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3340 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3358 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3362 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3364 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3376 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3392 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3426 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3432 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3440 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3468 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3476 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3478 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3488 hm hf BG G hG hGF s v hv

#print axioms original_negative_rows_b
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveOriginalSignedRow118V1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Matrix Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open scoped Topology

certificate_batch {
theorem original_signed_negative_row118 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    ((1+primeParameter 2 m s*((Real.sqrt 2:ℂ)*f 2)+(primeParameter 2 m s)^2)/
      (primeParameter 2 m s)^2)*v 192=0 := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  have h1 := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift row118Word0
  change v (gridIndex 9)-rationalWordCoefficient m (ε*I^(2*m)) (.generator 4) 9 0 s*
    v (gridIndex (-140))=0 at h1
  have hrate : rationalRate (.generator 4) 9=
      (2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,integerRaw,integerSeed,Matrix.det_fin_two]
  have hcompat : (-u5*u7)^(frickeCount (.generator 4))=
      (-1:ℂ)^(frickeCount (.generator 4))*u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [frickeCount]
  have hc : rationalWordCoefficient m (-u5*u7) (.generator 4) 9 0 s=
      wordCoefficient m (-u5*u7) (.generator 4) 9 0 s :=
    (wordCoefficient_rational m (-u5*u7) (.generator 4) 9 0 s).symm
  rw [hphase,hc,
    word_leading_signed_laurent m (-u5*u7) u5 u7 (.generator 4) 9 (-2,2,-1,-1) hrate hcompat s] at h1
  norm_num [frickeCount,fourPrimeMonomial,gridIndex,zpow_neg,div_eq_mul_inv] at h1
  have hh := pole_hecke_two hm hf BG G hG hGF s v hv 9
  norm_num [gridIndex] at hh
  apply QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate.negative_row118
    (primeParameter 2 m s) (primeParameter 3 m s)
    (u5*primeParameter 5 m s) (u7*primeParameter 7 m s) ((Real.sqrt 2:ℂ)*f 2) 0
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) v v
  · exact actual_signed_negative_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) h1
  · exact actual_signed_negative_source_34 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · simpa only [one_mul] using pole_ramanujan_three hm hf BG G hG hGF s v hv
  · simp only [one_mul,neg_mul,neg_div,one_div,inv_pow] at *
    linear_combination hh

#print axioms original_signed_negative_row118
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveOriginalSignedRowsAV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

certificate_batch {
theorem original_signed_negative_rows_a {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    negativeRowsAConclusion (primeParameter 2 m s) (primeParameter 3 m s)
      (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate.negative_rows_a
    (primeParameter 2 m s) (primeParameter 3 m s)
    (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3)
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s)) (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) v v
  · exact actual_signed_negative_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_34 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_54 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_298 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_320 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_372 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_374 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_398 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_2790 hm hf BG G hG hGF s v hv
  · exact actual_signed_negative_source_2804 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2840 hm hf BG G hG hGF s v hv
  · exact actual_signed_negative_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2852 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2860 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2870 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2932 hm hf BG G hG hGF s v hv
  · exact actual_signed_negative_source_2942 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2952 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2954 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_3006 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3032 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3058 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3084 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3158 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3206 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3210 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3212 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3216 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3222 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3226 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3232 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3238 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3242 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3250 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3252 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3262 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3292 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3298 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3302 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3304 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3310 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3312 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3358 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3362 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3364 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3376 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3392 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3426 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3432 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3478 hm hf BG G hG hGF s v hv

#print axioms original_signed_negative_rows_a
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## QuantitativeArithmeticSmallLevelThirtyFiveOriginalSignedRowsBV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

certificate_batch {
theorem original_signed_negative_rows_b {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    negativeRowsBConclusion (primeParameter 2 m s) (primeParameter 3 m s)
      (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate.negative_rows_b
    (primeParameter 2 m s) (primeParameter 3 m s)
    (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3)
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s)) (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) v v
  · exact actual_signed_negative_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_34 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_54 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_62 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_292 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_298 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_320 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_370 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_372 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_374 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_382 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_394 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_398 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift
  · exact actual_negative_source_2790 hm hf BG G hG hGF s v hv
  · exact actual_signed_negative_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2840 hm hf BG G hG hGF s v hv
  · exact actual_signed_negative_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2858 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2860 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_2932 hm hf BG G hG hGF s v hv
  · exact actual_signed_negative_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2958 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2964 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2968 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_signed_negative_source_2978 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_3006 hm hf BG G hG hGF s v hv
  · exact actual_signed_negative_source_3026 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_3032 hm hf BG G hG hGF s v hv
  · exact actual_signed_negative_source_3046 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_3058 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3084 hm hf BG G hG hGF s v hv
  · exact actual_signed_negative_source_3174 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift
  · exact actual_negative_source_3206 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3210 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3212 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3216 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3226 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3232 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3242 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3250 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3256 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3262 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3274 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3292 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3302 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3304 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3310 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3340 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3358 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3362 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3364 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3376 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3392 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3426 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3432 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3440 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3468 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3476 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3478 hm hf BG G hG hGF s v hv
  · exact actual_negative_source_3488 hm hf BG G hG hGF s v hv

#print axioms original_signed_negative_rows_b
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

