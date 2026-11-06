module
public import QuantitativeArithmeticLevelThirtyFivePoleAlgebraV4

set_option Elab.async false

/-! ## ThirtyFiveOriginalAllSignLeadingExclusion -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

theorem original_all_sign_leading_exclusion {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re) : v 192=0 := by
  have hp := phaseRoot_sign m hε
  change ε*I^(2*m)=1 ∨ ε*I^(2*m)= -1 at hp
  have h5 := badFive_sign hf.toEulerData
  have h7 := badSeven_sign hf.toEulerData
  have hsign : ε*I^(2*m)*badFive f*badSeven f=1 ∨ ε*I^(2*m)*badFive f*badSeven f= -1 := by
    rcases hp with hp|hp <;> rcases h5 with h5|h5 <;> rcases h7 with h7|h7 <;>
      rw [hp,h5,h7] <;> norm_num
  rcases hsign with hpos|hneg
  · exact original_positive_product_pole_exclusion hm hf ε hε hlaw hpos BG G hG hGF s v hv hshift hs
  · exact original_negative_product_pole_exclusion hm hf ε hε hlaw hneg BG G hG hGF s v hv hshift hs

theorem original_all_sign_chi3_leading_zero {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re) : v 70-v 140=0 := by
  rw [original_all_sign_chi3_leading_relation hm hf ε hε hlaw BG G hG hGF s v hv hshift,
    original_all_sign_leading_exclusion hm hf ε hε hlaw BG G hG hGF s v hv hshift hs,mul_zero]

#print axioms original_all_sign_leading_exclusion
#print axioms original_all_sign_chi3_leading_zero
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveRow119 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 30000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate

/-- Exact operation-DAG replay. The displayed initial equations are
literal source rows, not reduced-output assumptions. -/
theorem positive_row119 (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h32 : (1)*v 15 + (((-1)*z)/(x^(2:ℕ)*w))*v 126 = 0)
    (h38 : (1)*v 21 + (((-1)*w)/(x^(2:ℕ)*z))*v 150 = 0)
    (h42 : (1)*v 30 + (((-1)*z)/(w))*v 168 = 0)
    (h48 : (1)*v 42 + (((-1)*w)/(z))*v 180 = 0)
    (h58 : (1)*v 84 + (((-1)*x^(2:ℕ)*w)/(z))*v 195 = 0)
    (h64 : (1)*v 126 + (((-1)*y^(2:ℕ)*w)/(z))*v 200 = 0)
    (h68 : (1)*v 180 + (((-1)*x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203 = 0)
    (h270 : (1)*v 90 + ((-1)*y^(2:ℕ))*v 200 = 0)
    (h300 : (1)*v 120 + ((-1)*x^(2:ℕ))*v 195 = 0)
    (h358 : (1)*v 168 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 203 = 0)
    (h2840 : (1)*v 42 + (1)*v 84 + (1)*v 126 + (1)*v 168 = 0)
    (h2932 : (1)*v 30 + (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + (1)*v 180 = 0)
    (h3232 : (1)*v 15 + (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 = 0)
    (h3244 : (1)*v 21 + (((-1)*a)/(x))*v 42 + ((1)/(x^(2:ℕ)))*v 84 + (1)*v 126 = 0)
    : ((-2 + (-2)*x*a + (-2)*x^(2:ℕ))/(x^(2:ℕ)))*v 42 = 0 := by
  have h17170 : (1)*v 15 + (((-1)*z)/(x^(2:ℕ)*w))*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h32
  have h17218 : (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 + ((z)/(x^(2:ℕ)*w))*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3232-(1)*h17170
  have h17398 : (1)*v 21 + (((-1)*w)/(x^(2:ℕ)*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h38
  have h17437 : (((-1)*a)/(x))*v 42 + ((1)/(x^(2:ℕ)))*v 84 + (1)*v 126 + ((w)/(x^(2:ℕ)*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h3244-(1)*h17398
  have h17537 : (1)*v 30 + (((-1)*z)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h42
  have h17610 : (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + ((z)/(w))*v 168 + (1)*v 180 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2932-(1)*h17537
  have h17667 : ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 + ((z)/(x^(2:ℕ)*w))*v 126 + (((-1)*z*a)/(x*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17218-(((-1)*a)/(x))*h17537
  have h17778 : (((-1)*z)/(w))*v 42 + (1)*v 180 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*z)/(w))*h48
  have h17779 : ((z)/(w))*v 42 + (((-1)*x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h68-(1)*h17778
  have h17832 : ((z)/(w))*v 42 + (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + ((z)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17610-(1)*h17778
  have h18389 : (((-1)*z)/(x^(2:ℕ)*w))*v 84 + (1)*v 195 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*z)/(x^(2:ℕ)*w))*h58
  have h18393 : (((-1)*z)/(w))*v 84 + (1)*v 120 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h300-((-1)*x^(2:ℕ))*h18389
  have h18596 : (((-1)*z)/(y^(2:ℕ)*w))*v 126 + (1)*v 200 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*z)/(y^(2:ℕ)*w))*h64
  have h18600 : (1)*v 90 + (((-1)*z)/(w))*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h270-((-1)*y^(2:ℕ))*h18596
  have h18836 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 42 + (1)*v 203 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (((-1)*w)/(x^(2:ℕ)*y^(2:ℕ)*z))*h17779
  have h18840 : (-1)*v 42 + (1)*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h358-((-1)*x^(2:ℕ)*y^(2:ℕ))*h18836
  have h19189 : (1)*v 90 + (((-1)*z)/(w))*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18600
  have h19230 : ((z)/(w))*v 42 + (1)*v 60 + (1)*v 120 + ((z)/(w))*v 126 + (1)*v 150 + ((z)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17832-(1)*h19189
  have h19820 : (((-1)*z)/(w))*v 84 + (1)*v 120 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18393
  have h19857 : ((z)/(w))*v 42 + (1)*v 60 + ((z)/(w))*v 84 + ((z)/(w))*v 126 + (1)*v 150 + ((z)/(w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19230-(1)*h19820
  have h19929 : ((1)/(x^(2:ℕ)))*v 60 + ((z)/(w))*v 84 + ((z)/(x^(2:ℕ)*w))*v 126 + (((-1)*z*a)/(x*w))*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17667-(1)*h19820
  have h20291 : (-1)*v 42 + (1)*v 168 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h18840
  have h20349 : (2)*v 42 + (1)*v 84 + (1)*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h2840-(1)*h20291
  have h20368 : (((2)*z)/(w))*v 42 + (1)*v 60 + ((z)/(w))*v 84 + ((z)/(w))*v 126 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19857-((z)/(w))*h20291
  have h20456 : (((-1)*z*a)/(x*w))*v 42 + ((1)/(x^(2:ℕ)))*v 60 + ((z)/(w))*v 84 + ((z)/(x^(2:ℕ)*w))*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h19929-(((-1)*z*a)/(x*w))*h20291
  have h21902 : (2)*v 42 + (1)*v 84 + (1)*v 126 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h20349
  have h21923 : (1)*v 60 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20368-((z)/(w))*h21902
  have h22021 : (((-2)*z + (-1)*x*z*a)/(x^(2:ℕ)*w))*v 42 + ((1)/(x^(2:ℕ)))*v 60 + (((-1)*z + x^(2:ℕ)*z)/(x^(2:ℕ)*w))*v 84 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h20456-((z)/(x^(2:ℕ)*w))*h21902
  have h22022 : (((-1)*a + (-2)*x)/(x))*v 42 + ((1 + (-1)*x^(2:ℕ))/(x^(2:ℕ)))*v 84 + ((w)/(x^(2:ℕ)*z))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h17437-(1)*h21902
  have h22163 : (1)*v 60 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) (1)*h21923
  have h22247 : (((-2)*z + (-1)*x*z*a)/(x^(2:ℕ)*w))*v 42 + (((-1)*z + x^(2:ℕ)*z)/(x^(2:ℕ)*w))*v 84 + ((-1)/(x^(2:ℕ)))*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22021-((1)/(x^(2:ℕ)))*h22163
  have h22642 : (((2)*z + x*z*a)/(w))*v 42 + ((z + (-1)*x^(2:ℕ)*z)/(w))*v 84 + (1)*v 150 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) ((-1)*x^(2:ℕ))*h22247
  have h22716 : ((-2 + (-2)*x*a + (-2)*x^(2:ℕ))/(x^(2:ℕ)))*v 42 = 0 := by
    linear_combination (norm := (field_simp [hx,hy,hz,hw]; all_goals ring)) h22022-((w)/(x^(2:ℕ)*z))*h22642
  exact h22716

#print axioms positive_row119

end QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate
end
end

/-! ## ThirtyFiveShiftedScalarAlgebra -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars
open Complex

/-- A pole one or more positive integer shifts to the left cannot satisfy
both the old quadratic divisor and the divisor at the rightmost point. -/
theorem shifted_p_ne_zero (x : ℂ) (r : ℝ) (hr : 2≤r) (hx : r≤‖x‖) :
    x^(2:ℕ)+x*(-x/(r:ℂ)-(r:ℂ)/x)+1≠0 := by
  have hr0 : 0<r := by linarith
  have hrC : (r:ℂ)≠0 := ofReal_ne_zero.mpr hr0.ne'
  have hx0 : x≠0 := by intro h; rw [h,norm_zero] at hx; linarith
  have hr1 : (r:ℂ)-1≠0 := by
    exact_mod_cast (show r-1≠0 by linarith)
  intro h
  have hf : ((r:ℂ)-1)*(x^(2:ℕ)-(r:ℂ))=0 := by
    linear_combination (norm := (field_simp [hrC,hx0]; ring)) (r:ℂ)*h
  have he := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hr1)
  have hn := congrArg norm he
  simp only [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0.le] at hn
  have hsq : r^2≤‖x‖^2 := (sq_le_sq₀ hr0.le (norm_nonneg _)).2 hx
  nlinarith

/-- A useful quantitative version of the unit-circle quadratic root bound. -/
theorem large_quartic_ne_zero (x : ℂ) (r : ℝ) (hr : 1≤r)
    (hx : 2*r≤‖x‖^(2:ℕ)) :
    x^(4:ℕ)-(r:ℂ)*x^(2:ℕ)+(r:ℂ)^(2:ℕ)≠0 := by
  have hr0 : 0≤r := by linarith
  intro h
  have he : x^(4:ℕ)=(r:ℂ)*x^(2:ℕ)-(r:ℂ)^(2:ℕ) := by linear_combination h
  have hn : ‖x‖^(4:ℕ)≤r*‖x‖^(2:ℕ)+r^(2:ℕ) := by
    calc
      ‖x‖^(4:ℕ)=‖x^(4:ℕ)‖ := (norm_pow _ _).symm
      _ = ‖(r:ℂ)*x^(2:ℕ)-(r:ℂ)^(2:ℕ)‖ := congrArg norm he
      _ ≤ ‖(r:ℂ)*x^(2:ℕ)‖+‖(r:ℂ)^(2:ℕ)‖ := norm_sub_le _ _
      _ = _ := by simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0]
  have hmul := mul_nonneg (sq_nonneg ‖x‖) (sub_nonneg.mpr hx)
  have hrmul := mul_nonneg hr0 (sub_nonneg.mpr hx)
  nlinarith

/-- The two-coordinate determinant is nonzero throughout the shifted
physical region; the statement also covers the r=1 weightpoint region. -/
theorem shifted_determinant_ne_zero (x : ℂ) (r : ℝ) (hr : 1≤r)
    (hx : 2*r≤‖x‖^(2:ℕ)) :
    let a := -x/(r:ℂ)-(r:ℂ)/x
    (x-a)*(a^(2:ℕ)*x^(2:ℕ)+a*x^(3:ℕ)+a*x+x^(4:ℕ)-x^(2:ℕ)+1)≠0 := by
  have hr0 : 0<r := by linarith
  have hrC : (r:ℂ)≠0 := ofReal_ne_zero.mpr hr0.ne'
  have hx0 : x≠0 := by intro h; rw [h,norm_zero] at hx; norm_num at hx; linarith
  let a := -x/(r:ℂ)-(r:ℂ)/x
  have hfirst : x-a≠0 := by
    intro h
    have he : ((r:ℂ)+1)*x^(2:ℕ)= -(r:ℂ)^(2:ℕ) := by
      dsimp [a] at h
      linear_combination (norm := (field_simp [hrC,hx0]; ring)) ((r:ℂ)*x)*h
    have hn := congrArg norm he
    have heC : (r:ℂ)+1=((r+1:ℝ):ℂ) := by push_cast; rfl
    rw [heC] at hn
    simp only [norm_mul,norm_pow,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hr0.le,abs_of_nonneg (show 0≤r+1 by linarith)] at hn
    have hmul := mul_nonneg (show 0≤r+1 by linarith) (sub_nonneg.mpr hx)
    nlinarith
  apply mul_ne_zero hfirst
  have hc : (r:ℂ)^(2:ℕ)-(r:ℂ)+1≠0 := by
    exact_mod_cast (show r^(2:ℕ)-r+1≠0 by nlinarith [sq_nonneg (r-1)])
  have hq := large_quartic_ne_zero x r hr hx
  intro h
  have hf : ((r:ℂ)^(2:ℕ)-(r:ℂ)+1)*
      (x^(4:ℕ)-(r:ℂ)*x^(2:ℕ)+(r:ℂ)^(2:ℕ))=0 := by
    linear_combination (norm := (field_simp [hrC,hx0]; ring)) (r:ℂ)^(2:ℕ)*h
  exact (mul_ne_zero hc hq) hf

#print axioms shifted_p_ne_zero
#print axioms large_quartic_ne_zero
#print axioms shifted_determinant_ne_zero
end QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars
end
end

/-! ## ThirtyFiveOriginalRow119 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

/-- This row uses only word, entire Ramanujan, and good-prime Hecke rows.
Consequently the auxiliary signs can be chosen from the Fricke phase alone. -/
theorem original_all_sign_row119 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1+primeParameter 2 m s*((Real.sqrt 2:ℂ)*f 2)+(primeParameter 2 m s)^2)*v 42=0 := by
  let u5 := phaseRoot m ε
  have hu5 : u5=1 ∨ u5= -1 := phaseRoot_sign m hε
  have hu7 : (1:ℂ)=1 ∨ (1:ℂ)= -1 := Or.inl rfl
  have hp : ε*I^(2*m)=u5*1 := by simp [u5,phaseRoot]
  have hu5n : u5≠0 := by rcases hu5 with h|h <;> simp [h]
  have hz := mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s)
  have hw : (1:ℂ)*primeParameter 7 m s≠0 := by
    simpa using primeParameter_ne_zero 7 m (by decide) s
  have hrow := QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate.positive_row119
    (primeParameter 2 m s) (primeParameter 3 m s)
    (u5*primeParameter 5 m s) (1*primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3)
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    hz hw v v
    (actual_positive_source_32 hm hf ε hε hlaw u5 1 hu5 hu7 hp BG G hG hGF s v hv hshift)
    (actual_positive_source_38 hm hf ε hε hlaw u5 1 hu5 hu7 hp BG G hG hGF s v hv hshift)
    (actual_positive_source_42 hm hf ε hε hlaw u5 1 hu5 hu7 hp BG G hG hGF s v hv hshift)
    (actual_positive_source_48 hm hf ε hε hlaw u5 1 hu5 hu7 hp BG G hG hGF s v hv hshift)
    (actual_positive_source_58 hm hf ε hε hlaw u5 1 hu5 hu7 hp BG G hG hGF s v hv hshift)
    (actual_positive_source_64 hm hf ε hε hlaw u5 1 hu5 hu7 hp BG G hG hGF s v hv hshift)
    (actual_positive_source_68 hm hf ε hε hlaw u5 1 hu5 hu7 hp BG G hG hGF s v hv hshift)
    (actual_positive_source_270 hm hf ε hε hlaw u5 1 hu5 hu7 hp BG G hG hGF s v hv hshift)
    (actual_positive_source_300 hm hf ε hε hlaw u5 1 hu5 hu7 hp BG G hG hGF s v hv hshift)
    (actual_positive_source_358 hm hf ε hε hlaw u5 1 hu5 hu7 hp BG G hG hGF s v hv hshift)
    (actual_negative_source_2840 hm hf BG G hG hGF s v hv)
    (actual_negative_source_2932 hm hf BG G hG hGF s v hv)
    (actual_negative_source_3232 hm hf BG G hG hGF s v hv)
    (actual_negative_source_3244 hm hf BG G hG hGF s v hv)
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring))
    (-(primeParameter 2 m s)^2/2)*hrow

#print axioms original_all_sign_row119
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveShiftedFirstRow -/
section
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex

/-- The first reduced row has nonzero coefficient at every shifted point
with shift at least two. The parameter bound retains the original shift. -/
theorem shifted_first_row_ne_zero (m : ℕ) (s : ℂ) (r : ℝ)
    (hr : 4≤r) (hα : 2≤s.re-(m:ℝ))
    (hrα : r≤(2:ℝ)^(s.re-(m:ℝ))) :
    let x := primeParameter 2 m s
    let y := primeParameter 3 m s
    x^(4:ℕ)-2*x^(2:ℕ)+x*(-x/(r:ℂ)-(r:ℂ)/x)-y^(2:ℕ)≠0 := by
  let x := primeParameter 2 m s
  let y := primeParameter 3 m s
  let α := s.re-(m:ℝ)
  have hr0 : 0<r := by linarith
  have hrC : (r:ℂ)≠0 := ofReal_ne_zero.mpr hr0.ne'
  have hx0 : x≠0 := cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hx2 : ‖x^(2:ℕ)‖=(4:ℝ)^α := by
    convert primeParameter_pow_norm 2 m 2 (by decide) s using 1 <;> norm_num [x,α]
  have hx4 : ‖x^(4:ℕ)‖=(16:ℝ)^α := by
    convert primeParameter_pow_norm 2 m 4 (by decide) s using 1 <;> norm_num [x,α]
  have hy2 : ‖y^(2:ℕ)‖=(9:ℝ)^α := by
    convert primeParameter_pow_norm 3 m 2 (by decide) s using 1 <;> norm_num [y,α]
  change x^(4:ℕ)-2*x^(2:ℕ)+x*(-x/(r:ℂ)-(r:ℂ)/x)-y^(2:ℕ)≠0
  intro h
  have he : x^4=(((2+1/r:ℝ):ℂ)*x^2+(r:ℂ))+y^2 := by
    push_cast
    linear_combination (norm := (field_simp [hrC,hx0]; ring)) h
  have hc : 0≤2+1/r := by positivity
  have hn : (16:ℝ)^α ≤ (2+1/r)*(4:ℝ)^α+r+(9:ℝ)^α := by
    calc
      (16:ℝ)^α=‖x^4‖ := hx4.symm
      _ = ‖(((2+1/r:ℝ):ℂ)*x^2+(r:ℂ))+y^2‖ := congrArg norm he
      _ ≤ ‖((2+1/r:ℝ):ℂ)*x^2+(r:ℂ)‖+‖y^2‖ := norm_add_le _ _
      _ ≤ (‖((2+1/r:ℝ):ℂ)*x^2‖+‖(r:ℂ)‖)+‖y^2‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc,
          Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0.le,hx2,hy2]
  have hrec : 1/r≤(1/4:ℝ) := (div_le_iff₀ hr0).2 (by linarith)
  have hmul := mul_le_mul_of_nonneg_right (show 2+1/r≤(9/4:ℝ) by linarith)
    (Real.rpow_nonneg (show (0:ℝ)≤4 by norm_num) α)
  have hd := QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars.shifted_exponential_dominance α hα
  linarith

#print axioms shifted_first_row_ne_zero
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveShiftedPivot -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars
open Complex

/-- The coefficient eliminating coordinate 24 is nonzero in every positive
shift, including the one-step case. -/
theorem shifted_h_ne_zero (x : ℂ) (r : ℝ) (hr : 2≤r) (hx : r≤‖x‖) :
    let a := -x/(r:ℂ)-(r:ℂ)/x
    2*x^(3:ℕ)*a+x^(2:ℕ)*a^(2:ℕ)+x^(2:ℕ)-3≠0 := by
  have hr0 : 0<r := by linarith
  have hrC : (r:ℂ)≠0 := ofReal_ne_zero.mpr hr0.ne'
  have hx0 : x≠0 := by intro h; rw [h,norm_zero] at hx; linarith
  change 2*x^3*(-x/(r:ℂ)-(r:ℂ)/x)+x^2*(-x/(r:ℂ)-(r:ℂ)/x)^2+x^2-3≠0
  intro h
  have he : ((2*r-1:ℝ):ℂ)*x^4 =
      -(((2*r-3)*r^2:ℝ):ℂ)*x^2+(((r^2-3)*r^2:ℝ):ℂ) := by
    push_cast
    linear_combination (norm := (field_simp [hrC,hx0]; ring)) -(r:ℂ)^2*h
  have hA : 0≤2*r-1 := by linarith
  have hB : 0≤2*r-3 := by linarith
  have hC : 0≤r^2-3 := by nlinarith
  have hn := norm_add_le (-(((2*r-3)*r^2:ℝ):ℂ)*x^2) (((r^2-3)*r^2:ℝ):ℂ)
  rw [← he] at hn
  simp only [norm_mul,norm_neg,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hA,abs_of_nonneg hB,abs_of_nonneg hC,abs_of_nonneg hr0.le] at hn
  have hsq : r^2≤‖x‖^2 := (sq_le_sq₀ hr0.le (norm_nonneg _)).2 hx
  have hp : 0≤(‖x‖^2-r^2)*((2*r-1)*‖x‖^2+2*r^2) :=
    mul_nonneg (sub_nonneg.mpr hsq) (by positivity)
  nlinarith [sq_nonneg (r^2)]

#print axioms shifted_h_ne_zero
end QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars
end
end

/-! ## ThirtyFiveOriginalLargeShift -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars
open scoped Topology

theorem original_large_shift_four_zero {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (r : ℝ) (hr : 4≤r) (hα : 2≤s.re-(m:ℝ))
    (hrα : r≤(2:ℝ)^(s.re-(m:ℝ)))
    (ha : (Real.sqrt 2:ℂ)*f 2= -primeParameter 2 m s/(r:ℂ)-(r:ℂ)/primeParameter 2 m s) : v 24=0 ∧ v 42=0 ∧ v 84=0 ∧ v 192=0 := by
  have hs : (m:ℝ)≤s.re := by linarith
  have hx : r≤‖primeParameter 2 m s‖ := by
    rw [primeParameter_norm 2 m (by decide)]
    exact hrα
  have hP := shifted_p_ne_zero (primeParameter 2 m s) r (by linarith) hx
  have hE := shifted_first_row_ne_zero m s r hr hα hrα
  have hH := shifted_h_ne_zero (primeParameter 2 m s) r (by linarith) hx
  dsimp only at hE hH
  rw [← ha] at hP hE hH
  have h192 := original_all_sign_leading_exclusion hm hf ε hε hlaw BG G hG hGF s v hv hshift hs
  have h42 : v 42=0 := by
    have h := original_all_sign_row119 hm hf ε hε hlaw BG G hG hGF s v hv hshift
    have hn : 1+primeParameter 2 m s*((Real.sqrt 2:ℂ)*f 2)+(primeParameter 2 m s)^2≠0 := by
      convert hP using 1 <;> ring
    exact (mul_eq_zero.mp h).resolve_left hn
  have hu5 : -badFive f=1 ∨ -badFive f= -1 := by
    rcases badFive_sign hf.toEulerData with h|h <;> simp [h]
  have hu7 : -badSeven f=1 ∨ -badSeven f= -1 := by
    rcases badSeven_sign hf.toEulerData with h|h <;> simp [h]
  have hp := phaseRoot_sign m hε
  change ε*I^(2*m)=1 ∨ ε*I^(2*m)= -1 at hp
  have hsign : ε*I^(2*m)=(-badFive f)*(-badSeven f) ∨
      ε*I^(2*m)= -(-badFive f)*(-badSeven f) := by
    rcases hp with hp|hp <;> rcases hu5 with h5|h5 <;> rcases hu7 with h7|h7 <;>
      rw [hp,h5,h7] <;> norm_num
  rcases hsign with hpos|hneg
  · obtain ⟨_,h3,_,_,_,_,_,h45,_,_,_,_,_⟩ := original_positive_rows hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hpos (by simp) (by simp)
      BG G hG hGF s v hv hshift
    have h84 : v 84=0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hE
      simp only [h42,h192,mul_zero,zero_add,add_zero] at h45
      convert h45 using 1 <;> ring
    have h24 : v 24=0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hH
      simp only [h42,h84,h192,mul_zero,zero_add,add_zero] at h3
      convert h3 using 1 <;> ring
    exact ⟨h24,h42,h84,h192⟩
  · obtain ⟨_,_,_,_,h45,_,_,_,_,_,_⟩ := original_signed_negative_rows_b hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hneg (by simp) (by simp)
      BG G hG hGF s v hv hshift
    have h84 : v 84=0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hE
      simp only [h42,h192,mul_zero,zero_add,add_zero] at h45
      convert h45 using 1 <;> ring
    obtain ⟨_,h3,_,_,_⟩ := original_signed_negative_rows_a hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hneg (by simp) (by simp)
      BG G hG hGF s v hv hshift
    have h24 : v 24=0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hH
      simp only [h42,h84,h192,mul_zero,zero_add,add_zero] at h3
      convert h3 using 1 <;> ring
    exact ⟨h24,h42,h84,h192⟩

#print axioms original_large_shift_four_zero
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveNegativeLastPairReducedRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.unusedVariables false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate

theorem negative_last_pair_reduced_rows (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h0 : (1)*v 0 + (x^(2:ℕ)*z*w)*v 207 = 0)
    (h2 : (1)*v 0 + (z*w)*v 204 = 0)
    (h4 : ((x^(2:ℕ)*y^(2:ℕ)*w)/(z))*v 205 = 0)
    (h8 : (1)*v 0 = 0)
    (h12 : ((1)/(y^(2:ℕ)*z*w))*v 0 + (1)*v 2 = 0)
    (h16 : (1)*v 4 + ((x^(2:ℕ))/(y^(2:ℕ)*z*w))*v 105 = 0)
    (h18 : (1)*v 5 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h20 : ((1)/(z*w))*v 0 + (1)*v 6 = 0)
    (h22 : (1)*v 7 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 = 0)
    (h26 : (1)*v 10 = 0)
    (h28 : (1)*v 12 + ((x^(2:ℕ))/(z*w))*v 105 = 0)
    (h30 : (1)*v 14 + ((w)/(y^(2:ℕ)*z))*v 120 = 0)
    (h32 : (1)*v 15 + ((z)/(x^(2:ℕ)*w))*v 126 = 0)
    (h34 : (1)*v 18 + ((y^(2:ℕ))/(z*w))*v 140 = 0)
    (h36 : (1)*v 20 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 = 0)
    (h38 : (1)*v 21 + ((w)/(x^(2:ℕ)*z))*v 150 = 0)
    (h40 : (1)*v 28 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0)
    (h42 : (1)*v 30 + ((z)/(w))*v 168 = 0)
    (h44 : (1)*v 35 + ((z*w)/(x^(2:ℕ)*y^(2:ℕ)))*v 174 = 0)
    (h46 : (1)*v 36 + ((x^(2:ℕ)*y^(2:ℕ))/(z*w))*v 175 = 0)
    (h48 : ((w)/(z))*v 180 = 0)
    (h50 : (1)*v 45 + ((y^(2:ℕ)*z)/(x^(2:ℕ)*w))*v 182 = 0)
    (h52 : (1)*v 60 + ((x^(2:ℕ)*z)/(w))*v 189 = 0)
    (h54 : (1)*v 63 + ((y^(2:ℕ)*w)/(x^(2:ℕ)*z))*v 190 = 0)
    (h56 : (1)*v 70 = 0)
    (h58 : ((x^(2:ℕ)*w)/(z))*v 195 = 0)
    (h60 : (1)*v 90 + ((y^(2:ℕ)*z)/(w))*v 196 = 0)
    (h62 : (1)*v 105 + ((z*w)/(x^(2:ℕ)))*v 198 = 0)
    (h64 : (1)*v 126 + ((y^(2:ℕ)*w)/(z))*v 200 = 0)
    (h66 : (1)*v 140 + ((x^(2:ℕ)*z*w)/(y^(2:ℕ)))*v 201 = 0)
    (h68 : (1)*v 180 + ((x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203 = 0)
    (h128 : ((1)/(y^(2:ℕ)*z*w))*v 0 + (1)*v 208 = 0)
    (h150 : ((-1)*y^(2:ℕ))*v 8 + (1)*v 186 = 0)
    (h162 : (1)*v 202 = 0)
    (h246 : (1)*v 102 + ((-1)*y^(2:ℕ))*v 208 = 0)
    (h248 : ((-1)/(x^(2:ℕ)))*v 0 + (1)*v 105 = 0)
    (h252 : (1)*v 108 + ((-1)*x^(2:ℕ))*v 207 = 0)
    (h262 : (1)*v 107 + ((-1)/(x^(2:ℕ)))*v 202 = 0)
    (h266 : (1)*v 110 + ((-1)*x^(2:ℕ))*v 205 = 0)
    (h268 : (1)*v 72 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 199 = 0)
    (h270 : (1)*v 90 + ((-1)*y^(2:ℕ))*v 200 = 0)
    (h272 : (1)*v 96 + ((-1)*x^(2:ℕ))*v 201 = 0)
    (h274 : (1)*v 99 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 202 = 0)
    (h288 : (1)*v 109 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 = 0)
    (h292 : (1)*v 111 + ((-1)/(x^(2:ℕ)))*v 186 = 0)
    (h294 : (1)*v 112 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 189 = 0)
    (h296 : (1)*v 114 = 0)
    (h298 : (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0)
    (h300 : (1)*v 120 + ((-1)*x^(2:ℕ))*v 195 = 0)
    (h304 : (1)*v 144 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 197 = 0)
    (h312 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 93 = 0)
    (h316 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 21 + (1)*v 98 = 0)
    (h320 : ((-1)/(y^(2:ℕ)))*v 30 + (1)*v 100 = 0)
    (h326 : (1)*v 103 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0)
    (h342 : ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 11 + (1)*v 138 = 0)
    (h358 : (1)*v 168 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 203 = 0)
    (h360 : (1)*v 174 + (-1)*v 204 = 0)
    (h362 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 0 + (1)*v 175 = 0)
    (h364 : (1)*v 176 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 201 = 0)
    (h366 : (1)*v 177 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 202 = 0)
    (h368 : ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 37 + (1)*v 138 = 0)
    (h370 : ((-1)*y^(2:ℕ))*v 38 + (1)*v 156 = 0)
    (h374 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 40 + (1)*v 165 = 0)
    (h378 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170 = 0)
    (h380 : ((-1)/(x^(2:ℕ)))*v 48 + (1)*v 171 = 0)
    (h382 : ((-1)/(y^(2:ℕ)))*v 54 + (1)*v 172 = 0)
    (h384 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 173 = 0)
    (h394 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 27 + (1)*v 178 = 0)
    (h398 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 183 = 0)
    (h400 : ((-1)*x^(2:ℕ))*v 33 + (1)*v 186 = 0)
    (h2790 : (1)*v 70 + (1)*v 140 = 0)
    (h2796 : ((1)/(z*w))*v 0 + ((1)/(z*w))*v 70 + (1)*v 72 + (1)*v 142 = 0)
    (h2798 : ((1)/(z*w))*v 0 + (1)*v 68 + (1)*v 138 + ((1)/(z*w))*v 140 = 0)
    (h2800 : ((x^(2:ℕ))/(z*w))*v 35 + (1)*v 74 + ((x^(2:ℕ))/(z*w))*v 105 + (1)*v 144 = 0)
    (h2802 : (1)*v 66 + ((x^(2:ℕ))/(z*w))*v 105 + (1)*v 136 + ((x^(2:ℕ))/(z*w))*v 175 = 0)
    (h2806 : (1)*v 65 + ((z)/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + ((z)/(x^(2:ℕ)*w))*v 168 = 0)
    (h2808 : ((w)/(x^(2:ℕ)*z))*v 50 + (1)*v 77 + ((w)/(x^(2:ℕ)*z))*v 120 + (1)*v 147 = 0)
    (h2812 : ((z)/(w))*v 56 + (1)*v 80 + ((z)/(w))*v 126 + (1)*v 150 = 0)
    (h2814 : (1)*v 60 + (1)*v 130 + ((z)/(w))*v 154 = 0)
    (h2840 : (1)*v 126 + (1)*v 168 = 0)
    (h2844 : ((1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 0 + (1)*v 41 + (1)*v 83 + (1)*v 125 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 167 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h2846 : ((1)/(y^(2:ℕ)*w))*v 0 + (1)*v 44 + (1)*v 86 + ((1)/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + ((1)/(y^(2:ℕ)*w))*v 168 + (1)*v 170 = 0)
    (h2848 : ((1)/(y^(2:ℕ)*w))*v 0 + (1)*v 40 + (1)*v 82 + (1)*v 124 + (1)*v 166 + ((1)/(y^(2:ℕ)*w))*v 168 = 0)
    (h2850 : ((1)/(x^(2:ℕ)*w))*v 0 + (1)*v 45 + (1)*v 87 + (1)*v 129 + ((1)/(x^(2:ℕ)*w))*v 168 + (1)*v 171 = 0)
    (h2854 : ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 46 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 105 + (1)*v 130 + (1)*v 172 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0)
    (h2856 : ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 38 + (1)*v 80 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 105 + (1)*v 122 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 164 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0)
    (h2858 : ((1)/(w))*v 0 + (1)*v 48 + (1)*v 90 + ((1)/(w))*v 126 + (1)*v 132 + (1)*v 174 = 0)
    (h2860 : ((1)/(w))*v 0 + (1)*v 36 + (1)*v 78 + (1)*v 120 + ((1)/(w))*v 126 + (1)*v 162 + ((1)/(w))*v 168 = 0)
    (h2866 : ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 14 + (1)*v 51 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 93 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + (1)*v 177 = 0)
    (h2868 : (1)*v 33 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 70 + (1)*v 75 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 112 + (1)*v 117 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 196 = 0)
    (h2872 : (1)*v 30 + ((x^(2:ℕ))/(w))*v 63 + (1)*v 72 + ((x^(2:ℕ))/(w))*v 105 + (1)*v 114 + ((x^(2:ℕ))/(w))*v 147 + (1)*v 156 + ((x^(2:ℕ))/(w))*v 189 = 0)
    (h2874 : (1)*v 56 + ((w)/(y^(2:ℕ)))*v 66 + (1)*v 98 + ((w)/(y^(2:ℕ)))*v 108 + (1)*v 140 + ((w)/(y^(2:ℕ)))*v 150 + (1)*v 182 = 0)
    (h2876 : (1)*v 28 + ((w)/(y^(2:ℕ)))*v 60 + (1)*v 70 + ((w)/(y^(2:ℕ)))*v 102 + (1)*v 112 + ((w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((w)/(y^(2:ℕ)))*v 186 = 0)
    (h2932 : (1)*v 30 + (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + (1)*v 180 = 0)
    (h2936 : ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 0 + (1)*v 29 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 119 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + (1)*v 149 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 179 = 0)
    (h2950 : (1)*v 35 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 114 + (1)*v 125 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 204 = 0)
    (h3006 : (1)*v 21 + (1)*v 63 + (1)*v 147 + (1)*v 189 = 0)
    (h3032 : (1)*v 15 + (1)*v 45 + (1)*v 75 + (1)*v 135 + (1)*v 165 + (1)*v 195 = 0)
    (h3058 : (1)*v 14 + (1)*v 28 + (1)*v 56 + (1)*v 98 + (1)*v 112 + (1)*v 154 + (1)*v 182 + (1)*v 196 = 0)
    (h3060 : ((1)/(x^(2:ℕ)*w))*v 0 + (1)*v 15 + ((1)/(x^(2:ℕ)*w))*v 28 + (1)*v 29 + (1)*v 57 + ((1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((1)/(x^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0)
    (h3064 : ((1)/(w))*v 0 + ((1)/(w))*v 14 + (1)*v 16 + (1)*v 30 + (1)*v 58 + ((1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((1)/(w))*v 140 + (1)*v 156 + ((1)/(w))*v 168 + ((1)/(w))*v 182 + (1)*v 184 + (1)*v 198 = 0)
    (h3084 : (1)*v 10 + (1)*v 20 + (1)*v 40 + (1)*v 50 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + (1)*v 160 + (1)*v 170 + (1)*v 190 + (1)*v 200 = 0)
    (h3092 : ((1)/(z))*v 0 + (1)*v 8 + (1)*v 18 + ((1)/(z))*v 20 + ((1)/(z))*v 30 + (1)*v 38 + (1)*v 48 + ((1)/(z))*v 50 + ((1)/(z))*v 60 + (1)*v 78 + ((1)/(z))*v 90 + (1)*v 98 + (1)*v 108 + ((1)/(z))*v 110 + ((1)/(z))*v 120 + (1)*v 128 + ((1)/(z))*v 140 + (1)*v 158 + (1)*v 168 + ((1)/(z))*v 170 + ((1)/(z))*v 180 + (1)*v 188 + (1)*v 198 + ((1)/(z))*v 200 = 0)
    (h3206 : (1)*v 2 + (((-1)*a)/(x))*v 4 + ((1)/(x^(2:ℕ)))*v 8 + (1)*v 107 = 0)
    (h3210 : (1)*v 4 + (((-1)*a)/(x))*v 8 + ((1)/(x^(2:ℕ)))*v 16 + (1)*v 109 = 0)
    (h3212 : (1)*v 5 + (((-1)*a)/(x))*v 10 + ((1)/(x^(2:ℕ)))*v 20 + (1)*v 110 = 0)
    (h3216 : (1)*v 7 + (((-1)*a)/(x))*v 14 + ((1)/(x^(2:ℕ)))*v 28 + (1)*v 112 = 0)
    (h3218 : (1)*v 8 + (((-1)*a)/(x))*v 16 + ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 = 0)
    (h3226 : (1)*v 12 + ((1)/(x^(2:ℕ)))*v 48 + (1)*v 117 = 0)
    (h3230 : (1)*v 14 + (((-1)*a)/(x))*v 28 + ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 = 0)
    (h3232 : (1)*v 15 + (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 = 0)
    (h3242 : (1)*v 20 + (((-1)*a)/(x))*v 40 + ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 = 0)
    (h3250 : (((-1)*a)/(x))*v 48 + ((1)/(x^(2:ℕ)))*v 96 + (1)*v 129 = 0)
    (h3256 : (1)*v 27 + (((-1)*a)/(x))*v 54 + ((1)/(x^(2:ℕ)))*v 108 + (1)*v 132 = 0)
    (h3262 : (1)*v 30 + (((-1)*a)/(x))*v 60 + ((1)/(x^(2:ℕ)))*v 120 + (1)*v 135 = 0)
    (h3276 : (1)*v 37 + (((-1)*a)/(x))*v 74 + (1)*v 142 + ((1)/(x^(2:ℕ)))*v 148 = 0)
    (h3284 : (1)*v 41 + (((-1)*a)/(x))*v 82 + (1)*v 146 + ((1)/(x^(2:ℕ)))*v 164 = 0)
    (h3290 : (1)*v 44 + (((-1)*a)/(x))*v 88 + (1)*v 149 + ((1)/(x^(2:ℕ)))*v 176 = 0)
    (h3292 : (1)*v 45 + (((-1)*a)/(x))*v 90 + (1)*v 150 + ((1)/(x^(2:ℕ)))*v 180 = 0)
    (h3294 : (1)*v 46 + (((-1)*a)/(x))*v 92 + (1)*v 151 + ((1)/(x^(2:ℕ)))*v 184 = 0)
    (h3302 : (1)*v 50 + (((-1)*a)/(x))*v 100 + (1)*v 155 + ((1)/(x^(2:ℕ)))*v 200 = 0)
    (h3304 : (1)*v 51 + (((-1)*a)/(x))*v 102 + (1)*v 156 + ((1)/(x^(2:ℕ)))*v 204 = 0)
    (h3310 : ((1)/(x^(2:ℕ)))*v 6 + (1)*v 54 + (((-1)*a)/(x))*v 108 + (1)*v 159 = 0)
    (h3316 : ((1)/(x^(2:ℕ)))*v 18 + (1)*v 57 + (((-1)*a)/(x))*v 114 + (1)*v 162 = 0)
    (h3326 : ((1)/(x^(2:ℕ)))*v 38 + (1)*v 62 + (((-1)*a)/(x))*v 124 + (1)*v 167 = 0)
    (h3338 : ((1)/(x^(2:ℕ)))*v 62 + (1)*v 68 + (((-1)*a)/(x))*v 136 + (1)*v 173 = 0)
    (h3350 : (1)*v 74 + ((1)/(x^(2:ℕ)))*v 86 + (((-1)*a)/(x))*v 148 + (1)*v 179 = 0)
    (h3358 : (1)*v 78 + ((1)/(x^(2:ℕ)))*v 102 + (((-1)*a)/(x))*v 156 + (1)*v 183 = 0)
    (h3362 : (1)*v 80 + ((1)/(x^(2:ℕ)))*v 110 + (((-1)*a)/(x))*v 160 + (1)*v 185 = 0)
    (h3364 : (1)*v 81 + ((1)/(x^(2:ℕ)))*v 114 + (((-1)*a)/(x))*v 162 + (1)*v 186 = 0)
    (h3368 : (1)*v 83 + ((1)/(x^(2:ℕ)))*v 122 + (((-1)*a)/(x))*v 166 + (1)*v 188 = 0)
    (h3376 : (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 + (((-1)*a)/(x))*v 174 = 0)
    (h3380 : (1)*v 89 + ((1)/(x^(2:ℕ)))*v 146 + (((-1)*a)/(x))*v 178 + (1)*v 194 = 0)
    (h3386 : (1)*v 92 + ((1)/(x^(2:ℕ)))*v 158 + (((-1)*a)/(x))*v 184 + (1)*v 197 = 0)
    (h3392 : (1)*v 95 + ((1)/(x^(2:ℕ)))*v 170 + (((-1)*a)/(x))*v 190 + (1)*v 200 = 0)
    (h3424 : (1)*v 6 + (((-1)*b)/(y))*v 18 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0)
    (h3426 : (1)*v 7 + (((-1)*b)/(y))*v 21 + ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 = 0)
    (h3432 : (1)*v 10 + (((-1)*b)/(y))*v 30 + (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150 = 0)
    (h3434 : (1)*v 11 + (((-1)*b)/(y))*v 33 + (1)*v 81 + ((1)/(y^(2:ℕ)))*v 99 + (1)*v 151 = 0)
    (h3436 : (1)*v 12 + (((-1)*b)/(y))*v 36 + (1)*v 82 + ((1)/(y^(2:ℕ)))*v 108 + (1)*v 152 = 0)
    (h3444 : (1)*v 16 + (((-1)*b)/(y))*v 48 + (1)*v 86 + ((1)/(y^(2:ℕ)))*v 144 + (1)*v 156 = 0)
    (h3448 : (1)*v 18 + (((-1)*b)/(y))*v 54 + (1)*v 88 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 162 = 0)
    (h3478 : (1)*v 33 + ((1)/(y^(2:ℕ)))*v 87 + (((-1)*b)/(y))*v 99 + (1)*v 103 + (1)*v 173 = 0)
    (h3528 : (1)*v 58 + ((1)/(y^(2:ℕ)))*v 102 + (1)*v 128 + (((-1)*b)/(y))*v 174 + (1)*v 198 = 0)
    (h3530 : (1)*v 59 + ((1)/(y^(2:ℕ)))*v 111 + (1)*v 129 + (((-1)*b)/(y))*v 177 + (1)*v 199 = 0)
    : (1 + (-1)*x^(2:ℕ))*v 128 + (1 + x*a)*v 158 = 0 ∧
      ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 128 + (((-1)*a + (-1)*x^(3:ℕ))/(x^(3:ℕ)))*v 158 = 0 := by
  obtain ⟨h14224, h14400, h14401, h14407, h14408, h14409, h14410, h14412, h14413, h14427, h14458, h14460, h14469, h14716, h14797, h14845, h15228, h15230, h15383, h15414, h15415, h15419, h15451, h15452, h15538, h15539, h15542, h15543, h15545, h15754, h15755⟩ := negative_last_pair_reduced_rows_chunk0 x y z w a b hx hy hz hw u v h0 h2 h8 h12 h16 h20 h28 h62 h128 h246 h248 h252 h360 h362 h2796 h2798 h2800 h2802 h2844 h2846 h2848 h2850 h2854 h2856 h2858 h2860 h2872 h2876 h2936 h2950 h3060 h3064 h3092 h3206 h3210 h3304 h3310 h3358 h3424 h3528
  obtain ⟨h15850, h16188, h16220, h16221, h16373, h16405, h16408, h16523, h16528, h16619, h16754, h16789, h16841, h17077, h17190, h17207, h17210, h17252, h17258, h17260, h17275, h17276, h17331, h17332, h17348, h17378, h17418⟩ := negative_last_pair_reduced_rows_chunk1 x y z w a b hx hy hz hw u v h4 h18 h22 h26 h30 h32 h34 h44 h46 h266 h2866 h2874 h3032 h3058 h3084 h3212 h3216 h3226 h3230 h3232 h3256 h3376 h3426 h3432 h3436 h14224 h14412 h14413 h14458 h14460 h14469 h14716 h14797 h14845 h15228 h15419 h15451 h15452 h15538 h15539
  obtain ⟨h17443, h17445, h17446, h17510, h17512, h17534, h17623, h17632, h17647, h17677, h17745, h17806, h17807, h17808, h17810, h17811, h17920, h17973, h18001, h18032, h18167, h18175, h18177, h18223, h18239, h18240, h18241, h18247, h18331, h18349⟩ := negative_last_pair_reduced_rows_chunk2 x y z w a b hx hy hz hw u v h36 h38 h40 h42 h48 h50 h52 h54 h68 h294 h316 h320 h2932 h3006 h3242 h3262 h3292 h3316 h3392 h3448 h14427 h15230 h15383 h15542 h15543 h15545 h16188 h17077 h17190 h17207 h17210 h17258 h17260 h17275 h17276 h17332 h17348 h17378 h17418
  obtain ⟨h18418, h18420, h18424, h18541, h18570, h18795, h18796, h18871, h18872, h18988, h19073, h19074, h19131, h19132, h19214, h19264, h19281, h19283, h19327, h19337, h19372, h19374, h19378, h19380, h19401, h19402, h19408⟩ := negative_last_pair_reduced_rows_chunk3 x y z w a b hx hy hz hw u v h56 h58 h60 h64 h66 h150 h162 h262 h268 h270 h272 h274 h300 h358 h364 h366 h2790 h2868 h3218 h3302 h3362 h3530 h14400 h15754 h15755 h16373 h16841 h17331 h17510 h17623 h17632 h17745 h17920 h17973 h18001 h18175 h18331 h18349
  obtain ⟨h19450, h19456, h19601, h19667, h19669, h19704, h19754, h19792, h19870, h19872, h19904, h19905, h19948, h19961, h20005, h20007, h20013, h20015, h20043, h20085, h20086, h20087, h20088, h20186, h20191, h20254, h20268, h20270, h20271, h20274, h20275⟩ := negative_last_pair_reduced_rows_chunk4 x y z w a b hx hy hz hw u v h288 h292 h296 h298 h304 h312 h2806 h2808 h3250 h3364 h3386 h3434 h3478 h15850 h16528 h16754 h17252 h17443 h17534 h17647 h17806 h17807 h17808 h17811 h18032 h18167 h18177 h18223 h18241 h18424 h18541 h18871 h19073 h19131 h19327 h19337 h19374 h19378 h19380 h19401 h19402 h19408
  obtain ⟨h20420, h20441, h20505, h20507, h20508, h20511, h20513, h20514, h20526, h20527, h20563, h20564, h20616, h20617, h20618, h20620, h20622, h20628, h20629, h20812, h20847, h20863, h20902, h20924, h20939, h21018, h21044, h21082, h21092, h21102, h21104⟩ := negative_last_pair_reduced_rows_chunk5 x y z w a b hx hy hz hw u v h326 h342 h368 h370 h374 h378 h2840 h3276 h3290 h3326 h14407 h14408 h14409 h14410 h17512 h17677 h17810 h18240 h18795 h18872 h18988 h19132 h19264 h19281 h19456 h19667 h19669 h19754 h19870 h20007 h20013 h20015 h20043 h20085 h20087 h20088 h20186 h20254 h20268 h20270 h20275
  obtain ⟨h21119, h21151, h21190, h21269, h21295, h21306, h21457, h21462, h21487, h21539, h21541, h21543, h21550, h21551, h21687, h21689, h21714, h21726, h21746, h21783, h21785, h21787, h21792, h21794, h21799, h21894, h21941, h21966, h21979⟩ := negative_last_pair_reduced_rows_chunk6 x y z w a b hx hy hz hw u v h380 h382 h384 h394 h398 h400 h3284 h3338 h3350 h3380 h14401 h15414 h15415 h16221 h16523 h16619 h16789 h17445 h17446 h18239 h18418 h18796 h19074 h19214 h19601 h19704 h19792 h19904 h19905 h19948 h20271 h20420 h20441 h20511 h20563 h20564 h20812 h20847 h20863 h20902 h21018 h21082 h21104
  obtain ⟨h21993, h22050, h22077, h22089, h22093, h22094, h22096, h22097, h22141, h22151, h22212, h22214, h22220, h22224, h22355, h22358, h22360, h22362, h22369, h22393, h22442, h22443, h22445, h22540, h22542, h22544, h22558, h22560, h22581, h22583, h22585, h22624, h22625⟩ := negative_last_pair_reduced_rows_chunk7 x y z w a b hx hy hz hw u v h2812 h2814 h16408 h18247 h18420 h18570 h19372 h19450 h20005 h20274 h20507 h20508 h20513 h20514 h20526 h20527 h20616 h20617 h20618 h20620 h20622 h20628 h20629 h20924 h21044 h21092 h21102 h21119 h21190 h21295 h21457 h21487 h21687 h21714 h21726 h21746 h21783 h21894 h21941
  obtain ⟨h22649, h22652, h22674, h22678, h22679, h22735, h22842, h22843, h22849, h22851, h22852, h22876, h22887, h22925, h22926, h23015, h23017, h23038, h23039, h23043, h23069, h23070, h23205, h23229, h23239, h23274, h23318, h23319, h23320⟩ := negative_last_pair_reduced_rows_chunk8 x y z w a b hx hy hz hw u v h3444 h16220 h19872 h19961 h20086 h20505 h21151 h21269 h21462 h21785 h21966 h21993 h22089 h22094 h22141 h22151 h22212 h22220 h22224 h22355 h22358 h22360 h22362 h22393 h22442 h22443 h22445 h22540 h22542 h22544 h22558 h22560 h22581 h22583 h22585 h22624 h22625
  obtain ⟨h23344, h23638, h23672, h23687, h23741, h23778, h23798, h23821, h23823, h23843, h23844, h23845, h23846, h23859, h23883, h23922, h23930⟩ := negative_last_pair_reduced_rows_chunk9 x y z w a b hx hy hz hw u v h16405 h19283 h21306 h21543 h21794 h22214 h22649 h22674 h22678 h22679 h22735 h22842 h22843 h22849 h22852 h22876 h22887 h22925 h22926 h23017 h23038 h23039 h23043 h23069 h23070 h23229 h23239 h23274 h23318 h23320
  obtain ⟨h24153, h24296, h24300, h24333, h24484, h24796, h24811, h24871, h24872, h25003, h25023, h25047, h25093⟩ := negative_last_pair_reduced_rows_chunk10 x y z w a b hx hy hz hw u v h3294 h3368 h20191 h20939 h21539 h21541 h21550 h21689 h21787 h21792 h21799 h21979 h22050 h22077 h22093 h22096 h22097 h22369 h22652 h23015 h23205 h23319 h23638 h23672 h23687 h23741 h23778 h23821 h23823 h23859 h23883 h23922 h23930
  obtain ⟨h25551, h25760, h25840, h25883, h25949, h25972, h26103, h26110, h26147, h26149, h26150, h26212⟩ := negative_last_pair_reduced_rows_chunk11 x y z w a b hx hy hz hw u v h21551 h22851 h23344 h23798 h23843 h23844 h23845 h23846 h24153 h24296 h24300 h24333 h24484 h24796 h24811 h24871 h24872 h25003 h25023 h25047 h25093
  obtain ⟨h26698, h26835⟩ := negative_last_pair_reduced_rows_chunk12 x y z w a b hx hy hz hw u v h25551 h25760 h25840 h25883 h25949 h25972 h26103 h26110 h26147 h26149 h26150 h26212
  exact ⟨h26835, h26698⟩

#print axioms negative_last_pair_reduced_rows

end QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate
end
end

/-! ## ThirtyFiveLastPairNegativeSourcesBundleV4 -/
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

theorem actual_signed_negative_source_268 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 72 + ((-1)*(primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ))*v 199 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord029, source := 72, target := -11
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 72=(2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 72)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 72 0 s*v (gridIndex (-11))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 72 0 s=wordCoefficient m (-u5*u7) witnessWord029 72 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 72 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=(-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 72 (2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_268


theorem actual_signed_negative_source_304 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 144 + ((-1)*(primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ))*v 197 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord029, source := 144, target := -13
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 144=(2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 144)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 144 0 s*v (gridIndex (-13))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord029 144 0 s=wordCoefficient m (-u5*u7) witnessWord029 144 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord029 144 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord029)=(-1:ℂ)^(frickeCount witnessWord029)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord029 144 (2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_304


theorem actual_signed_negative_source_342 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    ((-1)*(primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ))*v 11 + (1)*v 138 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord030, source := 138, target := 11
    nonaffine := by norm_num [witnessWord030_matrix]
    denominator := by norm_num [integerDen,witnessWord030_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord030_matrix] }
  have hr : rationalRate witnessWord030 138=(2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord030_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 138)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord030 138 0 s*v (gridIndex (11))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord030 138 0 s=wordCoefficient m (-u5*u7) witnessWord030 138 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord030 138 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord030)=(-1:ℂ)^(frickeCount witnessWord030)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord030 138 (2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_342


theorem actual_signed_negative_source_364 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 176 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)))*v 201 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord041, source := 176, target := -9
    nonaffine := by norm_num [witnessWord041_matrix]
    denominator := by norm_num [integerDen,witnessWord041_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord041_matrix] }
  have hr : rationalRate witnessWord041 176=(2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord041_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 176)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord041 176 0 s*v (gridIndex (-9))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord041 176 0 s=wordCoefficient m (-u5*u7) witnessWord041 176 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord041 176 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord041)=(-1:ℂ)^(frickeCount witnessWord041)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord041 176 (2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_364


theorem actual_signed_negative_source_368 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    ((-1)*(primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ))*v 37 + (1)*v 138 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord042, source := 138, target := 37
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 138=(2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 138)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 138 0 s*v (gridIndex (37))=0 at hh
  have hc : rationalWordCoefficient m (-u5*u7) witnessWord042 138 0 s=wordCoefficient m (-u5*u7) witnessWord042 138 0 s :=
    (wordCoefficient_rational m (-u5*u7) witnessWord042 138 0 s).symm
  have hcompat : (-u5*u7)^(frickeCount witnessWord042)=(-1:ℂ)^(frickeCount witnessWord042)*u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_signed_laurent m (-u5*u7) u5 u7 witnessWord042 138 (2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_368


theorem actual_signed_negative_source_2796 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + ((1)/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 70 + (1)*v 72 + (1)*v 142 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=-u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (2) (0,0,-1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (2) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2796

theorem actual_signed_negative_source_2798 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 68 + (1)*v 138 + ((1)/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 140 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=-u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (-2) (0,0,-1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-2) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2798


theorem actual_signed_negative_source_2800 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 35 + (1)*v 74 + (((primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 105 + (1)*v 144 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((4:ℚ)/210)^2=(2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=-u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (4) (2,0,-1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (4) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2800


theorem actual_signed_negative_source_2802 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 66 + (((primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 105 + (1)*v 136 + (((primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 175 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-4:ℚ)/210)^2=(2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=-u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 3 (-4) (2,0,-1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-4) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2802


theorem actual_signed_negative_source_2844 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 41 + (1)*v 83 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 84 + (1)*v 125 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 126 + (1)*v 167 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)=-u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (-1) (-2,-2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-1) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2844


theorem actual_signed_negative_source_2846 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 42 + (1)*v 44 + (1)*v 86 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 126 + (1)*v 128 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 + (1)*v 170 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)=-u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (2) (0,-2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (2) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2846


theorem actual_signed_negative_source_2848 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 40 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 42 + (1)*v 82 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 84 + (1)*v 124 + (1)*v 166 + ((1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)=-u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (-2) (0,-2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-2) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2848

theorem actual_signed_negative_source_2854 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 21 + (1)*v 46 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 63 + (1)*v 88 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 105 + (1)*v 130 + (1)*v 172 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 189 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((4:ℚ)/210)^2=(2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)=-u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (4) (2,-2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (4) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2854


theorem actual_signed_negative_source_2856 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 21 + (1)*v 38 + (1)*v 80 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 105 + (1)*v 122 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 147 + (1)*v 164 + (((primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 189 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-4:ℚ)/210)^2=(2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)=-u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 5 (-4) (2,-2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-4) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2856


theorem actual_signed_negative_source_2936 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 0 + (1)*v 29 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 30 + (1)*v 59 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 60 + (1)*v 89 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 90 + (1)*v 119 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 120 + (1)*v 149 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 150 + (1)*v 179 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((-1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)=-u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 7 (-1) (-2,-2,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (-1) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_2936


theorem actual_signed_negative_source_3060 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 15 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 28 + (1)*v 29 + (1)*v 57 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 70 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 84 + (1)*v 99 + (1)*v 113 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 126 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 154 + (1)*v 155 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 + (1)*v 183 + ((1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 196 + (1)*v 197 = 0 := by
  have hroot : root 35 f 15=u5 := by simp [root_signed_15,h5,h7]
  have hr : (Nat.lcm 35 (15^2):ℚ)*((1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 15*ε*I^(2*m)=-u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 15 (1) (-2,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    15 (by decide) (by decide) (1) 28 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_3060


theorem actual_signed_negative_source_3064 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((u7*primeParameter 7 m s)))*v 0 + ((1)/((u7*primeParameter 7 m s)))*v 14 + (1)*v 16 + (1)*v 30 + ((1)/((u7*primeParameter 7 m s)))*v 42 + (1)*v 58 + ((1)/((u7*primeParameter 7 m s)))*v 84 + ((1)/((u7*primeParameter 7 m s)))*v 98 + (1)*v 100 + (1)*v 114 + ((1)/((u7*primeParameter 7 m s)))*v 140 + (1)*v 156 + ((1)/((u7*primeParameter 7 m s)))*v 168 + ((1)/((u7*primeParameter 7 m s)))*v 182 + (1)*v 184 + (1)*v 198 = 0 := by
  have hroot : root 35 f 15=u5 := by simp [root_signed_15,h5,h7]
  have hr : (Nat.lcm 35 (15^2):ℚ)*((2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 15*ε*I^(2*m)=-u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 15 (2) (0,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    15 (by decide) (by decide) (2) 28 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_3064


theorem actual_signed_negative_source_3092 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((1)/((u5*primeParameter 5 m s)))*v 0 + (1)*v 8 + (1)*v 18 + ((1)/((u5*primeParameter 5 m s)))*v 20 + ((1)/((u5*primeParameter 5 m s)))*v 30 + (1)*v 38 + (1)*v 48 + ((1)/((u5*primeParameter 5 m s)))*v 50 + ((1)/((u5*primeParameter 5 m s)))*v 60 + (1)*v 78 + ((1)/((u5*primeParameter 5 m s)))*v 90 + (1)*v 98 + (1)*v 108 + ((1)/((u5*primeParameter 5 m s)))*v 110 + ((1)/((u5*primeParameter 5 m s)))*v 120 + (1)*v 128 + ((1)/((u5*primeParameter 5 m s)))*v 140 + (1)*v 158 + (1)*v 168 + ((1)/((u5*primeParameter 5 m s)))*v 170 + ((1)/((u5*primeParameter 5 m s)))*v 180 + (1)*v 188 + (1)*v 198 + ((1)/((u5*primeParameter 5 m s)))*v 200 = 0 := by
  have hroot : root 35 f 21=u7 := by simp [root_signed_21,h5,h7]
  have hr : (Nat.lcm 35 (21^2):ℚ)*((-2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 21*ε*I^(2*m)=-u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_signed_laurent m f ε u5 u7 21 (-2) (0,0,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    21 (by decide) (by decide) (-2) 20 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_signed_negative_source_3092

theorem actual_negative_source_3218 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 8 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 16 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 32 + (1)*v 113 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 8
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3218


theorem actual_negative_source_3230 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 14 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 28 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 56 + (1)*v 119 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 14
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3230


theorem actual_negative_source_3276 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 37 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 74 + (1)*v 142 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 148 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 37
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3276


theorem actual_negative_source_3284 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 41 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 82 + (1)*v 146 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 164 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 41
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3284


theorem actual_negative_source_3290 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 44 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 88 + (1)*v 149 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 176 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 44
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3290


theorem actual_negative_source_3294 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 46 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 92 + (1)*v 151 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 184 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 46
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3294

theorem actual_negative_source_3316 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 18 + (1)*v 57 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 114 + (1)*v 162 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 57
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3316


theorem actual_negative_source_3326 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 38 + (1)*v 62 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 124 + (1)*v 167 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 62
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3326


theorem actual_negative_source_3338 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 62 + (1)*v 68 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 136 + (1)*v 173 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 68
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3338


theorem actual_negative_source_3350 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 74 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 86 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 148 + (1)*v 179 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 74
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3350


theorem actual_negative_source_3368 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 83 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 122 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 166 + (1)*v 188 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 83
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3368


theorem actual_negative_source_3380 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 89 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 146 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 178 + (1)*v 194 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 89
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3380

theorem actual_negative_source_3386 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 92 + ((1)/((primeParameter 2 m s)^(2:ℕ)))*v 158 + (((-1)*((Real.sqrt 2:ℂ)*f 2))/((primeParameter 2 m s)))*v 184 + (1)*v 197 = 0 := by
  have hp : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 2 (by decide) (by decide) 92
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 2 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3386


theorem actual_negative_source_3424 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 6 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 18 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 6
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3424


theorem actual_negative_source_3434 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 11 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 33 + (1)*v 81 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 99 + (1)*v 151 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 11
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3434


theorem actual_negative_source_3436 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 12 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 36 + (1)*v 82 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 108 + (1)*v 152 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 12
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3436


theorem actual_negative_source_3444 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 16 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 48 + (1)*v 86 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 144 + (1)*v 156 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 16
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3444


theorem actual_negative_source_3448 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 18 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 54 + (1)*v 88 + (1)*v 158 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 162 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 18
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3448

theorem actual_negative_source_3528 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 58 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 102 + (1)*v 128 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 174 + (1)*v 198 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 58
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3528


theorem actual_negative_source_3530 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    (1)*v 59 + ((1)/((primeParameter 3 m s)^(2:ℕ)))*v 111 + (1)*v 129 + (((-1)*((Real.sqrt 3:ℂ)*f 3))/((primeParameter 3 m s)))*v 177 + (1)*v 199 = 0 := by
  have hp : (3:ℂ)^((m:ℂ)-s)=(primeParameter 3 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 3 (by decide) (by decide) 59
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  linear_combination (norm := (field_simp [primeParameter_ne_zero 3 m (by decide) s]; ring)) hh

#print axioms actual_negative_source_3530

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveLastPairPositiveSourcesBundleV4 -/
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

theorem actual_positive_source_268 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 72 + ((-1)*(primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ))*v 199 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord029, source := 72, target := -11
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 72=(2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 72)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 72 0 s*v (gridIndex (-11))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord029 72 0 s=wordCoefficient m (u5*u7) witnessWord029 72 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord029 72 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord029)=u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord029 72 (2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_268


theorem actual_positive_source_292 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 111 + ((-1)/((primeParameter 2 m s)^(2:ℕ)))*v 186 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord029, source := 111, target := -24
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 111=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 111)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 111 0 s*v (gridIndex (-24))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord029 111 0 s=wordCoefficient m (u5*u7) witnessWord029 111 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord029 111 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord029)=u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord029 111 (-2,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_292


theorem actual_positive_source_304 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 144 + ((-1)*(primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ))*v 197 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord029, source := 144, target := -13
    nonaffine := by norm_num [witnessWord029_matrix]
    denominator := by norm_num [integerDen,witnessWord029_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord029_matrix] }
  have hr : rationalRate witnessWord029 144=(2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord029_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 144)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord029 144 0 s*v (gridIndex (-13))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord029 144 0 s=wordCoefficient m (u5*u7) witnessWord029 144 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord029 144 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord029)=u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord029_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord029 144 (2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord029_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_304


theorem actual_positive_source_342 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    ((-1)*(primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ))*v 11 + (1)*v 138 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord030, source := 138, target := 11
    nonaffine := by norm_num [witnessWord030_matrix]
    denominator := by norm_num [integerDen,witnessWord030_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord030_matrix] }
  have hr : rationalRate witnessWord030 138=(2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord030_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 138)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord030 138 0 s*v (gridIndex (11))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord030 138 0 s=wordCoefficient m (u5*u7) witnessWord030 138 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord030 138 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord030)=u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord030 138 (2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_342


theorem actual_positive_source_364 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 176 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)))*v 201 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord041, source := 176, target := -9
    nonaffine := by norm_num [witnessWord041_matrix]
    denominator := by norm_num [integerDen,witnessWord041_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord041_matrix] }
  have hr : rationalRate witnessWord041 176=(2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord041_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 176)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord041 176 0 s*v (gridIndex (-9))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord041 176 0 s=wordCoefficient m (u5*u7) witnessWord041 176 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord041 176 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord041)=u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord041_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord041 176 (2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord041_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_364


theorem actual_positive_source_368 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    ((-1)*(primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ))*v 37 + (1)*v 138 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord042, source := 138, target := 37
    nonaffine := by norm_num [witnessWord042_matrix]
    denominator := by norm_num [integerDen,witnessWord042_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord042_matrix] }
  have hr : rationalRate witnessWord042 138=(2:ℚ)^(2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord042_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 138)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord042 138 0 s*v (gridIndex (37))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord042 138 0 s=wordCoefficient m (u5*u7) witnessWord042 138 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord042 138 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord042)=u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord042 138 (2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_368

theorem actual_positive_source_2796 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + ((-1)/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 70 + (1)*v 72 + (1)*v 142 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 3 (2) (0,0,-1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (2) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2796


theorem actual_positive_source_2798 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 68 + (1)*v 138 + ((-1)/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 140 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 3 (-2) (0,0,-1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-2) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2798


theorem actual_positive_source_2800 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 35 + (1)*v 74 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 105 + (1)*v 144 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((4:ℚ)/210)^2=(2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 3 (4) (2,0,-1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (4) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2800


theorem actual_positive_source_2802 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 66 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 105 + (1)*v 136 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 175 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-4:ℚ)/210)^2=(2:ℚ)^(2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 3 (-4) (2,0,-1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-4) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2802


theorem actual_positive_source_2844 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 41 + (1)*v 83 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 84 + (1)*v 125 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 126 + (1)*v 167 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)=u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (-1) (-2,-2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-1) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2844


theorem actual_positive_source_2846 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 42 + (1)*v 44 + (1)*v 86 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 126 + (1)*v 128 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 + (1)*v 170 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)=u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (2) (0,-2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (2) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2846

theorem actual_positive_source_2848 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 40 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 42 + (1)*v 82 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 84 + (1)*v 124 + (1)*v 166 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)=u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (-2) (0,-2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-2) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2848


theorem actual_positive_source_2854 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 21 + (1)*v 46 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 63 + (1)*v 88 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 105 + (1)*v 130 + (1)*v 172 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 189 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((4:ℚ)/210)^2=(2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)=u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (4) (2,-2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (4) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2854


theorem actual_positive_source_2856 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 21 + (1)*v 38 + (1)*v 80 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 105 + (1)*v 122 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 147 + (1)*v 164 + (((-1)*(primeParameter 2 m s)^(2:ℕ))/((primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 189 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((-4:ℚ)/210)^2=(2:ℚ)^(2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)=u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (-4) (2,-2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (-4) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2856


theorem actual_positive_source_2936 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 0 + (1)*v 29 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 30 + (1)*v 59 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 60 + (1)*v 89 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 90 + (1)*v 119 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 120 + (1)*v 149 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 150 + (1)*v 179 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((-1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)=u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 7 (-1) (-2,-2,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (-1) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2936


theorem actual_positive_source_3060 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 15 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 28 + (1)*v 29 + (1)*v 57 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 70 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 84 + (1)*v 99 + (1)*v 113 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 126 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 154 + (1)*v 155 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 168 + (1)*v 183 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 196 + (1)*v 197 = 0 := by
  have hroot : root 35 f 15=u5 := by simp [root_signed_15,h5,h7]
  have hr : (Nat.lcm 35 (15^2):ℚ)*((1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 15*ε*I^(2*m)=u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 15 (1) (-2,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    15 (by decide) (by decide) (1) 28 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_3060


theorem actual_positive_source_3064 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((u7*primeParameter 7 m s)))*v 0 + ((-1)/((u7*primeParameter 7 m s)))*v 14 + (1)*v 16 + (1)*v 30 + ((-1)/((u7*primeParameter 7 m s)))*v 42 + (1)*v 58 + ((-1)/((u7*primeParameter 7 m s)))*v 84 + ((-1)/((u7*primeParameter 7 m s)))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/((u7*primeParameter 7 m s)))*v 140 + (1)*v 156 + ((-1)/((u7*primeParameter 7 m s)))*v 168 + ((-1)/((u7*primeParameter 7 m s)))*v 182 + (1)*v 184 + (1)*v 198 = 0 := by
  have hroot : root 35 f 15=u5 := by simp [root_signed_15,h5,h7]
  have hr : (Nat.lcm 35 (15^2):ℚ)*((2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 15*ε*I^(2*m)=u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 15 (2) (0,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    15 (by decide) (by decide) (2) 28 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_3064

theorem actual_positive_source_3092 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((u5*primeParameter 5 m s)))*v 0 + (1)*v 8 + (1)*v 18 + ((-1)/((u5*primeParameter 5 m s)))*v 20 + ((-1)/((u5*primeParameter 5 m s)))*v 30 + (1)*v 38 + (1)*v 48 + ((-1)/((u5*primeParameter 5 m s)))*v 50 + ((-1)/((u5*primeParameter 5 m s)))*v 60 + (1)*v 78 + ((-1)/((u5*primeParameter 5 m s)))*v 90 + (1)*v 98 + (1)*v 108 + ((-1)/((u5*primeParameter 5 m s)))*v 110 + ((-1)/((u5*primeParameter 5 m s)))*v 120 + (1)*v 128 + ((-1)/((u5*primeParameter 5 m s)))*v 140 + (1)*v 158 + (1)*v 168 + ((-1)/((u5*primeParameter 5 m s)))*v 170 + ((-1)/((u5*primeParameter 5 m s)))*v 180 + (1)*v 188 + (1)*v 198 + ((-1)/((u5*primeParameter 5 m s)))*v 200 = 0 := by
  have hroot : root 35 f 21=u7 := by simp [root_signed_21,h5,h7]
  have hr : (Nat.lcm 35 (21^2):ℚ)*((-2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 21*ε*I^(2*m)=u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 21 (-2) (0,0,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    21 (by decide) (by decide) (-2) 20 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_3092

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalNegativeLastPairReducedRows -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

def negativeLastPairReducedConclusion (x y z w a b : ℂ) (v : Fin 210 → ℂ) : Prop :=
(1 + (-1)*x^(2:ℕ))*v 128 + (1 + x*a)*v 158 = 0 ∧
      ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 128 + (((-1)*a + (-1)*x^(3:ℕ))/(x^(3:ℕ)))*v 158 = 0

theorem original_negative_last_pair_reduced_rows {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (h24 : v 24=0) (h42 : v 42=0) (h84 : v 84=0) (h192 : v 192=0) :
    negativeLastPairReducedConclusion (primeParameter 2 m s) (primeParameter 3 m s)
      (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate.negative_last_pair_reduced_rows
    (primeParameter 2 m s) (primeParameter 3 m s)
    (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3)
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) v v
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_34 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_54 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_62 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_268 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_292 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_298 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_304 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_320 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_342 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_364 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_368 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_370 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_374 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_382 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_394 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_398 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_2790 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2796 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2798 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2800 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2802 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_2840 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2844 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2846 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2848 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2854 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2856 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2858 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2860 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_2932 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2936 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3006 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3032 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3058 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_3060 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_3064 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3084 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_3092 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3206 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3210 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3212 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3216 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3218 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3226 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3230 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3232 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3242 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3250 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3256 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3262 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3276 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3284 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3290 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3292 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3294 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3302 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3304 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3310 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3316 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3326 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3338 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3350 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3358 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3362 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3364 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3368 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3376 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3380 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3386 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3392 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3424 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3426 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3432 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3434 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3436 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3444 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3448 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3478 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3528 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3530 hm hf BG G hG hGF s v hv)

#print axioms original_negative_last_pair_reduced_rows
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveLastPairReducedRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.unusedVariables false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate

theorem positive_last_pair_reduced_rows (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h0 : (1)*v 0 + ((-1)*x^(2:ℕ)*z*w)*v 207 = 0)
    (h2 : (1)*v 0 + ((-1)*z*w)*v 204 = 0)
    (h4 : (((-1)*x^(2:ℕ)*y^(2:ℕ)*w)/(z))*v 205 = 0)
    (h8 : (1)*v 0 = 0)
    (h12 : ((-1)/(y^(2:ℕ)*z*w))*v 0 + (1)*v 2 = 0)
    (h16 : (1)*v 4 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z*w))*v 105 = 0)
    (h18 : (1)*v 5 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h20 : ((-1)/(z*w))*v 0 + (1)*v 6 = 0)
    (h22 : (1)*v 7 + (((-1)*w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 = 0)
    (h26 : (1)*v 10 = 0)
    (h28 : (1)*v 12 + (((-1)*x^(2:ℕ))/(z*w))*v 105 = 0)
    (h30 : (1)*v 14 + (((-1)*w)/(y^(2:ℕ)*z))*v 120 = 0)
    (h32 : (1)*v 15 + (((-1)*z)/(x^(2:ℕ)*w))*v 126 = 0)
    (h34 : (1)*v 18 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0)
    (h36 : (1)*v 20 + (((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 = 0)
    (h38 : (1)*v 21 + (((-1)*w)/(x^(2:ℕ)*z))*v 150 = 0)
    (h40 : (1)*v 28 + (((-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0)
    (h42 : (1)*v 30 + (((-1)*z)/(w))*v 168 = 0)
    (h44 : (1)*v 35 + (((-1)*z*w)/(x^(2:ℕ)*y^(2:ℕ)))*v 174 = 0)
    (h46 : (1)*v 36 + (((-1)*x^(2:ℕ)*y^(2:ℕ))/(z*w))*v 175 = 0)
    (h48 : (((-1)*w)/(z))*v 180 = 0)
    (h50 : (1)*v 45 + (((-1)*y^(2:ℕ)*z)/(x^(2:ℕ)*w))*v 182 = 0)
    (h52 : (1)*v 60 + (((-1)*x^(2:ℕ)*z)/(w))*v 189 = 0)
    (h54 : (1)*v 63 + (((-1)*y^(2:ℕ)*w)/(x^(2:ℕ)*z))*v 190 = 0)
    (h56 : (1)*v 70 = 0)
    (h58 : (((-1)*x^(2:ℕ)*w)/(z))*v 195 = 0)
    (h60 : (1)*v 90 + (((-1)*y^(2:ℕ)*z)/(w))*v 196 = 0)
    (h62 : (1)*v 105 + (((-1)*z*w)/(x^(2:ℕ)))*v 198 = 0)
    (h64 : (1)*v 126 + (((-1)*y^(2:ℕ)*w)/(z))*v 200 = 0)
    (h66 : (1)*v 140 + (((-1)*x^(2:ℕ)*z*w)/(y^(2:ℕ)))*v 201 = 0)
    (h68 : (1)*v 180 + (((-1)*x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203 = 0)
    (h128 : ((-1)/(y^(2:ℕ)*z*w))*v 0 + (1)*v 208 = 0)
    (h150 : ((-1)*y^(2:ℕ))*v 8 + (1)*v 186 = 0)
    (h162 : (1)*v 202 = 0)
    (h246 : (1)*v 102 + ((-1)*y^(2:ℕ))*v 208 = 0)
    (h248 : ((-1)/(x^(2:ℕ)))*v 0 + (1)*v 105 = 0)
    (h252 : (1)*v 108 + ((-1)*x^(2:ℕ))*v 207 = 0)
    (h262 : (1)*v 107 + ((-1)/(x^(2:ℕ)))*v 202 = 0)
    (h266 : (1)*v 110 + ((-1)*x^(2:ℕ))*v 205 = 0)
    (h268 : (1)*v 72 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 199 = 0)
    (h270 : (1)*v 90 + ((-1)*y^(2:ℕ))*v 200 = 0)
    (h272 : (1)*v 96 + ((-1)*x^(2:ℕ))*v 201 = 0)
    (h274 : (1)*v 99 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 202 = 0)
    (h288 : (1)*v 109 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 = 0)
    (h292 : (1)*v 111 + ((-1)/(x^(2:ℕ)))*v 186 = 0)
    (h294 : (1)*v 112 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 189 = 0)
    (h296 : (1)*v 114 = 0)
    (h298 : (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0)
    (h300 : (1)*v 120 + ((-1)*x^(2:ℕ))*v 195 = 0)
    (h304 : (1)*v 144 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 197 = 0)
    (h312 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 93 = 0)
    (h316 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 21 + (1)*v 98 = 0)
    (h320 : ((-1)/(y^(2:ℕ)))*v 30 + (1)*v 100 = 0)
    (h326 : (1)*v 103 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0)
    (h342 : ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 11 + (1)*v 138 = 0)
    (h358 : (1)*v 168 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 203 = 0)
    (h360 : (1)*v 174 + (-1)*v 204 = 0)
    (h362 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 0 + (1)*v 175 = 0)
    (h364 : (1)*v 176 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 201 = 0)
    (h366 : (1)*v 177 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 202 = 0)
    (h368 : ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 37 + (1)*v 138 = 0)
    (h370 : ((-1)*y^(2:ℕ))*v 38 + (1)*v 156 = 0)
    (h374 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 40 + (1)*v 165 = 0)
    (h378 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170 = 0)
    (h380 : ((-1)/(x^(2:ℕ)))*v 48 + (1)*v 171 = 0)
    (h382 : ((-1)/(y^(2:ℕ)))*v 54 + (1)*v 172 = 0)
    (h384 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 173 = 0)
    (h394 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 27 + (1)*v 178 = 0)
    (h398 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 183 = 0)
    (h400 : ((-1)*x^(2:ℕ))*v 33 + (1)*v 186 = 0)
    (h2790 : (1)*v 70 + (1)*v 140 = 0)
    (h2796 : ((-1)/(z*w))*v 0 + ((-1)/(z*w))*v 70 + (1)*v 72 + (1)*v 142 = 0)
    (h2798 : ((-1)/(z*w))*v 0 + (1)*v 68 + (1)*v 138 + ((-1)/(z*w))*v 140 = 0)
    (h2800 : (((-1)*x^(2:ℕ))/(z*w))*v 35 + (1)*v 74 + (((-1)*x^(2:ℕ))/(z*w))*v 105 + (1)*v 144 = 0)
    (h2802 : (1)*v 66 + (((-1)*x^(2:ℕ))/(z*w))*v 105 + (1)*v 136 + (((-1)*x^(2:ℕ))/(z*w))*v 175 = 0)
    (h2806 : (1)*v 65 + (((-1)*z)/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + (((-1)*z)/(x^(2:ℕ)*w))*v 168 = 0)
    (h2808 : (((-1)*w)/(x^(2:ℕ)*z))*v 50 + (1)*v 77 + (((-1)*w)/(x^(2:ℕ)*z))*v 120 + (1)*v 147 = 0)
    (h2812 : (((-1)*z)/(w))*v 56 + (1)*v 80 + (((-1)*z)/(w))*v 126 + (1)*v 150 = 0)
    (h2814 : (1)*v 60 + (1)*v 130 + (((-1)*z)/(w))*v 154 = 0)
    (h2840 : (1)*v 126 + (1)*v 168 = 0)
    (h2844 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 0 + (1)*v 41 + (1)*v 83 + (1)*v 125 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 167 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h2846 : ((-1)/(y^(2:ℕ)*w))*v 0 + (1)*v 44 + (1)*v 86 + ((-1)/(y^(2:ℕ)*w))*v 126 + (1)*v 128 + ((-1)/(y^(2:ℕ)*w))*v 168 + (1)*v 170 = 0)
    (h2848 : ((-1)/(y^(2:ℕ)*w))*v 0 + (1)*v 40 + (1)*v 82 + (1)*v 124 + (1)*v 166 + ((-1)/(y^(2:ℕ)*w))*v 168 = 0)
    (h2850 : ((-1)/(x^(2:ℕ)*w))*v 0 + (1)*v 45 + (1)*v 87 + (1)*v 129 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 171 = 0)
    (h2854 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 46 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 105 + (1)*v 130 + (1)*v 172 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0)
    (h2856 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 38 + (1)*v 80 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 105 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 164 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0)
    (h2858 : ((-1)/(w))*v 0 + (1)*v 48 + (1)*v 90 + ((-1)/(w))*v 126 + (1)*v 132 + (1)*v 174 = 0)
    (h2860 : ((-1)/(w))*v 0 + (1)*v 36 + (1)*v 78 + (1)*v 120 + ((-1)/(w))*v 126 + (1)*v 162 + ((-1)/(w))*v 168 = 0)
    (h2866 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 14 + (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 93 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + (1)*v 177 = 0)
    (h2868 : (1)*v 33 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 70 + (1)*v 75 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 112 + (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 196 = 0)
    (h2872 : (1)*v 30 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (((-1)*x^(2:ℕ))/(w))*v 105 + (1)*v 114 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 + (((-1)*x^(2:ℕ))/(w))*v 189 = 0)
    (h2874 : (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + (1)*v 98 + (((-1)*w)/(y^(2:ℕ)))*v 108 + (1)*v 140 + (((-1)*w)/(y^(2:ℕ)))*v 150 + (1)*v 182 = 0)
    (h2876 : (1)*v 28 + (((-1)*w)/(y^(2:ℕ)))*v 60 + (1)*v 70 + (((-1)*w)/(y^(2:ℕ)))*v 102 + (1)*v 112 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0)
    (h2932 : (1)*v 30 + (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + (1)*v 180 = 0)
    (h2936 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 0 + (1)*v 29 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 179 = 0)
    (h2950 : (1)*v 35 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 114 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 204 = 0)
    (h3006 : (1)*v 21 + (1)*v 63 + (1)*v 147 + (1)*v 189 = 0)
    (h3032 : (1)*v 15 + (1)*v 45 + (1)*v 75 + (1)*v 135 + (1)*v 165 + (1)*v 195 = 0)
    (h3058 : (1)*v 14 + (1)*v 28 + (1)*v 56 + (1)*v 98 + (1)*v 112 + (1)*v 154 + (1)*v 182 + (1)*v 196 = 0)
    (h3060 : ((-1)/(x^(2:ℕ)*w))*v 0 + (1)*v 15 + ((-1)/(x^(2:ℕ)*w))*v 28 + (1)*v 29 + (1)*v 57 + ((-1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((-1)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((-1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0)
    (h3064 : ((-1)/(w))*v 0 + ((-1)/(w))*v 14 + (1)*v 16 + (1)*v 30 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1)/(w))*v 168 + ((-1)/(w))*v 182 + (1)*v 184 + (1)*v 198 = 0)
    (h3084 : (1)*v 10 + (1)*v 20 + (1)*v 40 + (1)*v 50 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + (1)*v 160 + (1)*v 170 + (1)*v 190 + (1)*v 200 = 0)
    (h3092 : ((-1)/(z))*v 0 + (1)*v 8 + (1)*v 18 + ((-1)/(z))*v 20 + ((-1)/(z))*v 30 + (1)*v 38 + (1)*v 48 + ((-1)/(z))*v 50 + ((-1)/(z))*v 60 + (1)*v 78 + ((-1)/(z))*v 90 + (1)*v 98 + (1)*v 108 + ((-1)/(z))*v 110 + ((-1)/(z))*v 120 + (1)*v 128 + ((-1)/(z))*v 140 + (1)*v 158 + (1)*v 168 + ((-1)/(z))*v 170 + ((-1)/(z))*v 180 + (1)*v 188 + (1)*v 198 + ((-1)/(z))*v 200 = 0)
    (h3206 : (1)*v 2 + (((-1)*a)/(x))*v 4 + ((1)/(x^(2:ℕ)))*v 8 + (1)*v 107 = 0)
    (h3210 : (1)*v 4 + (((-1)*a)/(x))*v 8 + ((1)/(x^(2:ℕ)))*v 16 + (1)*v 109 = 0)
    (h3212 : (1)*v 5 + (((-1)*a)/(x))*v 10 + ((1)/(x^(2:ℕ)))*v 20 + (1)*v 110 = 0)
    (h3216 : (1)*v 7 + (((-1)*a)/(x))*v 14 + ((1)/(x^(2:ℕ)))*v 28 + (1)*v 112 = 0)
    (h3218 : (1)*v 8 + (((-1)*a)/(x))*v 16 + ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 = 0)
    (h3226 : (1)*v 12 + ((1)/(x^(2:ℕ)))*v 48 + (1)*v 117 = 0)
    (h3230 : (1)*v 14 + (((-1)*a)/(x))*v 28 + ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 = 0)
    (h3232 : (1)*v 15 + (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 = 0)
    (h3242 : (1)*v 20 + (((-1)*a)/(x))*v 40 + ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 = 0)
    (h3250 : (((-1)*a)/(x))*v 48 + ((1)/(x^(2:ℕ)))*v 96 + (1)*v 129 = 0)
    (h3256 : (1)*v 27 + (((-1)*a)/(x))*v 54 + ((1)/(x^(2:ℕ)))*v 108 + (1)*v 132 = 0)
    (h3262 : (1)*v 30 + (((-1)*a)/(x))*v 60 + ((1)/(x^(2:ℕ)))*v 120 + (1)*v 135 = 0)
    (h3276 : (1)*v 37 + (((-1)*a)/(x))*v 74 + (1)*v 142 + ((1)/(x^(2:ℕ)))*v 148 = 0)
    (h3284 : (1)*v 41 + (((-1)*a)/(x))*v 82 + (1)*v 146 + ((1)/(x^(2:ℕ)))*v 164 = 0)
    (h3290 : (1)*v 44 + (((-1)*a)/(x))*v 88 + (1)*v 149 + ((1)/(x^(2:ℕ)))*v 176 = 0)
    (h3292 : (1)*v 45 + (((-1)*a)/(x))*v 90 + (1)*v 150 + ((1)/(x^(2:ℕ)))*v 180 = 0)
    (h3294 : (1)*v 46 + (((-1)*a)/(x))*v 92 + (1)*v 151 + ((1)/(x^(2:ℕ)))*v 184 = 0)
    (h3302 : (1)*v 50 + (((-1)*a)/(x))*v 100 + (1)*v 155 + ((1)/(x^(2:ℕ)))*v 200 = 0)
    (h3304 : (1)*v 51 + (((-1)*a)/(x))*v 102 + (1)*v 156 + ((1)/(x^(2:ℕ)))*v 204 = 0)
    (h3310 : ((1)/(x^(2:ℕ)))*v 6 + (1)*v 54 + (((-1)*a)/(x))*v 108 + (1)*v 159 = 0)
    (h3316 : ((1)/(x^(2:ℕ)))*v 18 + (1)*v 57 + (((-1)*a)/(x))*v 114 + (1)*v 162 = 0)
    (h3326 : ((1)/(x^(2:ℕ)))*v 38 + (1)*v 62 + (((-1)*a)/(x))*v 124 + (1)*v 167 = 0)
    (h3338 : ((1)/(x^(2:ℕ)))*v 62 + (1)*v 68 + (((-1)*a)/(x))*v 136 + (1)*v 173 = 0)
    (h3350 : (1)*v 74 + ((1)/(x^(2:ℕ)))*v 86 + (((-1)*a)/(x))*v 148 + (1)*v 179 = 0)
    (h3358 : (1)*v 78 + ((1)/(x^(2:ℕ)))*v 102 + (((-1)*a)/(x))*v 156 + (1)*v 183 = 0)
    (h3362 : (1)*v 80 + ((1)/(x^(2:ℕ)))*v 110 + (((-1)*a)/(x))*v 160 + (1)*v 185 = 0)
    (h3364 : (1)*v 81 + ((1)/(x^(2:ℕ)))*v 114 + (((-1)*a)/(x))*v 162 + (1)*v 186 = 0)
    (h3368 : (1)*v 83 + ((1)/(x^(2:ℕ)))*v 122 + (((-1)*a)/(x))*v 166 + (1)*v 188 = 0)
    (h3376 : (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 + (((-1)*a)/(x))*v 174 = 0)
    (h3380 : (1)*v 89 + ((1)/(x^(2:ℕ)))*v 146 + (((-1)*a)/(x))*v 178 + (1)*v 194 = 0)
    (h3386 : (1)*v 92 + ((1)/(x^(2:ℕ)))*v 158 + (((-1)*a)/(x))*v 184 + (1)*v 197 = 0)
    (h3392 : (1)*v 95 + ((1)/(x^(2:ℕ)))*v 170 + (((-1)*a)/(x))*v 190 + (1)*v 200 = 0)
    (h3424 : (1)*v 6 + (((-1)*b)/(y))*v 18 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0)
    (h3426 : (1)*v 7 + (((-1)*b)/(y))*v 21 + ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 = 0)
    (h3432 : (1)*v 10 + (((-1)*b)/(y))*v 30 + (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150 = 0)
    (h3434 : (1)*v 11 + (((-1)*b)/(y))*v 33 + (1)*v 81 + ((1)/(y^(2:ℕ)))*v 99 + (1)*v 151 = 0)
    (h3436 : (1)*v 12 + (((-1)*b)/(y))*v 36 + (1)*v 82 + ((1)/(y^(2:ℕ)))*v 108 + (1)*v 152 = 0)
    (h3444 : (1)*v 16 + (((-1)*b)/(y))*v 48 + (1)*v 86 + ((1)/(y^(2:ℕ)))*v 144 + (1)*v 156 = 0)
    (h3448 : (1)*v 18 + (((-1)*b)/(y))*v 54 + (1)*v 88 + (1)*v 158 + ((1)/(y^(2:ℕ)))*v 162 = 0)
    (h3478 : (1)*v 33 + ((1)/(y^(2:ℕ)))*v 87 + (((-1)*b)/(y))*v 99 + (1)*v 103 + (1)*v 173 = 0)
    (h3528 : (1)*v 58 + ((1)/(y^(2:ℕ)))*v 102 + (1)*v 128 + (((-1)*b)/(y))*v 174 + (1)*v 198 = 0)
    (h3530 : (1)*v 59 + ((1)/(y^(2:ℕ)))*v 111 + (1)*v 129 + (((-1)*b)/(y))*v 177 + (1)*v 199 = 0)
    : (1 + (-1)*x^(2:ℕ))*v 128 + (1 + x*a)*v 158 = 0 ∧
      ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 128 + (((-1)*a + (-1)*x^(3:ℕ))/(x^(3:ℕ)))*v 158 = 0 := by
  obtain ⟨h14144, h14320, h14321, h14327, h14328, h14329, h14330, h14332, h14333, h14347, h14378, h14380, h14389, h14626, h14707, h14755, h15128, h15130, h15281, h15308, h15309, h15313, h15345, h15346, h15432, h15433, h15436, h15437, h15439, h15648, h15649⟩ := positive_last_pair_reduced_rows_chunk0 x y z w a b hx hy hz hw u v h0 h2 h8 h12 h16 h20 h28 h62 h128 h246 h248 h252 h360 h362 h2796 h2798 h2800 h2802 h2844 h2846 h2848 h2850 h2854 h2856 h2858 h2860 h2872 h2876 h2936 h2950 h3060 h3064 h3092 h3206 h3210 h3304 h3310 h3358 h3424 h3528
  obtain ⟨h15740, h16074, h16102, h16103, h16255, h16283, h16286, h16399, h16404, h16495, h16630, h16661, h16711, h16947, h17060, h17077, h17080, h17122, h17128, h17130, h17145, h17146, h17201, h17202, h17218, h17248, h17288⟩ := positive_last_pair_reduced_rows_chunk1 x y z w a b hx hy hz hw u v h4 h18 h22 h26 h30 h32 h34 h44 h46 h266 h2866 h2874 h3032 h3058 h3084 h3212 h3216 h3226 h3230 h3232 h3256 h3376 h3426 h3432 h3436 h14144 h14332 h14333 h14378 h14380 h14389 h14626 h14707 h14755 h15128 h15313 h15345 h15346 h15432 h15433
  obtain ⟨h17309, h17311, h17312, h17376, h17378, h17400, h17489, h17498, h17513, h17543, h17611, h17666, h17667, h17668, h17670, h17671, h17779, h17832, h17860, h17885, h18019, h18027, h18029, h18075, h18091, h18092, h18093, h18099, h18183, h18201⟩ := positive_last_pair_reduced_rows_chunk2 x y z w a b hx hy hz hw u v h36 h38 h40 h42 h48 h50 h52 h54 h68 h294 h316 h320 h2932 h3006 h3242 h3262 h3292 h3316 h3392 h3448 h14347 h15130 h15281 h15436 h15437 h15439 h16074 h16947 h17060 h17077 h17080 h17128 h17130 h17145 h17146 h17202 h17218 h17248 h17288
  obtain ⟨h18270, h18272, h18276, h18393, h18422, h18647, h18648, h18723, h18724, h18840, h18925, h18926, h18983, h18984, h19066, h19116, h19133, h19135, h19179, h19189, h19224, h19226, h19230, h19232, h19253, h19254, h19260⟩ := positive_last_pair_reduced_rows_chunk3 x y z w a b hx hy hz hw u v h56 h58 h60 h64 h66 h150 h162 h262 h268 h270 h272 h274 h300 h358 h364 h366 h2790 h2868 h3218 h3302 h3362 h3530 h14320 h15648 h15649 h16255 h16711 h17201 h17376 h17489 h17498 h17611 h17779 h17832 h17860 h18027 h18183 h18201
  obtain ⟨h19300, h19306, h19449, h19514, h19516, h19551, h19601, h19639, h19717, h19719, h19749, h19750, h19792, h19805, h19849, h19851, h19857, h19859, h19887, h19927, h19928, h19929, h19930, h20028, h20033, h20096, h20110, h20112, h20113, h20116, h20117⟩ := positive_last_pair_reduced_rows_chunk4 x y z w a b hx hy hz hw u v h288 h292 h296 h298 h304 h312 h2806 h2808 h3250 h3364 h3386 h3434 h3478 h15740 h16404 h16630 h17122 h17309 h17400 h17513 h17666 h17667 h17668 h17671 h17885 h18019 h18029 h18075 h18093 h18276 h18393 h18723 h18925 h18983 h19179 h19189 h19226 h19230 h19232 h19253 h19254 h19260
  obtain ⟨h20262, h20283, h20347, h20349, h20350, h20353, h20355, h20356, h20368, h20369, h20405, h20406, h20454, h20455, h20456, h20458, h20460, h20466, h20467, h20650, h20685, h20701, h20740, h20762, h20777, h20856, h20882, h20920, h20930, h20940, h20942⟩ := positive_last_pair_reduced_rows_chunk5 x y z w a b hx hy hz hw u v h326 h342 h368 h370 h374 h378 h2840 h3276 h3290 h3326 h14327 h14328 h14329 h14330 h17378 h17543 h17670 h18092 h18647 h18724 h18840 h18984 h19116 h19133 h19306 h19514 h19516 h19601 h19717 h19851 h19857 h19859 h19887 h19927 h19929 h19930 h20028 h20096 h20110 h20112 h20117
  obtain ⟨h20957, h20989, h21028, h21107, h21133, h21144, h21295, h21300, h21325, h21371, h21373, h21375, h21382, h21383, h21517, h21519, h21544, h21556, h21576, h21603, h21605, h21607, h21612, h21614, h21619, h21709, h21756, h21781, h21794⟩ := positive_last_pair_reduced_rows_chunk6 x y z w a b hx hy hz hw u v h380 h382 h384 h394 h398 h400 h3284 h3338 h3350 h3380 h14321 h15308 h15309 h16103 h16399 h16495 h16661 h17311 h17312 h18091 h18270 h18648 h18926 h19066 h19449 h19551 h19639 h19749 h19750 h19792 h20113 h20262 h20283 h20353 h20405 h20406 h20650 h20685 h20701 h20740 h20856 h20920 h20942
  obtain ⟨h21808, h21865, h21892, h21904, h21908, h21909, h21911, h21912, h21956, h21966, h22023, h22025, h22031, h22035, h22165, h22168, h22170, h22172, h22179, h22203, h22246, h22247, h22249, h22343, h22345, h22347, h22361, h22363, h22384, h22386, h22388, h22427, h22428⟩ := positive_last_pair_reduced_rows_chunk7 x y z w a b hx hy hz hw u v h2812 h2814 h16286 h18099 h18272 h18422 h19224 h19300 h19849 h20116 h20349 h20350 h20355 h20356 h20368 h20369 h20454 h20455 h20456 h20458 h20460 h20466 h20467 h20762 h20882 h20930 h20940 h20957 h21028 h21133 h21295 h21325 h21517 h21544 h21556 h21576 h21603 h21709 h21756
  obtain ⟨h22450, h22453, h22474, h22478, h22479, h22539, h22645, h22646, h22652, h22654, h22655, h22679, h22690, h22728, h22729, h22818, h22820, h22841, h22842, h22846, h22872, h22873, h23006, h23029, h23039, h23074, h23118, h23119, h23120⟩ := positive_last_pair_reduced_rows_chunk8 x y z w a b hx hy hz hw u v h3444 h16102 h19719 h19805 h19928 h20347 h20989 h21107 h21300 h21605 h21781 h21808 h21904 h21909 h21956 h21966 h22023 h22031 h22035 h22165 h22168 h22170 h22172 h22203 h22246 h22247 h22249 h22343 h22345 h22347 h22361 h22363 h22384 h22386 h22388 h22427 h22428
  obtain ⟨h23144, h23436, h23469, h23484, h23538, h23575, h23595, h23618, h23620, h23640, h23641, h23642, h23643, h23656, h23682, h23722, h23730⟩ := positive_last_pair_reduced_rows_chunk9 x y z w a b hx hy hz hw u v h16283 h19135 h21144 h21375 h21614 h22025 h22450 h22474 h22478 h22479 h22539 h22645 h22646 h22652 h22655 h22679 h22690 h22728 h22729 h22820 h22841 h22842 h22846 h22872 h22873 h23029 h23039 h23074 h23118 h23120
  obtain ⟨h23953, h24093, h24097, h24128, h24278, h24590, h24605, h24663, h24664, h24796, h24816, h24840, h24886⟩ := positive_last_pair_reduced_rows_chunk10 x y z w a b hx hy hz hw u v h3294 h3368 h20033 h20777 h21371 h21373 h21382 h21519 h21607 h21612 h21619 h21794 h21865 h21892 h21908 h21911 h21912 h22179 h22453 h22818 h23006 h23119 h23436 h23469 h23484 h23538 h23575 h23618 h23620 h23656 h23682 h23722 h23730
  obtain ⟨h25353, h25560, h25642, h25685, h25751, h25774, h25906, h25913, h25954, h25956, h25957, h26021⟩ := positive_last_pair_reduced_rows_chunk11 x y z w a b hx hy hz hw u v h21383 h22654 h23144 h23595 h23640 h23641 h23642 h23643 h23953 h24093 h24097 h24128 h24278 h24590 h24605 h24663 h24664 h24796 h24816 h24840 h24886
  obtain ⟨h26507, h26644⟩ := positive_last_pair_reduced_rows_chunk12 x y z w a b hx hy hz hw u v h25353 h25560 h25642 h25685 h25751 h25774 h25906 h25913 h25954 h25956 h25957 h26021
  exact ⟨h26644, h26507⟩

#print axioms positive_last_pair_reduced_rows

end QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate
end
end

/-! ## ThirtyFiveOriginalPositiveLastPairReducedRows -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

def positiveLastPairReducedConclusion (x y z w a b : ℂ) (v : Fin 210 → ℂ) : Prop :=
(1 + (-1)*x^(2:ℕ))*v 128 + (1 + x*a)*v 158 = 0 ∧
      ((-1 + a^(2:ℕ))/(x^(2:ℕ)))*v 128 + (((-1)*a + (-1)*x^(3:ℕ))/(x^(3:ℕ)))*v 158 = 0

theorem original_positive_last_pair_reduced_rows {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (h24 : v 24=0) (h42 : v 42=0) (h84 : v 84=0) (h192 : v 192=0) :
    positiveLastPairReducedConclusion (primeParameter 2 m s) (primeParameter 3 m s)
      (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate.positive_last_pair_reduced_rows
    (primeParameter 2 m s) (primeParameter 3 m s)
    (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3)
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) v v
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_34 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_54 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_62 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_268 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_292 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_298 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_304 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_320 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_342 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_364 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_368 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_370 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_374 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_382 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_394 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_398 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_2790 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2796 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2798 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2800 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2802 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_2840 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2844 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2846 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2848 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2854 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2856 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2858 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2860 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_2932 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2936 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3006 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3032 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3058 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_3060 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_3064 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3084 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_3092 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3206 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3210 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3212 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3216 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3218 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3226 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3230 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3232 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3242 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3250 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3256 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3262 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3276 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3284 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3290 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3292 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3294 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3302 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3304 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3310 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3316 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3326 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3338 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3350 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3358 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3362 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3364 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3368 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3376 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3380 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3386 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3392 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3424 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3426 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3432 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3434 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3436 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3444 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3448 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3478 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3528 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3530 hm hf BG G hG hGF s v hv)

#print axioms original_positive_last_pair_reduced_rows
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveShiftedLastPair -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars
open Complex

/-- Exact final two-coordinate elimination for the shifted reduced system.
The two row equations are explicit inputs, to be supplied from Taylor rows. -/
theorem shifted_last_pair_zero (x a u v : ℂ) (r : ℝ) (hr : 2≤r)
    (hx : r≤‖x‖) (ha : a= -x/(r:ℂ)-(r:ℂ)/x)
    (h67 : (-x^2+1)*u+(x*a+1)*v=0)
    (h148 : ((a^2-1)/x^2)*u+((-x^3-a)/x^3)*v=0) : u=0 ∧ v=0 := by
  have hr0 : 0<r := by linarith
  have hx0 : x≠0 := by intro h; rw [h,norm_zero] at hx; linarith
  have hsq : r^2≤‖x‖^2 := (sq_le_sq₀ hr0.le (norm_nonneg _)).2 hx
  have hn : 2*r≤‖x‖^2 := by nlinarith
  have hd := shifted_determinant_ne_zero x r (by linarith) hn
  dsimp only at hd
  rw [← ha] at hd
  have h148' : x*(a^2-1)*u+(-x^3-a)*v=0 := by
    linear_combination (norm := (field_simp [hx0]; ring)) x^3*h148
  constructor
  · apply (mul_eq_zero.mp ?_).resolve_left hd
    linear_combination (-x^3-a)*h67-(x*a+1)*h148'
  · apply (mul_eq_zero.mp ?_).resolve_left hd
    linear_combination (-x^2+1)*h148'-x*(a^2-1)*h67

#print axioms shifted_last_pair_zero
end QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars
end
end

/-! ## ThirtyFiveOriginalLargeShiftSix -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars
open scoped Topology

theorem original_large_shift_six_zero {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (r : ℝ) (hr : 4≤r) (hα : 2≤s.re-(m:ℝ))
    (hrα : r≤(2:ℝ)^(s.re-(m:ℝ)))
    (ha : (Real.sqrt 2:ℂ)*f 2= -primeParameter 2 m s/(r:ℂ)-(r:ℂ)/primeParameter 2 m s) : v 24=0 ∧ v 42=0 ∧ v 84=0 ∧ v 128=0 ∧ v 158=0 ∧ v 192=0 := by
  obtain ⟨h24,h42,h84,h192⟩ := original_large_shift_four_zero hm hf ε hε hlaw
    BG G hG hGF s v hv hshift r hr hα hrα ha
  have hx : r≤‖primeParameter 2 m s‖ := by
    rw [primeParameter_norm 2 m (by decide)]
    exact hrα
  have finish : ∀ z w : ℂ,
      positiveLastPairReducedConclusion (primeParameter 2 m s) (primeParameter 3 m s)
        z w ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v → v 128=0 ∧ v 158=0 := by
    intro z w hrows
    obtain ⟨h67,h148⟩ := hrows
    apply shifted_last_pair_zero (primeParameter 2 m s) ((Real.sqrt 2:ℂ)*f 2)
      (v 128) (v 158) r (by linarith) hx ha
    · convert h67 using 1 <;> ring
    · convert h148 using 1 <;> ring
  have hu5 : -badFive f=1 ∨ -badFive f= -1 := by
    rcases badFive_sign hf.toEulerData with h|h <;> simp [h]
  have hu7 : -badSeven f=1 ∨ -badSeven f= -1 := by
    rcases badSeven_sign hf.toEulerData with h|h <;> simp [h]
  have hp := phaseRoot_sign m hε
  change ε*I^(2*m)=1 ∨ ε*I^(2*m)= -1 at hp
  have hsign : ε*I^(2*m)=(-badFive f)*(-badSeven f) ∨
      ε*I^(2*m)= -(-badFive f)*(-badSeven f) := by
    rcases hp with hp|hp <;> rcases hu5 with h5|h5 <;> rcases hu7 with h7|h7 <;>
      rw [hp,h5,h7] <;> norm_num
  have hpair : v 128=0 ∧ v 158=0 := by
    apply finish ((-badFive f)*primeParameter 5 m s) ((-badSeven f)*primeParameter 7 m s)
    rcases hsign with hpos|hneg
    · exact original_positive_last_pair_reduced_rows hm hf ε hε hlaw
        (-badFive f) (-badSeven f) hu5 hu7 hpos (by simp) (by simp)
        BG G hG hGF s v hv hshift h24 h42 h84 h192
    · exact original_negative_last_pair_reduced_rows hm hf ε hε hlaw
        (-badFive f) (-badSeven f) hu5 hu7 hneg (by simp) (by simp)
        BG G hG hGF s v hv hshift h24 h42 h84 h192
  exact ⟨h24,h42,h84,hpair.1,hpair.2,h192⟩

#print axioms original_large_shift_six_zero
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveNegativeGridRecoveryRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.unusedVariables false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate

theorem negative_grid_recovery_rows (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h0 : (1)*v 0 + (x^(2:ℕ)*z*w)*v 207 = 0)
    (h2 : (1)*v 0 + (z*w)*v 204 = 0)
    (h4 : ((x^(2:ℕ)*y^(2:ℕ)*w)/(z))*v 205 = 0)
    (h6 : (1)*v 105 + ((y^(2:ℕ)*z*w)/(x^(2:ℕ)))*v 206 = 0)
    (h8 : (1)*v 0 = 0)
    (h10 : ((1)/(x^(2:ℕ)*y^(2:ℕ)*z*w))*v 0 + (1)*v 1 = 0)
    (h12 : ((1)/(y^(2:ℕ)*z*w))*v 0 + (1)*v 2 = 0)
    (h14 : ((1)/(x^(2:ℕ)*z*w))*v 0 + (1)*v 3 = 0)
    (h16 : (1)*v 4 + ((x^(2:ℕ))/(y^(2:ℕ)*z*w))*v 105 = 0)
    (h18 : (1)*v 5 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h20 : ((1)/(z*w))*v 0 + (1)*v 6 = 0)
    (h22 : (1)*v 7 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 = 0)
    (h24 : (1)*v 9 + ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 70 = 0)
    (h26 : (1)*v 10 = 0)
    (h28 : (1)*v 12 + ((x^(2:ℕ))/(z*w))*v 105 = 0)
    (h30 : (1)*v 14 + ((w)/(y^(2:ℕ)*z))*v 120 = 0)
    (h32 : (1)*v 15 + ((z)/(x^(2:ℕ)*w))*v 126 = 0)
    (h34 : (1)*v 18 + ((y^(2:ℕ))/(z*w))*v 140 = 0)
    (h36 : (1)*v 20 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 = 0)
    (h38 : (1)*v 21 + ((w)/(x^(2:ℕ)*z))*v 150 = 0)
    (h40 : (1)*v 28 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0)
    (h42 : (1)*v 30 + ((z)/(w))*v 168 = 0)
    (h44 : (1)*v 35 + ((z*w)/(x^(2:ℕ)*y^(2:ℕ)))*v 174 = 0)
    (h46 : (1)*v 36 + ((x^(2:ℕ)*y^(2:ℕ))/(z*w))*v 175 = 0)
    (h48 : ((w)/(z))*v 180 = 0)
    (h50 : (1)*v 45 + ((y^(2:ℕ)*z)/(x^(2:ℕ)*w))*v 182 = 0)
    (h52 : (1)*v 60 + ((x^(2:ℕ)*z)/(w))*v 189 = 0)
    (h54 : (1)*v 63 + ((y^(2:ℕ)*w)/(x^(2:ℕ)*z))*v 190 = 0)
    (h56 : (1)*v 70 = 0)
    (h58 : ((x^(2:ℕ)*w)/(z))*v 195 = 0)
    (h60 : (1)*v 90 + ((y^(2:ℕ)*z)/(w))*v 196 = 0)
    (h62 : (1)*v 105 + ((z*w)/(x^(2:ℕ)))*v 198 = 0)
    (h64 : (1)*v 126 + ((y^(2:ℕ)*w)/(z))*v 200 = 0)
    (h66 : (1)*v 140 + ((x^(2:ℕ)*z*w)/(y^(2:ℕ)))*v 201 = 0)
    (h68 : (1)*v 180 + ((x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203 = 0)
    (h128 : ((1)/(y^(2:ℕ)*z*w))*v 0 + (1)*v 208 = 0)
    (h130 : ((1)/(x^(2:ℕ)*y^(2:ℕ)*z*w))*v 0 + (1)*v 209 = 0)
    (h150 : ((-1)*y^(2:ℕ))*v 8 + (1)*v 186 = 0)
    (h162 : (1)*v 202 = 0)
    (h246 : (1)*v 102 + ((-1)*y^(2:ℕ))*v 208 = 0)
    (h248 : ((-1)/(x^(2:ℕ)))*v 0 + (1)*v 105 = 0)
    (h250 : (1)*v 106 + ((-1)/(y^(2:ℕ)))*v 204 = 0)
    (h252 : (1)*v 108 + ((-1)*x^(2:ℕ))*v 207 = 0)
    (h256 : (1)*v 104 + (-1)*v 208 = 0)
    (h262 : (1)*v 107 + ((-1)/(x^(2:ℕ)))*v 202 = 0)
    (h266 : (1)*v 110 + ((-1)*x^(2:ℕ))*v 205 = 0)
    (h268 : (1)*v 72 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 199 = 0)
    (h270 : (1)*v 90 + ((-1)*y^(2:ℕ))*v 200 = 0)
    (h272 : (1)*v 96 + ((-1)*x^(2:ℕ))*v 201 = 0)
    (h274 : (1)*v 99 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 202 = 0)
    (h288 : (1)*v 109 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 = 0)
    (h292 : (1)*v 111 + ((-1)/(x^(2:ℕ)))*v 186 = 0)
    (h294 : (1)*v 112 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 189 = 0)
    (h296 : (1)*v 114 = 0)
    (h298 : (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0)
    (h300 : (1)*v 120 + ((-1)*x^(2:ℕ))*v 195 = 0)
    (h304 : (1)*v 144 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 197 = 0)
    (h306 : ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 13 + (1)*v 66 = 0)
    (h312 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 93 = 0)
    (h316 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 21 + (1)*v 98 = 0)
    (h320 : ((-1)/(y^(2:ℕ)))*v 30 + (1)*v 100 = 0)
    (h322 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 48 + (1)*v 101 = 0)
    (h326 : (1)*v 103 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0)
    (h342 : ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 11 + (1)*v 138 = 0)
    (h358 : (1)*v 168 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 203 = 0)
    (h360 : (1)*v 174 + (-1)*v 204 = 0)
    (h362 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 0 + (1)*v 175 = 0)
    (h364 : (1)*v 176 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 201 = 0)
    (h366 : (1)*v 177 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 202 = 0)
    (h368 : ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 37 + (1)*v 138 = 0)
    (h370 : ((-1)*y^(2:ℕ))*v 38 + (1)*v 156 = 0)
    (h372 : ((-1)*x^(2:ℕ))*v 39 + (1)*v 162 = 0)
    (h374 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 40 + (1)*v 165 = 0)
    (h378 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170 = 0)
    (h380 : ((-1)/(x^(2:ℕ)))*v 48 + (1)*v 171 = 0)
    (h382 : ((-1)/(y^(2:ℕ)))*v 54 + (1)*v 172 = 0)
    (h384 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 173 = 0)
    (h394 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 27 + (1)*v 178 = 0)
    (h398 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 183 = 0)
    (h400 : ((-1)*x^(2:ℕ))*v 33 + (1)*v 186 = 0)
    (h402 : ((-1)*y^(2:ℕ))*v 34 = 0)
    (h2790 : (1)*v 70 + (1)*v 140 = 0)
    (h2792 : ((1)/(x^(2:ℕ)*z*w))*v 0 + (1)*v 71 + ((1)/(x^(2:ℕ)*z*w))*v 140 + (1)*v 141 = 0)
    (h2794 : ((1)/(x^(2:ℕ)*z*w))*v 0 + (1)*v 69 + ((1)/(x^(2:ℕ)*z*w))*v 70 + (1)*v 139 = 0)
    (h2796 : ((1)/(z*w))*v 0 + ((1)/(z*w))*v 70 + (1)*v 72 + (1)*v 142 = 0)
    (h2798 : ((1)/(z*w))*v 0 + (1)*v 68 + (1)*v 138 + ((1)/(z*w))*v 140 = 0)
    (h2800 : ((x^(2:ℕ))/(z*w))*v 35 + (1)*v 74 + ((x^(2:ℕ))/(z*w))*v 105 + (1)*v 144 = 0)
    (h2802 : (1)*v 66 + ((x^(2:ℕ))/(z*w))*v 105 + (1)*v 136 + ((x^(2:ℕ))/(z*w))*v 175 = 0)
    (h2804 : (1)*v 75 + ((z)/(x^(2:ℕ)*w))*v 112 + (1)*v 145 = 0)
    (h2806 : (1)*v 65 + ((z)/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + ((z)/(x^(2:ℕ)*w))*v 168 = 0)
    (h2808 : ((w)/(x^(2:ℕ)*z))*v 50 + (1)*v 77 + ((w)/(x^(2:ℕ)*z))*v 120 + (1)*v 147 = 0)
    (h2810 : (1)*v 63 + ((w)/(x^(2:ℕ)*z))*v 90 + (1)*v 133 + ((w)/(x^(2:ℕ)*z))*v 160 = 0)
    (h2812 : ((z)/(w))*v 56 + (1)*v 80 + ((z)/(w))*v 126 + (1)*v 150 = 0)
    (h2814 : (1)*v 60 + (1)*v 130 + ((z)/(w))*v 154 = 0)
    (h2840 : (1)*v 126 + (1)*v 168 = 0)
    (h2842 : ((1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 0 + (1)*v 43 + (1)*v 85 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 127 + (1)*v 169 = 0)
    (h2844 : ((1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 0 + (1)*v 41 + (1)*v 83 + (1)*v 125 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 167 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h2846 : ((1)/(y^(2:ℕ)*w))*v 0 + (1)*v 44 + (1)*v 86 + ((1)/(y^(2:ℕ)*w))*v 126 + ((1)/(y^(2:ℕ)*w))*v 168 + (1)*v 170 = 0)
    (h2848 : ((1)/(y^(2:ℕ)*w))*v 0 + (1)*v 40 + (1)*v 82 + (1)*v 124 + (1)*v 166 + ((1)/(y^(2:ℕ)*w))*v 168 = 0)
    (h2850 : ((1)/(x^(2:ℕ)*w))*v 0 + (1)*v 45 + (1)*v 87 + (1)*v 129 + ((1)/(x^(2:ℕ)*w))*v 168 + (1)*v 171 = 0)
    (h2854 : ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 46 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 105 + (1)*v 130 + (1)*v 172 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0)
    (h2856 : ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 38 + (1)*v 80 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 105 + (1)*v 122 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 164 + ((x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0)
    (h2858 : ((1)/(w))*v 0 + (1)*v 48 + (1)*v 90 + ((1)/(w))*v 126 + (1)*v 132 + (1)*v 174 = 0)
    (h2860 : ((1)/(w))*v 0 + (1)*v 36 + (1)*v 78 + (1)*v 120 + ((1)/(w))*v 126 + (1)*v 162 + ((1)/(w))*v 168 = 0)
    (h2866 : ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 14 + (1)*v 51 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 93 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + (1)*v 177 = 0)
    (h2868 : (1)*v 33 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 70 + (1)*v 75 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 112 + (1)*v 117 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 + ((y^(2:ℕ))/(x^(2:ℕ)*w))*v 196 = 0)
    (h2872 : (1)*v 30 + ((x^(2:ℕ))/(w))*v 63 + (1)*v 72 + ((x^(2:ℕ))/(w))*v 105 + (1)*v 114 + ((x^(2:ℕ))/(w))*v 147 + (1)*v 156 + ((x^(2:ℕ))/(w))*v 189 = 0)
    (h2874 : (1)*v 56 + ((w)/(y^(2:ℕ)))*v 66 + (1)*v 98 + ((w)/(y^(2:ℕ)))*v 108 + (1)*v 140 + ((w)/(y^(2:ℕ)))*v 150 + (1)*v 182 = 0)
    (h2876 : (1)*v 28 + ((w)/(y^(2:ℕ)))*v 60 + (1)*v 70 + ((w)/(y^(2:ℕ)))*v 102 + (1)*v 112 + ((w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + ((w)/(y^(2:ℕ)))*v 186 = 0)
    (h2932 : (1)*v 30 + (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + (1)*v 180 = 0)
    (h2934 : ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 0 + (1)*v 31 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 61 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 91 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + (1)*v 121 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 151 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 180 + (1)*v 181 = 0)
    (h2936 : ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 0 + (1)*v 29 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + (1)*v 59 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 119 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + (1)*v 149 + ((1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 179 = 0)
    (h2938 : ((1)/(y^(2:ℕ)*z))*v 0 + ((1)/(y^(2:ℕ)*z))*v 30 + (1)*v 32 + ((1)/(y^(2:ℕ)*z))*v 60 + (1)*v 62 + ((1)/(y^(2:ℕ)*z))*v 90 + (1)*v 92 + (1)*v 122 + ((1)/(y^(2:ℕ)*z))*v 150 + (1)*v 152 + ((1)/(y^(2:ℕ)*z))*v 180 + (1)*v 182 = 0)
    (h2950 : (1)*v 35 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 114 + (1)*v 125 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 + ((z)/(x^(2:ℕ)*y^(2:ℕ)))*v 204 = 0)
    (h3006 : (1)*v 21 + (1)*v 63 + (1)*v 147 + (1)*v 189 = 0)
    (h3032 : (1)*v 15 + (1)*v 45 + (1)*v 75 + (1)*v 135 + (1)*v 165 + (1)*v 195 = 0)
    (h3034 : ((1)/(y^(2:ℕ)*z))*v 0 + (1)*v 16 + ((1)/(y^(2:ℕ)*z))*v 30 + (1)*v 46 + (1)*v 76 + ((1)/(y^(2:ℕ)*z))*v 90 + ((1)/(y^(2:ℕ)*z))*v 120 + (1)*v 136 + ((1)/(y^(2:ℕ)*z))*v 150 + (1)*v 166 + ((1)/(y^(2:ℕ)*z))*v 180 + (1)*v 196 = 0)
    (h3058 : (1)*v 14 + (1)*v 28 + (1)*v 56 + (1)*v 98 + (1)*v 112 + (1)*v 154 + (1)*v 182 + (1)*v 196 = 0)
    (h3060 : ((1)/(x^(2:ℕ)*w))*v 0 + (1)*v 15 + ((1)/(x^(2:ℕ)*w))*v 28 + (1)*v 29 + (1)*v 57 + ((1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((1)/(x^(2:ℕ)*w))*v 126 + ((1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0)
    (h3064 : ((1)/(w))*v 0 + ((1)/(w))*v 14 + (1)*v 16 + (1)*v 30 + (1)*v 58 + ((1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((1)/(w))*v 140 + (1)*v 156 + ((1)/(w))*v 168 + ((1)/(w))*v 182 + (1)*v 184 + (1)*v 198 = 0)
    (h3066 : ((1)/(w))*v 0 + (1)*v 12 + (1)*v 26 + ((1)/(w))*v 28 + (1)*v 54 + ((1)/(w))*v 70 + (1)*v 96 + (1)*v 110 + ((1)/(w))*v 112 + ((1)/(w))*v 126 + (1)*v 152 + ((1)/(w))*v 168 + (1)*v 180 + (1)*v 194 + ((1)/(w))*v 196 = 0)
    (h3084 : (1)*v 10 + (1)*v 20 + (1)*v 40 + (1)*v 50 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + (1)*v 160 + (1)*v 170 + (1)*v 190 + (1)*v 200 = 0)
    (h3110 : (1)*v 7 + (1)*v 49 + (1)*v 77 + (1)*v 91 + (1)*v 119 + (1)*v 133 + (1)*v 161 + (1)*v 203 = 0)
    (h3122 : ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 0 + (1)*v 7 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 12 + (1)*v 13 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 18 + (1)*v 19 + (1)*v 25 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 30 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 36 + (1)*v 37 + (1)*v 49 + (1)*v 55 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 60 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 66 + (1)*v 67 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 73 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 78 + (1)*v 79 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 96 + (1)*v 97 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 102 + (1)*v 103 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 108 + (1)*v 109 + (1)*v 115 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 120 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 126 + (1)*v 133 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 139 + (1)*v 145 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 150 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + (1)*v 157 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 + (1)*v 163 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 168 + (1)*v 175 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 180 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 + (1)*v 187 + (1)*v 193 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 198 + (1)*v 199 + (1)*v 205 = 0)
    (h3158 : (1)*v 5 + (1)*v 25 + (1)*v 55 + (1)*v 65 + (1)*v 85 + (1)*v 95 + (1)*v 115 + (1)*v 125 + (1)*v 145 + (1)*v 155 + (1)*v 185 + (1)*v 205 = 0)
    (h3206 : (1)*v 2 + (((-1)*a)/(x))*v 4 + ((1)/(x^(2:ℕ)))*v 8 + (1)*v 107 = 0)
    (h3210 : (1)*v 4 + (((-1)*a)/(x))*v 8 + ((1)/(x^(2:ℕ)))*v 16 + (1)*v 109 = 0)
    (h3212 : (1)*v 5 + (((-1)*a)/(x))*v 10 + ((1)/(x^(2:ℕ)))*v 20 + (1)*v 110 = 0)
    (h3216 : (1)*v 7 + (((-1)*a)/(x))*v 14 + ((1)/(x^(2:ℕ)))*v 28 + (1)*v 112 = 0)
    (h3218 : (1)*v 8 + (((-1)*a)/(x))*v 16 + ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 = 0)
    (h3222 : (1)*v 10 + (((-1)*a)/(x))*v 20 + ((1)/(x^(2:ℕ)))*v 40 + (1)*v 115 = 0)
    (h3224 : (1)*v 11 + (((-1)*a)/(x))*v 22 + ((1)/(x^(2:ℕ)))*v 44 + (1)*v 116 = 0)
    (h3226 : (1)*v 12 + ((1)/(x^(2:ℕ)))*v 48 + (1)*v 117 = 0)
    (h3228 : (1)*v 13 + (((-1)*a)/(x))*v 26 + ((1)/(x^(2:ℕ)))*v 52 + (1)*v 118 = 0)
    (h3230 : (1)*v 14 + (((-1)*a)/(x))*v 28 + ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 = 0)
    (h3232 : (1)*v 15 + (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 = 0)
    (h3234 : (1)*v 16 + (((-1)*a)/(x))*v 32 + ((1)/(x^(2:ℕ)))*v 64 + (1)*v 121 = 0)
    (h3236 : (1)*v 17 + (((-1)*a)/(x))*v 34 + ((1)/(x^(2:ℕ)))*v 68 + (1)*v 122 = 0)
    (h3238 : (1)*v 18 + (((-1)*a)/(x))*v 36 + ((1)/(x^(2:ℕ)))*v 72 + (1)*v 123 = 0)
    (h3240 : (1)*v 19 + (((-1)*a)/(x))*v 38 + ((1)/(x^(2:ℕ)))*v 76 + (1)*v 124 = 0)
    (h3242 : (1)*v 20 + (((-1)*a)/(x))*v 40 + ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 = 0)
    (h3246 : (1)*v 22 + (((-1)*a)/(x))*v 44 + ((1)/(x^(2:ℕ)))*v 88 + (1)*v 127 = 0)
    (h3248 : (1)*v 23 + (((-1)*a)/(x))*v 46 + ((1)/(x^(2:ℕ)))*v 92 = 0)
    (h3250 : (((-1)*a)/(x))*v 48 + ((1)/(x^(2:ℕ)))*v 96 + (1)*v 129 = 0)
    (h3252 : (1)*v 25 + (((-1)*a)/(x))*v 50 + ((1)/(x^(2:ℕ)))*v 100 + (1)*v 130 = 0)
    (h3254 : (1)*v 26 + (((-1)*a)/(x))*v 52 + ((1)/(x^(2:ℕ)))*v 104 + (1)*v 131 = 0)
    (h3256 : (1)*v 27 + (((-1)*a)/(x))*v 54 + ((1)/(x^(2:ℕ)))*v 108 + (1)*v 132 = 0)
    (h3262 : (1)*v 30 + (((-1)*a)/(x))*v 60 + ((1)/(x^(2:ℕ)))*v 120 + (1)*v 135 = 0)
    (h3264 : (1)*v 31 + (((-1)*a)/(x))*v 62 + ((1)/(x^(2:ℕ)))*v 124 + (1)*v 136 = 0)
    (h3274 : (1)*v 36 + (((-1)*a)/(x))*v 72 + (1)*v 141 + ((1)/(x^(2:ℕ)))*v 144 = 0)
    (h3276 : (1)*v 37 + (((-1)*a)/(x))*v 74 + (1)*v 142 + ((1)/(x^(2:ℕ)))*v 148 = 0)
    (h3278 : (1)*v 38 + (((-1)*a)/(x))*v 76 + (1)*v 143 + ((1)/(x^(2:ℕ)))*v 152 = 0)
    (h3284 : (1)*v 41 + (((-1)*a)/(x))*v 82 + (1)*v 146 + ((1)/(x^(2:ℕ)))*v 164 = 0)
    (h3288 : (1)*v 43 + (((-1)*a)/(x))*v 86 + (1)*v 148 + ((1)/(x^(2:ℕ)))*v 172 = 0)
    (h3290 : (1)*v 44 + (((-1)*a)/(x))*v 88 + (1)*v 149 + ((1)/(x^(2:ℕ)))*v 176 = 0)
    (h3292 : (1)*v 45 + (((-1)*a)/(x))*v 90 + (1)*v 150 + ((1)/(x^(2:ℕ)))*v 180 = 0)
    (h3294 : (1)*v 46 + (((-1)*a)/(x))*v 92 + (1)*v 151 + ((1)/(x^(2:ℕ)))*v 184 = 0)
    (h3296 : (1)*v 47 + (((-1)*a)/(x))*v 94 + (1)*v 152 + ((1)/(x^(2:ℕ)))*v 188 = 0)
    (h3298 : (1)*v 48 + (((-1)*a)/(x))*v 96 + (1)*v 153 = 0)
    (h3300 : (1)*v 49 + (((-1)*a)/(x))*v 98 + (1)*v 154 + ((1)/(x^(2:ℕ)))*v 196 = 0)
    (h3302 : (1)*v 50 + (((-1)*a)/(x))*v 100 + (1)*v 155 + ((1)/(x^(2:ℕ)))*v 200 = 0)
    (h3304 : (1)*v 51 + (((-1)*a)/(x))*v 102 + (1)*v 156 + ((1)/(x^(2:ℕ)))*v 204 = 0)
    (h3306 : (1)*v 52 + (((-1)*a)/(x))*v 104 + (1)*v 157 + ((1)/(x^(2:ℕ)))*v 208 = 0)
    (h3308 : ((1)/(x^(2:ℕ)))*v 2 + (1)*v 53 + (((-1)*a)/(x))*v 106 = 0)
    (h3310 : ((1)/(x^(2:ℕ)))*v 6 + (1)*v 54 + (((-1)*a)/(x))*v 108 + (1)*v 159 = 0)
    (h3312 : ((1)/(x^(2:ℕ)))*v 10 + (1)*v 55 + (((-1)*a)/(x))*v 110 + (1)*v 160 = 0)
    (h3314 : ((1)/(x^(2:ℕ)))*v 14 + (1)*v 56 + (((-1)*a)/(x))*v 112 + (1)*v 161 = 0)
    (h3316 : ((1)/(x^(2:ℕ)))*v 18 + (1)*v 57 + (((-1)*a)/(x))*v 114 + (1)*v 162 = 0)
    (h3318 : ((1)/(x^(2:ℕ)))*v 22 + (1)*v 58 + (((-1)*a)/(x))*v 116 + (1)*v 163 = 0)
    (h3324 : ((1)/(x^(2:ℕ)))*v 34 + (1)*v 61 + (((-1)*a)/(x))*v 122 + (1)*v 166 = 0)
    (h3326 : ((1)/(x^(2:ℕ)))*v 38 + (1)*v 62 + (((-1)*a)/(x))*v 124 + (1)*v 167 = 0)
    (h3330 : ((1)/(x^(2:ℕ)))*v 46 + (1)*v 64 + (1)*v 169 = 0)
    (h3336 : ((1)/(x^(2:ℕ)))*v 58 + (1)*v 67 + (((-1)*a)/(x))*v 134 + (1)*v 172 = 0)
    (h3338 : ((1)/(x^(2:ℕ)))*v 62 + (1)*v 68 + (((-1)*a)/(x))*v 136 + (1)*v 173 = 0)
    (h3340 : ((1)/(x^(2:ℕ)))*v 66 + (1)*v 69 + (((-1)*a)/(x))*v 138 + (1)*v 174 = 0)
    (h3350 : (1)*v 74 + ((1)/(x^(2:ℕ)))*v 86 + (((-1)*a)/(x))*v 148 + (1)*v 179 = 0)
    (h3354 : (1)*v 76 + ((1)/(x^(2:ℕ)))*v 94 + (((-1)*a)/(x))*v 152 + (1)*v 181 = 0)
    (h3358 : (1)*v 78 + ((1)/(x^(2:ℕ)))*v 102 + (((-1)*a)/(x))*v 156 + (1)*v 183 = 0)
    (h3360 : (1)*v 79 + ((1)/(x^(2:ℕ)))*v 106 + (1)*v 184 = 0)
    (h3362 : (1)*v 80 + ((1)/(x^(2:ℕ)))*v 110 + (((-1)*a)/(x))*v 160 + (1)*v 185 = 0)
    (h3364 : (1)*v 81 + ((1)/(x^(2:ℕ)))*v 114 + (((-1)*a)/(x))*v 162 + (1)*v 186 = 0)
    (h3368 : (1)*v 83 + ((1)/(x^(2:ℕ)))*v 122 + (((-1)*a)/(x))*v 166 + (1)*v 188 = 0)
    (h3374 : (1)*v 86 + ((1)/(x^(2:ℕ)))*v 134 + (((-1)*a)/(x))*v 172 + (1)*v 191 = 0)
    (h3376 : (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 + (((-1)*a)/(x))*v 174 = 0)
    (h3378 : (1)*v 88 + ((1)/(x^(2:ℕ)))*v 142 + (((-1)*a)/(x))*v 176 + (1)*v 193 = 0)
    (h3380 : (1)*v 89 + ((1)/(x^(2:ℕ)))*v 146 + (((-1)*a)/(x))*v 178 + (1)*v 194 = 0)
    (h3386 : (1)*v 92 + (((-1)*a)/(x))*v 184 + (1)*v 197 = 0)
    (h3390 : (1)*v 94 + ((1)/(x^(2:ℕ)))*v 166 + (((-1)*a)/(x))*v 188 + (1)*v 199 = 0)
    (h3392 : (1)*v 95 + ((1)/(x^(2:ℕ)))*v 170 + (((-1)*a)/(x))*v 190 + (1)*v 200 = 0)
    (h3396 : (1)*v 97 + ((1)/(x^(2:ℕ)))*v 178 + (((-1)*a)/(x))*v 194 + (1)*v 202 = 0)
    (h3424 : (1)*v 6 + (((-1)*b)/(y))*v 18 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0)
    (h3426 : (1)*v 7 + (((-1)*b)/(y))*v 21 + ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 = 0)
    (h3432 : (1)*v 10 + (((-1)*b)/(y))*v 30 + (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150 = 0)
    (h3436 : (1)*v 12 + (((-1)*b)/(y))*v 36 + (1)*v 82 + ((1)/(y^(2:ℕ)))*v 108 + (1)*v 152 = 0)
    (h3444 : (1)*v 16 + (((-1)*b)/(y))*v 48 + (1)*v 86 + ((1)/(y^(2:ℕ)))*v 144 + (1)*v 156 = 0)
    (h3446 : (1)*v 17 + (((-1)*b)/(y))*v 51 + (1)*v 87 + ((1)/(y^(2:ℕ)))*v 153 + (1)*v 157 = 0)
    (h3448 : (1)*v 18 + (((-1)*b)/(y))*v 54 + (1)*v 88 + ((1)/(y^(2:ℕ)))*v 162 = 0)
    (h3450 : (1)*v 19 + (((-1)*b)/(y))*v 57 + (1)*v 89 + (1)*v 159 + ((1)/(y^(2:ℕ)))*v 171 = 0)
    (h3478 : (1)*v 33 + ((1)/(y^(2:ℕ)))*v 87 + (((-1)*b)/(y))*v 99 + (1)*v 103 + (1)*v 173 = 0)
    (h3528 : (1)*v 58 + ((1)/(y^(2:ℕ)))*v 102 + (((-1)*b)/(y))*v 174 + (1)*v 198 = 0)
    (h3530 : (1)*v 59 + ((1)/(y^(2:ℕ)))*v 111 + (1)*v 129 + (((-1)*b)/(y))*v 177 + (1)*v 199 = 0)
    (h3540 : (1)*v 64 + (1)*v 134 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 204 = 0)
    (h3574 : (1)*v 11 + (1)*v 53 + ((1)/(z))*v 55 + (1)*v 95 + (1)*v 137 + (1)*v 179 = 0)
    (h3614 : (1)*v 31 + (1)*v 73 + (1)*v 115 + ((1)/(z))*v 155 + (1)*v 157 + (1)*v 199 = 0)
    : (1)*v 0 = 0 ∧
      (1)*v 207 = 0 ∧
      (1)*v 204 = 0 ∧
      (1)*v 1 = 0 ∧
      (1)*v 2 = 0 ∧
      (1)*v 3 = 0 ∧
      (1)*v 6 = 0 ∧
      (1)*v 208 = 0 ∧
      (1)*v 209 = 0 ∧
      (1)*v 102 = 0 ∧
      (1)*v 105 = 0 ∧
      (1)*v 206 = 0 ∧
      (1)*v 4 = 0 ∧
      (1)*v 12 = 0 ∧
      (1)*v 198 = 0 ∧
      (1)*v 106 = 0 ∧
      (1)*v 108 = 0 ∧
      (1)*v 104 = 0 ∧
      (1)*v 174 = 0 ∧
      (1)*v 35 = 0 ∧
      (1)*v 175 = 0 ∧
      (1)*v 36 = 0 ∧
      (1)*v 205 = 0 ∧
      (1)*v 5 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 ∧
      (1)*v 7 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 = 0 ∧
      (1)*v 9 + ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 70 = 0 ∧
      (1)*v 10 = 0 ∧
      (1)*v 14 + ((w)/(y^(2:ℕ)*z))*v 120 = 0 ∧
      (1)*v 15 + ((z)/(x^(2:ℕ)*w))*v 126 = 0 ∧
      (1)*v 18 + ((y^(2:ℕ))/(z*w))*v 140 = 0 ∧
      (1)*v 20 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 = 0 ∧
      (1)*v 21 + ((w)/(x^(2:ℕ)*z))*v 150 = 0 ∧
      (1)*v 28 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      (1)*v 30 + ((z)/(w))*v 168 = 0 ∧
      (1)*v 180 = 0 ∧
      ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 182 = 0 ∧
      ((w)/(x^(2:ℕ)*z))*v 60 + (1)*v 189 = 0 ∧
      ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 190 = 0 ∧
      (1)*v 70 = 0 ∧
      (1)*v 195 = 0 ∧
      ((w)/(y^(2:ℕ)*z))*v 90 + (1)*v 196 = 0 ∧
      ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 200 = 0 ∧
      ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 + (1)*v 201 = 0 ∧
      (1)*v 203 = 0 ∧
      (1)*v 8 + ((-1)/(y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 202 = 0 ∧
      (1)*v 107 = 0 ∧
      (1)*v 110 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 199 = 0 ∧
      (1)*v 90 + ((z)/(w))*v 126 = 0 ∧
      (1)*v 96 + ((y^(2:ℕ))/(z*w))*v 140 = 0 ∧
      (1)*v 99 = 0 ∧
      (1)*v 109 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 111 + ((-1)/(x^(2:ℕ)))*v 186 = 0 ∧
      ((w)/(y^(2:ℕ)*z))*v 60 + (1)*v 112 = 0 ∧
      (1)*v 114 = 0 ∧
      (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 ∧
      (1)*v 120 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 197 = 0 ∧
      (1)*v 13 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 66 = 0 ∧
      (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 93 = 0 ∧
      (1)*v 98 + ((w)/(y^(2:ℕ)*z))*v 150 = 0 ∧
      (1)*v 100 + ((z)/(y^(2:ℕ)*w))*v 168 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 48 + (1)*v 101 = 0 ∧
      (1)*v 103 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 11 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 168 = 0 ∧
      ((1)/(z*w))*v 140 + (1)*v 176 = 0 ∧
      (1)*v 177 = 0 ∧
      (1)*v 37 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 38 + ((-1)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 39 + ((-1)/(x^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 40 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 165 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 48 + (1)*v 171 = 0 ∧
      ((-1)/(y^(2:ℕ)))*v 54 + (1)*v 172 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 173 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 27 + (1)*v 178 = 0 ∧
      (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 183 = 0 ∧
      (1)*v 33 + ((-1)/(x^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 34 = 0 ∧
      (1)*v 140 = 0 ∧
      (1)*v 74 + (1)*v 144 = 0 ∧
      (1)*v 66 + (1)*v 136 = 0 ∧
      (1)*v 186 = 0 ∧
      (1)*v 51 + (1)*v 156 = 0 ∧
      (1)*v 52 + (1)*v 157 = 0 ∧
      (1)*v 53 = 0 ∧
      (1)*v 54 + (1)*v 159 = 0 ∧
      (1)*v 82 + (1)*v 152 = 0 ∧
      (1)*v 58 = 0 ∧
      (1)*v 71 + (1)*v 141 = 0 ∧
      (1)*v 69 + (1)*v 139 = 0 ∧
      (1)*v 72 + (1)*v 142 = 0 ∧
      (1)*v 68 + (1)*v 138 = 0 ∧
      (1)*v 126 = 0 ∧
      (1)*v 60 + (1)*v 150 = 0 ∧
      (1)*v 63 + (1)*v 147 = 0 ∧
      (1)*v 16 + ((1)/(y^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 63 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 48 + (1)*v 194 = 0 ∧
      (1)*v 150 = 0 ∧
      (1)*v 165 = 0 ∧
      (1)*v 115 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 72 + (1)*v 123 = 0 ∧
      (1)*v 26 + (((-1)*a)/(x))*v 52 + (1)*v 131 = 0 ∧
      (1)*v 27 + (((-1)*a)/(x))*v 54 + (1)*v 132 = 0 ∧
      (1)*v 135 = 0 ∧
      (1)*v 65 = 0 ∧
      (((-1)*a)/(x))*v 72 + (1)*v 141 + ((1)/(x^(2:ℕ)))*v 144 = 0 ∧
      (1)*v 45 = 0 ∧
      (1)*v 75 = 0 ∧
      (1)*v 145 = 0 ∧
      (1)*v 56 + (1)*v 154 = 0 ∧
      (1)*v 48 + (1)*v 153 = 0 ∧
      (1)*v 57 + (1)*v 162 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 66 + (1)*v 69 + (((-1)*a)/(x))*v 138 = 0 ∧
      (1)*v 32 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 78 + (((-1)*x*a)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 79 + (1)*v 184 = 0 ∧
      (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 95 = 0 ∧
      (1)*v 77 = 0 ∧
      (1)*v 50 = 0 ∧
      (1)*v 155 = 0 ∧
      (1)*v 80 = 0 ∧
      (1)*v 154 = 0 ∧
      (1)*v 130 = 0 ∧
      (1)*v 160 = 0 ∧
      (1)*v 133 = 0 ∧
      (1)*v 119 = 0 ∧
      (1)*v 125 = 0 ∧
      (1)*v 25 = 0 ∧
      (1)*v 49 = 0 ∧
      (1)*v 55 = 0 ∧
      (1)*v 161 = 0 ∧
      (1)*v 91 = 0 ∧
      (1)*v 185 = 0 ∧
      (1)*v 85 = 0 ∧
      (1)*v 48 + (1)*v 132 = 0 ∧
      (1)*v 78 + (1)*v 162 = 0 ∧
      (((-1)*a)/(x))*v 22 + ((1)/(x^(2:ℕ)))*v 44 + (1)*v 116 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 ∧
      (((-1)*a)/(x))*v 26 + ((1)/(x^(2:ℕ)))*v 52 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 66 + (1)*v 118 = 0 ∧
      (1)*v 17 + (1)*v 122 + ((-1)/(x^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 19 + ((1)/(x^(2:ℕ)))*v 76 + (1)*v 124 + (((-1)*a)/(x*y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 22 + (((-1)*a)/(x))*v 44 + ((1)/(x^(2:ℕ)))*v 88 + (1)*v 127 = 0 ∧
      (1)*v 23 + (((-1)*a)/(x))*v 46 + ((1)/(x^(2:ℕ)))*v 92 = 0 ∧
      (((-1)*a)/(x))*v 48 + (1)*v 129 = 0 ∧
      (1)*v 31 + (((-1)*a)/(x))*v 62 + (-1)*v 66 + ((1)/(x^(2:ℕ)))*v 124 = 0 ∧
      (((-1)*a)/(x))*v 76 + (1)*v 143 + ((1)/(x^(2:ℕ)))*v 152 + ((1)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 41 + (1)*v 146 + ((a)/(x))*v 152 + ((1)/(x^(2:ℕ)))*v 164 = 0 ∧
      (1)*v 43 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (((-1)*a)/(x))*v 86 + (1)*v 148 = 0 ∧
      (1)*v 44 + (((-1)*a)/(x))*v 88 + (1)*v 149 = 0 ∧
      (1)*v 46 + (((-1)*a)/(x))*v 92 + (1)*v 151 + ((1)/(x^(2:ℕ)))*v 184 = 0 ∧
      (1)*v 47 + (((-1)*a)/(x))*v 94 + (1)*v 152 + ((1)/(x^(2:ℕ)))*v 188 = 0 ∧
      (1)*v 61 + (((-1)*a)/(x))*v 122 + (1)*v 166 = 0 ∧
      (1)*v 62 + (((-1)*a)/(x))*v 124 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + (1)*v 167 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 46 + (1)*v 64 + (1)*v 169 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 54 + (1)*v 67 + (((-1)*a)/(x))*v 134 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 86 + (-1)*v 144 + (((-1)*a)/(x))*v 148 + (1)*v 179 = 0 ∧
      (1)*v 76 + ((1)/(x^(2:ℕ)))*v 94 + (((-1)*a)/(x))*v 152 + (1)*v 181 = 0 ∧
      (1)*v 81 + (((-1)*a)/(x))*v 162 = 0 ∧
      (1)*v 83 + ((1)/(x^(2:ℕ)))*v 122 + (((-1)*a)/(x))*v 166 + (1)*v 188 = 0 ∧
      (((-1)*a)/(x*y^(2:ℕ)))*v 54 + (1)*v 86 + ((1)/(x^(2:ℕ)))*v 134 + (1)*v 191 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 72 + (1)*v 88 + (1)*v 193 = 0 ∧
      (1)*v 92 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (((-1)*a)/(x))*v 184 = 0 ∧
      ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 94 + ((1)/(x^(2:ℕ)))*v 166 + (((-1)*a)/(x))*v 188 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0 ∧
      (-1)*v 72 + (1)*v 138 = 0 ∧
      ((1 + (-1)*x^(2:ℕ)*y^(2:ℕ))/(y^(2:ℕ)))*v 72 + (x*a)*v 144 + (1)*v 148 = 0 ∧
      (1)*v 64 + (1)*v 134 + ((1)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 44 + (1)*v 86 = 0 ∧
      (1)*v 124 + (-1)*v 152 + (1)*v 166 = 0 ∧
      (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 88 = 0 ∧
      (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 ∧
      (1)*v 72 + (1)*v 156 = 0 ∧
      (1)*v 66 = 0 ∧
      (1)*v 144 = 0 ∧
      (1)*v 54 = 0 ∧
      (1)*v 48 = 0 ∧
      (1)*v 72 = 0 ∧
      (1)*v 162 = 0 ∧
      (1)*v 113 = 0 ∧
      (1)*v 29 = 0 ∧
      (1)*v 62 = 0 ∧
      (1)*v 97 = 0 ∧
      (1)*v 59 = 0 ∧
      (1)*v 22 + (-1)*v 134 = 0 ∧
      (-1)*v 76 + (1)*v 188 = 0 ∧
      (1)*v 184 = 0 ∧
      (1)*v 26 + (1)*v 152 = 0 ∧
      (1)*v 121 + ((-1)/(x^(2:ℕ)))*v 134 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 76 + (1)*v 89 = 0 ∧
      (1)*v 44 = 0 ∧
      (1)*v 52 + (1)*v 122 = 0 ∧
      (1)*v 46 = 0 ∧
      (-1)*v 152 + (1)*v 166 = 0 ∧
      (1)*v 137 = 0 ∧
      (-1)*v 52 + (1)*v 73 = 0 ∧
      (1)*v 76 = 0 ∧
      (1)*v 152 = 0 ∧
      (1)*v 52 = 0 ∧
      (1)*v 134 = 0 ∧
      (1)*v 163 = 0 ∧
      (1)*v 187 = 0 := by
  obtain ⟨h14206, h14217, h14219, h14224, h14398, h14399, h14400, h14401, h14406, h14407, h14408, h14409, h14410, h14412, h14413, h14426, h14427, h14428, h14450, h14458, h14460, h14461, h14478, h14708, h14716, h14783, h14793, h14797, h14845, h14874, h14878, h14938, h14957, h14997, h14998, h15018, h15101, h15228, h15230, h15288, h15293, h15294, h15317⟩ := negative_grid_recovery_rows_chunk0 x y z w a b hx hy hz hw u v h0 h2 h8 h10 h12 h14 h20 h128 h130 h246 h248 h250 h252 h256 h360 h362 h2792 h2794 h2796 h2798 h2842 h2844 h2846 h2848 h2850 h2858 h2860 h2934 h2936 h2938 h2950 h3034 h3060 h3064 h3066 h3122 h3206 h3304 h3306 h3308 h3310 h3424 h3540
  obtain ⟨h15337, h15351, h15383, h15414, h15415, h15448, h15539, h15542, h15543, h15545, h15657, h15718, h15754, h15755, h15772, h15823, h15850, h15889, h15958, h16049, h16095, h16096, h16118, h16188, h16199, h16220, h16221, h16222, h16274, h16309, h16310, h16327, h16373, h16404, h16405, h16408, h16460, h16523⟩ := negative_grid_recovery_rows_chunk1 x y z w a b hx hy hz hw u v h6 h16 h28 h44 h62 h2800 h2802 h2854 h2856 h2872 h2874 h2876 h3210 h3226 h3254 h3256 h3340 h3358 h3360 h3376 h3436 h3528 h14217 h14219 h14412 h14460 h14461 h14478 h14716 h14793 h14797 h14874 h14997 h14998 h15228 h15293 h15294 h15317
  obtain ⟨h16528, h16576, h16619, h16677, h16754, h16787, h16789, h16837, h16841, h16983, h17018, h17041, h17071, h17077, h17095, h17160, h17208, h17209, h17210, h17235, h17252, h17258, h17260, h17275, h17276, h17277, h17300, h17331, h17332, h17348, h17378, h17421, h17442, h17443, h17445, h17446, h17477, h17493, h17510⟩ := negative_grid_recovery_rows_chunk2 x y z w a b hx hy hz hw u v h4 h18 h22 h24 h26 h30 h32 h34 h36 h46 h266 h2866 h3032 h3058 h3084 h3110 h3158 h3212 h3216 h3222 h3230 h3232 h3238 h3274 h3312 h3314 h3316 h3426 h3432 h3448 h14224 h14413 h14458 h14845 h15230 h15539 h15958 h16199 h16222 h16460
  obtain ⟨h17511, h17512, h17532, h17534, h17607, h17623, h17632, h17647, h17671, h17677, h17745, h17779, h17806, h17807, h17808, h17810, h17811, h17919, h17920, h17973, h17974, h17988, h17996, h18006, h18032, h18155, h18167, h18171, h18175, h18177, h18221, h18223, h18239, h18240, h18241, h18247⟩ := negative_grid_recovery_rows_chunk3 x y z w a b hx hy hz hw u v h38 h40 h42 h48 h50 h52 h68 h294 h316 h320 h2932 h3006 h3242 h3262 h3292 h14426 h14427 h14428 h14450 h15383 h15542 h15543 h15545 h15823 h16188 h17071 h17077 h17208 h17210 h17258 h17260 h17275 h17276 h17332 h17348 h17421 h17477
  obtain ⟨h18315, h18374, h18418, h18419, h18420, h18424, h18537, h18541, h18570, h18659, h18680, h18684, h18686, h18687, h18703, h18744, h18748, h18795, h18796, h18867, h18871, h18872, h18984, h18988, h19009, h19037, h19073, h19074, h19128, h19131, h19132, h19163, h19189, h19214, h19228, h19262, h19264, h19281, h19282, h19283, h19311⟩ := negative_grid_recovery_rows_chunk4 x y z w a b hx hy hz hw u v h54 h56 h58 h60 h64 h66 h150 h162 h262 h268 h270 h272 h274 h300 h358 h364 h366 h2790 h2868 h3218 h3300 h3302 h3362 h3392 h3396 h14399 h14400 h15754 h15755 h16841 h17209 h17331 h17493 h17510 h17623 h17632 h17779 h17920 h17988 h17996 h18175
  obtain ⟨h19326, h19328, h19337, h19370, h19372, h19378, h19379, h19380, h19381, h19395, h19450, h19451, h19456, h19545, h19601, h19602, h19636, h19655, h19669, h19685, h19701, h19704, h19716, h19754, h19773, h19789, h19792, h19795, h19796, h19812, h19814, h19842, h19870, h19872, h19876, h19904, h19905, h19940, h19948, h19961, h19976⟩ := negative_grid_recovery_rows_chunk5 x y z w a b hx hy hz hw u v h288 h292 h296 h298 h2804 h2810 h3250 h3298 h3364 h3390 h3478 h3530 h3614 h15850 h16373 h16528 h17277 h17443 h17745 h17806 h17811 h17973 h17974 h18006 h18032 h18171 h18177 h18223 h18241 h18424 h18541 h18680 h18684 h18686 h18687 h18703 h18748 h18871 h19073 h19131 h19262 h19311
  obtain ⟨h20005, h20013, h20014, h20015, h20030, h20085, h20086, h20087, h20088, h20089, h20178, h20186, h20191, h20200, h20211, h20220, h20254, h20270, h20271, h20274, h20291, h20317, h20338, h20340, h20357, h20358, h20383, h20404, h20414, h20420, h20429, h20440, h20442, h20449, h20505, h20507, h20508, h20509, h20510, h20511, h20513⟩ := negative_grid_recovery_rows_chunk6 x y z w a b hx hy hz hw u v h304 h306 h312 h322 h326 h342 h2806 h2808 h2840 h3224 h3228 h3252 h3386 h3574 h14407 h14408 h14409 h14410 h16754 h17252 h17534 h17647 h17677 h17807 h17808 h18167 h18795 h18988 h19264 h19378 h19379 h19380 h19395 h19451 h19655 h19669 h19701 h19795 h19812 h19814 h19876 h19976
  obtain ⟨h20514, h20526, h20527, h20528, h20555, h20563, h20564, h20565, h20582, h20599, h20616, h20617, h20618, h20619, h20620, h20622, h20628, h20629, h20786, h20812, h20814, h20832, h20847, h20863, h20889, h20897, h20902, h20916, h20924, h20937, h20938, h20939, h20954, h21004, h21018, h21043, h21044, h21082, h21092, h21102, h21119, h21142, h21151, h21165, h21182, h21190, h21203⟩ := negative_grid_recovery_rows_chunk7 x y z w a b hx hy hz hw u v h368 h370 h372 h374 h378 h380 h382 h3240 h3276 h3278 h3288 h3290 h3326 h3378 h3450 h17018 h17511 h17512 h17810 h18239 h18240 h18796 h18872 h19009 h19132 h19281 h19381 h19456 h19754 h19796 h19870 h20013 h20015 h20030 h20085 h20087 h20088 h20186 h20270 h20338 h20340 h20357 h20358 h20414 h20449 h20509 h20510 h20511
  obtain ⟨h21204, h21205, h21220, h21247, h21269, h21270, h21285, h21295, h21306, h21323, h21392, h21431, h21433, h21455, h21456, h21457, h21460, h21462, h21487, h21488, h21538, h21539, h21541, h21542, h21543, h21546, h21550, h21551, h21674, h21687, h21689, h21699, h21701, h21712, h21714, h21724, h21725, h21726, h21754, h21783, h21785, h21787, h21794, h21799, h21893⟩ := negative_grid_recovery_rows_chunk8 x y z w a b hx hy hz hw u v h384 h394 h398 h400 h402 h3236 h3264 h3324 h3336 h3338 h3350 h3374 h3380 h14398 h14401 h15414 h15415 h16523 h16619 h17442 h17445 h17446 h18418 h19074 h19163 h19214 h19601 h19602 h19704 h19792 h19904 h19905 h19948 h20271 h20420 h20555 h20563 h20564 h20565 h20812 h20814 h20847 h20863 h20897 h20902 h21182
  obtain ⟨h21894, h21918, h21924, h21925, h21929, h21936, h21940, h21954, h21965, h21966, h21979, h21990, h21993, h22005, h22006, h22015, h22026, h22037, h22050, h22052, h22062, h22075, h22077, h22087, h22088, h22089, h22092, h22093, h22094, h22096, h22097, h22099, h22108, h22109, h22110, h22111, h22141, h22142, h22150, h22151, h22153, h22159, h22174, h22210, h22212, h22213⟩ := negative_grid_recovery_rows_chunk9 x y z w a b hx hy hz hw u v h2812 h3284 h3318 h3446 h14406 h16095 h16221 h16310 h16408 h16789 h18419 h18420 h18570 h19328 h19370 h19372 h19450 h20014 h20274 h20291 h20442 h20507 h20508 h20513 h20526 h20527 h20528 h20618 h21018 h21092 h21102 h21165 h21204 h21295 h21431 h21456 h21457 h21460 h21487 h21488 h21546 h21687 h21701 h21714 h21725 h21754 h21893
  obtain ⟨h22214, h22224, h22353, h22354, h22355, h22362, h22368, h22369, h22370, h22393, h22410, h22442, h22443, h22445, h22446, h22539, h22544, h22558, h22624, h22625, h22629, h22631, h22649, h22650, h22652, h22673, h22674, h22675, h22678, h22679, h22730, h22731, h22735, h22737, h22790, h22791, h22797⟩ := negative_grid_recovery_rows_chunk10 x y z w a b hx hy hz hw u v h2814 h3234 h3444 h18247 h19789 h19961 h20005 h20089 h20514 h20616 h20617 h20620 h20622 h20628 h20629 h20924 h21043 h21044 h21119 h21190 h21726 h21783 h21785 h21894 h21993 h22087 h22088 h22099 h22108 h22109 h22110 h22111 h22142 h22150 h22153 h22159 h22174 h22210
  obtain ⟨h22839, h22840, h22842, h22843, h22849, h22851, h22852, h22872, h22876, h22916, h22917, h22918, h22925, h22926, h23014, h23015, h23017, h23038, h23039, h23040, h23043, h23069, h23070, h23125, h23130, h23137, h23143, h23168, h23179, h23205, h23206, h23226, h23229, h23239, h23272, h23274, h23278, h23290⟩ := negative_grid_recovery_rows_chunk11 x y z w a b hx hy hz hw u v h16220 h16309 h16787 h19872 h20086 h20505 h20599 h21269 h21270 h21462 h21538 h21925 h21966 h22089 h22141 h22151 h22212 h22213 h22224 h22354 h22355 h22362 h22393 h22410 h22442 h22443 h22445 h22446 h22544 h22558 h22625 h22629 h22631 h22730 h22731 h22737 h22790 h22791 h22797
  obtain ⟨h23318, h23319, h23344, h23427, h23430, h23473, h23491, h23492, h23494, h23495, h23516, h23518, h23535, h23560, h23574, h23585, h23613, h23614, h23618, h23638, h23639, h23660, h23663, h23671, h23672, h23685, h23687, h23696, h23697, h23703, h23707, h23714, h23719, h23732, h23740, h23757⟩ := negative_grid_recovery_rows_chunk12 x y z w a b hx hy hz hw u v h16096 h16404 h16405 h20582 h20619 h21151 h21306 h21542 h21543 h21794 h21924 h21936 h21954 h22094 h22370 h22649 h22650 h22674 h22735 h22840 h22842 h22849 h22852 h22876 h22916 h22918 h22925 h23038 h23039 h23043 h23069 h23130 h23229 h23239 h23274 h23278
  obtain ⟨h23777, h23789, h23795, h23798, h23839, h23843, h23844, h23845, h23846, h23859, h23886, h23920, h23922, h23964, h23991, h24008, h24026, h24029, h24044, h24045, h24047, h24062, h24080, h24087, h24098, h24105, h24107, h24109⟩ := negative_grid_recovery_rows_chunk13 x y z w a b hx hy hz hw u v h19282 h19283 h22093 h22214 h22369 h22675 h22678 h22679 h22843 h22917 h22926 h23017 h23070 h23137 h23430 h23492 h23494 h23495 h23516 h23518 h23618 h23663 h23697 h23703 h23707 h23719 h23732 h23740 h23757
  obtain ⟨h24116, h24134, h24152, h24153, h24170, h24188, h24242, h24243, h24282, h24286, h24296, h24333, h24334, h24375, h24390, h24400, h24425, h24431, h24436, h24439, h24442, h24447, h24458, h24469, h24470, h24484, h24494, h24501, h24505, h24516, h24527, h24528, h24538, h24539, h24549, h24560, h24571, h24572, h24582, h24583, h24593⟩ := negative_grid_recovery_rows_chunk14 x y z w a b hx hy hz hw u v h3246 h3248 h3294 h3296 h3330 h20211 h20440 h20937 h20938 h20939 h21203 h21433 h21539 h21541 h21712 h21799 h21979 h22005 h22075 h22092 h22096 h22097 h22368 h23205 h23206 h23574 h23614 h23638 h23639 h23672 h23685 h23789 h23859 h23886 h23991 h24029 h24045 h24047 h24087 h24105 h24107
  obtain ⟨h24604, h24615, h24626, h24637, h24662, h24673, h24684, h24695, h24697, h24734, h24776, h24796, h24810, h24811, h24870, h24871, h24926, h24965, h24984, h24999, h25023, h25029, h25046, h25047, h25050, h25056, h25070, h25075, h25093, h25094, h25097⟩ := negative_grid_recovery_rows_chunk15 x y z w a b hx hy hz hw u v h3354 h3368 h14878 h19326 h20191 h21205 h21550 h21689 h21787 h22006 h22050 h22052 h22077 h22652 h23015 h23319 h23687 h23922 h24109 h24242 h24286 h24334 h24390 h24439 h24442 h24470 h24501 h24528 h24539 h24572 h24583 h24593
  obtain ⟨h25137, h25171, h25173, h25198, h25249, h25250, h25327, h25341, h25350, h25378, h25390, h25429, h25430, h25433, h25435, h25455, h25503, h25550, h25551, h25557, h25630, h25692, h25720, h25760, h25761, h25765, h25766, h25767, h25780, h25829⟩ := negative_grid_recovery_rows_chunk16 x y z w a b hx hy hz hw u v h21551 h22851 h22872 h23040 h23344 h23798 h23843 h23844 h23845 h23846 h24153 h24243 h24296 h24333 h24431 h24484 h24697 h24796 h24811 h24871 h24984 h25023 h25029 h25047 h25050 h25056 h25070 h25075 h25093 h25094 h25097
  obtain ⟨h25956, h25981, h26075, h26097, h26141, h26149, h26150, h26151, h26212, h26223, h26234, h26259, h26273, h26284, h26285, h26295, h26326, h26350, h26418, h26419, h26420, h26430, h26483⟩ := negative_grid_recovery_rows_chunk17 x y z w a b hx hy hz hw u v h24870 h25173 h25198 h25249 h25250 h25341 h25350 h25378 h25390 h25430 h25433 h25435 h25455 h25503 h25551 h25557 h25630 h25720 h25761 h25765 h25766 h25767 h25780 h25829
  obtain ⟨h26538, h26549, h26560, h26625, h26672, h26724, h26797, h26808, h26819, h26913, h27012, h27094, h27180, h27191⟩ := negative_grid_recovery_rows_chunk18 x y z w a b hx hy hz hw u v h25760 h25956 h25981 h26097 h26141 h26149 h26150 h26151 h26259 h26285 h26326 h26419 h26420 h26430
  exact ⟨h14206, h14708, h14783, h14938, h14957, h15018, h15101, h15288, h15337, h15351, h15448, h15657, h15718, h15772, h15889, h16049, h16118, h16274, h16327, h16460, h16576, h16677, h16837, h16983, h17041, h17095, h17160, h17235, h17300, h17378, h17477, h17532, h17607, h17671, h17919, h18155, h18221, h18315, h18374, h18537, h18659, h18744, h18867, h18984, h19037, h19128, h19189, h19228, h19311, h19337, h19545, h19636, h19685, h19716, h19773, h19842, h19940, h19976, h20178, h20200, h20220, h20254, h20317, h20383, h20404, h20429, h20449, h20786, h20832, h20889, h20916, h20954, h21004, h21082, h21142, h21182, h21220, h21247, h21285, h21323, h21392, h21455, h21674, h21699, h21724, h21893, h21918, h21929, h21940, h21965, h21990, h22015, h22026, h22037, h22062, h22087, h22353, h22539, h22624, h22673, h22790, h22839, h23014, h23125, h23143, h23168, h23179, h23226, h23272, h23290, h23318, h23427, h23473, h23491, h23535, h23560, h23585, h23613, h23660, h23671, h23696, h23714, h23732, h23777, h23795, h23839, h23920, h23964, h24008, h24026, h24044, h24062, h24080, h24098, h24116, h24134, h24152, h24170, h24188, h24282, h24375, h24400, h24425, h24436, h24447, h24458, h24469, h24494, h24505, h24516, h24527, h24538, h24549, h24560, h24571, h24582, h24593, h24604, h24615, h24626, h24637, h24662, h24673, h24684, h24695, h24734, h24776, h24810, h24926, h24965, h24999, h25046, h25093, h25137, h25171, h25327, h25429, h25550, h25692, h25829, h26075, h26212, h26223, h26234, h26273, h26284, h26295, h26350, h26418, h26483, h26538, h26549, h26560, h26625, h26672, h26724, h26797, h26808, h26819, h26913, h27012, h27094, h27180, h27191⟩

#print axioms negative_grid_recovery_rows

end QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate
end
end

/-! ## ThirtyFiveNegativeGridRecoveryKernel -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate

def negativeGridRecoveryConclusion (x y z w a b : ℂ) (v : Fin 210 → ℂ) : Prop :=
(1)*v 0 = 0 ∧
      (1)*v 207 = 0 ∧
      (1)*v 204 = 0 ∧
      (1)*v 1 = 0 ∧
      (1)*v 2 = 0 ∧
      (1)*v 3 = 0 ∧
      (1)*v 6 = 0 ∧
      (1)*v 208 = 0 ∧
      (1)*v 209 = 0 ∧
      (1)*v 102 = 0 ∧
      (1)*v 105 = 0 ∧
      (1)*v 206 = 0 ∧
      (1)*v 4 = 0 ∧
      (1)*v 12 = 0 ∧
      (1)*v 198 = 0 ∧
      (1)*v 106 = 0 ∧
      (1)*v 108 = 0 ∧
      (1)*v 104 = 0 ∧
      (1)*v 174 = 0 ∧
      (1)*v 35 = 0 ∧
      (1)*v 175 = 0 ∧
      (1)*v 36 = 0 ∧
      (1)*v 205 = 0 ∧
      (1)*v 5 + ((z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 ∧
      (1)*v 7 + ((w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 = 0 ∧
      (1)*v 9 + ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 70 = 0 ∧
      (1)*v 10 = 0 ∧
      (1)*v 14 + ((w)/(y^(2:ℕ)*z))*v 120 = 0 ∧
      (1)*v 15 + ((z)/(x^(2:ℕ)*w))*v 126 = 0 ∧
      (1)*v 18 + ((y^(2:ℕ))/(z*w))*v 140 = 0 ∧
      (1)*v 20 + ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 = 0 ∧
      (1)*v 21 + ((w)/(x^(2:ℕ)*z))*v 150 = 0 ∧
      (1)*v 28 + ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      (1)*v 30 + ((z)/(w))*v 168 = 0 ∧
      (1)*v 180 = 0 ∧
      ((x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 182 = 0 ∧
      ((w)/(x^(2:ℕ)*z))*v 60 + (1)*v 189 = 0 ∧
      ((x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 190 = 0 ∧
      (1)*v 70 = 0 ∧
      (1)*v 195 = 0 ∧
      ((w)/(y^(2:ℕ)*z))*v 90 + (1)*v 196 = 0 ∧
      ((z)/(y^(2:ℕ)*w))*v 126 + (1)*v 200 = 0 ∧
      ((y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 + (1)*v 201 = 0 ∧
      (1)*v 203 = 0 ∧
      (1)*v 8 + ((-1)/(y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 202 = 0 ∧
      (1)*v 107 = 0 ∧
      (1)*v 110 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 199 = 0 ∧
      (1)*v 90 + ((z)/(w))*v 126 = 0 ∧
      (1)*v 96 + ((y^(2:ℕ))/(z*w))*v 140 = 0 ∧
      (1)*v 99 = 0 ∧
      (1)*v 109 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 111 + ((-1)/(x^(2:ℕ)))*v 186 = 0 ∧
      ((w)/(y^(2:ℕ)*z))*v 60 + (1)*v 112 = 0 ∧
      (1)*v 114 = 0 ∧
      (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 ∧
      (1)*v 120 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 197 = 0 ∧
      (1)*v 13 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 66 = 0 ∧
      (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 93 = 0 ∧
      (1)*v 98 + ((w)/(y^(2:ℕ)*z))*v 150 = 0 ∧
      (1)*v 100 + ((z)/(y^(2:ℕ)*w))*v 168 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 48 + (1)*v 101 = 0 ∧
      (1)*v 103 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 11 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 168 = 0 ∧
      ((1)/(z*w))*v 140 + (1)*v 176 = 0 ∧
      (1)*v 177 = 0 ∧
      (1)*v 37 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 38 + ((-1)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 39 + ((-1)/(x^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 40 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 165 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 48 + (1)*v 171 = 0 ∧
      ((-1)/(y^(2:ℕ)))*v 54 + (1)*v 172 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 173 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 27 + (1)*v 178 = 0 ∧
      (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 183 = 0 ∧
      (1)*v 33 + ((-1)/(x^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 34 = 0 ∧
      (1)*v 140 = 0 ∧
      (1)*v 74 + (1)*v 144 = 0 ∧
      (1)*v 66 + (1)*v 136 = 0 ∧
      (1)*v 186 = 0 ∧
      (1)*v 51 + (1)*v 156 = 0 ∧
      (1)*v 52 + (1)*v 157 = 0 ∧
      (1)*v 53 = 0 ∧
      (1)*v 54 + (1)*v 159 = 0 ∧
      (1)*v 82 + (1)*v 152 = 0 ∧
      (1)*v 58 = 0 ∧
      (1)*v 71 + (1)*v 141 = 0 ∧
      (1)*v 69 + (1)*v 139 = 0 ∧
      (1)*v 72 + (1)*v 142 = 0 ∧
      (1)*v 68 + (1)*v 138 = 0 ∧
      (1)*v 126 = 0 ∧
      (1)*v 60 + (1)*v 150 = 0 ∧
      (1)*v 63 + (1)*v 147 = 0 ∧
      (1)*v 16 + ((1)/(y^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 63 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 48 + (1)*v 194 = 0 ∧
      (1)*v 150 = 0 ∧
      (1)*v 165 = 0 ∧
      (1)*v 115 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 72 + (1)*v 123 = 0 ∧
      (1)*v 26 + (((-1)*a)/(x))*v 52 + (1)*v 131 = 0 ∧
      (1)*v 27 + (((-1)*a)/(x))*v 54 + (1)*v 132 = 0 ∧
      (1)*v 135 = 0 ∧
      (1)*v 65 = 0 ∧
      (((-1)*a)/(x))*v 72 + (1)*v 141 + ((1)/(x^(2:ℕ)))*v 144 = 0 ∧
      (1)*v 45 = 0 ∧
      (1)*v 75 = 0 ∧
      (1)*v 145 = 0 ∧
      (1)*v 56 + (1)*v 154 = 0 ∧
      (1)*v 48 + (1)*v 153 = 0 ∧
      (1)*v 57 + (1)*v 162 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 66 + (1)*v 69 + (((-1)*a)/(x))*v 138 = 0 ∧
      (1)*v 32 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 78 + (((-1)*x*a)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 79 + (1)*v 184 = 0 ∧
      (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 95 = 0 ∧
      (1)*v 77 = 0 ∧
      (1)*v 50 = 0 ∧
      (1)*v 155 = 0 ∧
      (1)*v 80 = 0 ∧
      (1)*v 154 = 0 ∧
      (1)*v 130 = 0 ∧
      (1)*v 160 = 0 ∧
      (1)*v 133 = 0 ∧
      (1)*v 119 = 0 ∧
      (1)*v 125 = 0 ∧
      (1)*v 25 = 0 ∧
      (1)*v 49 = 0 ∧
      (1)*v 55 = 0 ∧
      (1)*v 161 = 0 ∧
      (1)*v 91 = 0 ∧
      (1)*v 185 = 0 ∧
      (1)*v 85 = 0 ∧
      (1)*v 48 + (1)*v 132 = 0 ∧
      (1)*v 78 + (1)*v 162 = 0 ∧
      (((-1)*a)/(x))*v 22 + ((1)/(x^(2:ℕ)))*v 44 + (1)*v 116 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 ∧
      (((-1)*a)/(x))*v 26 + ((1)/(x^(2:ℕ)))*v 52 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 66 + (1)*v 118 = 0 ∧
      (1)*v 17 + (1)*v 122 + ((-1)/(x^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 19 + ((1)/(x^(2:ℕ)))*v 76 + (1)*v 124 + (((-1)*a)/(x*y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 22 + (((-1)*a)/(x))*v 44 + ((1)/(x^(2:ℕ)))*v 88 + (1)*v 127 = 0 ∧
      (1)*v 23 + (((-1)*a)/(x))*v 46 + ((1)/(x^(2:ℕ)))*v 92 = 0 ∧
      (((-1)*a)/(x))*v 48 + (1)*v 129 = 0 ∧
      (1)*v 31 + (((-1)*a)/(x))*v 62 + (-1)*v 66 + ((1)/(x^(2:ℕ)))*v 124 = 0 ∧
      (((-1)*a)/(x))*v 76 + (1)*v 143 + ((1)/(x^(2:ℕ)))*v 152 + ((1)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 41 + (1)*v 146 + ((a)/(x))*v 152 + ((1)/(x^(2:ℕ)))*v 164 = 0 ∧
      (1)*v 43 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (((-1)*a)/(x))*v 86 + (1)*v 148 = 0 ∧
      (1)*v 44 + (((-1)*a)/(x))*v 88 + (1)*v 149 = 0 ∧
      (1)*v 46 + (((-1)*a)/(x))*v 92 + (1)*v 151 + ((1)/(x^(2:ℕ)))*v 184 = 0 ∧
      (1)*v 47 + (((-1)*a)/(x))*v 94 + (1)*v 152 + ((1)/(x^(2:ℕ)))*v 188 = 0 ∧
      (1)*v 61 + (((-1)*a)/(x))*v 122 + (1)*v 166 = 0 ∧
      (1)*v 62 + (((-1)*a)/(x))*v 124 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + (1)*v 167 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 46 + (1)*v 64 + (1)*v 169 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 54 + (1)*v 67 + (((-1)*a)/(x))*v 134 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 86 + (-1)*v 144 + (((-1)*a)/(x))*v 148 + (1)*v 179 = 0 ∧
      (1)*v 76 + ((1)/(x^(2:ℕ)))*v 94 + (((-1)*a)/(x))*v 152 + (1)*v 181 = 0 ∧
      (1)*v 81 + (((-1)*a)/(x))*v 162 = 0 ∧
      (1)*v 83 + ((1)/(x^(2:ℕ)))*v 122 + (((-1)*a)/(x))*v 166 + (1)*v 188 = 0 ∧
      (((-1)*a)/(x*y^(2:ℕ)))*v 54 + (1)*v 86 + ((1)/(x^(2:ℕ)))*v 134 + (1)*v 191 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 72 + (1)*v 88 + (1)*v 193 = 0 ∧
      (1)*v 92 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (((-1)*a)/(x))*v 184 = 0 ∧
      ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 94 + ((1)/(x^(2:ℕ)))*v 166 + (((-1)*a)/(x))*v 188 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0 ∧
      (-1)*v 72 + (1)*v 138 = 0 ∧
      ((1 + (-1)*x^(2:ℕ)*y^(2:ℕ))/(y^(2:ℕ)))*v 72 + (x*a)*v 144 + (1)*v 148 = 0 ∧
      (1)*v 64 + (1)*v 134 + ((1)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 44 + (1)*v 86 = 0 ∧
      (1)*v 124 + (-1)*v 152 + (1)*v 166 = 0 ∧
      (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 88 = 0 ∧
      (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 ∧
      (1)*v 72 + (1)*v 156 = 0 ∧
      (1)*v 66 = 0 ∧
      (1)*v 144 = 0 ∧
      (1)*v 54 = 0 ∧
      (1)*v 48 = 0 ∧
      (1)*v 72 = 0 ∧
      (1)*v 162 = 0 ∧
      (1)*v 113 = 0 ∧
      (1)*v 29 = 0 ∧
      (1)*v 62 = 0 ∧
      (1)*v 97 = 0 ∧
      (1)*v 59 = 0 ∧
      (1)*v 22 + (-1)*v 134 = 0 ∧
      (-1)*v 76 + (1)*v 188 = 0 ∧
      (1)*v 184 = 0 ∧
      (1)*v 26 + (1)*v 152 = 0 ∧
      (1)*v 121 + ((-1)/(x^(2:ℕ)))*v 134 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 76 + (1)*v 89 = 0 ∧
      (1)*v 44 = 0 ∧
      (1)*v 52 + (1)*v 122 = 0 ∧
      (1)*v 46 = 0 ∧
      (-1)*v 152 + (1)*v 166 = 0 ∧
      (1)*v 137 = 0 ∧
      (-1)*v 52 + (1)*v 73 = 0 ∧
      (1)*v 76 = 0 ∧
      (1)*v 152 = 0 ∧
      (1)*v 52 = 0 ∧
      (1)*v 134 = 0 ∧
      (1)*v 163 = 0 ∧
      (1)*v 187 = 0

theorem negative_grid_recovery_kernel (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (h : negativeGridRecoveryConclusion x y z w a b v)
    (h24 : v 24=0) (h42 : v 42=0) (h84 : v 84=0)
    (h128 : v 128=0) (h158 : v 158=0) (h192 : v 192=0) : v=0 := by
  obtain ⟨hp0,hp1,hp2,hp3,hp4,hp5,hp6,hp7,hp8,hp9,hp10,hp11,hp12,hp13,hp14,hp15,hp16,hp17,hp18,hp19,hp20,hp21,hp22,hp23,hp24,hp25,hp26,hp27,hp28,hp29,hp30,hp31,hp32,hp33,hp34,hp35,hp36,hp37,hp38,hp39,hp40,hp41,hp42,hp43,hp44,hp45,hp46,hp47,hp48,hp49,hp50,hp51,hp52,hp53,hp54,hp55,hp56,hp57,hp58,hp59,hp60,hp61,hp62,hp63,hp64,hp65,hp66,hp67,hp68,hp69,hp70,hp71,hp72,hp73,hp74,hp75,hp76,hp77,hp78,hp79,hp80,hp81,hp82,hp83,hp84,hp85,hp86,hp87,hp88,hp89,hp90,hp91,hp92,hp93,hp94,hp95,hp96,hp97,hp98,hp99,hp100,hp101,hp102,hp103,hp104,hp105,hp106,hp107,hp108,hp109,hp110,hp111,hp112,hp113,hp114,hp115,hp116,hp117,hp118,hp119,hp120,hp121,hp122,hp123,hp124,hp125,hp126,hp127,hp128,hp129,hp130,hp131,hp132,hp133,hp134,hp135,hp136,hp137,hp138,hp139,hp140,hp141,hp142,hp143,hp144,hp145,hp146,hp147,hp148,hp149,hp150,hp151,hp152,hp153,hp154,hp155,hp156,hp157,hp158,hp159,hp160,hp161,hp162,hp163,hp164,hp165,hp166,hp167,hp168,hp169,hp170,hp171,hp172,hp173,hp174,hp175,hp176,hp177,hp178,hp179,hp180,hp181,hp182,hp183,hp184,hp185,hp186,hp187,hp188,hp189,hp190,hp191,hp192,hp193,hp194,hp195,hp196,hp197,hp198,hp199,hp200,hp201,hp202,hp203⟩ := h
  have hv187 : v 187=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp203
  have hv163 : v 163=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp202
  have hv134 : v 134=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp201
  have hv52 : v 52=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp200
  have hv152 : v 152=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp199
  have hv76 : v 76=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp198
  have hv73 : v 73=0 := by
    simpa only [hv52,mul_zero,zero_add,add_zero,one_mul] using hp197
  have hv137 : v 137=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp196
  have hv166 : v 166=0 := by
    simpa only [hv152,mul_zero,zero_add,add_zero,one_mul] using hp195
  have hv46 : v 46=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp194
  have hv122 : v 122=0 := by
    simpa only [hv52,mul_zero,zero_add,add_zero,one_mul] using hp193
  have hv44 : v 44=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp192
  have hv89 : v 89=0 := by
    simpa only [hv76,mul_zero,zero_add,add_zero,one_mul] using hp191
  have hv121 : v 121=0 := by
    simpa only [hv134,mul_zero,zero_add,add_zero,one_mul] using hp190
  have hv26 : v 26=0 := by
    simpa only [hv152,mul_zero,zero_add,add_zero,one_mul] using hp189
  have hv184 : v 184=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp188
  have hv188 : v 188=0 := by
    simpa only [hv76,mul_zero,zero_add,add_zero,one_mul] using hp187
  have hv22 : v 22=0 := by
    simpa only [hv134,mul_zero,zero_add,add_zero,one_mul] using hp186
  have hv59 : v 59=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp185
  have hv97 : v 97=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp184
  have hv62 : v 62=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp183
  have hv29 : v 29=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp182
  have hv113 : v 113=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp181
  have hv162 : v 162=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp180
  have hv72 : v 72=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp179
  have hv48 : v 48=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp178
  have hv54 : v 54=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp177
  have hv144 : v 144=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp176
  have hv66 : v 66=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp175
  have hv156 : v 156=0 := by
    simpa only [hv72,mul_zero,zero_add,add_zero,one_mul] using hp174
  have hv164 : v 164=0 := by
    simpa only [hv122,hv156,mul_zero,zero_add,add_zero,one_mul] using hp173
  have hv88 : v 88=0 := by
    simpa only [hv46,hv54,mul_zero,zero_add,add_zero,one_mul] using hp172
  have hv124 : v 124=0 := by
    simpa only [hv152,hv166,mul_zero,zero_add,add_zero,one_mul] using hp171
  have hv86 : v 86=0 := by
    simpa only [hv44,mul_zero,zero_add,add_zero,one_mul] using hp170
  have hv64 : v 64=0 := by
    simpa only [hv134,hv156,mul_zero,zero_add,add_zero,one_mul] using hp169
  have hv148 : v 148=0 := by
    simpa only [hv72,hv144,mul_zero,zero_add,add_zero,one_mul] using hp168
  have hv138 : v 138=0 := by
    simpa only [hv72,mul_zero,zero_add,add_zero,one_mul] using hp167
  have hv146 : v 146=0 := by
    simpa only [hv54,hv76,mul_zero,zero_add,add_zero,one_mul] using hp166
  have hv94 : v 94=0 := by
    simpa only [hv72,hv166,hv188,mul_zero,zero_add,add_zero,one_mul] using hp165
  have hv92 : v 92=0 := by
    simpa only [hv144,hv184,mul_zero,zero_add,add_zero,one_mul] using hp164
  have hv193 : v 193=0 := by
    simpa only [hv72,hv88,mul_zero,zero_add,add_zero,one_mul] using hp163
  have hv191 : v 191=0 := by
    simpa only [hv54,hv86,hv134,mul_zero,zero_add,add_zero,one_mul] using hp162
  have hv83 : v 83=0 := by
    simpa only [hv122,hv166,hv188,mul_zero,zero_add,add_zero,one_mul] using hp161
  have hv81 : v 81=0 := by
    simpa only [hv162,mul_zero,zero_add,add_zero,one_mul] using hp160
  have hv181 : v 181=0 := by
    simpa only [hv76,hv94,hv152,mul_zero,zero_add,add_zero,one_mul] using hp159
  have hv179 : v 179=0 := by
    simpa only [hv86,hv144,hv148,mul_zero,zero_add,add_zero,one_mul] using hp158
  have hv67 : v 67=0 := by
    simpa only [hv54,hv134,mul_zero,zero_add,add_zero,one_mul] using hp157
  have hv169 : v 169=0 := by
    simpa only [hv46,hv64,mul_zero,zero_add,add_zero,one_mul] using hp156
  have hv167 : v 167=0 := by
    simpa only [hv62,hv124,hv156,mul_zero,zero_add,add_zero,one_mul] using hp155
  have hv61 : v 61=0 := by
    simpa only [hv122,hv166,mul_zero,zero_add,add_zero,one_mul] using hp154
  have hv47 : v 47=0 := by
    simpa only [hv94,hv152,hv188,mul_zero,zero_add,add_zero,one_mul] using hp153
  have hv151 : v 151=0 := by
    simpa only [hv46,hv92,hv184,mul_zero,zero_add,add_zero,one_mul] using hp152
  have hv149 : v 149=0 := by
    simpa only [hv44,hv88,mul_zero,zero_add,add_zero,one_mul] using hp151
  have hv43 : v 43=0 := by
    simpa only [hv54,hv86,hv148,mul_zero,zero_add,add_zero,one_mul] using hp150
  have hv41 : v 41=0 := by
    simpa only [hv146,hv152,hv164,mul_zero,zero_add,add_zero,one_mul] using hp149
  have hv143 : v 143=0 := by
    simpa only [hv76,hv152,hv156,mul_zero,zero_add,add_zero,one_mul] using hp148
  have hv31 : v 31=0 := by
    simpa only [hv62,hv66,hv124,mul_zero,zero_add,add_zero,one_mul] using hp147
  have hv129 : v 129=0 := by
    simpa only [hv48,mul_zero,zero_add,add_zero,one_mul] using hp146
  have hv23 : v 23=0 := by
    simpa only [hv46,hv92,mul_zero,zero_add,add_zero,one_mul] using hp145
  have hv127 : v 127=0 := by
    simpa only [hv22,hv44,hv88,mul_zero,zero_add,add_zero,one_mul] using hp144
  have hv19 : v 19=0 := by
    simpa only [hv76,hv124,hv156,mul_zero,zero_add,add_zero,one_mul] using hp143
  have hv17 : v 17=0 := by
    simpa only [hv122,hv138,mul_zero,zero_add,add_zero,one_mul] using hp142
  have hv118 : v 118=0 := by
    simpa only [hv26,hv52,hv66,mul_zero,zero_add,add_zero,one_mul] using hp141
  have hv116 : v 116=0 := by
    simpa only [hv22,hv44,hv138,mul_zero,zero_add,add_zero,one_mul] using hp140
  have hv78 : v 78=0 := by
    simpa only [hv162,mul_zero,zero_add,add_zero,one_mul] using hp139
  have hv132 : v 132=0 := by
    simpa only [hv48,mul_zero,zero_add,add_zero,one_mul] using hp138
  have hv85 : v 85=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp137
  have hv185 : v 185=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp136
  have hv91 : v 91=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp135
  have hv161 : v 161=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp134
  have hv55 : v 55=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp133
  have hv49 : v 49=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp132
  have hv25 : v 25=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp131
  have hv125 : v 125=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp130
  have hv119 : v 119=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp129
  have hv133 : v 133=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp128
  have hv160 : v 160=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp127
  have hv130 : v 130=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp126
  have hv154 : v 154=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp125
  have hv80 : v 80=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp124
  have hv155 : v 155=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp123
  have hv50 : v 50=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp122
  have hv77 : v 77=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp121
  have hv95 : v 95=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp120
  have hv87 : v 87=0 := by
    simpa only [hv138,mul_zero,zero_add,add_zero,one_mul] using hp119
  have hv79 : v 79=0 := by
    simpa only [hv184,mul_zero,zero_add,add_zero,one_mul] using hp118
  have hv32 : v 32=0 := by
    simpa only [hv78,hv156,mul_zero,zero_add,add_zero,one_mul] using hp117
  have hv69 : v 69=0 := by
    simpa only [hv66,hv138,mul_zero,zero_add,add_zero,one_mul] using hp116
  have hv57 : v 57=0 := by
    simpa only [hv162,mul_zero,zero_add,add_zero,one_mul] using hp115
  have hv153 : v 153=0 := by
    simpa only [hv48,mul_zero,zero_add,add_zero,one_mul] using hp114
  have hv56 : v 56=0 := by
    simpa only [hv154,mul_zero,zero_add,add_zero,one_mul] using hp113
  have hv145 : v 145=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp112
  have hv75 : v 75=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp111
  have hv45 : v 45=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp110
  have hv141 : v 141=0 := by
    simpa only [hv72,hv144,mul_zero,zero_add,add_zero,one_mul] using hp109
  have hv65 : v 65=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp108
  have hv135 : v 135=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp107
  have hv27 : v 27=0 := by
    simpa only [hv54,hv132,mul_zero,zero_add,add_zero,one_mul] using hp106
  have hv131 : v 131=0 := by
    simpa only [hv26,hv52,mul_zero,zero_add,add_zero,one_mul] using hp105
  have hv123 : v 123=0 := by
    simpa only [hv72,mul_zero,zero_add,add_zero,one_mul] using hp104
  have hv115 : v 115=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp103
  have hv165 : v 165=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp102
  have hv150 : v 150=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp101
  have hv194 : v 194=0 := by
    simpa only [hv48,mul_zero,zero_add,add_zero,one_mul] using hp100
  have hv63 : v 63=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp99
  have hv16 : v 16=0 := by
    simpa only [hv162,mul_zero,zero_add,add_zero,one_mul] using hp98
  have hv147 : v 147=0 := by
    simpa only [hv63,mul_zero,zero_add,add_zero,one_mul] using hp97
  have hv60 : v 60=0 := by
    simpa only [hv150,mul_zero,zero_add,add_zero,one_mul] using hp96
  have hv126 : v 126=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp95
  have hv68 : v 68=0 := by
    simpa only [hv138,mul_zero,zero_add,add_zero,one_mul] using hp94
  have hv142 : v 142=0 := by
    simpa only [hv72,mul_zero,zero_add,add_zero,one_mul] using hp93
  have hv139 : v 139=0 := by
    simpa only [hv69,mul_zero,zero_add,add_zero,one_mul] using hp92
  have hv71 : v 71=0 := by
    simpa only [hv141,mul_zero,zero_add,add_zero,one_mul] using hp91
  have hv58 : v 58=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp90
  have hv82 : v 82=0 := by
    simpa only [hv152,mul_zero,zero_add,add_zero,one_mul] using hp89
  have hv159 : v 159=0 := by
    simpa only [hv54,mul_zero,zero_add,add_zero,one_mul] using hp88
  have hv53 : v 53=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp87
  have hv157 : v 157=0 := by
    simpa only [hv52,mul_zero,zero_add,add_zero,one_mul] using hp86
  have hv51 : v 51=0 := by
    simpa only [hv156,mul_zero,zero_add,add_zero,one_mul] using hp85
  have hv186 : v 186=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp84
  have hv136 : v 136=0 := by
    simpa only [hv66,mul_zero,zero_add,add_zero,one_mul] using hp83
  have hv74 : v 74=0 := by
    simpa only [hv144,mul_zero,zero_add,add_zero,one_mul] using hp82
  have hv140 : v 140=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp81
  have hv34 : v 34=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp80
  have hv33 : v 33=0 := by
    simpa only [hv186,mul_zero,zero_add,add_zero,one_mul] using hp79
  have hv183 : v 183=0 := by
    simpa only [hv32,mul_zero,zero_add,add_zero,one_mul] using hp78
  have hv178 : v 178=0 := by
    simpa only [hv27,mul_zero,zero_add,add_zero,one_mul] using hp77
  have hv173 : v 173=0 := by
    simpa only [hv72,mul_zero,zero_add,add_zero,one_mul] using hp76
  have hv172 : v 172=0 := by
    simpa only [hv54,mul_zero,zero_add,add_zero,one_mul] using hp75
  have hv171 : v 171=0 := by
    simpa only [hv48,mul_zero,zero_add,add_zero,one_mul] using hp74
  have hv170 : v 170=0 := by
    simpa only [hv45,mul_zero,zero_add,add_zero,one_mul] using hp73
  have hv40 : v 40=0 := by
    simpa only [hv165,mul_zero,zero_add,add_zero,one_mul] using hp72
  have hv39 : v 39=0 := by
    simpa only [hv162,mul_zero,zero_add,add_zero,one_mul] using hp71
  have hv38 : v 38=0 := by
    simpa only [hv156,mul_zero,zero_add,add_zero,one_mul] using hp70
  have hv37 : v 37=0 := by
    simpa only [hv138,mul_zero,zero_add,add_zero,one_mul] using hp69
  have hv177 : v 177=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp68
  have hv176 : v 176=0 := by
    simpa only [hv140,mul_zero,zero_add,add_zero,one_mul] using hp67
  have hv168 : v 168=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp66
  have hv11 : v 11=0 := by
    simpa only [hv138,mul_zero,zero_add,add_zero,one_mul] using hp65
  have hv103 : v 103=0 := by
    simpa only [hv186,mul_zero,zero_add,add_zero,one_mul] using hp64
  have hv101 : v 101=0 := by
    simpa only [hv48,mul_zero,zero_add,add_zero,one_mul] using hp63
  have hv100 : v 100=0 := by
    simpa only [hv168,mul_zero,zero_add,add_zero,one_mul] using hp62
  have hv98 : v 98=0 := by
    simpa only [hv150,mul_zero,zero_add,add_zero,one_mul] using hp61
  have hv93 : v 93=0 := by
    simpa only [hv16,mul_zero,zero_add,add_zero,one_mul] using hp60
  have hv13 : v 13=0 := by
    simpa only [hv66,mul_zero,zero_add,add_zero,one_mul] using hp59
  have hv197 : v 197=0 := by
    simpa only [hv144,mul_zero,zero_add,add_zero,one_mul] using hp58
  have hv120 : v 120=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp57
  have hv117 : v 117=0 := by
    simpa only [hv194,mul_zero,zero_add,add_zero,one_mul] using hp56
  have hv114 : v 114=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp55
  have hv112 : v 112=0 := by
    simpa only [hv60,mul_zero,zero_add,add_zero,one_mul] using hp54
  have hv111 : v 111=0 := by
    simpa only [hv186,mul_zero,zero_add,add_zero,one_mul] using hp53
  have hv109 : v 109=0 := by
    simpa only [hv162,mul_zero,zero_add,add_zero,one_mul] using hp52
  have hv99 : v 99=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp51
  have hv96 : v 96=0 := by
    simpa only [hv140,mul_zero,zero_add,add_zero,one_mul] using hp50
  have hv90 : v 90=0 := by
    simpa only [hv126,mul_zero,zero_add,add_zero,one_mul] using hp49
  have hv199 : v 199=0 := by
    simpa only [hv72,mul_zero,zero_add,add_zero,one_mul] using hp48
  have hv110 : v 110=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp47
  have hv107 : v 107=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp46
  have hv202 : v 202=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp45
  have hv8 : v 8=0 := by
    simpa only [hv186,mul_zero,zero_add,add_zero,one_mul] using hp44
  have hv203 : v 203=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp43
  have hv201 : v 201=0 := by
    simpa only [hv140,mul_zero,zero_add,add_zero,one_mul] using hp42
  have hv200 : v 200=0 := by
    simpa only [hv126,mul_zero,zero_add,add_zero,one_mul] using hp41
  have hv196 : v 196=0 := by
    simpa only [hv90,mul_zero,zero_add,add_zero,one_mul] using hp40
  have hv195 : v 195=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp39
  have hv70 : v 70=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp38
  have hv190 : v 190=0 := by
    simpa only [hv63,mul_zero,zero_add,add_zero,one_mul] using hp37
  have hv189 : v 189=0 := by
    simpa only [hv60,mul_zero,zero_add,add_zero,one_mul] using hp36
  have hv182 : v 182=0 := by
    simpa only [hv45,mul_zero,zero_add,add_zero,one_mul] using hp35
  have hv180 : v 180=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp34
  have hv30 : v 30=0 := by
    simpa only [hv168,mul_zero,zero_add,add_zero,one_mul] using hp33
  have hv28 : v 28=0 := by
    simpa only [hv165,mul_zero,zero_add,add_zero,one_mul] using hp32
  have hv21 : v 21=0 := by
    simpa only [hv150,mul_zero,zero_add,add_zero,one_mul] using hp31
  have hv20 : v 20=0 := by
    simpa only [hv147,mul_zero,zero_add,add_zero,one_mul] using hp30
  have hv18 : v 18=0 := by
    simpa only [hv140,mul_zero,zero_add,add_zero,one_mul] using hp29
  have hv15 : v 15=0 := by
    simpa only [hv126,mul_zero,zero_add,add_zero,one_mul] using hp28
  have hv14 : v 14=0 := by
    simpa only [hv120,mul_zero,zero_add,add_zero,one_mul] using hp27
  have hv10 : v 10=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp26
  have hv9 : v 9=0 := by
    simpa only [hv70,mul_zero,zero_add,add_zero,one_mul] using hp25
  have hv7 : v 7=0 := by
    simpa only [hv30,mul_zero,zero_add,add_zero,one_mul] using hp24
  have hv5 : v 5=0 := by
    simpa only [hv168,mul_zero,zero_add,add_zero,one_mul] using hp23
  have hv205 : v 205=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp22
  have hv36 : v 36=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp21
  have hv175 : v 175=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp20
  have hv35 : v 35=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp19
  have hv174 : v 174=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp18
  have hv104 : v 104=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp17
  have hv108 : v 108=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp16
  have hv106 : v 106=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp15
  have hv198 : v 198=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp14
  have hv12 : v 12=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp13
  have hv4 : v 4=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp12
  have hv206 : v 206=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp11
  have hv105 : v 105=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp10
  have hv102 : v 102=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp9
  have hv209 : v 209=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp8
  have hv208 : v 208=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp7
  have hv6 : v 6=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp6
  have hv3 : v 3=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp5
  have hv2 : v 2=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp4
  have hv1 : v 1=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp3
  have hv204 : v 204=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp2
  have hv207 : v 207=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp1
  have hv0 : v 0=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp0
  funext j
  fin_cases j
  · exact hv0
  · exact hv1
  · exact hv2
  · exact hv3
  · exact hv4
  · exact hv5
  · exact hv6
  · exact hv7
  · exact hv8
  · exact hv9
  · exact hv10
  · exact hv11
  · exact hv12
  · exact hv13
  · exact hv14
  · exact hv15
  · exact hv16
  · exact hv17
  · exact hv18
  · exact hv19
  · exact hv20
  · exact hv21
  · exact hv22
  · exact hv23
  · exact h24
  · exact hv25
  · exact hv26
  · exact hv27
  · exact hv28
  · exact hv29
  · exact hv30
  · exact hv31
  · exact hv32
  · exact hv33
  · exact hv34
  · exact hv35
  · exact hv36
  · exact hv37
  · exact hv38
  · exact hv39
  · exact hv40
  · exact hv41
  · exact h42
  · exact hv43
  · exact hv44
  · exact hv45
  · exact hv46
  · exact hv47
  · exact hv48
  · exact hv49
  · exact hv50
  · exact hv51
  · exact hv52
  · exact hv53
  · exact hv54
  · exact hv55
  · exact hv56
  · exact hv57
  · exact hv58
  · exact hv59
  · exact hv60
  · exact hv61
  · exact hv62
  · exact hv63
  · exact hv64
  · exact hv65
  · exact hv66
  · exact hv67
  · exact hv68
  · exact hv69
  · exact hv70
  · exact hv71
  · exact hv72
  · exact hv73
  · exact hv74
  · exact hv75
  · exact hv76
  · exact hv77
  · exact hv78
  · exact hv79
  · exact hv80
  · exact hv81
  · exact hv82
  · exact hv83
  · exact h84
  · exact hv85
  · exact hv86
  · exact hv87
  · exact hv88
  · exact hv89
  · exact hv90
  · exact hv91
  · exact hv92
  · exact hv93
  · exact hv94
  · exact hv95
  · exact hv96
  · exact hv97
  · exact hv98
  · exact hv99
  · exact hv100
  · exact hv101
  · exact hv102
  · exact hv103
  · exact hv104
  · exact hv105
  · exact hv106
  · exact hv107
  · exact hv108
  · exact hv109
  · exact hv110
  · exact hv111
  · exact hv112
  · exact hv113
  · exact hv114
  · exact hv115
  · exact hv116
  · exact hv117
  · exact hv118
  · exact hv119
  · exact hv120
  · exact hv121
  · exact hv122
  · exact hv123
  · exact hv124
  · exact hv125
  · exact hv126
  · exact hv127
  · exact h128
  · exact hv129
  · exact hv130
  · exact hv131
  · exact hv132
  · exact hv133
  · exact hv134
  · exact hv135
  · exact hv136
  · exact hv137
  · exact hv138
  · exact hv139
  · exact hv140
  · exact hv141
  · exact hv142
  · exact hv143
  · exact hv144
  · exact hv145
  · exact hv146
  · exact hv147
  · exact hv148
  · exact hv149
  · exact hv150
  · exact hv151
  · exact hv152
  · exact hv153
  · exact hv154
  · exact hv155
  · exact hv156
  · exact hv157
  · exact h158
  · exact hv159
  · exact hv160
  · exact hv161
  · exact hv162
  · exact hv163
  · exact hv164
  · exact hv165
  · exact hv166
  · exact hv167
  · exact hv168
  · exact hv169
  · exact hv170
  · exact hv171
  · exact hv172
  · exact hv173
  · exact hv174
  · exact hv175
  · exact hv176
  · exact hv177
  · exact hv178
  · exact hv179
  · exact hv180
  · exact hv181
  · exact hv182
  · exact hv183
  · exact hv184
  · exact hv185
  · exact hv186
  · exact hv187
  · exact hv188
  · exact hv189
  · exact hv190
  · exact hv191
  · exact h192
  · exact hv193
  · exact hv194
  · exact hv195
  · exact hv196
  · exact hv197
  · exact hv198
  · exact hv199
  · exact hv200
  · exact hv201
  · exact hv202
  · exact hv203
  · exact hv204
  · exact hv205
  · exact hv206
  · exact hv207
  · exact hv208
  · exact hv209

#print axioms negative_grid_recovery_kernel
end QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate
end
end

/-! ## ThirtyFiveGridRecoveryPositiveSourcesBundleV4 -/
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

theorem actual_positive_source_6 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 105 + (((-1)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)))*v 206 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord001, source := 105, target := -4
    nonaffine := by norm_num [witnessWord001_matrix]
    denominator := by norm_num [integerDen,witnessWord001_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord001_matrix] }
  have hr : rationalRate witnessWord001 105=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(1:ℤ)*(7:ℚ)^(1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord001_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 105)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord001 105 0 s*v (gridIndex (-4))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord001 105 0 s=wordCoefficient m (u5*u7) witnessWord001 105 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord001 105 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord001)=u5^(1:ℤ)*u7^(1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord001_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord001 105 (-2,2,1,1) hr hcompat s] at hh
  norm_num [witnessWord001_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_6


theorem actual_positive_source_10 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 1 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord002, source := 1, target := -1260
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 1=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 1)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 1 0 s*v (gridIndex (-1260))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 1 0 s=wordCoefficient m (u5*u7) witnessWord002 1 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 1 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 1 (-2,-2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_10


theorem actual_positive_source_14 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 3 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord002, source := 3, target := -420
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 3=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 3)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 3 0 s*v (gridIndex (-420))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 3 0 s=wordCoefficient m (u5*u7) witnessWord002 3 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 3 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 3 (-2,0,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_14


theorem actual_positive_source_24 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    (1)*v 9 + (((-1)*(primeParameter 3 m s)^(2:ℕ))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 70 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord002, source := 9, target := -140
    nonaffine := by norm_num [witnessWord002_matrix]
    denominator := by norm_num [integerDen,witnessWord002_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord002_matrix] }
  have hr : rationalRate witnessWord002 9=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord002_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 9)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord002 9 0 s*v (gridIndex (-140))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord002 9 0 s=wordCoefficient m (u5*u7) witnessWord002 9 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord002 9 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord002)=u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord002_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord002 9 (-2,2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord002_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_24


theorem actual_positive_source_130 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 209 = 0 := by
  let rr : ClosedWordRow := {
    word := witnessWord003, source := 209, target := 1260
    nonaffine := by norm_num [witnessWord003_matrix]
    denominator := by norm_num [integerDen,witnessWord003_matrix]
    closed := by norm_num [integerDen,integerNumer,witnessWord003_matrix] }
  have hr : rationalRate witnessWord003 209=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by
    norm_num [rationalRate,integerDen,witnessWord003_matrix,Matrix.det_fin_two]
  have hh := pole_word_constraint hm hf ε hε hlaw BG G hG hGF s v hv hshift rr
  change v (gridIndex 209)-rationalWordCoefficient m (ε*I^(2*m)) witnessWord003 209 0 s*v (gridIndex (1260))=0 at hh
  have hc : rationalWordCoefficient m (u5*u7) witnessWord003 209 0 s=wordCoefficient m (u5*u7) witnessWord003 209 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord003 209 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord003)=u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord003_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord003 209 (-2,-2,-1,-1) hr hcompat s] at hh
  norm_num [witnessWord003_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_130


theorem actual_positive_source_250 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (u5*u7) witnessWord027 106 0 s=wordCoefficient m (u5*u7) witnessWord027 106 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord027 106 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord027)=u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord027_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord027 106 (0,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord027_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_250

theorem actual_positive_source_256 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (u5*u7) witnessWord028 104 0 s=wordCoefficient m (u5*u7) witnessWord028 104 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord028 104 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord028)=u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord028_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord028 104 (0,0,0,0) hr hcompat s] at hh
  norm_num [witnessWord028_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_256


theorem actual_positive_source_306 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (u5*u7) witnessWord030 66 0 s=wordCoefficient m (u5*u7) witnessWord030 66 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord030 66 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord030)=u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord030 66 (2,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_306


theorem actual_positive_source_322 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (u5*u7) witnessWord030 101 0 s=wordCoefficient m (u5*u7) witnessWord030 101 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord030 101 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord030)=u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord030_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord030 101 (-2,-2,0,0) hr hcompat s] at hh
  norm_num [witnessWord030_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_322


theorem actual_positive_source_402 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
  have hc : rationalWordCoefficient m (u5*u7) witnessWord042 192 0 s=wordCoefficient m (u5*u7) witnessWord042 192 0 s :=
    (wordCoefficient_rational m (u5*u7) witnessWord042 192 0 s).symm
  have hcompat : (u5*u7)^(frickeCount witnessWord042)=u5^(0:ℤ)*u7^(0:ℤ) := by
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num [witnessWord042_count]
  rw [hphase,hc,word_leading_positive_signed_laurent m (u5*u7) u5 u7 witnessWord042 192 (0,2,0,0) hr hcompat s] at hh
  norm_num [witnessWord042_count,fourPrimeMonomial,gridIndex,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_402


theorem actual_positive_source_2792 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 71 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 140 + (1)*v 141 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 3 (1) (-2,0,-1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (1) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2792


theorem actual_positive_source_2794 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 0 + (1)*v 69 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)*(u7*primeParameter 7 m s)))*v 70 + (1)*v 139 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=u5^(-1:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 3 (-1) (-2,0,-1,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-1) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2794

theorem actual_positive_source_2810 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    (1)*v 63 + (((-1)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 90 + (1)*v 133 + (((-1)*(u7*primeParameter 7 m s))/((primeParameter 2 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 160 = 0 := by
  have hroot : root 35 f 3=1 := by simp [root_three,h5,h7]
  have hr : (Nat.lcm 35 (3^2):ℚ)*((-7:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(1:ℤ) := by norm_num
  have hcompat : root 35 f 3*ε*I^(2*m)=u5^(-1:ℤ)*u7^(1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 3 (-7) (-2,0,-1,1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    3 (by decide) (by decide) (-7) 140 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2810


theorem actual_positive_source_2842 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 0 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 42 + (1)*v 43 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 84 + (1)*v 85 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u7*primeParameter 7 m s)))*v 126 + (1)*v 127 + (1)*v 169 = 0 := by
  have hroot : root 35 f 5=u5 := by simp [root_five,h5,h7]
  have hr : (Nat.lcm 35 (5^2):ℚ)*((1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 5*ε*I^(2*m)=u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 5 (1) (-2,-2,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    5 (by decide) (by decide) (1) 252 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2842


theorem actual_positive_source_2934 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 0 + (1)*v 31 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 60 + (1)*v 61 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 90 + (1)*v 91 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 120 + (1)*v 121 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 150 + (1)*v 151 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 180 + (1)*v 181 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)=u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 7 (1) (-2,-2,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (1) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2934


theorem actual_positive_source_2938 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 0 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 30 + (1)*v 32 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 60 + (1)*v 62 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 90 + (1)*v 92 + (1)*v 122 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 150 + (1)*v 152 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 180 + (1)*v 182 = 0 := by
  have hroot : root 35 f 7=u7 := by simp [root_seven,h5,h7]
  have hr : (Nat.lcm 35 (7^2):ℚ)*((2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 7*ε*I^(2*m)=u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 7 (2) (0,-2,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    7 (by decide) (by decide) (2) 180 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_2938


theorem actual_positive_source_3034 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 0 + (1)*v 16 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 30 + (1)*v 46 + (1)*v 76 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 90 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 120 + (1)*v 136 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 150 + (1)*v 166 + ((-1)/((primeParameter 3 m s)^(2:ℕ)*(u5*primeParameter 5 m s)))*v 180 + (1)*v 196 = 0 := by
  have hroot : root 35 f 14=u7 := by simp [root_signed_14,h5,h7]
  have hr : (Nat.lcm 35 (14^2):ℚ)*((1:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(-1:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 14*ε*I^(2*m)=u5^(-1:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 14 (1) (0,-2,-1,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    14 (by decide) (by decide) (1) 45 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_3034


theorem actual_positive_source_3066 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((u7*primeParameter 7 m s)))*v 0 + (1)*v 12 + (1)*v 26 + ((-1)/((u7*primeParameter 7 m s)))*v 28 + ((-1)/((u7*primeParameter 7 m s)))*v 42 + (1)*v 54 + ((-1)/((u7*primeParameter 7 m s)))*v 70 + (1)*v 96 + (1)*v 110 + ((-1)/((u7*primeParameter 7 m s)))*v 112 + ((-1)/((u7*primeParameter 7 m s)))*v 126 + (1)*v 152 + ((-1)/((u7*primeParameter 7 m s)))*v 168 + (1)*v 180 + (1)*v 194 + ((-1)/((u7*primeParameter 7 m s)))*v 196 = 0 := by
  have hroot : root 35 f 15=u5 := by simp [root_signed_15,h5,h7]
  have hr : (Nat.lcm 35 (15^2):ℚ)*((-2:ℚ)/210)^2=(2:ℚ)^(0:ℤ)*(3:ℚ)^(0:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(-1:ℤ) := by norm_num
  have hcompat : root 35 f 15*ε*I^(2*m)=u5^(0:ℤ)*u7^(-1:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 15 (-2) (0,0,0,-1) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    15 (by decide) (by decide) (-2) 28 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_3066

theorem actual_positive_source_3122 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n)) :
    ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 0 + (1)*v 7 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 12 + (1)*v 13 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 18 + (1)*v 19 + (1)*v 25 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 30 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 36 + (1)*v 37 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 42 + (1)*v 49 + (1)*v 55 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 60 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 66 + (1)*v 67 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 72 + (1)*v 73 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 78 + (1)*v 79 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 96 + (1)*v 97 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 102 + (1)*v 103 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 108 + (1)*v 109 + (1)*v 115 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 120 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 126 + (1)*v 133 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 138 + (1)*v 139 + (1)*v 145 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 150 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 156 + (1)*v 157 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 162 + (1)*v 163 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 168 + (1)*v 175 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 180 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 186 + (1)*v 187 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 192 + (1)*v 193 + ((-1)/((primeParameter 2 m s)^(2:ℕ)*(primeParameter 3 m s)^(2:ℕ)))*v 198 + (1)*v 199 + (1)*v 205 = 0 := by
  have hroot : root 35 f 35=u5*u7 := by simp [root_signed_35,h5,h7]
  have hr : (Nat.lcm 35 (35^2):ℚ)*((1:ℚ)/210)^2=(2:ℚ)^(-2:ℤ)*(3:ℚ)^(-2:ℤ)*(5:ℚ)^(0:ℤ)*(7:ℚ)^(0:ℤ) := by norm_num
  have hcompat : root 35 f 35*ε*I^(2*m)=u5^(0:ℤ)*u7^(0:ℤ) := by
    rw [mul_assoc,hphase,hroot]
    rcases hu5 with rfl|rfl <;> rcases hu7 with rfl|rfl <;> norm_num
  have hc := fullTaylorCoefficient_positive_signed_laurent m f ε u5 u7 35 (1) (-2,-2,0,0) hr hcompat s
  have hh := pole_full_taylor hf ε hlaw BG G hG hGF s v hv hshift
    35 (by decide) (by decide) (1) 36 (by decide) (by decide) (by decide)
  rw [hc] at hh
  norm_num [sampleSum,residues,Finset.sum_filter,Finset.sum_range_succ,gridIndex,
    fourPrimeMonomial,_root_.zpow_neg,div_eq_mul_inv] at hh
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  linear_combination (norm := (field_simp [hu5n,hu7n,primeParameter_ne_zero 2 m (by decide) s,primeParameter_ne_zero 3 m (by decide) s,primeParameter_ne_zero 5 m (by decide) s,primeParameter_ne_zero 7 m (by decide) s]; ring)) hh

#print axioms actual_positive_source_3122

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveGridRecoveryBadFive -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open FinitenessRamanujanSum
open scoped Topology

theorem actual_signed_badfive_source_3574 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (u5 : ℂ) (hu5 : u5=1 ∨ u5= -1) (h5 : badFive f= -u5)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    v 11 + v 53 + v 95 + v 137 + v 179 + (1/(u5*primeParameter 5 m s))*v 55=0 := by
  have hp : (5:ℂ)^((m:ℂ)-s)=(primeParameter 5 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 5 (by decide) (by decide) 11
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  change (Real.sqrt 5:ℂ)*f 5= -u5 at h5
  rw [h5] at hh
  rcases hu5 with rfl|rfl <;>
    linear_combination (norm := (field_simp [primeParameter_ne_zero 5 m (by decide) s]; ring)) hh

#print axioms actual_signed_badfive_source_3574

theorem actual_signed_badfive_source_3614 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (u5 : ℂ) (hu5 : u5=1 ∨ u5= -1) (h5 : badFive f= -u5)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v) :
    v 31 + v 73 + v 115 + v 157 + v 199 + (1/(u5*primeParameter 5 m s))*v 155=0 := by
  have hp : (5:ℂ)^((m:ℂ)-s)=(primeParameter 5 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hh := pole_full_hecke hm hf BG G hG hGF s v hv 5 (by decide) (by decide) 31
  norm_num [fullHeckeRow,completeSum,Finset.sum_range_succ,gridIndex,hp] at hh
  change (Real.sqrt 5:ℂ)*f 5= -u5 at h5
  rw [h5] at hh
  rcases hu5 with rfl|rfl <;>
    linear_combination (norm := (field_simp [primeParameter_ne_zero 5 m (by decide) s]; ring)) hh

#print axioms actual_signed_badfive_source_3614
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalNegativeGridRecovery -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology
theorem original_negative_grid_recovery {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (h24 : v 24=0) (h42 : v 42=0) (h84 : v 84=0)
    (h128 : v 128=0) (h158 : v 158=0) (h192 : v 192=0) : v=0 := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate.negative_grid_recovery_kernel
    (primeParameter 2 m s) (primeParameter 3 m s)
    (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v _ h24 h42 h84 h128 h158 h192
  apply QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate.negative_grid_recovery_rows
    (primeParameter 2 m s) (primeParameter 3 m s)
    (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3)
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) v v
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_6 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_10 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_14 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_24 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_34 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_54 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_62 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_130 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_250 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_256 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_268 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_292 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_298 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_304 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_306 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_320 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_322 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_342 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_364 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_368 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_370 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_372 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_374 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_382 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_394 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_398 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_402 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_2790 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2792 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2794 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2796 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2798 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2800 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2802 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2804 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2810 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_2840 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2842 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2844 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2846 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2848 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2854 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2856 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2858 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2860 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_2932 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2934 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2936 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2938 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3006 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3032 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_3034 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3058 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_3060 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_3064 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_3066 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3084 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3110 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_signed_negative_source_3122 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3158 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3206 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3210 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3212 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3216 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3218 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3222 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3224 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3226 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3228 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3230 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3232 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3234 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3236 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3238 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3240 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3242 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3246 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3248 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3250 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3252 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3254 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3256 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3262 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3264 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3274 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3276 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3278 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3284 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3288 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3290 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3292 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3294 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3296 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3298 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3300 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3302 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3304 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3306 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3308 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3310 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3312 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3314 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3316 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3318 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3324 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3326 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3330 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3336 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3338 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3340 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3350 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3354 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3358 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3360 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3362 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3364 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3368 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3374 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3376 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3378 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3380 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3386 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3390 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3392 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3396 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3424 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3426 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3432 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3436 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3444 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3446 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3448 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3450 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3478 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3528 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3530 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3540 hm hf BG G hG hGF s v hv)
  · have hh := actual_signed_badfive_source_3574 hm hf u5 hu5 h5 BG G hG hGF s v hv
    convert hh using 1 <;> ring
  · have hh := actual_signed_badfive_source_3614 hm hf u5 hu5 h5 BG G hG hGF s v hv
    convert hh using 1 <;> ring

#print axioms original_negative_grid_recovery
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveGridRecoveryRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.unusedVariables false
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate

theorem positive_grid_recovery_rows (x y z w a b : ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hw : w≠0)
    (u v : Fin 210 → ℂ)
    (h0 : (1)*v 0 + ((-1)*x^(2:ℕ)*z*w)*v 207 = 0)
    (h2 : (1)*v 0 + ((-1)*z*w)*v 204 = 0)
    (h4 : (((-1)*x^(2:ℕ)*y^(2:ℕ)*w)/(z))*v 205 = 0)
    (h6 : (1)*v 105 + (((-1)*y^(2:ℕ)*z*w)/(x^(2:ℕ)))*v 206 = 0)
    (h8 : (1)*v 0 = 0)
    (h10 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z*w))*v 0 + (1)*v 1 = 0)
    (h12 : ((-1)/(y^(2:ℕ)*z*w))*v 0 + (1)*v 2 = 0)
    (h14 : ((-1)/(x^(2:ℕ)*z*w))*v 0 + (1)*v 3 = 0)
    (h16 : (1)*v 4 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*z*w))*v 105 = 0)
    (h18 : (1)*v 5 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h20 : ((-1)/(z*w))*v 0 + (1)*v 6 = 0)
    (h22 : (1)*v 7 + (((-1)*w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 = 0)
    (h24 : (1)*v 9 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 70 = 0)
    (h26 : (1)*v 10 = 0)
    (h28 : (1)*v 12 + (((-1)*x^(2:ℕ))/(z*w))*v 105 = 0)
    (h30 : (1)*v 14 + (((-1)*w)/(y^(2:ℕ)*z))*v 120 = 0)
    (h32 : (1)*v 15 + (((-1)*z)/(x^(2:ℕ)*w))*v 126 = 0)
    (h34 : (1)*v 18 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0)
    (h36 : (1)*v 20 + (((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 = 0)
    (h38 : (1)*v 21 + (((-1)*w)/(x^(2:ℕ)*z))*v 150 = 0)
    (h40 : (1)*v 28 + (((-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0)
    (h42 : (1)*v 30 + (((-1)*z)/(w))*v 168 = 0)
    (h44 : (1)*v 35 + (((-1)*z*w)/(x^(2:ℕ)*y^(2:ℕ)))*v 174 = 0)
    (h46 : (1)*v 36 + (((-1)*x^(2:ℕ)*y^(2:ℕ))/(z*w))*v 175 = 0)
    (h48 : (((-1)*w)/(z))*v 180 = 0)
    (h50 : (1)*v 45 + (((-1)*y^(2:ℕ)*z)/(x^(2:ℕ)*w))*v 182 = 0)
    (h52 : (1)*v 60 + (((-1)*x^(2:ℕ)*z)/(w))*v 189 = 0)
    (h54 : (1)*v 63 + (((-1)*y^(2:ℕ)*w)/(x^(2:ℕ)*z))*v 190 = 0)
    (h56 : (1)*v 70 = 0)
    (h58 : (((-1)*x^(2:ℕ)*w)/(z))*v 195 = 0)
    (h60 : (1)*v 90 + (((-1)*y^(2:ℕ)*z)/(w))*v 196 = 0)
    (h62 : (1)*v 105 + (((-1)*z*w)/(x^(2:ℕ)))*v 198 = 0)
    (h64 : (1)*v 126 + (((-1)*y^(2:ℕ)*w)/(z))*v 200 = 0)
    (h66 : (1)*v 140 + (((-1)*x^(2:ℕ)*z*w)/(y^(2:ℕ)))*v 201 = 0)
    (h68 : (1)*v 180 + (((-1)*x^(2:ℕ)*y^(2:ℕ)*z)/(w))*v 203 = 0)
    (h128 : ((-1)/(y^(2:ℕ)*z*w))*v 0 + (1)*v 208 = 0)
    (h130 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z*w))*v 0 + (1)*v 209 = 0)
    (h150 : ((-1)*y^(2:ℕ))*v 8 + (1)*v 186 = 0)
    (h162 : (1)*v 202 = 0)
    (h246 : (1)*v 102 + ((-1)*y^(2:ℕ))*v 208 = 0)
    (h248 : ((-1)/(x^(2:ℕ)))*v 0 + (1)*v 105 = 0)
    (h250 : (1)*v 106 + ((-1)/(y^(2:ℕ)))*v 204 = 0)
    (h252 : (1)*v 108 + ((-1)*x^(2:ℕ))*v 207 = 0)
    (h256 : (1)*v 104 + (-1)*v 208 = 0)
    (h262 : (1)*v 107 + ((-1)/(x^(2:ℕ)))*v 202 = 0)
    (h266 : (1)*v 110 + ((-1)*x^(2:ℕ))*v 205 = 0)
    (h268 : (1)*v 72 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 199 = 0)
    (h270 : (1)*v 90 + ((-1)*y^(2:ℕ))*v 200 = 0)
    (h272 : (1)*v 96 + ((-1)*x^(2:ℕ))*v 201 = 0)
    (h274 : (1)*v 99 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 202 = 0)
    (h288 : (1)*v 109 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 = 0)
    (h292 : (1)*v 111 + ((-1)/(x^(2:ℕ)))*v 186 = 0)
    (h294 : (1)*v 112 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 189 = 0)
    (h296 : (1)*v 114 = 0)
    (h298 : (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0)
    (h300 : (1)*v 120 + ((-1)*x^(2:ℕ))*v 195 = 0)
    (h304 : (1)*v 144 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 197 = 0)
    (h306 : ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 13 + (1)*v 66 = 0)
    (h312 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 93 = 0)
    (h316 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 21 + (1)*v 98 = 0)
    (h320 : ((-1)/(y^(2:ℕ)))*v 30 + (1)*v 100 = 0)
    (h322 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 48 + (1)*v 101 = 0)
    (h326 : (1)*v 103 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0)
    (h342 : ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 11 + (1)*v 138 = 0)
    (h358 : (1)*v 168 + ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 203 = 0)
    (h360 : (1)*v 174 + (-1)*v 204 = 0)
    (h362 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 0 + (1)*v 175 = 0)
    (h364 : (1)*v 176 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 201 = 0)
    (h366 : (1)*v 177 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 202 = 0)
    (h368 : ((-1)*x^(2:ℕ)*y^(2:ℕ))*v 37 + (1)*v 138 = 0)
    (h370 : ((-1)*y^(2:ℕ))*v 38 + (1)*v 156 = 0)
    (h372 : ((-1)*x^(2:ℕ))*v 39 + (1)*v 162 = 0)
    (h374 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 40 + (1)*v 165 = 0)
    (h378 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170 = 0)
    (h380 : ((-1)/(x^(2:ℕ)))*v 48 + (1)*v 171 = 0)
    (h382 : ((-1)/(y^(2:ℕ)))*v 54 + (1)*v 172 = 0)
    (h384 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 173 = 0)
    (h394 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 27 + (1)*v 178 = 0)
    (h398 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 183 = 0)
    (h400 : ((-1)*x^(2:ℕ))*v 33 + (1)*v 186 = 0)
    (h402 : ((-1)*y^(2:ℕ))*v 34 = 0)
    (h2790 : (1)*v 70 + (1)*v 140 = 0)
    (h2792 : ((-1)/(x^(2:ℕ)*z*w))*v 0 + (1)*v 71 + ((-1)/(x^(2:ℕ)*z*w))*v 140 + (1)*v 141 = 0)
    (h2794 : ((-1)/(x^(2:ℕ)*z*w))*v 0 + (1)*v 69 + ((-1)/(x^(2:ℕ)*z*w))*v 70 + (1)*v 139 = 0)
    (h2796 : ((-1)/(z*w))*v 0 + ((-1)/(z*w))*v 70 + (1)*v 72 + (1)*v 142 = 0)
    (h2798 : ((-1)/(z*w))*v 0 + (1)*v 68 + (1)*v 138 + ((-1)/(z*w))*v 140 = 0)
    (h2800 : (((-1)*x^(2:ℕ))/(z*w))*v 35 + (1)*v 74 + (((-1)*x^(2:ℕ))/(z*w))*v 105 + (1)*v 144 = 0)
    (h2802 : (1)*v 66 + (((-1)*x^(2:ℕ))/(z*w))*v 105 + (1)*v 136 + (((-1)*x^(2:ℕ))/(z*w))*v 175 = 0)
    (h2804 : (1)*v 75 + (((-1)*z)/(x^(2:ℕ)*w))*v 112 + (1)*v 145 = 0)
    (h2806 : (1)*v 65 + (((-1)*z)/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + (((-1)*z)/(x^(2:ℕ)*w))*v 168 = 0)
    (h2808 : (((-1)*w)/(x^(2:ℕ)*z))*v 50 + (1)*v 77 + (((-1)*w)/(x^(2:ℕ)*z))*v 120 + (1)*v 147 = 0)
    (h2810 : (1)*v 63 + (((-1)*w)/(x^(2:ℕ)*z))*v 90 + (1)*v 133 + (((-1)*w)/(x^(2:ℕ)*z))*v 160 = 0)
    (h2812 : (((-1)*z)/(w))*v 56 + (1)*v 80 + (((-1)*z)/(w))*v 126 + (1)*v 150 = 0)
    (h2814 : (1)*v 60 + (1)*v 130 + (((-1)*z)/(w))*v 154 = 0)
    (h2840 : (1)*v 126 + (1)*v 168 = 0)
    (h2842 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 0 + (1)*v 43 + (1)*v 85 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 127 + (1)*v 169 = 0)
    (h2844 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 0 + (1)*v 41 + (1)*v 83 + (1)*v 125 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 126 + (1)*v 167 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0)
    (h2846 : ((-1)/(y^(2:ℕ)*w))*v 0 + (1)*v 44 + (1)*v 86 + ((-1)/(y^(2:ℕ)*w))*v 126 + ((-1)/(y^(2:ℕ)*w))*v 168 + (1)*v 170 = 0)
    (h2848 : ((-1)/(y^(2:ℕ)*w))*v 0 + (1)*v 40 + (1)*v 82 + (1)*v 124 + (1)*v 166 + ((-1)/(y^(2:ℕ)*w))*v 168 = 0)
    (h2850 : ((-1)/(x^(2:ℕ)*w))*v 0 + (1)*v 45 + (1)*v 87 + (1)*v 129 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 171 = 0)
    (h2854 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 46 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 63 + (1)*v 88 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 105 + (1)*v 130 + (1)*v 172 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0)
    (h2856 : (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 21 + (1)*v 38 + (1)*v 80 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 105 + (1)*v 122 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 147 + (1)*v 164 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)*w))*v 189 = 0)
    (h2858 : ((-1)/(w))*v 0 + (1)*v 48 + (1)*v 90 + ((-1)/(w))*v 126 + (1)*v 132 + (1)*v 174 = 0)
    (h2860 : ((-1)/(w))*v 0 + (1)*v 36 + (1)*v 78 + (1)*v 120 + ((-1)/(w))*v 126 + (1)*v 162 + ((-1)/(w))*v 168 = 0)
    (h2866 : (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 14 + (1)*v 51 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 56 + (1)*v 93 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 98 + (1)*v 135 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 140 + (1)*v 177 = 0)
    (h2868 : (1)*v 33 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 70 + (1)*v 75 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 112 + (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 154 + (1)*v 159 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*w))*v 196 = 0)
    (h2872 : (1)*v 30 + (((-1)*x^(2:ℕ))/(w))*v 63 + (1)*v 72 + (((-1)*x^(2:ℕ))/(w))*v 105 + (1)*v 114 + (((-1)*x^(2:ℕ))/(w))*v 147 + (1)*v 156 + (((-1)*x^(2:ℕ))/(w))*v 189 = 0)
    (h2874 : (1)*v 56 + (((-1)*w)/(y^(2:ℕ)))*v 66 + (1)*v 98 + (((-1)*w)/(y^(2:ℕ)))*v 108 + (1)*v 140 + (((-1)*w)/(y^(2:ℕ)))*v 150 + (1)*v 182 = 0)
    (h2876 : (1)*v 28 + (((-1)*w)/(y^(2:ℕ)))*v 60 + (1)*v 70 + (((-1)*w)/(y^(2:ℕ)))*v 102 + (1)*v 112 + (((-1)*w)/(y^(2:ℕ)))*v 144 + (1)*v 154 + (((-1)*w)/(y^(2:ℕ)))*v 186 = 0)
    (h2932 : (1)*v 30 + (1)*v 60 + (1)*v 90 + (1)*v 120 + (1)*v 150 + (1)*v 180 = 0)
    (h2934 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 0 + (1)*v 31 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 61 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 91 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + (1)*v 121 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 151 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 180 + (1)*v 181 = 0)
    (h2936 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 0 + (1)*v 29 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 + (1)*v 59 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 60 + (1)*v 89 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 90 + (1)*v 119 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 120 + (1)*v 149 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 150 + (1)*v 179 = 0)
    (h2938 : ((-1)/(y^(2:ℕ)*z))*v 0 + ((-1)/(y^(2:ℕ)*z))*v 30 + (1)*v 32 + ((-1)/(y^(2:ℕ)*z))*v 60 + (1)*v 62 + ((-1)/(y^(2:ℕ)*z))*v 90 + (1)*v 92 + (1)*v 122 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 152 + ((-1)/(y^(2:ℕ)*z))*v 180 + (1)*v 182 = 0)
    (h2950 : (1)*v 35 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (1)*v 65 + (1)*v 95 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 114 + (1)*v 125 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 155 + (1)*v 185 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)))*v 204 = 0)
    (h3006 : (1)*v 21 + (1)*v 63 + (1)*v 147 + (1)*v 189 = 0)
    (h3032 : (1)*v 15 + (1)*v 45 + (1)*v 75 + (1)*v 135 + (1)*v 165 + (1)*v 195 = 0)
    (h3034 : ((-1)/(y^(2:ℕ)*z))*v 0 + (1)*v 16 + ((-1)/(y^(2:ℕ)*z))*v 30 + (1)*v 46 + (1)*v 76 + ((-1)/(y^(2:ℕ)*z))*v 90 + ((-1)/(y^(2:ℕ)*z))*v 120 + (1)*v 136 + ((-1)/(y^(2:ℕ)*z))*v 150 + (1)*v 166 + ((-1)/(y^(2:ℕ)*z))*v 180 + (1)*v 196 = 0)
    (h3058 : (1)*v 14 + (1)*v 28 + (1)*v 56 + (1)*v 98 + (1)*v 112 + (1)*v 154 + (1)*v 182 + (1)*v 196 = 0)
    (h3060 : ((-1)/(x^(2:ℕ)*w))*v 0 + (1)*v 15 + ((-1)/(x^(2:ℕ)*w))*v 28 + (1)*v 29 + (1)*v 57 + ((-1)/(x^(2:ℕ)*w))*v 70 + (1)*v 99 + (1)*v 113 + ((-1)/(x^(2:ℕ)*w))*v 126 + ((-1)/(x^(2:ℕ)*w))*v 154 + (1)*v 155 + ((-1)/(x^(2:ℕ)*w))*v 168 + (1)*v 183 + ((-1)/(x^(2:ℕ)*w))*v 196 + (1)*v 197 = 0)
    (h3064 : ((-1)/(w))*v 0 + ((-1)/(w))*v 14 + (1)*v 16 + (1)*v 30 + (1)*v 58 + ((-1)/(w))*v 98 + (1)*v 100 + (1)*v 114 + ((-1)/(w))*v 140 + (1)*v 156 + ((-1)/(w))*v 168 + ((-1)/(w))*v 182 + (1)*v 184 + (1)*v 198 = 0)
    (h3066 : ((-1)/(w))*v 0 + (1)*v 12 + (1)*v 26 + ((-1)/(w))*v 28 + (1)*v 54 + ((-1)/(w))*v 70 + (1)*v 96 + (1)*v 110 + ((-1)/(w))*v 112 + ((-1)/(w))*v 126 + (1)*v 152 + ((-1)/(w))*v 168 + (1)*v 180 + (1)*v 194 + ((-1)/(w))*v 196 = 0)
    (h3084 : (1)*v 10 + (1)*v 20 + (1)*v 40 + (1)*v 50 + (1)*v 80 + (1)*v 100 + (1)*v 110 + (1)*v 130 + (1)*v 160 + (1)*v 170 + (1)*v 190 + (1)*v 200 = 0)
    (h3110 : (1)*v 7 + (1)*v 49 + (1)*v 77 + (1)*v 91 + (1)*v 119 + (1)*v 133 + (1)*v 161 + (1)*v 203 = 0)
    (h3122 : ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 0 + (1)*v 7 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 12 + (1)*v 13 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 18 + (1)*v 19 + (1)*v 25 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 30 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 36 + (1)*v 37 + (1)*v 49 + (1)*v 55 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 60 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 66 + (1)*v 67 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 73 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 78 + (1)*v 79 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 96 + (1)*v 97 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 102 + (1)*v 103 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 108 + (1)*v 109 + (1)*v 115 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 120 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 126 + (1)*v 133 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 + (1)*v 139 + (1)*v 145 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 150 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + (1)*v 157 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 + (1)*v 163 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 168 + (1)*v 175 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 180 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 + (1)*v 187 + (1)*v 193 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 198 + (1)*v 199 + (1)*v 205 = 0)
    (h3158 : (1)*v 5 + (1)*v 25 + (1)*v 55 + (1)*v 65 + (1)*v 85 + (1)*v 95 + (1)*v 115 + (1)*v 125 + (1)*v 145 + (1)*v 155 + (1)*v 185 + (1)*v 205 = 0)
    (h3206 : (1)*v 2 + (((-1)*a)/(x))*v 4 + ((1)/(x^(2:ℕ)))*v 8 + (1)*v 107 = 0)
    (h3210 : (1)*v 4 + (((-1)*a)/(x))*v 8 + ((1)/(x^(2:ℕ)))*v 16 + (1)*v 109 = 0)
    (h3212 : (1)*v 5 + (((-1)*a)/(x))*v 10 + ((1)/(x^(2:ℕ)))*v 20 + (1)*v 110 = 0)
    (h3216 : (1)*v 7 + (((-1)*a)/(x))*v 14 + ((1)/(x^(2:ℕ)))*v 28 + (1)*v 112 = 0)
    (h3218 : (1)*v 8 + (((-1)*a)/(x))*v 16 + ((1)/(x^(2:ℕ)))*v 32 + (1)*v 113 = 0)
    (h3222 : (1)*v 10 + (((-1)*a)/(x))*v 20 + ((1)/(x^(2:ℕ)))*v 40 + (1)*v 115 = 0)
    (h3224 : (1)*v 11 + (((-1)*a)/(x))*v 22 + ((1)/(x^(2:ℕ)))*v 44 + (1)*v 116 = 0)
    (h3226 : (1)*v 12 + ((1)/(x^(2:ℕ)))*v 48 + (1)*v 117 = 0)
    (h3228 : (1)*v 13 + (((-1)*a)/(x))*v 26 + ((1)/(x^(2:ℕ)))*v 52 + (1)*v 118 = 0)
    (h3230 : (1)*v 14 + (((-1)*a)/(x))*v 28 + ((1)/(x^(2:ℕ)))*v 56 + (1)*v 119 = 0)
    (h3232 : (1)*v 15 + (((-1)*a)/(x))*v 30 + ((1)/(x^(2:ℕ)))*v 60 + (1)*v 120 = 0)
    (h3234 : (1)*v 16 + (((-1)*a)/(x))*v 32 + ((1)/(x^(2:ℕ)))*v 64 + (1)*v 121 = 0)
    (h3236 : (1)*v 17 + (((-1)*a)/(x))*v 34 + ((1)/(x^(2:ℕ)))*v 68 + (1)*v 122 = 0)
    (h3238 : (1)*v 18 + (((-1)*a)/(x))*v 36 + ((1)/(x^(2:ℕ)))*v 72 + (1)*v 123 = 0)
    (h3240 : (1)*v 19 + (((-1)*a)/(x))*v 38 + ((1)/(x^(2:ℕ)))*v 76 + (1)*v 124 = 0)
    (h3242 : (1)*v 20 + (((-1)*a)/(x))*v 40 + ((1)/(x^(2:ℕ)))*v 80 + (1)*v 125 = 0)
    (h3246 : (1)*v 22 + (((-1)*a)/(x))*v 44 + ((1)/(x^(2:ℕ)))*v 88 + (1)*v 127 = 0)
    (h3248 : (1)*v 23 + (((-1)*a)/(x))*v 46 + ((1)/(x^(2:ℕ)))*v 92 = 0)
    (h3250 : (((-1)*a)/(x))*v 48 + ((1)/(x^(2:ℕ)))*v 96 + (1)*v 129 = 0)
    (h3252 : (1)*v 25 + (((-1)*a)/(x))*v 50 + ((1)/(x^(2:ℕ)))*v 100 + (1)*v 130 = 0)
    (h3254 : (1)*v 26 + (((-1)*a)/(x))*v 52 + ((1)/(x^(2:ℕ)))*v 104 + (1)*v 131 = 0)
    (h3256 : (1)*v 27 + (((-1)*a)/(x))*v 54 + ((1)/(x^(2:ℕ)))*v 108 + (1)*v 132 = 0)
    (h3262 : (1)*v 30 + (((-1)*a)/(x))*v 60 + ((1)/(x^(2:ℕ)))*v 120 + (1)*v 135 = 0)
    (h3264 : (1)*v 31 + (((-1)*a)/(x))*v 62 + ((1)/(x^(2:ℕ)))*v 124 + (1)*v 136 = 0)
    (h3274 : (1)*v 36 + (((-1)*a)/(x))*v 72 + (1)*v 141 + ((1)/(x^(2:ℕ)))*v 144 = 0)
    (h3276 : (1)*v 37 + (((-1)*a)/(x))*v 74 + (1)*v 142 + ((1)/(x^(2:ℕ)))*v 148 = 0)
    (h3278 : (1)*v 38 + (((-1)*a)/(x))*v 76 + (1)*v 143 + ((1)/(x^(2:ℕ)))*v 152 = 0)
    (h3284 : (1)*v 41 + (((-1)*a)/(x))*v 82 + (1)*v 146 + ((1)/(x^(2:ℕ)))*v 164 = 0)
    (h3288 : (1)*v 43 + (((-1)*a)/(x))*v 86 + (1)*v 148 + ((1)/(x^(2:ℕ)))*v 172 = 0)
    (h3290 : (1)*v 44 + (((-1)*a)/(x))*v 88 + (1)*v 149 + ((1)/(x^(2:ℕ)))*v 176 = 0)
    (h3292 : (1)*v 45 + (((-1)*a)/(x))*v 90 + (1)*v 150 + ((1)/(x^(2:ℕ)))*v 180 = 0)
    (h3294 : (1)*v 46 + (((-1)*a)/(x))*v 92 + (1)*v 151 + ((1)/(x^(2:ℕ)))*v 184 = 0)
    (h3296 : (1)*v 47 + (((-1)*a)/(x))*v 94 + (1)*v 152 + ((1)/(x^(2:ℕ)))*v 188 = 0)
    (h3298 : (1)*v 48 + (((-1)*a)/(x))*v 96 + (1)*v 153 = 0)
    (h3300 : (1)*v 49 + (((-1)*a)/(x))*v 98 + (1)*v 154 + ((1)/(x^(2:ℕ)))*v 196 = 0)
    (h3302 : (1)*v 50 + (((-1)*a)/(x))*v 100 + (1)*v 155 + ((1)/(x^(2:ℕ)))*v 200 = 0)
    (h3304 : (1)*v 51 + (((-1)*a)/(x))*v 102 + (1)*v 156 + ((1)/(x^(2:ℕ)))*v 204 = 0)
    (h3306 : (1)*v 52 + (((-1)*a)/(x))*v 104 + (1)*v 157 + ((1)/(x^(2:ℕ)))*v 208 = 0)
    (h3308 : ((1)/(x^(2:ℕ)))*v 2 + (1)*v 53 + (((-1)*a)/(x))*v 106 = 0)
    (h3310 : ((1)/(x^(2:ℕ)))*v 6 + (1)*v 54 + (((-1)*a)/(x))*v 108 + (1)*v 159 = 0)
    (h3312 : ((1)/(x^(2:ℕ)))*v 10 + (1)*v 55 + (((-1)*a)/(x))*v 110 + (1)*v 160 = 0)
    (h3314 : ((1)/(x^(2:ℕ)))*v 14 + (1)*v 56 + (((-1)*a)/(x))*v 112 + (1)*v 161 = 0)
    (h3316 : ((1)/(x^(2:ℕ)))*v 18 + (1)*v 57 + (((-1)*a)/(x))*v 114 + (1)*v 162 = 0)
    (h3318 : ((1)/(x^(2:ℕ)))*v 22 + (1)*v 58 + (((-1)*a)/(x))*v 116 + (1)*v 163 = 0)
    (h3324 : ((1)/(x^(2:ℕ)))*v 34 + (1)*v 61 + (((-1)*a)/(x))*v 122 + (1)*v 166 = 0)
    (h3326 : ((1)/(x^(2:ℕ)))*v 38 + (1)*v 62 + (((-1)*a)/(x))*v 124 + (1)*v 167 = 0)
    (h3330 : ((1)/(x^(2:ℕ)))*v 46 + (1)*v 64 + (1)*v 169 = 0)
    (h3336 : ((1)/(x^(2:ℕ)))*v 58 + (1)*v 67 + (((-1)*a)/(x))*v 134 + (1)*v 172 = 0)
    (h3338 : ((1)/(x^(2:ℕ)))*v 62 + (1)*v 68 + (((-1)*a)/(x))*v 136 + (1)*v 173 = 0)
    (h3340 : ((1)/(x^(2:ℕ)))*v 66 + (1)*v 69 + (((-1)*a)/(x))*v 138 + (1)*v 174 = 0)
    (h3350 : (1)*v 74 + ((1)/(x^(2:ℕ)))*v 86 + (((-1)*a)/(x))*v 148 + (1)*v 179 = 0)
    (h3354 : (1)*v 76 + ((1)/(x^(2:ℕ)))*v 94 + (((-1)*a)/(x))*v 152 + (1)*v 181 = 0)
    (h3358 : (1)*v 78 + ((1)/(x^(2:ℕ)))*v 102 + (((-1)*a)/(x))*v 156 + (1)*v 183 = 0)
    (h3360 : (1)*v 79 + ((1)/(x^(2:ℕ)))*v 106 + (1)*v 184 = 0)
    (h3362 : (1)*v 80 + ((1)/(x^(2:ℕ)))*v 110 + (((-1)*a)/(x))*v 160 + (1)*v 185 = 0)
    (h3364 : (1)*v 81 + ((1)/(x^(2:ℕ)))*v 114 + (((-1)*a)/(x))*v 162 + (1)*v 186 = 0)
    (h3368 : (1)*v 83 + ((1)/(x^(2:ℕ)))*v 122 + (((-1)*a)/(x))*v 166 + (1)*v 188 = 0)
    (h3374 : (1)*v 86 + ((1)/(x^(2:ℕ)))*v 134 + (((-1)*a)/(x))*v 172 + (1)*v 191 = 0)
    (h3376 : (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 + (((-1)*a)/(x))*v 174 = 0)
    (h3378 : (1)*v 88 + ((1)/(x^(2:ℕ)))*v 142 + (((-1)*a)/(x))*v 176 + (1)*v 193 = 0)
    (h3380 : (1)*v 89 + ((1)/(x^(2:ℕ)))*v 146 + (((-1)*a)/(x))*v 178 + (1)*v 194 = 0)
    (h3386 : (1)*v 92 + (((-1)*a)/(x))*v 184 + (1)*v 197 = 0)
    (h3390 : (1)*v 94 + ((1)/(x^(2:ℕ)))*v 166 + (((-1)*a)/(x))*v 188 + (1)*v 199 = 0)
    (h3392 : (1)*v 95 + ((1)/(x^(2:ℕ)))*v 170 + (((-1)*a)/(x))*v 190 + (1)*v 200 = 0)
    (h3396 : (1)*v 97 + ((1)/(x^(2:ℕ)))*v 178 + (((-1)*a)/(x))*v 194 + (1)*v 202 = 0)
    (h3424 : (1)*v 6 + (((-1)*b)/(y))*v 18 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0)
    (h3426 : (1)*v 7 + (((-1)*b)/(y))*v 21 + ((1)/(y^(2:ℕ)))*v 63 + (1)*v 77 + (1)*v 147 = 0)
    (h3432 : (1)*v 10 + (((-1)*b)/(y))*v 30 + (1)*v 80 + ((1)/(y^(2:ℕ)))*v 90 + (1)*v 150 = 0)
    (h3436 : (1)*v 12 + (((-1)*b)/(y))*v 36 + (1)*v 82 + ((1)/(y^(2:ℕ)))*v 108 + (1)*v 152 = 0)
    (h3444 : (1)*v 16 + (((-1)*b)/(y))*v 48 + (1)*v 86 + ((1)/(y^(2:ℕ)))*v 144 + (1)*v 156 = 0)
    (h3446 : (1)*v 17 + (((-1)*b)/(y))*v 51 + (1)*v 87 + ((1)/(y^(2:ℕ)))*v 153 + (1)*v 157 = 0)
    (h3448 : (1)*v 18 + (((-1)*b)/(y))*v 54 + (1)*v 88 + ((1)/(y^(2:ℕ)))*v 162 = 0)
    (h3450 : (1)*v 19 + (((-1)*b)/(y))*v 57 + (1)*v 89 + (1)*v 159 + ((1)/(y^(2:ℕ)))*v 171 = 0)
    (h3478 : (1)*v 33 + ((1)/(y^(2:ℕ)))*v 87 + (((-1)*b)/(y))*v 99 + (1)*v 103 + (1)*v 173 = 0)
    (h3528 : (1)*v 58 + ((1)/(y^(2:ℕ)))*v 102 + (((-1)*b)/(y))*v 174 + (1)*v 198 = 0)
    (h3530 : (1)*v 59 + ((1)/(y^(2:ℕ)))*v 111 + (1)*v 129 + (((-1)*b)/(y))*v 177 + (1)*v 199 = 0)
    (h3540 : (1)*v 64 + (1)*v 134 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 204 = 0)
    (h3574 : (1)*v 11 + (1)*v 53 + ((1)/(z))*v 55 + (1)*v 95 + (1)*v 137 + (1)*v 179 = 0)
    (h3614 : (1)*v 31 + (1)*v 73 + (1)*v 115 + ((1)/(z))*v 155 + (1)*v 157 + (1)*v 199 = 0)
    : (1)*v 0 = 0 ∧
      (1)*v 207 = 0 ∧
      (1)*v 204 = 0 ∧
      (1)*v 1 = 0 ∧
      (1)*v 2 = 0 ∧
      (1)*v 3 = 0 ∧
      (1)*v 6 = 0 ∧
      (1)*v 208 = 0 ∧
      (1)*v 209 = 0 ∧
      (1)*v 102 = 0 ∧
      (1)*v 105 = 0 ∧
      (1)*v 206 = 0 ∧
      (1)*v 4 = 0 ∧
      (1)*v 12 = 0 ∧
      (1)*v 198 = 0 ∧
      (1)*v 106 = 0 ∧
      (1)*v 108 = 0 ∧
      (1)*v 104 = 0 ∧
      (1)*v 174 = 0 ∧
      (1)*v 35 = 0 ∧
      (1)*v 175 = 0 ∧
      (1)*v 36 = 0 ∧
      (1)*v 205 = 0 ∧
      (1)*v 5 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 ∧
      (1)*v 7 + (((-1)*w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 = 0 ∧
      (1)*v 9 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 70 = 0 ∧
      (1)*v 10 = 0 ∧
      (1)*v 14 + (((-1)*w)/(y^(2:ℕ)*z))*v 120 = 0 ∧
      (1)*v 15 + (((-1)*z)/(x^(2:ℕ)*w))*v 126 = 0 ∧
      (1)*v 18 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0 ∧
      (1)*v 20 + (((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 = 0 ∧
      (1)*v 21 + (((-1)*w)/(x^(2:ℕ)*z))*v 150 = 0 ∧
      (1)*v 28 + (((-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      (1)*v 30 + (((-1)*z)/(w))*v 168 = 0 ∧
      (1)*v 180 = 0 ∧
      (((-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 182 = 0 ∧
      (((-1)*w)/(x^(2:ℕ)*z))*v 60 + (1)*v 189 = 0 ∧
      (((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 190 = 0 ∧
      (1)*v 70 = 0 ∧
      (1)*v 195 = 0 ∧
      (((-1)*w)/(y^(2:ℕ)*z))*v 90 + (1)*v 196 = 0 ∧
      (((-1)*z)/(y^(2:ℕ)*w))*v 126 + (1)*v 200 = 0 ∧
      (((-1)*y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 + (1)*v 201 = 0 ∧
      (1)*v 203 = 0 ∧
      (1)*v 8 + ((-1)/(y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 202 = 0 ∧
      (1)*v 107 = 0 ∧
      (1)*v 110 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 199 = 0 ∧
      (1)*v 90 + (((-1)*z)/(w))*v 126 = 0 ∧
      (1)*v 96 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0 ∧
      (1)*v 99 = 0 ∧
      (1)*v 109 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 111 + ((-1)/(x^(2:ℕ)))*v 186 = 0 ∧
      (((-1)*w)/(y^(2:ℕ)*z))*v 60 + (1)*v 112 = 0 ∧
      (1)*v 114 = 0 ∧
      (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 ∧
      (1)*v 120 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 197 = 0 ∧
      (1)*v 13 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 66 = 0 ∧
      (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 93 = 0 ∧
      (1)*v 98 + (((-1)*w)/(y^(2:ℕ)*z))*v 150 = 0 ∧
      (1)*v 100 + (((-1)*z)/(y^(2:ℕ)*w))*v 168 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 48 + (1)*v 101 = 0 ∧
      (1)*v 103 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 11 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 168 = 0 ∧
      ((-1)/(z*w))*v 140 + (1)*v 176 = 0 ∧
      (1)*v 177 = 0 ∧
      (1)*v 37 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 38 + ((-1)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 39 + ((-1)/(x^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 40 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 165 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 48 + (1)*v 171 = 0 ∧
      ((-1)/(y^(2:ℕ)))*v 54 + (1)*v 172 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 173 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 27 + (1)*v 178 = 0 ∧
      (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 183 = 0 ∧
      (1)*v 33 + ((-1)/(x^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 34 = 0 ∧
      (1)*v 140 = 0 ∧
      (1)*v 74 + (1)*v 144 = 0 ∧
      (1)*v 66 + (1)*v 136 = 0 ∧
      (1)*v 186 = 0 ∧
      (1)*v 51 + (1)*v 156 = 0 ∧
      (1)*v 52 + (1)*v 157 = 0 ∧
      (1)*v 53 = 0 ∧
      (1)*v 54 + (1)*v 159 = 0 ∧
      (1)*v 82 + (1)*v 152 = 0 ∧
      (1)*v 58 = 0 ∧
      (1)*v 71 + (1)*v 141 = 0 ∧
      (1)*v 69 + (1)*v 139 = 0 ∧
      (1)*v 72 + (1)*v 142 = 0 ∧
      (1)*v 68 + (1)*v 138 = 0 ∧
      (1)*v 126 = 0 ∧
      (1)*v 60 + (1)*v 150 = 0 ∧
      (1)*v 63 + (1)*v 147 = 0 ∧
      (1)*v 16 + ((1)/(y^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 63 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 48 + (1)*v 194 = 0 ∧
      (1)*v 150 = 0 ∧
      (1)*v 165 = 0 ∧
      (1)*v 115 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 72 + (1)*v 123 = 0 ∧
      (1)*v 26 + (((-1)*a)/(x))*v 52 + (1)*v 131 = 0 ∧
      (1)*v 27 + (((-1)*a)/(x))*v 54 + (1)*v 132 = 0 ∧
      (1)*v 135 = 0 ∧
      (1)*v 65 = 0 ∧
      (((-1)*a)/(x))*v 72 + (1)*v 141 + ((1)/(x^(2:ℕ)))*v 144 = 0 ∧
      (1)*v 45 = 0 ∧
      (1)*v 75 = 0 ∧
      (1)*v 145 = 0 ∧
      (1)*v 56 + (1)*v 154 = 0 ∧
      (1)*v 48 + (1)*v 153 = 0 ∧
      (1)*v 57 + (1)*v 162 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 66 + (1)*v 69 + (((-1)*a)/(x))*v 138 = 0 ∧
      (1)*v 32 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 78 + (((-1)*x*a)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 79 + (1)*v 184 = 0 ∧
      (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 95 = 0 ∧
      (1)*v 77 = 0 ∧
      (1)*v 50 = 0 ∧
      (1)*v 155 = 0 ∧
      (1)*v 80 = 0 ∧
      (1)*v 154 = 0 ∧
      (1)*v 130 = 0 ∧
      (1)*v 160 = 0 ∧
      (1)*v 133 = 0 ∧
      (1)*v 119 = 0 ∧
      (1)*v 125 = 0 ∧
      (1)*v 25 = 0 ∧
      (1)*v 49 = 0 ∧
      (1)*v 55 = 0 ∧
      (1)*v 161 = 0 ∧
      (1)*v 91 = 0 ∧
      (1)*v 185 = 0 ∧
      (1)*v 85 = 0 ∧
      (1)*v 48 + (1)*v 132 = 0 ∧
      (1)*v 78 + (1)*v 162 = 0 ∧
      (((-1)*a)/(x))*v 22 + ((1)/(x^(2:ℕ)))*v 44 + (1)*v 116 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 ∧
      (((-1)*a)/(x))*v 26 + ((1)/(x^(2:ℕ)))*v 52 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 66 + (1)*v 118 = 0 ∧
      (1)*v 17 + (1)*v 122 + ((-1)/(x^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 19 + ((1)/(x^(2:ℕ)))*v 76 + (1)*v 124 + (((-1)*a)/(x*y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 22 + (((-1)*a)/(x))*v 44 + ((1)/(x^(2:ℕ)))*v 88 + (1)*v 127 = 0 ∧
      (1)*v 23 + (((-1)*a)/(x))*v 46 + ((1)/(x^(2:ℕ)))*v 92 = 0 ∧
      (((-1)*a)/(x))*v 48 + (1)*v 129 = 0 ∧
      (1)*v 31 + (((-1)*a)/(x))*v 62 + (-1)*v 66 + ((1)/(x^(2:ℕ)))*v 124 = 0 ∧
      (((-1)*a)/(x))*v 76 + (1)*v 143 + ((1)/(x^(2:ℕ)))*v 152 + ((1)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 41 + (1)*v 146 + ((a)/(x))*v 152 + ((1)/(x^(2:ℕ)))*v 164 = 0 ∧
      (1)*v 43 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (((-1)*a)/(x))*v 86 + (1)*v 148 = 0 ∧
      (1)*v 44 + (((-1)*a)/(x))*v 88 + (1)*v 149 = 0 ∧
      (1)*v 46 + (((-1)*a)/(x))*v 92 + (1)*v 151 + ((1)/(x^(2:ℕ)))*v 184 = 0 ∧
      (1)*v 47 + (((-1)*a)/(x))*v 94 + (1)*v 152 + ((1)/(x^(2:ℕ)))*v 188 = 0 ∧
      (1)*v 61 + (((-1)*a)/(x))*v 122 + (1)*v 166 = 0 ∧
      (1)*v 62 + (((-1)*a)/(x))*v 124 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + (1)*v 167 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 46 + (1)*v 64 + (1)*v 169 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 54 + (1)*v 67 + (((-1)*a)/(x))*v 134 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 86 + (-1)*v 144 + (((-1)*a)/(x))*v 148 + (1)*v 179 = 0 ∧
      (1)*v 76 + ((1)/(x^(2:ℕ)))*v 94 + (((-1)*a)/(x))*v 152 + (1)*v 181 = 0 ∧
      (1)*v 81 + (((-1)*a)/(x))*v 162 = 0 ∧
      (1)*v 83 + ((1)/(x^(2:ℕ)))*v 122 + (((-1)*a)/(x))*v 166 + (1)*v 188 = 0 ∧
      (((-1)*a)/(x*y^(2:ℕ)))*v 54 + (1)*v 86 + ((1)/(x^(2:ℕ)))*v 134 + (1)*v 191 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 72 + (1)*v 88 + (1)*v 193 = 0 ∧
      (1)*v 92 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (((-1)*a)/(x))*v 184 = 0 ∧
      ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 94 + ((1)/(x^(2:ℕ)))*v 166 + (((-1)*a)/(x))*v 188 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0 ∧
      (-1)*v 72 + (1)*v 138 = 0 ∧
      ((1 + (-1)*x^(2:ℕ)*y^(2:ℕ))/(y^(2:ℕ)))*v 72 + (x*a)*v 144 + (1)*v 148 = 0 ∧
      (1)*v 64 + (1)*v 134 + ((1)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 44 + (1)*v 86 = 0 ∧
      (1)*v 124 + (-1)*v 152 + (1)*v 166 = 0 ∧
      (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 88 = 0 ∧
      (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 ∧
      (1)*v 72 + (1)*v 156 = 0 ∧
      (1)*v 66 = 0 ∧
      (1)*v 144 = 0 ∧
      (1)*v 54 = 0 ∧
      (1)*v 48 = 0 ∧
      (1)*v 72 = 0 ∧
      (1)*v 162 = 0 ∧
      (1)*v 113 = 0 ∧
      (1)*v 29 = 0 ∧
      (1)*v 62 = 0 ∧
      (1)*v 97 = 0 ∧
      (1)*v 59 = 0 ∧
      (1)*v 22 + (-1)*v 134 = 0 ∧
      (-1)*v 76 + (1)*v 188 = 0 ∧
      (1)*v 184 = 0 ∧
      (1)*v 26 + (1)*v 152 = 0 ∧
      (1)*v 121 + ((-1)/(x^(2:ℕ)))*v 134 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 76 + (1)*v 89 = 0 ∧
      (1)*v 44 = 0 ∧
      (1)*v 52 + (1)*v 122 = 0 ∧
      (1)*v 46 = 0 ∧
      (-1)*v 152 + (1)*v 166 = 0 ∧
      (1)*v 137 = 0 ∧
      (-1)*v 52 + (1)*v 73 = 0 ∧
      (1)*v 76 = 0 ∧
      (1)*v 152 = 0 ∧
      (1)*v 52 = 0 ∧
      (1)*v 134 = 0 ∧
      (1)*v 163 = 0 ∧
      (1)*v 187 = 0 := by
  obtain ⟨h14126, h14137, h14139, h14144, h14318, h14319, h14320, h14321, h14326, h14327, h14328, h14329, h14330, h14332, h14333, h14346, h14347, h14348, h14370, h14378, h14380, h14381, h14398, h14618, h14626, h14693, h14703, h14707, h14755, h14780, h14784, h14842, h14861, h14901, h14902, h14922, h15005, h15128, h15130, h15186, h15191, h15192, h15215⟩ := positive_grid_recovery_rows_chunk0 x y z w a b hx hy hz hw u v h0 h2 h8 h10 h12 h14 h20 h128 h130 h246 h248 h250 h252 h256 h360 h362 h2792 h2794 h2796 h2798 h2842 h2844 h2846 h2848 h2850 h2858 h2860 h2934 h2936 h2938 h2950 h3034 h3060 h3064 h3066 h3122 h3206 h3304 h3306 h3308 h3310 h3424 h3540
  obtain ⟨h15235, h15249, h15281, h15308, h15309, h15342, h15433, h15436, h15437, h15439, h15551, h15612, h15648, h15649, h15666, h15717, h15740, h15779, h15848, h15935, h15981, h15982, h16004, h16074, h16085, h16102, h16103, h16104, h16156, h16191, h16192, h16209, h16255, h16282, h16283, h16286, h16336, h16399⟩ := positive_grid_recovery_rows_chunk1 x y z w a b hx hy hz hw u v h6 h16 h28 h44 h62 h2800 h2802 h2854 h2856 h2872 h2874 h2876 h3210 h3226 h3254 h3256 h3340 h3358 h3360 h3376 h3436 h3528 h14137 h14139 h14332 h14380 h14381 h14398 h14626 h14703 h14707 h14780 h14901 h14902 h15128 h15191 h15192 h15215
  obtain ⟨h16404, h16452, h16495, h16553, h16630, h16659, h16661, h16707, h16711, h16853, h16888, h16911, h16941, h16947, h16965, h17030, h17078, h17079, h17080, h17105, h17122, h17128, h17130, h17145, h17146, h17147, h17170, h17201, h17202, h17218, h17248, h17291, h17308, h17309, h17311, h17312, h17343, h17359, h17376⟩ := positive_grid_recovery_rows_chunk2 x y z w a b hx hy hz hw u v h4 h18 h22 h24 h26 h30 h32 h34 h36 h46 h266 h2866 h3032 h3058 h3084 h3110 h3158 h3212 h3216 h3222 h3230 h3232 h3238 h3274 h3312 h3314 h3316 h3426 h3432 h3448 h14144 h14333 h14378 h14755 h15130 h15433 h15848 h16085 h16104 h16336
  obtain ⟨h17377, h17378, h17398, h17400, h17473, h17489, h17498, h17513, h17537, h17543, h17611, h17645, h17666, h17667, h17668, h17670, h17671, h17778, h17779, h17832, h17833, h17847, h17855, h17865, h17885, h18007, h18019, h18023, h18027, h18029, h18073, h18075, h18091, h18092, h18093, h18099⟩ := positive_grid_recovery_rows_chunk3 x y z w a b hx hy hz hw u v h38 h40 h42 h48 h50 h52 h68 h294 h316 h320 h2932 h3006 h3242 h3262 h3292 h14346 h14347 h14348 h14370 h15281 h15436 h15437 h15439 h15717 h16074 h16941 h16947 h17078 h17080 h17128 h17130 h17145 h17146 h17202 h17218 h17291 h17343
  obtain ⟨h18167, h18226, h18270, h18271, h18272, h18276, h18389, h18393, h18422, h18511, h18532, h18536, h18538, h18539, h18555, h18596, h18600, h18647, h18648, h18719, h18723, h18724, h18836, h18840, h18861, h18889, h18925, h18926, h18980, h18983, h18984, h19015, h19041, h19066, h19080, h19114, h19116, h19133, h19134, h19135, h19163⟩ := positive_grid_recovery_rows_chunk4 x y z w a b hx hy hz hw u v h54 h56 h58 h60 h64 h66 h150 h162 h262 h268 h270 h272 h274 h300 h358 h364 h366 h2790 h2868 h3218 h3300 h3302 h3362 h3392 h3396 h14319 h14320 h15648 h15649 h16711 h17079 h17201 h17359 h17376 h17489 h17498 h17645 h17779 h17847 h17855 h18027
  obtain ⟨h19178, h19180, h19189, h19222, h19224, h19230, h19231, h19232, h19233, h19247, h19300, h19301, h19306, h19395, h19449, h19450, h19483, h19502, h19516, h19532, h19548, h19551, h19563, h19601, h19620, h19636, h19639, h19642, h19643, h19659, h19661, h19689, h19717, h19719, h19723, h19749, h19750, h19784, h19792, h19805, h19820⟩ := positive_grid_recovery_rows_chunk5 x y z w a b hx hy hz hw u v h288 h292 h296 h298 h2804 h2810 h3250 h3298 h3364 h3390 h3478 h3530 h3614 h15740 h16255 h16404 h17147 h17309 h17611 h17666 h17671 h17832 h17833 h17865 h17885 h18023 h18029 h18075 h18093 h18276 h18393 h18532 h18536 h18538 h18539 h18555 h18600 h18723 h18925 h18983 h19114 h19163
  obtain ⟨h19849, h19857, h19858, h19859, h19874, h19927, h19928, h19929, h19930, h19931, h20020, h20028, h20033, h20042, h20053, h20062, h20096, h20112, h20113, h20116, h20133, h20159, h20180, h20182, h20199, h20200, h20225, h20246, h20256, h20262, h20271, h20282, h20284, h20291, h20347, h20349, h20350, h20351, h20352, h20353, h20355⟩ := positive_grid_recovery_rows_chunk6 x y z w a b hx hy hz hw u v h304 h306 h312 h322 h326 h342 h2806 h2808 h2840 h3224 h3228 h3252 h3386 h3574 h14327 h14328 h14329 h14330 h16630 h17122 h17400 h17513 h17543 h17667 h17668 h18019 h18647 h18840 h19116 h19230 h19231 h19232 h19247 h19301 h19502 h19516 h19548 h19642 h19659 h19661 h19723 h19820
  obtain ⟨h20356, h20368, h20369, h20370, h20397, h20405, h20406, h20407, h20424, h20437, h20454, h20455, h20456, h20457, h20458, h20460, h20466, h20467, h20624, h20650, h20652, h20670, h20685, h20701, h20727, h20735, h20740, h20754, h20762, h20775, h20776, h20777, h20792, h20842, h20856, h20881, h20882, h20920, h20930, h20940, h20957, h20980, h20989, h21003, h21020, h21028, h21041⟩ := positive_grid_recovery_rows_chunk7 x y z w a b hx hy hz hw u v h368 h370 h372 h374 h378 h380 h382 h3240 h3276 h3278 h3288 h3290 h3326 h3378 h3450 h16888 h17377 h17378 h17670 h18091 h18092 h18648 h18724 h18861 h18984 h19133 h19233 h19306 h19601 h19643 h19717 h19857 h19859 h19874 h19927 h19929 h19930 h20028 h20112 h20180 h20182 h20199 h20200 h20256 h20291 h20351 h20352 h20353
  obtain ⟨h21042, h21043, h21058, h21085, h21107, h21108, h21123, h21133, h21144, h21161, h21230, h21269, h21271, h21293, h21294, h21295, h21300, h21325, h21326, h21341, h21370, h21371, h21373, h21374, h21375, h21378, h21382, h21383, h21504, h21517, h21519, h21529, h21531, h21542, h21544, h21554, h21555, h21556, h21603, h21605, h21607, h21614, h21619, h21708, h21709⟩ := positive_grid_recovery_rows_chunk8 x y z w a b hx hy hz hw u v h384 h394 h398 h400 h402 h3236 h3264 h3324 h3336 h3338 h3350 h3374 h3380 h14318 h14321 h15308 h15309 h16399 h16495 h17308 h17311 h17312 h18270 h18926 h19015 h19066 h19449 h19450 h19551 h19639 h19749 h19750 h19792 h20113 h20262 h20397 h20405 h20406 h20407 h20650 h20652 h20685 h20701 h20735 h20740 h21020
  obtain ⟨h21733, h21739, h21740, h21744, h21751, h21755, h21769, h21780, h21781, h21794, h21805, h21808, h21820, h21821, h21830, h21841, h21852, h21865, h21867, h21877, h21890, h21892, h21902, h21903, h21904, h21907, h21908, h21909, h21911, h21912, h21914, h21923, h21924, h21925, h21926, h21956, h21957, h21965, h21966, h21968, h21974, h21989, h22021, h22023, h22024, h22025⟩ := positive_grid_recovery_rows_chunk9 x y z w a b hx hy hz hw u v h2812 h3284 h3318 h3446 h14326 h15981 h16103 h16192 h16286 h16661 h18271 h18272 h18422 h19180 h19222 h19224 h19300 h19858 h20116 h20133 h20284 h20349 h20350 h20355 h20368 h20369 h20370 h20456 h20460 h20856 h20930 h20940 h21003 h21042 h21133 h21269 h21294 h21295 h21325 h21326 h21341 h21378 h21517 h21531 h21544 h21555 h21708
  obtain ⟨h22035, h22163, h22164, h22165, h22172, h22178, h22179, h22180, h22203, h22220, h22246, h22247, h22249, h22250, h22342, h22347, h22361, h22427, h22428, h22432, h22434, h22450, h22451, h22453, h22473, h22474, h22475, h22478, h22479, h22534, h22535, h22539, h22541, h22596, h22597, h22603, h22619⟩ := positive_grid_recovery_rows_chunk10 x y z w a b hx hy hz hw u v h2814 h3234 h3444 h18099 h19636 h19805 h19849 h19931 h20356 h20454 h20455 h20458 h20466 h20467 h20762 h20881 h20882 h20957 h21028 h21107 h21556 h21603 h21605 h21709 h21808 h21902 h21903 h21914 h21923 h21924 h21925 h21926 h21957 h21965 h21968 h21974 h21989 h22021
  obtain ⟨h22642, h22643, h22645, h22646, h22652, h22654, h22655, h22675, h22679, h22720, h22721, h22728, h22729, h22817, h22818, h22820, h22841, h22842, h22843, h22846, h22872, h22873, h22928, h22933, h22940, h22946, h22971, h22982, h23006, h23007, h23026, h23029, h23039, h23072, h23074, h23078, h23090, h23118⟩ := positive_grid_recovery_rows_chunk11 x y z w a b hx hy hz hw u v h16102 h16191 h16659 h19719 h19928 h20347 h20437 h21108 h21300 h21370 h21740 h21781 h21904 h21956 h21966 h22023 h22024 h22035 h22164 h22165 h22172 h22203 h22220 h22246 h22247 h22249 h22250 h22347 h22361 h22428 h22432 h22434 h22534 h22535 h22541 h22596 h22597 h22603 h22619
  obtain ⟨h23119, h23144, h23227, h23230, h23273, h23291, h23292, h23294, h23295, h23316, h23318, h23335, h23360, h23374, h23385, h23413, h23414, h23418, h23436, h23437, h23457, h23460, h23468, h23469, h23482, h23484, h23493, h23494, h23500, h23504, h23511, h23516, h23529, h23537, h23554, h23555⟩ := positive_grid_recovery_rows_chunk12 x y z w a b hx hy hz hw u v h15982 h16282 h16283 h20424 h20457 h20989 h21144 h21374 h21375 h21614 h21739 h21751 h21769 h21909 h22025 h22180 h22450 h22451 h22474 h22539 h22643 h22645 h22652 h22655 h22679 h22721 h22728 h22841 h22842 h22846 h22872 h22933 h23029 h23039 h23074 h23078 h23118
  obtain ⟨h23574, h23586, h23592, h23595, h23636, h23640, h23641, h23642, h23643, h23656, h23720, h23722, h23764, h23791, h23808, h23826, h23829, h23844, h23845, h23847, h23862, h23880, h23887, h23898, h23905, h23907, h23909, h23916⟩ := positive_grid_recovery_rows_chunk13 x y z w a b hx hy hz hw u v h19134 h19135 h21908 h22179 h22475 h22478 h22479 h22646 h22720 h22729 h22820 h22873 h22940 h23230 h23292 h23294 h23295 h23316 h23318 h23418 h23460 h23494 h23500 h23504 h23516 h23537 h23554 h23555
  obtain ⟨h23934, h23952, h23953, h23970, h23988, h24040, h24041, h24079, h24083, h24093, h24128, h24129, h24169, h24184, h24194, h24219, h24225, h24230, h24233, h24236, h24241, h24252, h24263, h24264, h24278, h24288, h24295, h24299, h24310, h24321, h24332, h24333, h24343, h24354, h24365, h24366, h24376, h24377, h24387, h24388⟩ := positive_grid_recovery_rows_chunk14 x y z w a b hx hy hz hw u v h3246 h3248 h3294 h3296 h3330 h20053 h20282 h20775 h20776 h20777 h21041 h21271 h21371 h21373 h21542 h21619 h21794 h21820 h21890 h21907 h21911 h21912 h22178 h23006 h23007 h23374 h23414 h23436 h23437 h23469 h23482 h23586 h23656 h23791 h23829 h23845 h23847 h23887 h23905 h23907 h23916
  obtain ⟨h24398, h24409, h24420, h24431, h24456, h24467, h24478, h24489, h24491, h24528, h24570, h24590, h24604, h24605, h24662, h24663, h24719, h24758, h24777, h24792, h24816, h24822, h24839, h24840, h24843, h24863, h24868, h24886, h24887, h24890, h24894⟩ := positive_grid_recovery_rows_chunk15 x y z w a b hx hy hz hw u v h3354 h3368 h14784 h19178 h20033 h21043 h21382 h21519 h21607 h21821 h21865 h21867 h21892 h22453 h22818 h23119 h23484 h23722 h23909 h24040 h24083 h24129 h24184 h24233 h24236 h24264 h24295 h24333 h24366 h24377 h24388
  obtain ⟨h24930, h24964, h24966, h24991, h25040, h25041, h25117, h25131, h25140, h25172, h25184, h25225, h25229, h25231, h25251, h25303, h25352, h25353, h25359, h25428, h25488, h25516, h25560, h25561, h25565, h25566, h25567, h25580, h25631, h25632⟩ := positive_grid_recovery_rows_chunk16 x y z w a b hx hy hz hw u v h21383 h22654 h22675 h22843 h23144 h23595 h23640 h23641 h23642 h23643 h23953 h24041 h24093 h24128 h24225 h24278 h24491 h24590 h24605 h24663 h24777 h24816 h24822 h24840 h24843 h24863 h24868 h24886 h24887 h24890 h24894
  obtain ⟨h25758, h25783, h25878, h25900, h25956, h25957, h25958, h26021, h26032, h26043, h26068, h26082, h26093, h26094, h26104, h26135, h26159, h26227, h26228, h26229, h26239, h26292, h26347⟩ := positive_grid_recovery_rows_chunk17 x y z w a b hx hy hz hw u v h24662 h24966 h24991 h25040 h25041 h25131 h25140 h25172 h25184 h25229 h25231 h25251 h25303 h25353 h25359 h25428 h25516 h25561 h25565 h25566 h25567 h25580 h25631 h25632
  obtain ⟨h26358, h26369, h26434, h26481, h26533, h26606, h26617, h26628, h26722, h26821, h26903, h26989, h27000⟩ := positive_grid_recovery_rows_chunk18 x y z w a b hx hy hz hw u v h25560 h25758 h25783 h25900 h25956 h25957 h25958 h26068 h26094 h26135 h26228 h26229 h26239 h26347
  exact ⟨h14126, h14618, h14693, h14842, h14861, h14922, h15005, h15186, h15235, h15249, h15342, h15551, h15612, h15666, h15779, h15935, h16004, h16156, h16209, h16336, h16452, h16553, h16707, h16853, h16911, h16965, h17030, h17105, h17170, h17248, h17343, h17398, h17473, h17537, h17778, h18007, h18073, h18167, h18226, h18389, h18511, h18596, h18719, h18836, h18889, h18980, h19041, h19080, h19163, h19189, h19395, h19483, h19532, h19563, h19620, h19689, h19784, h19820, h20020, h20042, h20062, h20096, h20159, h20225, h20246, h20271, h20291, h20624, h20670, h20727, h20754, h20792, h20842, h20920, h20980, h21020, h21058, h21085, h21123, h21161, h21230, h21293, h21504, h21529, h21554, h21708, h21733, h21744, h21755, h21780, h21805, h21830, h21841, h21852, h21877, h21902, h22163, h22342, h22427, h22473, h22596, h22642, h22817, h22928, h22946, h22971, h22982, h23026, h23072, h23090, h23118, h23227, h23273, h23291, h23335, h23360, h23385, h23413, h23457, h23468, h23493, h23511, h23529, h23574, h23592, h23636, h23720, h23764, h23808, h23826, h23844, h23862, h23880, h23898, h23916, h23934, h23952, h23970, h23988, h24079, h24169, h24194, h24219, h24230, h24241, h24252, h24263, h24288, h24299, h24310, h24321, h24332, h24343, h24354, h24365, h24376, h24387, h24398, h24409, h24420, h24431, h24456, h24467, h24478, h24489, h24528, h24570, h24604, h24719, h24758, h24792, h24839, h24886, h24930, h24964, h25117, h25225, h25352, h25488, h25631, h25878, h26021, h26032, h26043, h26082, h26093, h26104, h26159, h26227, h26292, h26347, h26358, h26369, h26434, h26481, h26533, h26606, h26617, h26628, h26722, h26821, h26903, h26989, h27000⟩

#print axioms positive_grid_recovery_rows

end QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate
end
end

/-! ## ThirtyFivePositiveGridRecoveryKernel -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate

def positiveGridRecoveryConclusion (x y z w a b : ℂ) (v : Fin 210 → ℂ) : Prop :=
(1)*v 0 = 0 ∧
      (1)*v 207 = 0 ∧
      (1)*v 204 = 0 ∧
      (1)*v 1 = 0 ∧
      (1)*v 2 = 0 ∧
      (1)*v 3 = 0 ∧
      (1)*v 6 = 0 ∧
      (1)*v 208 = 0 ∧
      (1)*v 209 = 0 ∧
      (1)*v 102 = 0 ∧
      (1)*v 105 = 0 ∧
      (1)*v 206 = 0 ∧
      (1)*v 4 = 0 ∧
      (1)*v 12 = 0 ∧
      (1)*v 198 = 0 ∧
      (1)*v 106 = 0 ∧
      (1)*v 108 = 0 ∧
      (1)*v 104 = 0 ∧
      (1)*v 174 = 0 ∧
      (1)*v 35 = 0 ∧
      (1)*v 175 = 0 ∧
      (1)*v 36 = 0 ∧
      (1)*v 205 = 0 ∧
      (1)*v 5 + (((-1)*z)/(x^(2:ℕ)*y^(2:ℕ)*w))*v 168 = 0 ∧
      (1)*v 7 + (((-1)*w)/(x^(2:ℕ)*y^(2:ℕ)*z))*v 30 = 0 ∧
      (1)*v 9 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 70 = 0 ∧
      (1)*v 10 = 0 ∧
      (1)*v 14 + (((-1)*w)/(y^(2:ℕ)*z))*v 120 = 0 ∧
      (1)*v 15 + (((-1)*z)/(x^(2:ℕ)*w))*v 126 = 0 ∧
      (1)*v 18 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0 ∧
      (1)*v 20 + (((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 147 = 0 ∧
      (1)*v 21 + (((-1)*w)/(x^(2:ℕ)*z))*v 150 = 0 ∧
      (1)*v 28 + (((-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 165 = 0 ∧
      (1)*v 30 + (((-1)*z)/(w))*v 168 = 0 ∧
      (1)*v 180 = 0 ∧
      (((-1)*x^(2:ℕ)*w)/(y^(2:ℕ)*z))*v 45 + (1)*v 182 = 0 ∧
      (((-1)*w)/(x^(2:ℕ)*z))*v 60 + (1)*v 189 = 0 ∧
      (((-1)*x^(2:ℕ)*z)/(y^(2:ℕ)*w))*v 63 + (1)*v 190 = 0 ∧
      (1)*v 70 = 0 ∧
      (1)*v 195 = 0 ∧
      (((-1)*w)/(y^(2:ℕ)*z))*v 90 + (1)*v 196 = 0 ∧
      (((-1)*z)/(y^(2:ℕ)*w))*v 126 + (1)*v 200 = 0 ∧
      (((-1)*y^(2:ℕ))/(x^(2:ℕ)*z*w))*v 140 + (1)*v 201 = 0 ∧
      (1)*v 203 = 0 ∧
      (1)*v 8 + ((-1)/(y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 202 = 0 ∧
      (1)*v 107 = 0 ∧
      (1)*v 110 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 199 = 0 ∧
      (1)*v 90 + (((-1)*z)/(w))*v 126 = 0 ∧
      (1)*v 96 + (((-1)*y^(2:ℕ))/(z*w))*v 140 = 0 ∧
      (1)*v 99 = 0 ∧
      (1)*v 109 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 111 + ((-1)/(x^(2:ℕ)))*v 186 = 0 ∧
      (((-1)*w)/(y^(2:ℕ)*z))*v 60 + (1)*v 112 = 0 ∧
      (1)*v 114 = 0 ∧
      (1)*v 117 + (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 194 = 0 ∧
      (1)*v 120 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (1)*v 197 = 0 ∧
      (1)*v 13 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 66 = 0 ∧
      (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 16 + (1)*v 93 = 0 ∧
      (1)*v 98 + (((-1)*w)/(y^(2:ℕ)*z))*v 150 = 0 ∧
      (1)*v 100 + (((-1)*z)/(y^(2:ℕ)*w))*v 168 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 48 + (1)*v 101 = 0 ∧
      (1)*v 103 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 11 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 168 = 0 ∧
      ((-1)/(z*w))*v 140 + (1)*v 176 = 0 ∧
      (1)*v 177 = 0 ∧
      (1)*v 37 + ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 38 + ((-1)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 39 + ((-1)/(x^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 40 + (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 165 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 45 + (1)*v 170 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 48 + (1)*v 171 = 0 ∧
      ((-1)/(y^(2:ℕ)))*v 54 + (1)*v 172 = 0 ∧
      ((-1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 173 = 0 ∧
      (((-1)*x^(2:ℕ))/(y^(2:ℕ)))*v 27 + (1)*v 178 = 0 ∧
      (((-1)*y^(2:ℕ))/(x^(2:ℕ)))*v 32 + (1)*v 183 = 0 ∧
      (1)*v 33 + ((-1)/(x^(2:ℕ)))*v 186 = 0 ∧
      (1)*v 34 = 0 ∧
      (1)*v 140 = 0 ∧
      (1)*v 74 + (1)*v 144 = 0 ∧
      (1)*v 66 + (1)*v 136 = 0 ∧
      (1)*v 186 = 0 ∧
      (1)*v 51 + (1)*v 156 = 0 ∧
      (1)*v 52 + (1)*v 157 = 0 ∧
      (1)*v 53 = 0 ∧
      (1)*v 54 + (1)*v 159 = 0 ∧
      (1)*v 82 + (1)*v 152 = 0 ∧
      (1)*v 58 = 0 ∧
      (1)*v 71 + (1)*v 141 = 0 ∧
      (1)*v 69 + (1)*v 139 = 0 ∧
      (1)*v 72 + (1)*v 142 = 0 ∧
      (1)*v 68 + (1)*v 138 = 0 ∧
      (1)*v 126 = 0 ∧
      (1)*v 60 + (1)*v 150 = 0 ∧
      (1)*v 63 + (1)*v 147 = 0 ∧
      (1)*v 16 + ((1)/(y^(2:ℕ)))*v 162 = 0 ∧
      (1)*v 63 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 48 + (1)*v 194 = 0 ∧
      (1)*v 150 = 0 ∧
      (1)*v 165 = 0 ∧
      (1)*v 115 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 72 + (1)*v 123 = 0 ∧
      (1)*v 26 + (((-1)*a)/(x))*v 52 + (1)*v 131 = 0 ∧
      (1)*v 27 + (((-1)*a)/(x))*v 54 + (1)*v 132 = 0 ∧
      (1)*v 135 = 0 ∧
      (1)*v 65 = 0 ∧
      (((-1)*a)/(x))*v 72 + (1)*v 141 + ((1)/(x^(2:ℕ)))*v 144 = 0 ∧
      (1)*v 45 = 0 ∧
      (1)*v 75 = 0 ∧
      (1)*v 145 = 0 ∧
      (1)*v 56 + (1)*v 154 = 0 ∧
      (1)*v 48 + (1)*v 153 = 0 ∧
      (1)*v 57 + (1)*v 162 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 66 + (1)*v 69 + (((-1)*a)/(x))*v 138 = 0 ∧
      (1)*v 32 + ((x^(2:ℕ))/(y^(2:ℕ)))*v 78 + (((-1)*x*a)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 79 + (1)*v 184 = 0 ∧
      (1)*v 87 + ((1)/(x^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 95 = 0 ∧
      (1)*v 77 = 0 ∧
      (1)*v 50 = 0 ∧
      (1)*v 155 = 0 ∧
      (1)*v 80 = 0 ∧
      (1)*v 154 = 0 ∧
      (1)*v 130 = 0 ∧
      (1)*v 160 = 0 ∧
      (1)*v 133 = 0 ∧
      (1)*v 119 = 0 ∧
      (1)*v 125 = 0 ∧
      (1)*v 25 = 0 ∧
      (1)*v 49 = 0 ∧
      (1)*v 55 = 0 ∧
      (1)*v 161 = 0 ∧
      (1)*v 91 = 0 ∧
      (1)*v 185 = 0 ∧
      (1)*v 85 = 0 ∧
      (1)*v 48 + (1)*v 132 = 0 ∧
      (1)*v 78 + (1)*v 162 = 0 ∧
      (((-1)*a)/(x))*v 22 + ((1)/(x^(2:ℕ)))*v 44 + (1)*v 116 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 138 = 0 ∧
      (((-1)*a)/(x))*v 26 + ((1)/(x^(2:ℕ)))*v 52 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 66 + (1)*v 118 = 0 ∧
      (1)*v 17 + (1)*v 122 + ((-1)/(x^(2:ℕ)))*v 138 = 0 ∧
      (1)*v 19 + ((1)/(x^(2:ℕ)))*v 76 + (1)*v 124 + (((-1)*a)/(x*y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 22 + (((-1)*a)/(x))*v 44 + ((1)/(x^(2:ℕ)))*v 88 + (1)*v 127 = 0 ∧
      (1)*v 23 + (((-1)*a)/(x))*v 46 + ((1)/(x^(2:ℕ)))*v 92 = 0 ∧
      (((-1)*a)/(x))*v 48 + (1)*v 129 = 0 ∧
      (1)*v 31 + (((-1)*a)/(x))*v 62 + (-1)*v 66 + ((1)/(x^(2:ℕ)))*v 124 = 0 ∧
      (((-1)*a)/(x))*v 76 + (1)*v 143 + ((1)/(x^(2:ℕ)))*v 152 + ((1)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 41 + (1)*v 146 + ((a)/(x))*v 152 + ((1)/(x^(2:ℕ)))*v 164 = 0 ∧
      (1)*v 43 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 54 + (((-1)*a)/(x))*v 86 + (1)*v 148 = 0 ∧
      (1)*v 44 + (((-1)*a)/(x))*v 88 + (1)*v 149 = 0 ∧
      (1)*v 46 + (((-1)*a)/(x))*v 92 + (1)*v 151 + ((1)/(x^(2:ℕ)))*v 184 = 0 ∧
      (1)*v 47 + (((-1)*a)/(x))*v 94 + (1)*v 152 + ((1)/(x^(2:ℕ)))*v 188 = 0 ∧
      (1)*v 61 + (((-1)*a)/(x))*v 122 + (1)*v 166 = 0 ∧
      (1)*v 62 + (((-1)*a)/(x))*v 124 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 156 + (1)*v 167 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 46 + (1)*v 64 + (1)*v 169 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 54 + (1)*v 67 + (((-1)*a)/(x))*v 134 = 0 ∧
      ((1)/(x^(2:ℕ)))*v 86 + (-1)*v 144 + (((-1)*a)/(x))*v 148 + (1)*v 179 = 0 ∧
      (1)*v 76 + ((1)/(x^(2:ℕ)))*v 94 + (((-1)*a)/(x))*v 152 + (1)*v 181 = 0 ∧
      (1)*v 81 + (((-1)*a)/(x))*v 162 = 0 ∧
      (1)*v 83 + ((1)/(x^(2:ℕ)))*v 122 + (((-1)*a)/(x))*v 166 + (1)*v 188 = 0 ∧
      (((-1)*a)/(x*y^(2:ℕ)))*v 54 + (1)*v 86 + ((1)/(x^(2:ℕ)))*v 134 + (1)*v 191 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 72 + (1)*v 88 + (1)*v 193 = 0 ∧
      (1)*v 92 + ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 144 + (((-1)*a)/(x))*v 184 = 0 ∧
      ((1)/(x^(2:ℕ)*y^(2:ℕ)))*v 72 + (1)*v 94 + ((1)/(x^(2:ℕ)))*v 166 + (((-1)*a)/(x))*v 188 = 0 ∧
      ((1)/(y^(2:ℕ)))*v 54 + (1)*v 76 + (1)*v 146 = 0 ∧
      (-1)*v 72 + (1)*v 138 = 0 ∧
      ((1 + (-1)*x^(2:ℕ)*y^(2:ℕ))/(y^(2:ℕ)))*v 72 + (x*a)*v 144 + (1)*v 148 = 0 ∧
      (1)*v 64 + (1)*v 134 + ((1)/(y^(2:ℕ)))*v 156 = 0 ∧
      (1)*v 44 + (1)*v 86 = 0 ∧
      (1)*v 124 + (-1)*v 152 + (1)*v 166 = 0 ∧
      (1)*v 46 + ((1)/(y^(2:ℕ)))*v 54 + (1)*v 88 = 0 ∧
      (1)*v 122 + ((1)/(y^(2:ℕ)))*v 156 + (1)*v 164 = 0 ∧
      (1)*v 72 + (1)*v 156 = 0 ∧
      (1)*v 66 = 0 ∧
      (1)*v 144 = 0 ∧
      (1)*v 54 = 0 ∧
      (1)*v 48 = 0 ∧
      (1)*v 72 = 0 ∧
      (1)*v 162 = 0 ∧
      (1)*v 113 = 0 ∧
      (1)*v 29 = 0 ∧
      (1)*v 62 = 0 ∧
      (1)*v 97 = 0 ∧
      (1)*v 59 = 0 ∧
      (1)*v 22 + (-1)*v 134 = 0 ∧
      (-1)*v 76 + (1)*v 188 = 0 ∧
      (1)*v 184 = 0 ∧
      (1)*v 26 + (1)*v 152 = 0 ∧
      (1)*v 121 + ((-1)/(x^(2:ℕ)))*v 134 = 0 ∧
      ((-1)/(x^(2:ℕ)))*v 76 + (1)*v 89 = 0 ∧
      (1)*v 44 = 0 ∧
      (1)*v 52 + (1)*v 122 = 0 ∧
      (1)*v 46 = 0 ∧
      (-1)*v 152 + (1)*v 166 = 0 ∧
      (1)*v 137 = 0 ∧
      (-1)*v 52 + (1)*v 73 = 0 ∧
      (1)*v 76 = 0 ∧
      (1)*v 152 = 0 ∧
      (1)*v 52 = 0 ∧
      (1)*v 134 = 0 ∧
      (1)*v 163 = 0 ∧
      (1)*v 187 = 0

theorem positive_grid_recovery_kernel (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (h : positiveGridRecoveryConclusion x y z w a b v)
    (h24 : v 24=0) (h42 : v 42=0) (h84 : v 84=0)
    (h128 : v 128=0) (h158 : v 158=0) (h192 : v 192=0) : v=0 := by
  obtain ⟨hp0,hp1,hp2,hp3,hp4,hp5,hp6,hp7,hp8,hp9,hp10,hp11,hp12,hp13,hp14,hp15,hp16,hp17,hp18,hp19,hp20,hp21,hp22,hp23,hp24,hp25,hp26,hp27,hp28,hp29,hp30,hp31,hp32,hp33,hp34,hp35,hp36,hp37,hp38,hp39,hp40,hp41,hp42,hp43,hp44,hp45,hp46,hp47,hp48,hp49,hp50,hp51,hp52,hp53,hp54,hp55,hp56,hp57,hp58,hp59,hp60,hp61,hp62,hp63,hp64,hp65,hp66,hp67,hp68,hp69,hp70,hp71,hp72,hp73,hp74,hp75,hp76,hp77,hp78,hp79,hp80,hp81,hp82,hp83,hp84,hp85,hp86,hp87,hp88,hp89,hp90,hp91,hp92,hp93,hp94,hp95,hp96,hp97,hp98,hp99,hp100,hp101,hp102,hp103,hp104,hp105,hp106,hp107,hp108,hp109,hp110,hp111,hp112,hp113,hp114,hp115,hp116,hp117,hp118,hp119,hp120,hp121,hp122,hp123,hp124,hp125,hp126,hp127,hp128,hp129,hp130,hp131,hp132,hp133,hp134,hp135,hp136,hp137,hp138,hp139,hp140,hp141,hp142,hp143,hp144,hp145,hp146,hp147,hp148,hp149,hp150,hp151,hp152,hp153,hp154,hp155,hp156,hp157,hp158,hp159,hp160,hp161,hp162,hp163,hp164,hp165,hp166,hp167,hp168,hp169,hp170,hp171,hp172,hp173,hp174,hp175,hp176,hp177,hp178,hp179,hp180,hp181,hp182,hp183,hp184,hp185,hp186,hp187,hp188,hp189,hp190,hp191,hp192,hp193,hp194,hp195,hp196,hp197,hp198,hp199,hp200,hp201,hp202,hp203⟩ := h
  have hv187 : v 187=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp203
  have hv163 : v 163=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp202
  have hv134 : v 134=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp201
  have hv52 : v 52=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp200
  have hv152 : v 152=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp199
  have hv76 : v 76=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp198
  have hv73 : v 73=0 := by
    simpa only [hv52,mul_zero,zero_add,add_zero,one_mul] using hp197
  have hv137 : v 137=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp196
  have hv166 : v 166=0 := by
    simpa only [hv152,mul_zero,zero_add,add_zero,one_mul] using hp195
  have hv46 : v 46=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp194
  have hv122 : v 122=0 := by
    simpa only [hv52,mul_zero,zero_add,add_zero,one_mul] using hp193
  have hv44 : v 44=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp192
  have hv89 : v 89=0 := by
    simpa only [hv76,mul_zero,zero_add,add_zero,one_mul] using hp191
  have hv121 : v 121=0 := by
    simpa only [hv134,mul_zero,zero_add,add_zero,one_mul] using hp190
  have hv26 : v 26=0 := by
    simpa only [hv152,mul_zero,zero_add,add_zero,one_mul] using hp189
  have hv184 : v 184=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp188
  have hv188 : v 188=0 := by
    simpa only [hv76,mul_zero,zero_add,add_zero,one_mul] using hp187
  have hv22 : v 22=0 := by
    simpa only [hv134,mul_zero,zero_add,add_zero,one_mul] using hp186
  have hv59 : v 59=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp185
  have hv97 : v 97=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp184
  have hv62 : v 62=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp183
  have hv29 : v 29=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp182
  have hv113 : v 113=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp181
  have hv162 : v 162=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp180
  have hv72 : v 72=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp179
  have hv48 : v 48=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp178
  have hv54 : v 54=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp177
  have hv144 : v 144=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp176
  have hv66 : v 66=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp175
  have hv156 : v 156=0 := by
    simpa only [hv72,mul_zero,zero_add,add_zero,one_mul] using hp174
  have hv164 : v 164=0 := by
    simpa only [hv122,hv156,mul_zero,zero_add,add_zero,one_mul] using hp173
  have hv88 : v 88=0 := by
    simpa only [hv46,hv54,mul_zero,zero_add,add_zero,one_mul] using hp172
  have hv124 : v 124=0 := by
    simpa only [hv152,hv166,mul_zero,zero_add,add_zero,one_mul] using hp171
  have hv86 : v 86=0 := by
    simpa only [hv44,mul_zero,zero_add,add_zero,one_mul] using hp170
  have hv64 : v 64=0 := by
    simpa only [hv134,hv156,mul_zero,zero_add,add_zero,one_mul] using hp169
  have hv148 : v 148=0 := by
    simpa only [hv72,hv144,mul_zero,zero_add,add_zero,one_mul] using hp168
  have hv138 : v 138=0 := by
    simpa only [hv72,mul_zero,zero_add,add_zero,one_mul] using hp167
  have hv146 : v 146=0 := by
    simpa only [hv54,hv76,mul_zero,zero_add,add_zero,one_mul] using hp166
  have hv94 : v 94=0 := by
    simpa only [hv72,hv166,hv188,mul_zero,zero_add,add_zero,one_mul] using hp165
  have hv92 : v 92=0 := by
    simpa only [hv144,hv184,mul_zero,zero_add,add_zero,one_mul] using hp164
  have hv193 : v 193=0 := by
    simpa only [hv72,hv88,mul_zero,zero_add,add_zero,one_mul] using hp163
  have hv191 : v 191=0 := by
    simpa only [hv54,hv86,hv134,mul_zero,zero_add,add_zero,one_mul] using hp162
  have hv83 : v 83=0 := by
    simpa only [hv122,hv166,hv188,mul_zero,zero_add,add_zero,one_mul] using hp161
  have hv81 : v 81=0 := by
    simpa only [hv162,mul_zero,zero_add,add_zero,one_mul] using hp160
  have hv181 : v 181=0 := by
    simpa only [hv76,hv94,hv152,mul_zero,zero_add,add_zero,one_mul] using hp159
  have hv179 : v 179=0 := by
    simpa only [hv86,hv144,hv148,mul_zero,zero_add,add_zero,one_mul] using hp158
  have hv67 : v 67=0 := by
    simpa only [hv54,hv134,mul_zero,zero_add,add_zero,one_mul] using hp157
  have hv169 : v 169=0 := by
    simpa only [hv46,hv64,mul_zero,zero_add,add_zero,one_mul] using hp156
  have hv167 : v 167=0 := by
    simpa only [hv62,hv124,hv156,mul_zero,zero_add,add_zero,one_mul] using hp155
  have hv61 : v 61=0 := by
    simpa only [hv122,hv166,mul_zero,zero_add,add_zero,one_mul] using hp154
  have hv47 : v 47=0 := by
    simpa only [hv94,hv152,hv188,mul_zero,zero_add,add_zero,one_mul] using hp153
  have hv151 : v 151=0 := by
    simpa only [hv46,hv92,hv184,mul_zero,zero_add,add_zero,one_mul] using hp152
  have hv149 : v 149=0 := by
    simpa only [hv44,hv88,mul_zero,zero_add,add_zero,one_mul] using hp151
  have hv43 : v 43=0 := by
    simpa only [hv54,hv86,hv148,mul_zero,zero_add,add_zero,one_mul] using hp150
  have hv41 : v 41=0 := by
    simpa only [hv146,hv152,hv164,mul_zero,zero_add,add_zero,one_mul] using hp149
  have hv143 : v 143=0 := by
    simpa only [hv76,hv152,hv156,mul_zero,zero_add,add_zero,one_mul] using hp148
  have hv31 : v 31=0 := by
    simpa only [hv62,hv66,hv124,mul_zero,zero_add,add_zero,one_mul] using hp147
  have hv129 : v 129=0 := by
    simpa only [hv48,mul_zero,zero_add,add_zero,one_mul] using hp146
  have hv23 : v 23=0 := by
    simpa only [hv46,hv92,mul_zero,zero_add,add_zero,one_mul] using hp145
  have hv127 : v 127=0 := by
    simpa only [hv22,hv44,hv88,mul_zero,zero_add,add_zero,one_mul] using hp144
  have hv19 : v 19=0 := by
    simpa only [hv76,hv124,hv156,mul_zero,zero_add,add_zero,one_mul] using hp143
  have hv17 : v 17=0 := by
    simpa only [hv122,hv138,mul_zero,zero_add,add_zero,one_mul] using hp142
  have hv118 : v 118=0 := by
    simpa only [hv26,hv52,hv66,mul_zero,zero_add,add_zero,one_mul] using hp141
  have hv116 : v 116=0 := by
    simpa only [hv22,hv44,hv138,mul_zero,zero_add,add_zero,one_mul] using hp140
  have hv78 : v 78=0 := by
    simpa only [hv162,mul_zero,zero_add,add_zero,one_mul] using hp139
  have hv132 : v 132=0 := by
    simpa only [hv48,mul_zero,zero_add,add_zero,one_mul] using hp138
  have hv85 : v 85=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp137
  have hv185 : v 185=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp136
  have hv91 : v 91=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp135
  have hv161 : v 161=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp134
  have hv55 : v 55=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp133
  have hv49 : v 49=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp132
  have hv25 : v 25=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp131
  have hv125 : v 125=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp130
  have hv119 : v 119=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp129
  have hv133 : v 133=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp128
  have hv160 : v 160=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp127
  have hv130 : v 130=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp126
  have hv154 : v 154=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp125
  have hv80 : v 80=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp124
  have hv155 : v 155=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp123
  have hv50 : v 50=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp122
  have hv77 : v 77=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp121
  have hv95 : v 95=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp120
  have hv87 : v 87=0 := by
    simpa only [hv138,mul_zero,zero_add,add_zero,one_mul] using hp119
  have hv79 : v 79=0 := by
    simpa only [hv184,mul_zero,zero_add,add_zero,one_mul] using hp118
  have hv32 : v 32=0 := by
    simpa only [hv78,hv156,mul_zero,zero_add,add_zero,one_mul] using hp117
  have hv69 : v 69=0 := by
    simpa only [hv66,hv138,mul_zero,zero_add,add_zero,one_mul] using hp116
  have hv57 : v 57=0 := by
    simpa only [hv162,mul_zero,zero_add,add_zero,one_mul] using hp115
  have hv153 : v 153=0 := by
    simpa only [hv48,mul_zero,zero_add,add_zero,one_mul] using hp114
  have hv56 : v 56=0 := by
    simpa only [hv154,mul_zero,zero_add,add_zero,one_mul] using hp113
  have hv145 : v 145=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp112
  have hv75 : v 75=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp111
  have hv45 : v 45=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp110
  have hv141 : v 141=0 := by
    simpa only [hv72,hv144,mul_zero,zero_add,add_zero,one_mul] using hp109
  have hv65 : v 65=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp108
  have hv135 : v 135=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp107
  have hv27 : v 27=0 := by
    simpa only [hv54,hv132,mul_zero,zero_add,add_zero,one_mul] using hp106
  have hv131 : v 131=0 := by
    simpa only [hv26,hv52,mul_zero,zero_add,add_zero,one_mul] using hp105
  have hv123 : v 123=0 := by
    simpa only [hv72,mul_zero,zero_add,add_zero,one_mul] using hp104
  have hv115 : v 115=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp103
  have hv165 : v 165=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp102
  have hv150 : v 150=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp101
  have hv194 : v 194=0 := by
    simpa only [hv48,mul_zero,zero_add,add_zero,one_mul] using hp100
  have hv63 : v 63=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp99
  have hv16 : v 16=0 := by
    simpa only [hv162,mul_zero,zero_add,add_zero,one_mul] using hp98
  have hv147 : v 147=0 := by
    simpa only [hv63,mul_zero,zero_add,add_zero,one_mul] using hp97
  have hv60 : v 60=0 := by
    simpa only [hv150,mul_zero,zero_add,add_zero,one_mul] using hp96
  have hv126 : v 126=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp95
  have hv68 : v 68=0 := by
    simpa only [hv138,mul_zero,zero_add,add_zero,one_mul] using hp94
  have hv142 : v 142=0 := by
    simpa only [hv72,mul_zero,zero_add,add_zero,one_mul] using hp93
  have hv139 : v 139=0 := by
    simpa only [hv69,mul_zero,zero_add,add_zero,one_mul] using hp92
  have hv71 : v 71=0 := by
    simpa only [hv141,mul_zero,zero_add,add_zero,one_mul] using hp91
  have hv58 : v 58=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp90
  have hv82 : v 82=0 := by
    simpa only [hv152,mul_zero,zero_add,add_zero,one_mul] using hp89
  have hv159 : v 159=0 := by
    simpa only [hv54,mul_zero,zero_add,add_zero,one_mul] using hp88
  have hv53 : v 53=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp87
  have hv157 : v 157=0 := by
    simpa only [hv52,mul_zero,zero_add,add_zero,one_mul] using hp86
  have hv51 : v 51=0 := by
    simpa only [hv156,mul_zero,zero_add,add_zero,one_mul] using hp85
  have hv186 : v 186=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp84
  have hv136 : v 136=0 := by
    simpa only [hv66,mul_zero,zero_add,add_zero,one_mul] using hp83
  have hv74 : v 74=0 := by
    simpa only [hv144,mul_zero,zero_add,add_zero,one_mul] using hp82
  have hv140 : v 140=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp81
  have hv34 : v 34=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp80
  have hv33 : v 33=0 := by
    simpa only [hv186,mul_zero,zero_add,add_zero,one_mul] using hp79
  have hv183 : v 183=0 := by
    simpa only [hv32,mul_zero,zero_add,add_zero,one_mul] using hp78
  have hv178 : v 178=0 := by
    simpa only [hv27,mul_zero,zero_add,add_zero,one_mul] using hp77
  have hv173 : v 173=0 := by
    simpa only [hv72,mul_zero,zero_add,add_zero,one_mul] using hp76
  have hv172 : v 172=0 := by
    simpa only [hv54,mul_zero,zero_add,add_zero,one_mul] using hp75
  have hv171 : v 171=0 := by
    simpa only [hv48,mul_zero,zero_add,add_zero,one_mul] using hp74
  have hv170 : v 170=0 := by
    simpa only [hv45,mul_zero,zero_add,add_zero,one_mul] using hp73
  have hv40 : v 40=0 := by
    simpa only [hv165,mul_zero,zero_add,add_zero,one_mul] using hp72
  have hv39 : v 39=0 := by
    simpa only [hv162,mul_zero,zero_add,add_zero,one_mul] using hp71
  have hv38 : v 38=0 := by
    simpa only [hv156,mul_zero,zero_add,add_zero,one_mul] using hp70
  have hv37 : v 37=0 := by
    simpa only [hv138,mul_zero,zero_add,add_zero,one_mul] using hp69
  have hv177 : v 177=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp68
  have hv176 : v 176=0 := by
    simpa only [hv140,mul_zero,zero_add,add_zero,one_mul] using hp67
  have hv168 : v 168=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp66
  have hv11 : v 11=0 := by
    simpa only [hv138,mul_zero,zero_add,add_zero,one_mul] using hp65
  have hv103 : v 103=0 := by
    simpa only [hv186,mul_zero,zero_add,add_zero,one_mul] using hp64
  have hv101 : v 101=0 := by
    simpa only [hv48,mul_zero,zero_add,add_zero,one_mul] using hp63
  have hv100 : v 100=0 := by
    simpa only [hv168,mul_zero,zero_add,add_zero,one_mul] using hp62
  have hv98 : v 98=0 := by
    simpa only [hv150,mul_zero,zero_add,add_zero,one_mul] using hp61
  have hv93 : v 93=0 := by
    simpa only [hv16,mul_zero,zero_add,add_zero,one_mul] using hp60
  have hv13 : v 13=0 := by
    simpa only [hv66,mul_zero,zero_add,add_zero,one_mul] using hp59
  have hv197 : v 197=0 := by
    simpa only [hv144,mul_zero,zero_add,add_zero,one_mul] using hp58
  have hv120 : v 120=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp57
  have hv117 : v 117=0 := by
    simpa only [hv194,mul_zero,zero_add,add_zero,one_mul] using hp56
  have hv114 : v 114=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp55
  have hv112 : v 112=0 := by
    simpa only [hv60,mul_zero,zero_add,add_zero,one_mul] using hp54
  have hv111 : v 111=0 := by
    simpa only [hv186,mul_zero,zero_add,add_zero,one_mul] using hp53
  have hv109 : v 109=0 := by
    simpa only [hv162,mul_zero,zero_add,add_zero,one_mul] using hp52
  have hv99 : v 99=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp51
  have hv96 : v 96=0 := by
    simpa only [hv140,mul_zero,zero_add,add_zero,one_mul] using hp50
  have hv90 : v 90=0 := by
    simpa only [hv126,mul_zero,zero_add,add_zero,one_mul] using hp49
  have hv199 : v 199=0 := by
    simpa only [hv72,mul_zero,zero_add,add_zero,one_mul] using hp48
  have hv110 : v 110=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp47
  have hv107 : v 107=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp46
  have hv202 : v 202=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp45
  have hv8 : v 8=0 := by
    simpa only [hv186,mul_zero,zero_add,add_zero,one_mul] using hp44
  have hv203 : v 203=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp43
  have hv201 : v 201=0 := by
    simpa only [hv140,mul_zero,zero_add,add_zero,one_mul] using hp42
  have hv200 : v 200=0 := by
    simpa only [hv126,mul_zero,zero_add,add_zero,one_mul] using hp41
  have hv196 : v 196=0 := by
    simpa only [hv90,mul_zero,zero_add,add_zero,one_mul] using hp40
  have hv195 : v 195=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp39
  have hv70 : v 70=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp38
  have hv190 : v 190=0 := by
    simpa only [hv63,mul_zero,zero_add,add_zero,one_mul] using hp37
  have hv189 : v 189=0 := by
    simpa only [hv60,mul_zero,zero_add,add_zero,one_mul] using hp36
  have hv182 : v 182=0 := by
    simpa only [hv45,mul_zero,zero_add,add_zero,one_mul] using hp35
  have hv180 : v 180=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp34
  have hv30 : v 30=0 := by
    simpa only [hv168,mul_zero,zero_add,add_zero,one_mul] using hp33
  have hv28 : v 28=0 := by
    simpa only [hv165,mul_zero,zero_add,add_zero,one_mul] using hp32
  have hv21 : v 21=0 := by
    simpa only [hv150,mul_zero,zero_add,add_zero,one_mul] using hp31
  have hv20 : v 20=0 := by
    simpa only [hv147,mul_zero,zero_add,add_zero,one_mul] using hp30
  have hv18 : v 18=0 := by
    simpa only [hv140,mul_zero,zero_add,add_zero,one_mul] using hp29
  have hv15 : v 15=0 := by
    simpa only [hv126,mul_zero,zero_add,add_zero,one_mul] using hp28
  have hv14 : v 14=0 := by
    simpa only [hv120,mul_zero,zero_add,add_zero,one_mul] using hp27
  have hv10 : v 10=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp26
  have hv9 : v 9=0 := by
    simpa only [hv70,mul_zero,zero_add,add_zero,one_mul] using hp25
  have hv7 : v 7=0 := by
    simpa only [hv30,mul_zero,zero_add,add_zero,one_mul] using hp24
  have hv5 : v 5=0 := by
    simpa only [hv168,mul_zero,zero_add,add_zero,one_mul] using hp23
  have hv205 : v 205=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp22
  have hv36 : v 36=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp21
  have hv175 : v 175=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp20
  have hv35 : v 35=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp19
  have hv174 : v 174=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp18
  have hv104 : v 104=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp17
  have hv108 : v 108=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp16
  have hv106 : v 106=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp15
  have hv198 : v 198=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp14
  have hv12 : v 12=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp13
  have hv4 : v 4=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp12
  have hv206 : v 206=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp11
  have hv105 : v 105=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp10
  have hv102 : v 102=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp9
  have hv209 : v 209=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp8
  have hv208 : v 208=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp7
  have hv6 : v 6=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp6
  have hv3 : v 3=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp5
  have hv2 : v 2=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp4
  have hv1 : v 1=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp3
  have hv204 : v 204=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp2
  have hv207 : v 207=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp1
  have hv0 : v 0=0 := by
    simpa only [mul_zero,zero_add,add_zero,one_mul] using hp0
  funext j
  fin_cases j
  · exact hv0
  · exact hv1
  · exact hv2
  · exact hv3
  · exact hv4
  · exact hv5
  · exact hv6
  · exact hv7
  · exact hv8
  · exact hv9
  · exact hv10
  · exact hv11
  · exact hv12
  · exact hv13
  · exact hv14
  · exact hv15
  · exact hv16
  · exact hv17
  · exact hv18
  · exact hv19
  · exact hv20
  · exact hv21
  · exact hv22
  · exact hv23
  · exact h24
  · exact hv25
  · exact hv26
  · exact hv27
  · exact hv28
  · exact hv29
  · exact hv30
  · exact hv31
  · exact hv32
  · exact hv33
  · exact hv34
  · exact hv35
  · exact hv36
  · exact hv37
  · exact hv38
  · exact hv39
  · exact hv40
  · exact hv41
  · exact h42
  · exact hv43
  · exact hv44
  · exact hv45
  · exact hv46
  · exact hv47
  · exact hv48
  · exact hv49
  · exact hv50
  · exact hv51
  · exact hv52
  · exact hv53
  · exact hv54
  · exact hv55
  · exact hv56
  · exact hv57
  · exact hv58
  · exact hv59
  · exact hv60
  · exact hv61
  · exact hv62
  · exact hv63
  · exact hv64
  · exact hv65
  · exact hv66
  · exact hv67
  · exact hv68
  · exact hv69
  · exact hv70
  · exact hv71
  · exact hv72
  · exact hv73
  · exact hv74
  · exact hv75
  · exact hv76
  · exact hv77
  · exact hv78
  · exact hv79
  · exact hv80
  · exact hv81
  · exact hv82
  · exact hv83
  · exact h84
  · exact hv85
  · exact hv86
  · exact hv87
  · exact hv88
  · exact hv89
  · exact hv90
  · exact hv91
  · exact hv92
  · exact hv93
  · exact hv94
  · exact hv95
  · exact hv96
  · exact hv97
  · exact hv98
  · exact hv99
  · exact hv100
  · exact hv101
  · exact hv102
  · exact hv103
  · exact hv104
  · exact hv105
  · exact hv106
  · exact hv107
  · exact hv108
  · exact hv109
  · exact hv110
  · exact hv111
  · exact hv112
  · exact hv113
  · exact hv114
  · exact hv115
  · exact hv116
  · exact hv117
  · exact hv118
  · exact hv119
  · exact hv120
  · exact hv121
  · exact hv122
  · exact hv123
  · exact hv124
  · exact hv125
  · exact hv126
  · exact hv127
  · exact h128
  · exact hv129
  · exact hv130
  · exact hv131
  · exact hv132
  · exact hv133
  · exact hv134
  · exact hv135
  · exact hv136
  · exact hv137
  · exact hv138
  · exact hv139
  · exact hv140
  · exact hv141
  · exact hv142
  · exact hv143
  · exact hv144
  · exact hv145
  · exact hv146
  · exact hv147
  · exact hv148
  · exact hv149
  · exact hv150
  · exact hv151
  · exact hv152
  · exact hv153
  · exact hv154
  · exact hv155
  · exact hv156
  · exact hv157
  · exact h158
  · exact hv159
  · exact hv160
  · exact hv161
  · exact hv162
  · exact hv163
  · exact hv164
  · exact hv165
  · exact hv166
  · exact hv167
  · exact hv168
  · exact hv169
  · exact hv170
  · exact hv171
  · exact hv172
  · exact hv173
  · exact hv174
  · exact hv175
  · exact hv176
  · exact hv177
  · exact hv178
  · exact hv179
  · exact hv180
  · exact hv181
  · exact hv182
  · exact hv183
  · exact hv184
  · exact hv185
  · exact hv186
  · exact hv187
  · exact hv188
  · exact hv189
  · exact hv190
  · exact hv191
  · exact h192
  · exact hv193
  · exact hv194
  · exact hv195
  · exact hv196
  · exact hv197
  · exact hv198
  · exact hv199
  · exact hv200
  · exact hv201
  · exact hv202
  · exact hv203
  · exact hv204
  · exact hv205
  · exact hv206
  · exact hv207
  · exact hv208
  · exact hv209

#print axioms positive_grid_recovery_kernel
end QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate
end
end

/-! ## ThirtyFiveOriginalPositiveGridRecovery -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology
theorem original_positive_grid_recovery {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (h24 : v 24=0) (h42 : v 42=0) (h84 : v 84=0)
    (h128 : v 128=0) (h158 : v 158=0) (h192 : v 192=0) : v=0 := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate.positive_grid_recovery_kernel
    (primeParameter 2 m s) (primeParameter 3 m s)
    (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v _ h24 h42 h84 h128 h158 h192
  apply QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate.positive_grid_recovery_rows
    (primeParameter 2 m s) (primeParameter 3 m s)
    (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3)
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) v v
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_4 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_6 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_8 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_10 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_12 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_14 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_20 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_22 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_24 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_28 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_30 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_32 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_34 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_36 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_38 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_40 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_42 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_44 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_46 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_48 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_50 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_52 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_54 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_56 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_58 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_60 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_62 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_64 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_66 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_68 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_128 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_130 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_162 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_246 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_248 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_250 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_252 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_256 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_262 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_266 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_268 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_270 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_272 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_274 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_288 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_292 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_294 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_296 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_298 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_300 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_304 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_306 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_312 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_316 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_320 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_322 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_326 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_342 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_358 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_360 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_362 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_364 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_366 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_368 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_370 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_372 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_374 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_378 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_380 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_382 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_384 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_394 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_398 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_400 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_402 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_2790 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2792 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2794 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2796 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2798 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2800 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2802 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2804 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2806 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2808 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2810 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2812 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2814 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_2840 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2842 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2844 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2846 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2848 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2850 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2854 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2856 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2858 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2860 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2866 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2868 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2872 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2874 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2876 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_2932 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2934 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2936 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2938 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_2950 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3006 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3032 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_3034 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3058 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_3060 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_3064 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_3066 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3084 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3110 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_positive_source_3122 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s v hv hshift)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3158 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3206 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3210 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3212 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3216 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3218 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3222 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3224 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3226 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3228 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3230 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3232 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3234 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3236 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3238 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3240 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3242 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3246 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3248 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3250 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3252 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3254 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3256 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3262 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3264 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3274 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3276 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3278 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3284 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3288 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3290 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3292 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3294 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3296 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3298 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3300 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3302 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3304 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3306 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3308 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3310 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3312 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3314 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3316 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3318 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3324 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3326 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3330 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3336 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3338 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3340 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3350 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3354 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3358 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3360 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3362 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3364 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3368 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3374 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3376 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3378 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3380 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3386 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3390 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3392 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3396 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3424 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3426 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3432 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3436 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3444 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3446 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3448 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3450 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3478 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3528 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3530 hm hf BG G hG hGF s v hv)
  · simpa only [h24,h42,h84,h128,h158,h192,mul_zero,add_zero,zero_add] using (actual_negative_source_3540 hm hf BG G hG hGF s v hv)
  · have hh := actual_signed_badfive_source_3574 hm hf u5 hu5 h5 BG G hG hGF s v hv
    convert hh using 1 <;> ring
  · have hh := actual_signed_badfive_source_3614 hm hf u5 hu5 h5 BG G hG hGF s v hv
    convert hh using 1 <;> ring

#print axioms original_positive_grid_recovery
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalLargeShiftExclusion -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars
open scoped Topology

theorem original_large_shift_exclusion {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (r : ℝ) (hr : 4≤r) (hα : 2≤s.re-(m:ℝ))
    (hrα : r≤(2:ℝ)^(s.re-(m:ℝ)))
    (ha : (Real.sqrt 2:ℂ)*f 2= -primeParameter 2 m s/(r:ℂ)-(r:ℂ)/primeParameter 2 m s) : False := by
  obtain ⟨h24,h42,h84,h128,h158,h192⟩ := original_large_shift_six_zero hm hf ε hε hlaw
    BG G hG hGF s v hv hshift r hr hα hrα ha
  have hu5 : -badFive f=1 ∨ -badFive f= -1 := by
    rcases badFive_sign hf.toEulerData with h|h <;> simp [h]
  have hu7 : -badSeven f=1 ∨ -badSeven f= -1 := by
    rcases badSeven_sign hf.toEulerData with h|h <;> simp [h]
  have hp := phaseRoot_sign m hε
  change ε*I^(2*m)=1 ∨ ε*I^(2*m)= -1 at hp
  have hsign : ε*I^(2*m)=(-badFive f)*(-badSeven f) ∨
      ε*I^(2*m)= -(-badFive f)*(-badSeven f) := by
    rcases hp with hp|hp <;> rcases hu5 with h5|h5 <;> rcases hu7 with h7|h7 <;>
      rw [hp,h5,h7] <;> norm_num
  apply hv.1
  rcases hsign with hpos|hneg
  · exact original_positive_grid_recovery hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hpos (by simp) (by simp)
      BG G hG hGF s v hv hshift h24 h42 h84 h128 h158 h192
  · exact original_negative_grid_recovery hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hneg (by simp) (by simp)
      BG G hG hGF s v hv hshift h24 h42 h84 h128 h158 h192

#print axioms original_large_shift_exclusion
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveChiThreeReflection -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiThree
open Complex SmallLevelAdditive QuantitativeArithmeticSmallLevelThirtyFiveCenters
open FinitenessOriginalFourier
def scaleTwo (k : ℕ) (s : ℂ) : ℂ := (2:ℂ)^((k:ℂ)-2*s)
def reflectionMultiplier (k : ℕ) (ε s : ℂ) : ℂ := ε*(Real.sqrt 315:ℂ)^((k:ℂ)-2*s)

theorem scaleTwo_ne_zero (k : ℕ) (s : ℂ) : scaleTwo k s≠0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

theorem scaleTwo_eq (k : ℕ) (s : ℂ) : scaleTwo k s=(2:ℂ)^k*(4:ℂ)^(-s) := by
  have h4 : (4:ℂ)^(-s)=(2:ℂ)^(-2*s) := by
    have h := Complex.natCast_cpow_natCast_mul 2 2 (-s)
    norm_num only [Nat.cast_ofNat] at h
    rw [← h]
    congr 1
    ring
  rw [h4,← Complex.cpow_natCast,← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
  unfold scaleTwo
  congr 1
  ring

theorem scaleTwo_product (k : ℕ) (s : ℂ) : scaleTwo k s*scaleTwo k ((k:ℂ)-s)=1 := by
  unfold scaleTwo
  rw [← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
  rw [show (k:ℂ)-2*s+((k:ℂ)-2*((k:ℂ)-s))=0 by ring,Complex.cpow_zero]

theorem center_conductor_factor (k : ℕ) (s : ℂ) :
    (Real.sqrt 1260:ℂ)^((k:ℂ)-2*s)=scaleTwo k s*(Real.sqrt 315:ℂ)^((k:ℂ)-2*s) := by
  have hs : Real.sqrt 1260=2*Real.sqrt 315 := by
    rw [show (1260:ℝ)=4*315 by norm_num,Real.sqrt_mul (by norm_num)]
    norm_num
  rw [hs,Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤2) (Real.sqrt_nonneg _) _

theorem reflectionMultiplier_entire (k : ℕ) (ε : ℂ) : Differentiable ℂ (reflectionMultiplier k ε) := by
  have hn : (Real.sqrt 315:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold reflectionMultiplier
  simp_rw [Complex.cpow_def_of_ne_zero hn]
  fun_prop

theorem reflectionMultiplier_ne_zero (k : ℕ) {ε : ℂ} (hε : ε≠0) (s : ℂ) :
    reflectionMultiplier k ε s≠0 := by
  apply mul_ne_zero hε
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by norm_num)).ne'))

theorem reflectionMultiplier_even (m : ℕ) (ε s : ℂ) :
    reflectionMultiplier (2*m) ε s=ε*(315:ℂ)^((m:ℂ)-s) := by
  have hn : (Real.sqrt 315:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs : (Real.sqrt 315:ℂ)*(Real.sqrt 315:ℂ)=315 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ)≤315)
  have hp := Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg 315) (Real.sqrt_nonneg 315) ((m:ℂ)-s)
  rw [hs] at hp
  unfold reflectionMultiplier
  rw [show ((2*m:ℕ):ℂ)-2*s=((m:ℂ)-s)+((m:ℂ)-s) by push_cast; ring,
    Complex.cpow_add _ _ hn,← hp]


theorem denominator_reflection (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    denominator k f s=scaleTwo k s*denominator k f ((k:ℂ)-s) := by
  have hp : scaleTwo k s*(2:ℂ)^(-((k:ℂ)-s))=(2:ℂ)^(-s) := by
    unfold scaleTwo
    rw [← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    ring
  have hq := scaleTwo_product k s
  unfold denominator
  rw [← scaleTwo_eq,← scaleTwo_eq]
  linear_combination -hq - (((2:ℝ)^(((k:ℝ)+1)/2):ℝ):ℂ)*f 2*hp

theorem original_numerator_reflection (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧ ∀ s : ℂ,
      numerator m f s=scaleTwo (2*m) s*reflectionMultiplier (2*m) ε s*
        numerator m f ((2*m:ℕ)-s) := by
  obtain ⟨χ,hχ,hc⟩ := original_centers_entire m hm hf
  let ε : ℂ := χ/I^(2*m)
  have hε : ε=1 ∨ ε= -1 := by
    have hi : I^(2*m)=(-1:ℂ)^m := by rw [pow_mul,I_sq]
    rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hχ with rfl|rfl <;> simp [ε,hi,h]
  have hp (positive : Bool) (s : ℂ) :=
    QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection
      (by decide : 0<1260)
      (coefficients (fullCoefficients f (2*m)) (center positive)) ε (hc positive).2.2 s
  refine ⟨ε,hε,fun s => ?_⟩
  have hpos := hp true s
  have hneg := hp false s
  norm_num only [center,Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat] at hpos hneg
  rw [center_conductor_factor] at hpos hneg
  unfold numerator reflectionMultiplier
  linear_combination hpos-hneg

theorem original_quadratic_functional_equation (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ (ε : ℂ) (bound : ℝ) (G : ℂ → ℂ), (ε=1 ∨ ε= -1) ∧
      (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) ∧
      (∀ s, G s=ε*(315:ℂ)^((m:ℂ)-s)*G ((2*m:ℕ)-s)) ∧
      (∀ s, denominator (2*m) f s≠0 → AnalyticAt ℂ G s) := by
  obtain ⟨ε,hε,hN⟩ := original_numerator_reflection m hm hf
  obtain ⟨B,G,hG,hagree,hpole,hgerm⟩ := original_continuation m hm hf
  have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
  have hraw (s : ℂ) : numerator m f s/denominator (2*m) f s=
      reflectionMultiplier (2*m) ε s*(numerator m f ((2*m:ℕ)-s)/denominator (2*m) f ((2*m:ℕ)-s)) := by
    rw [hN s,denominator_reflection (2*m) f s,mul_assoc,
      mul_div_mul_left _ _ (scaleTwo_ne_zero (2*m) s)]
    ring
  have hfe := QuantitativeArithmeticQuadraticTwistReflection.normal_form_reflection
    (fun s => numerator m f s/denominator (2*m) f s) G
    (reflectionMultiplier (2*m) ε) ((2*m:ℕ):ℂ) hG
    (fun s => (reflectionMultiplier_entire (2*m) ε).analyticAt s)
    (reflectionMultiplier_ne_zero (2*m) hε0) hgerm hraw
  refine ⟨ε,B,G,hε,hG,hagree,?_,hpole⟩
  intro s
  simpa only [reflectionMultiplier_even] using hfe s
#print axioms original_quadratic_functional_equation
end QuantitativeArithmeticSmallLevelThirtyFiveChiThree
end
end

/-! ## ThirtyFiveChiThreeCandidate -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex

theorem chi3_denominator_normalized (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=
      1+((Real.sqrt 2:ℂ)*f 2)/primeParameter 2 m s+1/(primeParameter 2 m s)^2 := by
  have hc : (((2:ℝ)^((((2*m:ℕ):ℝ)+1)/2):ℝ):ℂ)=
      (Real.sqrt 2:ℂ)*(2:ℂ)^m := by
    rw [show (((2*m:ℕ):ℝ)+1)/2=(m:ℝ)+1/2 by push_cast; ring,
      Real.rpow_add (by norm_num),Real.rpow_natCast,← Real.sqrt_eq_rpow]
    push_cast
    ring
  have hi : (2:ℂ)^((m:ℂ)-s)=(primeParameter 2 m s)⁻¹ := by
    rw [show (m:ℂ)-s= -(s-(m:ℂ)) by ring,Complex.cpow_neg]
    rfl
  have hm : (2:ℂ)^m*(2:ℂ)^(-s)=(primeParameter 2 m s)⁻¹ := by
    rw [← Complex.cpow_natCast,← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    simpa only [sub_eq_add_neg] using hi
  have hq : (2:ℂ)^(2*m)*(4:ℂ)^(-s)=((primeParameter 2 m s)⁻¹)^2 := by
    rw [← QuantitativeArithmeticSmallLevelThirtyFiveChiThree.scaleTwo_eq]
    unfold QuantitativeArithmeticSmallLevelThirtyFiveChiThree.scaleTwo
    rw [show ((2*m:ℕ):ℂ)-2*s=(2:ℂ)*((m:ℂ)-s) by push_cast; ring,
      show (2:ℂ)*((m:ℂ)-s)=((m:ℂ)-s)+((m:ℂ)-s) by ring,
      Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),hi,pow_two]
  unfold QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator
  rw [hc,hq]
  rw [show (Real.sqrt 2:ℂ)*(2:ℂ)^m*f 2*(2:ℂ)^(-s)=
    ((Real.sqrt 2:ℂ)*f 2)*((2:ℂ)^m*(2:ℂ)^(-s)) by ring,hm]
  simp only [div_eq_mul_inv,inv_pow,one_mul]

theorem primeParameter_add_nat (p m n : ℕ) (hp : p≠0) (s : ℂ) :
    primeParameter p m (s+(n:ℂ))=(p:ℂ)^n*primeParameter p m s := by
  unfold primeParameter
  rw [show s+(n:ℂ)-(m:ℂ)=(n:ℂ)+(s-(m:ℂ)) by ring,
    Complex.cpow_add _ _ (by exact_mod_cast hp),Complex.cpow_natCast]

/-- Translate the actual quadratic-twist pole divisor to a point n steps
to its right. The Hecke coefficient is the normalized coefficient f₂. -/
theorem chi3_shifted_candidate (m n : ℕ) (f : ℕ → ℂ) (s : ℂ)
    (h : QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0) :
    (Real.sqrt 2:ℂ)*f 2=
      -primeParameter 2 m (s+(n:ℂ))/((2:ℝ)^n:ℂ)-
      ((2:ℝ)^n:ℂ)/primeParameter 2 m (s+(n:ℂ)) := by
  rw [chi3_denominator_normalized] at h
  have hx := primeParameter_ne_zero 2 m (by decide) s
  have hr : (2:ℂ)^n≠0 := pow_ne_zero n (by norm_num)
  have hp : (Real.sqrt 2:ℂ)*f 2= -primeParameter 2 m s-1/primeParameter 2 m s := by
    linear_combination (norm := (field_simp [hx]; ring)) (primeParameter 2 m s)*h
  rw [primeParameter_add_nat 2 m n (by decide)]
  push_cast
  rw [hp]
  field_simp [hx,hr]

#print axioms chi3_denominator_normalized
#print axioms primeParameter_add_nat
#print axioms chi3_shifted_candidate
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveChiThreeLargeShift -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic

/-- Every shift by at least two of a quadratic-twist denominator root on
or to the right of the central line satisfies the large-shift bounds. -/
theorem chi3_large_shift_geometry (m n : ℕ) (hn : 2≤n) (s : ℂ)
    (hs : (m:ℝ)≤s.re) :
    4≤(2:ℝ)^n ∧ 2≤(s+(n:ℂ)).re-(m:ℝ) ∧
      (2:ℝ)^n≤(2:ℝ)^((s+(n:ℂ)).re-(m:ℝ)) := by
  have hnR : (2:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  have hα : (n:ℝ)≤(s+(n:ℂ)).re-(m:ℝ) := by
    simp only [Complex.add_re,Complex.natCast_re]
    linarith
  refine ⟨?_,le_trans hnR hα,?_⟩
  · have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hnR
    convert h using 1 <;> norm_num
  · simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hα

/-- A rightmost grid pole cannot occur at a shift of at least two of an
actual quadratic-twist denominator root. No assumed row equations occur. -/
theorem original_chi3_large_shift_regular {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (hs : (m:ℝ)≤s.re)
    (hden : QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0)
    (n : ℕ) (hn : 2≤n)
    (hshift : ∀ a : ℕ, 0<a → ∀ j,
      0≤meromorphicOrderAt (fun z => G z j) ((s+(n:ℂ))+a)) :
    ∀ j, AnalyticAt ℂ (fun z => G z j) (s+(n:ℂ)) := by
  have hregular : ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+(n:ℂ)) := by
    by_contra h
    push Not at h
    obtain ⟨j,hj⟩ := h
    obtain ⟨v,hv⟩ := exists_leading_vector G (s+(n:ℂ))
      (fun i => (hG i _).meromorphicAt) ⟨j,hj⟩
    obtain ⟨hr,hα,hrα⟩ := chi3_large_shift_geometry m n hn s hs
    exact original_large_shift_exclusion hm hf ε hε hlaw BG G hG hGF
      (s+(n:ℂ)) v hv hshift ((2:ℝ)^n) hr hα hrα (by simpa only [Complex.ofReal_pow] using chi3_shifted_candidate m n f s hden)
  intro j
  exact (hG j _).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hregular j)

/-- Right-half-plane holomorphy removes the rightmost-pole proviso:
all grid entries are regular at every shift n at least two. -/
theorem original_chi3_all_large_shifts_regular {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (B : ℝ) (hhalf : ∀ i z, B<z.re → AnalyticAt ℂ (fun s => G s i) z)
    (s : ℂ) (hs : (m:ℝ)≤s.re)
    (hden : QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0)
    (n : ℕ) (hn : 2≤n) :
    ∀ j, AnalyticAt ℂ (fun z => G z j) (s+(n:ℂ)) := by
  intro j
  apply (hG j _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hj
  obtain ⟨a,ha,hshift⟩ := SmallLevelPoleGrid.rightmost_pole
    (fun i z => G z i) ⟨j,hj⟩ B hhalf
  have he : s+((n+a:ℕ):ℂ)=(s+(n:ℂ))+(a:ℂ) := by push_cast; ring
  have hreg := original_chi3_large_shift_regular hm hf ε hε hlaw BG G hG hGF
    s hs hden (n+a) (by omega) (by simpa only [he] using hshift)
  obtain ⟨i,hi⟩ := ha
  rw [he] at hreg
  exact (not_lt_of_ge (hreg i).meromorphicOrderAt_nonneg) hi

#print axioms original_chi3_all_large_shifts_regular
#print axioms chi3_large_shift_geometry
#print axioms original_chi3_large_shift_regular
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalChiThreeShiftTail -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open scoped Topology
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic

theorem continued_grid_halfplane {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z) :
    ∃ B : ℝ, ∀ i z, B<z.re → AnalyticAt ℂ (fun s => G s i) z := by
  obtain ⟨BF,hF⟩ := SmallLevelAdditive.original_common_halfplane hf
  refine ⟨max BG BF,?_⟩
  intro i z hz
  have hnear : (fun s => G s i)=ᶠ[𝓝 z] (fun s => gridVector (2*m) f s i) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (lt_of_le_of_lt (le_max_left BG BF) hz)] with s hs
    exact congrFun (hGF s hs) i
  apply (analyticAt_congr hnear).mpr
  exact (hF (((i:ℕ):ℝ)/210) z (lt_of_le_of_lt (le_max_right BG BF) hz)).1

/-- Original-input continuation with the complete two-and-higher shift tail
regular at every candidate pole of the quadratic twist on the right half
of its functional equation. -/
theorem original_chi3_shift_tail {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      ∃ BG : ℝ, ∃ G : ℂ → Fin 210 → ℂ,
        (∀ i z, MeromorphicNFAt (fun s => G s i) z) ∧
        (∀ z, BG<z.re → G z=gridVector (2*m) f z) ∧
        (∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          ∀ n : ℕ, 2≤n → ∀ j, AnalyticAt ℂ (fun z => G z j) (s+(n:ℂ))) := by
  obtain ⟨ε,hε,hlaw⟩ := QuantitativeArithmeticCoherentTaylor.original_coherent_law
    (by decide : 0<35) hf
  obtain ⟨BG,G,hG,hGF⟩ := original_grid_continuation hm hf
  obtain ⟨B,hhalf⟩ := continued_grid_halfplane hf BG G hGF
  refine ⟨ε,hε,hlaw,BG,G,hG,hGF,?_⟩
  intro s hs hden n hn
  exact original_chi3_all_large_shifts_regular hm hf ε hε hlaw BG G hG hGF
    B hhalf s hs hden n hn

#print axioms continued_grid_halfplane
#print axioms original_chi3_shift_tail
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveGapOneModels -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGapOne
open Complex
open QuantitativeArithmeticOuterRootNorm

def negativePolynomial (u : ℂ) : ℂ := 14*u^7+49*u^6-391*u^5+133*u^4+1098*u^3-224*u^2-1448*u-176
def negativeModel (u : ℂ) : ℂ := 14*((7301/1000:ℂ)*u^0+(1:ℂ)*u^1)*((1/8:ℂ)*u^0+(1:ℂ)*u^1)*((-2629/1000:ℂ)*u^0+(1:ℂ)*u^1)*((1493/1000:ℂ)*u^0+(567/250:ℂ)*u^1+(1:ℂ)*u^2)*((3497/1000:ℂ)*u^0+(-713/200:ℂ)*u^1+(1:ℂ)*u^2)
def negativeRemainder : Fin 7 → ℂ := ![-2502036470637/4000000000000,-265423767843/4000000000000,1061226390441/1000000000000,-34739041027/100000000000,387877/15625000,-3897/250000,0]

theorem negative_remainder_identity (u : ℂ) :
    negativePolynomial u-negativeModel u=∑ i : Fin 7, negativeRemainder i*u^(i:ℕ) := by
  norm_num [negativePolynomial,negativeModel,negativeRemainder,Fin.sum_univ_succ]
  ring

theorem negative_error_bound (u : ℂ) (hu : 4≤‖u‖) :
    ‖negativePolynomial u-negativeModel u‖≤(249682520631353/16384000000000000:ℝ)*‖u‖^6 := by
  rw [negative_remainder_identity]
  have h := polynomial_six_norm negativeRemainder u hu
  have he : ((∑ i : Fin 7, ‖negativeRemainder i‖*(4:ℝ)^(i:ℕ))/4096)=
      (249682520631353/16384000000000000:ℝ) := by
    norm_num [negativeRemainder,Fin.sum_univ_succ,norm_div]
  rw [he] at h
  exact h

#print axioms negative_remainder_identity
#print axioms negative_error_bound

def positivePolynomial (u : ℂ) : ℂ := 14*u^7+21*u^6-273*u^5+91*u^4+1098*u^3-648*u^2-1576*u+48
def positiveModel (u : ℂ) : ℂ := 14*((9993/2000:ℂ)*u^0+(1:ℂ)*u^1)*((211/125:ℂ)*u^0+(1:ℂ)*u^1)*((5957/5000:ℂ)*u^0+(1:ℂ)*u^1)*((-301/10000:ℂ)*u^0+(1:ℂ)*u^1)*((-5091/2000:ℂ)*u^0+(1:ℂ)*u^1)*((89054737/20000000:ℂ)*u^0+(-19001/5000:ℂ)*u^1+(1:ℂ)*u^2)
def positiveRemainder : Fin 7 → ℂ := ![1399296639220099381641/250000000000000000000000,-16712677152555084629/2000000000000000000000,-62475118399189931/2000000000000000000,-15965051143467/1000000000000000,4234899697/250000000000,7/78125,-7/5000]

theorem positive_remainder_identity (u : ℂ) :
    positivePolynomial u-positiveModel u=∑ i : Fin 7, positiveRemainder i*u^(i:ℕ) := by
  norm_num [positivePolynomial,positiveModel,positiveRemainder,Fin.sum_univ_succ]
  ring

theorem positive_error_bound (u : ℂ) (hu : 4≤‖u‖) :
    ‖positivePolynomial u-positiveModel u‖≤(2930818612741349503696141/1024000000000000000000000000:ℝ)*‖u‖^6 := by
  rw [positive_remainder_identity]
  have h := polynomial_six_norm positiveRemainder u hu
  have he : ((∑ i : Fin 7, ‖positiveRemainder i‖*(4:ℝ)^(i:ℕ))/4096)=
      (2930818612741349503696141/1024000000000000000000000000:ℝ) := by
    norm_num [positiveRemainder,Fin.sum_univ_succ,norm_div]
  rw [he] at h
  exact h

#print axioms positive_remainder_identity
#print axioms positive_error_bound
end QuantitativeArithmeticSmallLevelThirtyFiveGapOne
end
end

/-! ## ThirtyFiveGapOneDeterminants -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGapOne
open Complex

def negativeRow3Z (u : ℂ) : ℂ := u^(5:ℕ) - 1/2*u^(4:ℕ) - 21/2*u^(3:ℕ) + 8*u^(2:ℕ) + 8*u - 4

def negativeRow3W (u : ℂ) : ℂ := -2*u^(4:ℕ) - u^(3:ℕ) + 5*u^(2:ℕ) + 10*u - 4

def negativeRow3C (u : ℂ) : ℂ := 2*u^(5:ℕ) - 19/2*u^(3:ℕ) - 5*u^(2:ℕ) + 10*u
def negativeRow3 (u z w : ℂ) : ℂ := negativeRow3Z u*z+negativeRow3W u*w+negativeRow3C u

def negativeRow164Z (u : ℂ) : ℂ := u^(5:ℕ) - 9/2*u^(4:ℕ) + 53/6*u^(3:ℕ) - 34/3*u^(2:ℕ) - 4*u + 32/3

def negativeRow164W (u : ℂ) : ℂ := -2*u^(4:ℕ) + 7/3*u^(3:ℕ) - 4/3*u^(2:ℕ) + 14/3*u + 32/3

def negativeRow164C (u : ℂ) : ℂ := 2*u^(5:ℕ) - 4*u^(4:ℕ) - 7/2*u^(3:ℕ) + 35/3*u^(2:ℕ) - 56/3*u
def negativeRow164 (u z w : ℂ) : ℂ := negativeRow164Z u*z+negativeRow164W u*w+negativeRow164C u

def negativeRow21Z (u : ℂ) : ℂ := u^(6:ℕ) - 3/2*u^(5:ℕ) - 6*u^(4:ℕ) - 7/2*u^(3:ℕ) + 28*u^(2:ℕ) - 8*u - 12

def negativeRow21W (u : ℂ) : ℂ := -2*u^(5:ℕ) + u^(4:ℕ) - 2*u^(3:ℕ) + 13*u^(2:ℕ) + 4*u - 12

def negativeRow21C (u : ℂ) : ℂ := 2*u^(6:ℕ) - 2*u^(5:ℕ) - 3/2*u^(4:ℕ) - 15/2*u^(3:ℕ) - 9*u^(2:ℕ) + 24*u
def negativeRow21 (u z w : ℂ) : ℂ := negativeRow21Z u*z+negativeRow21W u*w+negativeRow21C u

theorem negative_residual_determinant (u z w : ℂ)
    (h3 : negativeRow3 u z w=0)
    (h164 : negativeRow164 u z w=0)
    (h21 : negativeRow21 u z w=0)
    : u^2*(2*u-3)^2*negativePolynomial u=0 := by
  dsimp [negativeRow3Z,negativeRow3W,negativeRow3C,negativeRow3,negativeRow164Z,negativeRow164W,negativeRow164C,negativeRow164,negativeRow21Z,negativeRow21W,negativeRow21C,negativeRow21,negativePolynomial] at h3 h164 h21 ⊢
  linear_combination (-3:ℂ)*((u^(5:ℕ) - 9/2*u^(4:ℕ) + 53/6*u^(3:ℕ) - 34/3*u^(2:ℕ) - 4*u + 32/3)*(-2*u^(5:ℕ) + u^(4:ℕ) - 2*u^(3:ℕ) + 13*u^(2:ℕ) + 4*u - 12)-(-2*u^(4:ℕ) + 7/3*u^(3:ℕ) - 4/3*u^(2:ℕ) + 14/3*u + 32/3)*(u^(6:ℕ) - 3/2*u^(5:ℕ) - 6*u^(4:ℕ) - 7/2*u^(3:ℕ) + 28*u^(2:ℕ) - 8*u - 12))*h3 +
    (-3:ℂ)*((u^(6:ℕ) - 3/2*u^(5:ℕ) - 6*u^(4:ℕ) - 7/2*u^(3:ℕ) + 28*u^(2:ℕ) - 8*u - 12)*(-2*u^(4:ℕ) - u^(3:ℕ) + 5*u^(2:ℕ) + 10*u - 4)-(-2*u^(5:ℕ) + u^(4:ℕ) - 2*u^(3:ℕ) + 13*u^(2:ℕ) + 4*u - 12)*(u^(5:ℕ) - 1/2*u^(4:ℕ) - 21/2*u^(3:ℕ) + 8*u^(2:ℕ) + 8*u - 4))*h164 +
    (-3:ℂ)*((u^(5:ℕ) - 1/2*u^(4:ℕ) - 21/2*u^(3:ℕ) + 8*u^(2:ℕ) + 8*u - 4)*(-2*u^(4:ℕ) + 7/3*u^(3:ℕ) - 4/3*u^(2:ℕ) + 14/3*u + 32/3)-(-2*u^(4:ℕ) - u^(3:ℕ) + 5*u^(2:ℕ) + 10*u - 4)*(u^(5:ℕ) - 9/2*u^(4:ℕ) + 53/6*u^(3:ℕ) - 34/3*u^(2:ℕ) - 4*u + 32/3))*h21

#print axioms negative_residual_determinant

def positiveRow14Z (u : ℂ) : ℂ := u^(5:ℕ) - 1/2*u^(4:ℕ) - 21/2*u^(3:ℕ) + 8*u^(2:ℕ) + 8*u - 4

def positiveRow14W (u : ℂ) : ℂ := 2*u^(4:ℕ) + u^(3:ℕ) - 5*u^(2:ℕ) - 10*u + 4

def positiveRow14C (u : ℂ) : ℂ := 2*u^(5:ℕ) - 19/2*u^(3:ℕ) - 5*u^(2:ℕ) + 10*u
def positiveRow14 (u z w : ℂ) : ℂ := positiveRow14Z u*z+positiveRow14W u*w+positiveRow14C u

def positiveRow164Z (u : ℂ) : ℂ := u^(5:ℕ) - 9/4*u^(4:ℕ) - 17/4*u^(3:ℕ) + 9/2*u^(2:ℕ) + 11*u + 6

def positiveRow164W (u : ℂ) : ℂ := 2*u^(4:ℕ) + 11/4*u^(3:ℕ) - 17/2*u^(2:ℕ) - 14*u - 20

def positiveRow164C (u : ℂ) : ℂ := 2*u^(5:ℕ) + u^(4:ℕ) - 73/4*u^(3:ℕ) - 21/2*u^(2:ℕ) + 24*u + 8
def positiveRow164 (u z w : ℂ) : ℂ := positiveRow164Z u*z+positiveRow164W u*w+positiveRow164C u

def positiveRow16Z (u : ℂ) : ℂ := u^(6:ℕ) - 1/2*u^(5:ℕ) - 49/4*u^(4:ℕ) + 9/2*u^(3:ℕ) + 24*u^(2:ℕ) - 16

def positiveRow16W (u : ℂ) : ℂ := 2*u^(5:ℕ) + u^(4:ℕ) - 13/4*u^(3:ℕ) - 3*u^(2:ℕ) + 7*u + 12

def positiveRow16C (u : ℂ) : ℂ := 2*u^(6:ℕ) - 31/4*u^(4:ℕ) + 3/4*u^(3:ℕ) + u^(2:ℕ) - 15*u + 4
def positiveRow16 (u z w : ℂ) : ℂ := positiveRow16Z u*z+positiveRow16W u*w+positiveRow16C u

theorem positive_residual_determinant (u z w : ℂ)
    (h14 : positiveRow14 u z w=0)
    (h164 : positiveRow164 u z w=0)
    (h16 : positiveRow16 u z w=0)
    : (u+4)*(u+2)^2*(3*u-2)^2*positivePolynomial u=0 := by
  dsimp [positiveRow14Z,positiveRow14W,positiveRow14C,positiveRow14,positiveRow164Z,positiveRow164W,positiveRow164C,positiveRow164,positiveRow16Z,positiveRow16W,positiveRow16C,positiveRow16,positivePolynomial] at h14 h164 h16 ⊢
  linear_combination (32:ℂ)*((u^(5:ℕ) - 9/4*u^(4:ℕ) - 17/4*u^(3:ℕ) + 9/2*u^(2:ℕ) + 11*u + 6)*(2*u^(5:ℕ) + u^(4:ℕ) - 13/4*u^(3:ℕ) - 3*u^(2:ℕ) + 7*u + 12)-(2*u^(4:ℕ) + 11/4*u^(3:ℕ) - 17/2*u^(2:ℕ) - 14*u - 20)*(u^(6:ℕ) - 1/2*u^(5:ℕ) - 49/4*u^(4:ℕ) + 9/2*u^(3:ℕ) + 24*u^(2:ℕ) - 16))*h14 +
    (32:ℂ)*((u^(6:ℕ) - 1/2*u^(5:ℕ) - 49/4*u^(4:ℕ) + 9/2*u^(3:ℕ) + 24*u^(2:ℕ) - 16)*(2*u^(4:ℕ) + u^(3:ℕ) - 5*u^(2:ℕ) - 10*u + 4)-(2*u^(5:ℕ) + u^(4:ℕ) - 13/4*u^(3:ℕ) - 3*u^(2:ℕ) + 7*u + 12)*(u^(5:ℕ) - 1/2*u^(4:ℕ) - 21/2*u^(3:ℕ) + 8*u^(2:ℕ) + 8*u - 4))*h164 +
    (32:ℂ)*((u^(5:ℕ) - 1/2*u^(4:ℕ) - 21/2*u^(3:ℕ) + 8*u^(2:ℕ) + 8*u - 4)*(2*u^(4:ℕ) + 11/4*u^(3:ℕ) - 17/2*u^(2:ℕ) - 14*u - 20)-(2*u^(4:ℕ) + u^(3:ℕ) - 5*u^(2:ℕ) - 10*u + 4)*(u^(5:ℕ) - 9/4*u^(4:ℕ) - 17/4*u^(3:ℕ) + 9/2*u^(2:ℕ) + 11*u + 6))*h16

#print axioms positive_residual_determinant
end QuantitativeArithmeticSmallLevelThirtyFiveGapOne
end
end

/-! ## ThirtyFiveGapOneRowReduction -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGapOne
open Complex

def negativeBaseA (x y z w a b : ℂ) : ℂ := -y^(2:ℕ) - y*b - 5

def negativeBaseB (x y z w a b : ℂ) : ℂ := (2*x^(5:ℕ)*a + 2*x^(4:ℕ)*y^(2:ℕ) - 2*x^(4:ℕ)*y*b + 4*x^(4:ℕ) + 2*x^(3:ℕ)*y^(2:ℕ)*a - 2*x^(3:ℕ)*y*a*b - 6*x^(3:ℕ)*a + 2*x^(2:ℕ)*y^(2:ℕ) + 2*x^(2:ℕ)*y*b + 2*x^(2:ℕ)*z - 2*x^(2:ℕ)*a^(2:ℕ) + 2*x*y*a*b + 4*x*a - 2*y^(2:ℕ) - 2*z - 2*w)/w

def negativeCoeff3A (x y z w a b : ℂ) : ℂ := 2*x^(3:ℕ)*a + x^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ) - 3

def negativeCoeff3B (x y z w a b : ℂ) : ℂ := (-x^(8:ℕ)*a^(2:ℕ) - x^(7:ℕ)*y^(2:ℕ)*a + x^(7:ℕ)*y*a*b - 3*x^(7:ℕ)*a - x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) - x^(6:ℕ)*y^(2:ℕ) + x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*y*b + 3*x^(6:ℕ)*a^(2:ℕ) - 2*x^(6:ℕ) - 2*x^(5:ℕ)*y^(2:ℕ)*a - x^(5:ℕ)*z*a + x^(5:ℕ)*a^(3:ℕ) + 5*x^(5:ℕ)*a - x^(4:ℕ)*y*a^(2:ℕ)*b - 2*x^(4:ℕ)*y*b - x^(4:ℕ)*z*a^(2:ℕ) - x^(4:ℕ)*a^(2:ℕ) + 3*x^(4:ℕ) + 2*x^(3:ℕ)*y^(2:ℕ)*a - 2*x^(3:ℕ)*y*a*b + x^(3:ℕ)*w*a - 7*x^(3:ℕ)*a + 2*x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y*b + x^(2:ℕ)*z*a^(2:ℕ) + x^(2:ℕ)*z + x^(2:ℕ)*w - x^(2:ℕ)*a^(2:ℕ) - 2*x^(2:ℕ) - x*y^(2:ℕ)*a + x*y*a*b + x*z*a + 2*x*a - 2*y^(2:ℕ) - 2*z - w + 1)/w

theorem negative_determinant_reduction_3 (x y z w a b : ℂ) (hx : x≠0) (hy0 : y≠0) (hw : w≠0)
    (ha : a= -x/2-2/x) (hb : b=(x^4-x^2/2-3)/y)
    (hY : y^2=x^4-(5/2:ℂ)*x^2-2) :
    (2*w)*((negativeBaseA x y z w a b)*(negativeCoeff3B x y z w a b)-(negativeCoeff3A x y z w a b)*(negativeBaseB x y z w a b))=(-1)*(negativeRow3 (x^2) z w) := by
  dsimp only [negativeBaseA,negativeBaseB,negativeCoeff3A,negativeCoeff3B,negativeRow3,negativeRow3Z,negativeRow3W,negativeRow3C]
  rw [ha,hb]
  linear_combination (norm := (field_simp [hx,hy0,hw]; ring)) ((-2*x^(12:ℕ) + x^(10:ℕ) - 2*x^(8:ℕ)*y^(2:ℕ) + 10*x^(8:ℕ) - 2*x^(6:ℕ)*z + 8*x^(4:ℕ)*y^(2:ℕ) - 2*x^(4:ℕ)*z + 4*x^(4:ℕ)*w - 32*x^(4:ℕ) + 12*x^(2:ℕ)*y^(2:ℕ) + 12*x^(2:ℕ)*z + 8*x^(2:ℕ)*w + 28*x^(2:ℕ) + 8*w + 24)/4)*hY

theorem negative_homogeneous_residual_3 (x y z w a b : ℂ) (hx : x≠0) (hy0 : y≠0) (hw : w≠0)
    (ha : a= -x/2-2/x) (hb : b=(x^4-x^2/2-3)/y)
    (hY : y^2=x^4-(5/2:ℂ)*x^2-2)
    (v24 v84 : ℂ)
    (hbase : (negativeBaseA x y z w a b)*v24+(negativeBaseB x y z w a b)*v84=0)
    (hrow : (negativeCoeff3A x y z w a b)*v24+(negativeCoeff3B x y z w a b)*v84=0) : (negativeRow3 (x^2) z w)*v84=0 := by
  have hd := negative_determinant_reduction_3 x y z w a b hx hy0 hw ha hb hY
  have hh : ((negativeBaseA x y z w a b)*(negativeCoeff3B x y z w a b)-(negativeCoeff3A x y z w a b)*(negativeBaseB x y z w a b))*v84=0 := by
    linear_combination (negativeBaseA x y z w a b)*hrow-(negativeCoeff3A x y z w a b)*hbase
  have he : (-1:ℂ)*((negativeRow3 (x^2) z w)*v84)=0 := by
    calc
      (-1:ℂ)*((negativeRow3 (x^2) z w)*v84)=((-1)*(negativeRow3 (x^2) z w))*v84 := by ring
      _ = ((2*w)*((negativeBaseA x y z w a b)*(negativeCoeff3B x y z w a b)-(negativeCoeff3A x y z w a b)*(negativeBaseB x y z w a b)))*v84 := by rw [hd]
      _ = 0 := by linear_combination (2*w)*hh
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

#print axioms negative_determinant_reduction_3
#print axioms negative_homogeneous_residual_3

def negativeCoeff164A (x y z w a b : ℂ) : ℂ := (2*x^(4:ℕ) - x^(3:ℕ)*a - x^(2:ℕ)*a^(2:ℕ) - 4*x^(2:ℕ) - 3*x*a - y^(2:ℕ) - y*b + 1)/(y^(2:ℕ))

def negativeCoeff164B (x y z w a b : ℂ) : ℂ := (-x^(9:ℕ)*a - x^(8:ℕ)*y^(2:ℕ) + x^(8:ℕ)*y*b + x^(8:ℕ)*a^(2:ℕ) - 2*x^(8:ℕ) + 7*x^(7:ℕ)*a + x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ) - x^(6:ℕ)*y*a^(2:ℕ)*b - 3*x^(6:ℕ)*y*b - x^(6:ℕ)*z - x^(6:ℕ)*a^(2:ℕ) + 5*x^(6:ℕ) + 4*x^(5:ℕ)*y^(2:ℕ)*a - 3*x^(5:ℕ)*y*a*b - x^(5:ℕ)*a^(3:ℕ) - 7*x^(5:ℕ)*a + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + 3*x^(4:ℕ)*y^(2:ℕ) + 2*x^(4:ℕ)*y*b + x^(4:ℕ)*z*a^(2:ℕ) + 2*x^(4:ℕ)*z + x^(4:ℕ)*w - 3*x^(4:ℕ)*a^(2:ℕ) - 4*x^(4:ℕ) + 3*x^(3:ℕ)*y*a*b + 3*x^(3:ℕ)*z*a - x^(3:ℕ)*w*a - x^(3:ℕ)*a^(3:ℕ) + 5*x^(3:ℕ)*a - 3*x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y*a^(2:ℕ)*b - x^(2:ℕ)*z*a^(2:ℕ) - x^(2:ℕ)*z - 2*x^(2:ℕ)*w + 2*x^(2:ℕ)*a^(2:ℕ) + 5*x^(2:ℕ) - 3*x*z*a - x*w*a + x*a + 2*y^(2:ℕ) + z - 2)/(y^(2:ℕ)*w)

theorem negative_determinant_reduction_164 (x y z w a b : ℂ) (hx : x≠0) (hy0 : y≠0) (hw : w≠0)
    (ha : a= -x/2-2/x) (hb : b=(x^4-x^2/2-3)/y)
    (hY : y^2=x^4-(5/2:ℂ)*x^2-2) :
    (2*x^(4:ℕ)*w - 5*x^(2:ℕ)*w - 4*w)*((negativeBaseA x y z w a b)*(negativeCoeff164B x y z w a b)-(negativeCoeff164A x y z w a b)*(negativeBaseB x y z w a b))=(3)*(negativeRow164 (x^2) z w) := by
  dsimp only [negativeBaseA,negativeBaseB,negativeCoeff164A,negativeCoeff164B,negativeRow164,negativeRow164Z,negativeRow164W,negativeRow164C]
  rw [ha,hb]
  linear_combination (norm := (field_simp [hx,hy0,hw]; ring)) ((12*x^(16:ℕ) - 56*x^(14:ℕ) + 12*x^(12:ℕ)*y^(2:ℕ) + 39*x^(12:ℕ) - 50*x^(10:ℕ)*y^(2:ℕ) - 12*x^(10:ℕ)*z + 57*x^(10:ℕ) + 26*x^(8:ℕ)*y^(2:ℕ) + 42*x^(8:ℕ)*z + 24*x^(8:ℕ)*w - 208*x^(8:ℕ) - 8*x^(6:ℕ)*y^(2:ℕ) - 58*x^(6:ℕ)*z - 4*x^(6:ℕ)*w + 546*x^(6:ℕ) + 56*x^(4:ℕ)*y^(2:ℕ) + 44*x^(4:ℕ)*z + 36*x^(4:ℕ)*w + 68*x^(4:ℕ) + 256*x^(2:ℕ)*y^(2:ℕ) + 120*x^(2:ℕ)*z + 64*x^(2:ℕ)*w - 208*x^(2:ℕ) + 128*y^(2:ℕ) - 96*z - 128*w - 384)/(8*y^(2:ℕ)))*hY

theorem negative_homogeneous_residual_164 (x y z w a b : ℂ) (hx : x≠0) (hy0 : y≠0) (hw : w≠0)
    (ha : a= -x/2-2/x) (hb : b=(x^4-x^2/2-3)/y)
    (hY : y^2=x^4-(5/2:ℂ)*x^2-2)
    (v24 v84 : ℂ)
    (hbase : (negativeBaseA x y z w a b)*v24+(negativeBaseB x y z w a b)*v84=0)
    (hrow : (negativeCoeff164A x y z w a b)*v24+(negativeCoeff164B x y z w a b)*v84=0) : (negativeRow164 (x^2) z w)*v84=0 := by
  have hd := negative_determinant_reduction_164 x y z w a b hx hy0 hw ha hb hY
  have hh : ((negativeBaseA x y z w a b)*(negativeCoeff164B x y z w a b)-(negativeCoeff164A x y z w a b)*(negativeBaseB x y z w a b))*v84=0 := by
    linear_combination (negativeBaseA x y z w a b)*hrow-(negativeCoeff164A x y z w a b)*hbase
  have he : (3:ℂ)*((negativeRow164 (x^2) z w)*v84)=0 := by
    calc
      (3:ℂ)*((negativeRow164 (x^2) z w)*v84)=((3)*(negativeRow164 (x^2) z w))*v84 := by ring
      _ = ((2*x^(4:ℕ)*w - 5*x^(2:ℕ)*w - 4*w)*((negativeBaseA x y z w a b)*(negativeCoeff164B x y z w a b)-(negativeCoeff164A x y z w a b)*(negativeBaseB x y z w a b)))*v84 := by rw [hd]
      _ = 0 := by linear_combination (2*x^(4:ℕ)*w - 5*x^(2:ℕ)*w - 4*w)*hh
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

#print axioms negative_determinant_reduction_164
#print axioms negative_homogeneous_residual_164

def negativeCoeff21A (x y z w a b : ℂ) : ℂ := -2*x^(5:ℕ)*a - x^(4:ℕ)*a^(2:ℕ) - x^(4:ℕ) + 2*x^(3:ℕ)*a - x^(2:ℕ)*y^(2:ℕ) - x^(2:ℕ)*y*b + x^(2:ℕ)*a^(2:ℕ) + 3*x^(2:ℕ) + 2*x*a - 3

def negativeCoeff21B (x y z w a b : ℂ) : ℂ := (x^(10:ℕ)*a^(2:ℕ) + x^(9:ℕ)*y^(2:ℕ)*a - x^(9:ℕ)*y*a*b + 3*x^(9:ℕ)*a + x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(8:ℕ)*y^(2:ℕ) - x^(8:ℕ)*y*a^(2:ℕ)*b - x^(8:ℕ)*y*b - 4*x^(8:ℕ)*a^(2:ℕ) + 2*x^(8:ℕ) + x^(7:ℕ)*y^(2:ℕ)*a + x^(7:ℕ)*y*a*b + x^(7:ℕ)*z*a - x^(7:ℕ)*a^(3:ℕ) - 8*x^(7:ℕ)*a - x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) - x^(6:ℕ)*y^(2:ℕ) + 2*x^(6:ℕ)*y*a^(2:ℕ)*b + 3*x^(6:ℕ)*y*b + x^(6:ℕ)*z*a^(2:ℕ) + 4*x^(6:ℕ)*a^(2:ℕ) - 5*x^(6:ℕ) - 4*x^(5:ℕ)*y^(2:ℕ)*a + 2*x^(5:ℕ)*y*a*b - x^(5:ℕ)*z*a - x^(5:ℕ)*w*a + x^(5:ℕ)*a^(3:ℕ) + 11*x^(5:ℕ)*a - 3*x^(4:ℕ)*y^(2:ℕ) - x^(4:ℕ)*y*a^(2:ℕ)*b - 2*x^(4:ℕ)*y*b - 2*x^(4:ℕ)*z*a^(2:ℕ) - x^(4:ℕ)*z - x^(4:ℕ)*w + 5*x^(4:ℕ) + 2*x^(3:ℕ)*y^(2:ℕ)*a - 2*x^(3:ℕ)*y*a*b - 3*x^(3:ℕ)*z*a + x^(3:ℕ)*w*a - 6*x^(3:ℕ)*a + 3*x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*z*a^(2:ℕ) + 2*x^(2:ℕ)*z + 2*x^(2:ℕ)*w - 7*x^(2:ℕ) - x*y^(2:ℕ)*a + 3*x*z*a - 3*y^(2:ℕ) - 2*z)/w

theorem negative_determinant_reduction_21 (x y z w a b : ℂ) (hx : x≠0) (hy0 : y≠0) (hw : w≠0)
    (ha : a= -x/2-2/x) (hb : b=(x^4-x^2/2-3)/y)
    (hY : y^2=x^4-(5/2:ℂ)*x^2-2) :
    (2*w)*((negativeBaseA x y z w a b)*(negativeCoeff21B x y z w a b)-(negativeCoeff21A x y z w a b)*(negativeBaseB x y z w a b))=(1)*(negativeRow21 (x^2) z w) := by
  dsimp only [negativeBaseA,negativeBaseB,negativeCoeff21A,negativeCoeff21B,negativeRow21,negativeRow21Z,negativeRow21W,negativeRow21C]
  rw [ha,hb]
  linear_combination (norm := (field_simp [hx,hy0,hw]; ring)) ((2*x^(14:ℕ) - 3*x^(12:ℕ) + 2*x^(10:ℕ)*y^(2:ℕ) - x^(10:ℕ) - 2*x^(8:ℕ)*y^(2:ℕ) + 2*x^(8:ℕ)*z - 6*x^(8:ℕ) - 4*x^(6:ℕ)*w + 6*x^(6:ℕ) - 16*x^(4:ℕ)*y^(2:ℕ) - 6*x^(4:ℕ)*z - 4*x^(4:ℕ)*w + 32*x^(4:ℕ) - 12*x^(2:ℕ)*y^(2:ℕ) - 20*x^(2:ℕ)*z - 16*x^(2:ℕ)*w - 64*x^(2:ℕ) + 8*y^(2:ℕ) + 32*z - 48)/4)*hY

theorem negative_homogeneous_residual_21 (x y z w a b : ℂ) (hx : x≠0) (hy0 : y≠0) (hw : w≠0)
    (ha : a= -x/2-2/x) (hb : b=(x^4-x^2/2-3)/y)
    (hY : y^2=x^4-(5/2:ℂ)*x^2-2)
    (v24 v84 : ℂ)
    (hbase : (negativeBaseA x y z w a b)*v24+(negativeBaseB x y z w a b)*v84=0)
    (hrow : (negativeCoeff21A x y z w a b)*v24+(negativeCoeff21B x y z w a b)*v84=0) : (negativeRow21 (x^2) z w)*v84=0 := by
  have hd := negative_determinant_reduction_21 x y z w a b hx hy0 hw ha hb hY
  have hh : ((negativeBaseA x y z w a b)*(negativeCoeff21B x y z w a b)-(negativeCoeff21A x y z w a b)*(negativeBaseB x y z w a b))*v84=0 := by
    linear_combination (negativeBaseA x y z w a b)*hrow-(negativeCoeff21A x y z w a b)*hbase
  have he : (1:ℂ)*((negativeRow21 (x^2) z w)*v84)=0 := by
    calc
      (1:ℂ)*((negativeRow21 (x^2) z w)*v84)=((1)*(negativeRow21 (x^2) z w))*v84 := by ring
      _ = ((2*w)*((negativeBaseA x y z w a b)*(negativeCoeff21B x y z w a b)-(negativeCoeff21A x y z w a b)*(negativeBaseB x y z w a b)))*v84 := by rw [hd]
      _ = 0 := by linear_combination (2*w)*hh
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

#print axioms negative_determinant_reduction_21
#print axioms negative_homogeneous_residual_21

def positiveBaseA (x y z w a b : ℂ) : ℂ := 2*x^(3:ℕ)*a + x^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ) - 3

def positiveBaseB (x y z w a b : ℂ) : ℂ := (-x^(8:ℕ)*a^(2:ℕ) - x^(7:ℕ)*y^(2:ℕ)*a + x^(7:ℕ)*y*a*b - x^(7:ℕ)*a - x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) - x^(6:ℕ)*y^(2:ℕ) + x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*y*b + 3*x^(6:ℕ)*a^(2:ℕ) - 2*x^(5:ℕ)*y^(2:ℕ)*a + x^(5:ℕ)*z*a + x^(5:ℕ)*a^(3:ℕ) + x^(5:ℕ)*a - x^(4:ℕ)*y*a^(2:ℕ)*b - 2*x^(4:ℕ)*y*b + x^(4:ℕ)*z*a^(2:ℕ) + x^(4:ℕ)*a^(2:ℕ) - 3*x^(4:ℕ) - 2*x^(3:ℕ)*y*a*b + x^(3:ℕ)*w*a - x^(3:ℕ)*a + x^(2:ℕ)*y*b - x^(2:ℕ)*z*a^(2:ℕ) - x^(2:ℕ)*z + x^(2:ℕ)*w - x^(2:ℕ)*a^(2:ℕ) + 4*x^(2:ℕ) + x*y^(2:ℕ)*a + x*y*a*b - x*z*a + 2*y^(2:ℕ) + 2*z - w - 1)/w

def positiveCoeff14A (x y z w a b : ℂ) : ℂ := -2*x^(3:ℕ)*a - x^(2:ℕ)*a^(2:ℕ) - x^(2:ℕ) - y^(2:ℕ) - y*b - 2

def positiveCoeff14B (x y z w a b : ℂ) : ℂ := (x^(8:ℕ)*a^(2:ℕ) + x^(7:ℕ)*y^(2:ℕ)*a - x^(7:ℕ)*y*a*b + x^(7:ℕ)*a + x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ) - x^(6:ℕ)*y*a^(2:ℕ)*b - x^(6:ℕ)*y*b - 3*x^(6:ℕ)*a^(2:ℕ) + 2*x^(5:ℕ)*y^(2:ℕ)*a - x^(5:ℕ)*z*a - x^(5:ℕ)*a^(3:ℕ) + x^(4:ℕ)*y^(2:ℕ) + x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*y*b - x^(4:ℕ)*z*a^(2:ℕ) - x^(4:ℕ)*a^(2:ℕ) + 2*x^(4:ℕ) + x^(3:ℕ)*y^(2:ℕ)*a + x^(3:ℕ)*y*a*b - x^(3:ℕ)*w*a - 2*x^(3:ℕ)*a + x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*z*a^(2:ℕ) - x^(2:ℕ)*z - x^(2:ℕ)*w - x^(2:ℕ) - x*y^(2:ℕ)*a + x*z*a - x*a - w + 1)/w

theorem positive_determinant_reduction_14 (x y z w a b : ℂ) (hx : x≠0) (hy0 : y≠0) (hw : w≠0)
    (ha : a= -x/2-2/x) (hb : b=(x^4-x^2/2-3)/y)
    (hY : y^2=x^4-(5/2:ℂ)*x^2-2) :
    (2*w)*((positiveBaseA x y z w a b)*(positiveCoeff14B x y z w a b)-(positiveCoeff14A x y z w a b)*(positiveBaseB x y z w a b))=(-1)*(positiveRow14 (x^2) z w) := by
  dsimp only [positiveBaseA,positiveBaseB,positiveCoeff14A,positiveCoeff14B,positiveRow14,positiveRow14Z,positiveRow14W,positiveRow14C]
  rw [ha,hb]
  linear_combination (norm := (field_simp [hx,hy0,hw]; ring)) ((2*x^(12:ℕ) - x^(10:ℕ) + 2*x^(8:ℕ)*y^(2:ℕ) + x^(8:ℕ) - 2*x^(6:ℕ)*z - 6*x^(6:ℕ) - 2*x^(4:ℕ)*z - 4*x^(4:ℕ)*w - 4*x^(4:ℕ) - 4*x^(2:ℕ)*y^(2:ℕ) + 12*x^(2:ℕ)*z - 8*x^(2:ℕ)*w - 28*x^(2:ℕ) - 8*w + 24)/4)*hY

theorem positive_homogeneous_residual_14 (x y z w a b : ℂ) (hx : x≠0) (hy0 : y≠0) (hw : w≠0)
    (ha : a= -x/2-2/x) (hb : b=(x^4-x^2/2-3)/y)
    (hY : y^2=x^4-(5/2:ℂ)*x^2-2)
    (v24 v84 : ℂ)
    (hbase : (positiveBaseA x y z w a b)*v24+(positiveBaseB x y z w a b)*v84=0)
    (hrow : (positiveCoeff14A x y z w a b)*v24+(positiveCoeff14B x y z w a b)*v84=0) : (positiveRow14 (x^2) z w)*v84=0 := by
  have hd := positive_determinant_reduction_14 x y z w a b hx hy0 hw ha hb hY
  have hh : ((positiveBaseA x y z w a b)*(positiveCoeff14B x y z w a b)-(positiveCoeff14A x y z w a b)*(positiveBaseB x y z w a b))*v84=0 := by
    linear_combination (positiveBaseA x y z w a b)*hrow-(positiveCoeff14A x y z w a b)*hbase
  have he : (-1:ℂ)*((positiveRow14 (x^2) z w)*v84)=0 := by
    calc
      (-1:ℂ)*((positiveRow14 (x^2) z w)*v84)=((-1)*(positiveRow14 (x^2) z w))*v84 := by ring
      _ = ((2*w)*((positiveBaseA x y z w a b)*(positiveCoeff14B x y z w a b)-(positiveCoeff14A x y z w a b)*(positiveBaseB x y z w a b)))*v84 := by rw [hd]
      _ = 0 := by linear_combination (2*w)*hh
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

#print axioms positive_determinant_reduction_14
#print axioms positive_homogeneous_residual_14

def positiveCoeff164A (x y z w a b : ℂ) : ℂ := (2*x^(4:ℕ) - x^(3:ℕ)*a - x^(2:ℕ)*a^(2:ℕ) - 4*x^(2:ℕ) - 3*x*a - y^(2:ℕ) - y*b + 1)/(y^(2:ℕ))

def positiveCoeff164B (x y z w a b : ℂ) : ℂ := (-x^(9:ℕ)*a - x^(8:ℕ)*y^(2:ℕ) + x^(8:ℕ)*y*b + x^(8:ℕ)*a^(2:ℕ) + 5*x^(7:ℕ)*a + x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(6:ℕ)*y^(2:ℕ) - x^(6:ℕ)*y*a^(2:ℕ)*b - 3*x^(6:ℕ)*y*b + x^(6:ℕ)*z - x^(6:ℕ)*a^(2:ℕ) - 3*x^(6:ℕ) + 4*x^(5:ℕ)*y^(2:ℕ)*a - 3*x^(5:ℕ)*y*a*b - x^(5:ℕ)*a^(3:ℕ) - 3*x^(5:ℕ)*a + x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y^(2:ℕ) + 2*x^(4:ℕ)*y*b - x^(4:ℕ)*z*a^(2:ℕ) - 2*x^(4:ℕ)*z + x^(4:ℕ)*w - 5*x^(4:ℕ)*a^(2:ℕ) + 8*x^(4:ℕ) + 2*x^(3:ℕ)*y^(2:ℕ)*a + 3*x^(3:ℕ)*y*a*b - 3*x^(3:ℕ)*z*a - x^(3:ℕ)*w*a - x^(3:ℕ)*a^(3:ℕ) + x^(3:ℕ)*a + 3*x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y*a^(2:ℕ)*b + x^(2:ℕ)*z*a^(2:ℕ) + x^(2:ℕ)*z - 2*x^(2:ℕ)*w - 5*x^(2:ℕ) + 3*x*z*a - x*w*a - x*a - 2*y^(2:ℕ) - z + 2)/(y^(2:ℕ)*w)

theorem positive_determinant_reduction_164 (x y z w a b : ℂ) (hx : x≠0) (hy0 : y≠0) (hw : w≠0)
    (ha : a= -x/2-2/x) (hb : b=(x^4-x^2/2-3)/y)
    (hY : y^2=x^4-(5/2:ℂ)*x^2-2) :
    (2*x^(4:ℕ)*w - 5*x^(2:ℕ)*w - 4*w)*((positiveBaseA x y z w a b)*(positiveCoeff164B x y z w a b)-(positiveCoeff164A x y z w a b)*(positiveBaseB x y z w a b))=(-1)*(positiveRow164 (x^2) z w) := by
  dsimp only [positiveBaseA,positiveBaseB,positiveCoeff164A,positiveCoeff164B,positiveRow164,positiveRow164Z,positiveRow164W,positiveRow164C]
  rw [ha,hb]
  linear_combination (norm := (field_simp [hx,hy0,hw]; ring)) ((8*x^(16:ℕ) - 10*x^(14:ℕ) + 8*x^(12:ℕ)*y^(2:ℕ) - 105*x^(12:ℕ) - 20*x^(10:ℕ)*y^(2:ℕ) + 8*x^(10:ℕ)*z + 208*x^(10:ℕ) - 16*x^(8:ℕ)*y^(2:ℕ) - 24*x^(8:ℕ)*z + 16*x^(8:ℕ)*w - 114*x^(8:ℕ) - 16*x^(6:ℕ)*y^(2:ℕ) + 16*x^(6:ℕ)*z + 52*x^(6:ℕ)*w + 328*x^(6:ℕ) + 40*x^(4:ℕ)*y^(2:ℕ) - 32*x^(4:ℕ)*z - 56*x^(4:ℕ)*w - 544*x^(4:ℕ) + 32*x^(2:ℕ)*y^(2:ℕ) + 80*x^(2:ℕ)*z - 80*x^(2:ℕ)*w - 80*x^(2:ℕ) + 96*z - 256*w + 192)/(16*y^(2:ℕ)))*hY

theorem positive_homogeneous_residual_164 (x y z w a b : ℂ) (hx : x≠0) (hy0 : y≠0) (hw : w≠0)
    (ha : a= -x/2-2/x) (hb : b=(x^4-x^2/2-3)/y)
    (hY : y^2=x^4-(5/2:ℂ)*x^2-2)
    (v24 v84 : ℂ)
    (hbase : (positiveBaseA x y z w a b)*v24+(positiveBaseB x y z w a b)*v84=0)
    (hrow : (positiveCoeff164A x y z w a b)*v24+(positiveCoeff164B x y z w a b)*v84=0) : (positiveRow164 (x^2) z w)*v84=0 := by
  have hd := positive_determinant_reduction_164 x y z w a b hx hy0 hw ha hb hY
  have hh : ((positiveBaseA x y z w a b)*(positiveCoeff164B x y z w a b)-(positiveCoeff164A x y z w a b)*(positiveBaseB x y z w a b))*v84=0 := by
    linear_combination (positiveBaseA x y z w a b)*hrow-(positiveCoeff164A x y z w a b)*hbase
  have he : (-1:ℂ)*((positiveRow164 (x^2) z w)*v84)=0 := by
    calc
      (-1:ℂ)*((positiveRow164 (x^2) z w)*v84)=((-1)*(positiveRow164 (x^2) z w))*v84 := by ring
      _ = ((2*x^(4:ℕ)*w - 5*x^(2:ℕ)*w - 4*w)*((positiveBaseA x y z w a b)*(positiveCoeff164B x y z w a b)-(positiveCoeff164A x y z w a b)*(positiveBaseB x y z w a b)))*v84 := by rw [hd]
      _ = 0 := by linear_combination (2*x^(4:ℕ)*w - 5*x^(2:ℕ)*w - 4*w)*hh
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

#print axioms positive_determinant_reduction_164
#print axioms positive_homogeneous_residual_164

def positiveCoeff16A (x y z w a b : ℂ) : ℂ := (2*x^(5:ℕ)*a + 3*x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ) + x^(3:ℕ)*a^(3:ℕ) + 3*x^(3:ℕ)*a + x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y*b + x^(2:ℕ)*a^(2:ℕ) + x^(2:ℕ) - 3*x*a + 3)/(x^(2:ℕ))

def positiveCoeff16B (x y z w a b : ℂ) : ℂ := (-x^(10:ℕ)*a^(2:ℕ) - x^(9:ℕ)*y^(2:ℕ)*a + x^(9:ℕ)*y*a*b - x^(9:ℕ)*a^(3:ℕ) - x^(9:ℕ)*a - 2*x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) - x^(8:ℕ)*y^(2:ℕ) + 2*x^(8:ℕ)*y*a^(2:ℕ)*b + x^(8:ℕ)*y*b + x^(8:ℕ)*a^(2:ℕ) - x^(7:ℕ)*y^(2:ℕ)*a^(3:ℕ) - 4*x^(7:ℕ)*y^(2:ℕ)*a + x^(7:ℕ)*y*a^(3:ℕ)*b + 2*x^(7:ℕ)*y*a*b + x^(7:ℕ)*z*a + 4*x^(7:ℕ)*a^(3:ℕ) - x^(7:ℕ)*a - 3*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) - 2*x^(6:ℕ)*y^(2:ℕ) + 2*x^(6:ℕ)*z*a^(2:ℕ) + x^(6:ℕ)*a^(4:ℕ) + 4*x^(6:ℕ)*a^(2:ℕ) - 3*x^(6:ℕ) - 4*x^(5:ℕ)*y^(2:ℕ)*a - x^(5:ℕ)*y*a^(3:ℕ)*b - 2*x^(5:ℕ)*y*a*b + x^(5:ℕ)*z*a^(3:ℕ) + x^(5:ℕ)*z*a + x^(5:ℕ)*w*a + 2*x^(5:ℕ)*a^(3:ℕ) - x^(5:ℕ)*a - x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) - 2*x^(4:ℕ)*y^(2:ℕ) - 2*x^(4:ℕ)*y*a^(2:ℕ)*b - x^(4:ℕ)*y*b + x^(4:ℕ)*z + x^(4:ℕ)*w*a^(2:ℕ) + x^(4:ℕ)*w + 3*x^(4:ℕ)*a^(2:ℕ) - x^(3:ℕ)*y^(2:ℕ)*a - x^(3:ℕ)*y*a*b - x^(3:ℕ)*z*a^(3:ℕ) - 3*x^(3:ℕ)*z*a + 2*x^(3:ℕ)*w*a + 4*x^(3:ℕ)*a + x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) - x^(2:ℕ)*y^(2:ℕ) + x^(2:ℕ)*y*b - 2*x^(2:ℕ)*z*a^(2:ℕ) + x^(2:ℕ)*z - 3*x^(2:ℕ) + 2*x*y^(2:ℕ)*a + 3*x*z*a - 2*y^(2:ℕ) - y*b - 2*z + w)/(x^(2:ℕ)*w)

theorem positive_determinant_reduction_16 (x y z w a b : ℂ) (hx : x≠0) (hy0 : y≠0) (hw : w≠0)
    (ha : a= -x/2-2/x) (hb : b=(x^4-x^2/2-3)/y)
    (hY : y^2=x^4-(5/2:ℂ)*x^2-2) :
    (2*x^(2:ℕ)*w)*((positiveBaseA x y z w a b)*(positiveCoeff16B x y z w a b)-(positiveCoeff16A x y z w a b)*(positiveBaseB x y z w a b))=(1)*(positiveRow16 (x^2) z w) := by
  dsimp only [positiveBaseA,positiveBaseB,positiveCoeff16A,positiveCoeff16B,positiveRow16,positiveRow16Z,positiveRow16W,positiveRow16C]
  rw [ha,hb]
  linear_combination (norm := (field_simp [hx,hy0,hw]; ring)) ((-4*x^(14:ℕ) + 2*x^(12:ℕ) - 4*x^(10:ℕ)*y^(2:ℕ) + 3*x^(10:ℕ) + 4*x^(8:ℕ)*z - 16*x^(8:ℕ) + 4*x^(6:ℕ)*z + 8*x^(6:ℕ)*w + 18*x^(6:ℕ) + 8*x^(4:ℕ)*y^(2:ℕ) - 24*x^(4:ℕ)*z + 16*x^(4:ℕ)*w + 72*x^(4:ℕ) + 16*x^(2:ℕ)*w + 24*x^(2:ℕ) - 32)/8)*hY

theorem positive_homogeneous_residual_16 (x y z w a b : ℂ) (hx : x≠0) (hy0 : y≠0) (hw : w≠0)
    (ha : a= -x/2-2/x) (hb : b=(x^4-x^2/2-3)/y)
    (hY : y^2=x^4-(5/2:ℂ)*x^2-2)
    (v24 v84 : ℂ)
    (hbase : (positiveBaseA x y z w a b)*v24+(positiveBaseB x y z w a b)*v84=0)
    (hrow : (positiveCoeff16A x y z w a b)*v24+(positiveCoeff16B x y z w a b)*v84=0) : (positiveRow16 (x^2) z w)*v84=0 := by
  have hd := positive_determinant_reduction_16 x y z w a b hx hy0 hw ha hb hY
  have hh : ((positiveBaseA x y z w a b)*(positiveCoeff16B x y z w a b)-(positiveCoeff16A x y z w a b)*(positiveBaseB x y z w a b))*v84=0 := by
    linear_combination (positiveBaseA x y z w a b)*hrow-(positiveCoeff16A x y z w a b)*hbase
  have he : (1:ℂ)*((positiveRow16 (x^2) z w)*v84)=0 := by
    calc
      (1:ℂ)*((positiveRow16 (x^2) z w)*v84)=((1)*(positiveRow16 (x^2) z w))*v84 := by ring
      _ = ((2*x^(2:ℕ)*w)*((positiveBaseA x y z w a b)*(positiveCoeff16B x y z w a b)-(positiveCoeff16A x y z w a b)*(positiveBaseB x y z w a b)))*v84 := by rw [hd]
      _ = 0 := by linear_combination (2*x^(2:ℕ)*w)*hh
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

#print axioms positive_determinant_reduction_16
#print axioms positive_homogeneous_residual_16
end QuantitativeArithmeticSmallLevelThirtyFiveGapOne
end
end

/-! ## ThirtyFiveGapOneParameters -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGapOne
open Complex

/-- The actual reduced rows 45 and 159 force the two one-step parameter
relations whenever the remaining coordinate is nonzero. -/
theorem gap_one_parameter_relations (x y a b t : ℂ) (hx : x≠0) (hy : y≠0)
    (ht : t≠0) (ha : a= -x/2-2/x)
    (h45 : (x^4-2*x^2+x*a-y^2)*t=0)
    (h159 : ((x^4+x*a-y*b-1)/y^2)*t=0) :
    y^2=x^4-(5/2:ℂ)*x^2-2 ∧ b=(x^4-x^2/2-3)/y := by
  have hE := (mul_eq_zero.mp h45).resolve_right ht
  have hB := (mul_eq_zero.mp h159).resolve_right ht
  rw [ha] at hE hB
  constructor
  · linear_combination (norm := (field_simp [hx]; ring)) -hE
  · linear_combination (norm := (field_simp [hx,hy]; ring)) (-y)*hB

#print axioms gap_one_parameter_relations
end QuantitativeArithmeticSmallLevelThirtyFiveGapOne
end
end

/-! ## ThirtyFiveGapOneCofactors -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGapOne
open Complex QuantitativeArithmeticOuterRootNorm

theorem negative_model_lower (u : ℂ) (hu : 4≤‖u‖) :
    (2541/8192:ℝ)*‖u‖^6*‖u+(7301/1000:ℂ)‖≤‖negativeModel u‖ := by
  have h1 := root_factor_lower u (-1/8) 4 1 (by norm_num) hu (by norm_num) (by norm_num)
  have h2 := root_factor_lower u (2629/1000) 4 3 (by norm_num) hu (by norm_num) (by norm_num)
  have h3 := quadratic_outer_lower u (567/250) (1493/1000) (5/4) hu
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 := quadratic_outer_lower u (-713/200) (3497/1000) 2 hu
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h1 h2 h3 h4
  have he : negativeModel u=(14:ℂ)*(u+7301/1000)*(u+1/8)*(u-2629/1000)*
      (u^2+(567/250)*u+1493/1000)*(u^2-(713/200)*u+3497/1000) := by
    unfold negativeModel
    ring
  rw [he]
  simp only [norm_mul]
  norm_num only [norm_ofNat]
  calc
    (2541/8192:ℝ)*‖u‖^6*‖u+(7301/1000:ℂ)‖ =
        14*‖u+(7301/1000:ℂ)‖*((3/4)*‖u‖)*((1/4)*‖u‖)*
          ((121/256)*‖u‖^2)*((1/4)*‖u‖^2) := by ring
    _ ≤ _ := by
      gcongr
      simpa only [sub_eq_add_neg] using h4

theorem positive_model_lower (u : ℂ) (hu : 4≤‖u‖) :
    (2685375/8388608:ℝ)*‖u‖^6*‖u+(9993/2000:ℂ)‖≤‖positiveModel u‖ := by
  have h1 := root_factor_lower u (-211/125) 4 2 (by norm_num) hu (by norm_num) (by norm_num)
  have h2 := root_factor_lower u (-5957/5000) 4 (5/4) (by norm_num) hu (by norm_num) (by norm_num)
  have h3 := root_factor_lower u (301/10000) 4 (1/8) (by norm_num) hu (by norm_num) (by norm_num)
  have h4 := root_factor_lower u (5091/2000) 4 (11/4) (by norm_num) hu (by norm_num) (by norm_num)
  have h5 := quadratic_outer_lower u (-19001/5000) (89054737/20000000) (17/8) hu
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h1 h2 h3 h4 h5
  have he : positiveModel u=(14:ℂ)*(u+9993/2000)*(u+211/125)*(u+5957/5000)*
      (u-301/10000)*(u-5091/2000)*(u^2-(19001/5000)*u+89054737/20000000) := by
    unfold positiveModel
    ring
  rw [he]
  simp only [norm_mul]
  norm_num only [norm_ofNat]
  calc
    (2685375/8388608:ℝ)*‖u‖^6*‖u+(9993/2000:ℂ)‖ =
        14*‖u+(9993/2000:ℂ)‖*((1/2)*‖u‖)*((11/16)*‖u‖)*
          ((31/32)*‖u‖)*((5/16)*‖u‖)*((225/1024)*‖u‖^2) := by ring
    _ ≤ _ := by
      gcongr
      simpa only [sub_eq_add_neg] using h5

#print axioms negative_model_lower
#print axioms positive_model_lower
end QuantitativeArithmeticSmallLevelThirtyFiveGapOne
end
end

/-! ## ThirtyFiveGapOneRoots -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGapOne
open Complex QuantitativeArithmeticOuterRootNorm

/-- Outside the radius-four disk, a root lies in this small rational disk. -/
theorem negative_outer_disk (u : ℂ) (hu : 4≤‖u‖) (hzero : negativePolynomial u=0) :
    ‖u+(7301/1000:ℂ)‖<1/16 := by
  have he := negative_error_bound u hu
  rw [hzero,zero_sub,norm_neg] at he
  have hl := negative_model_lower u hu
  have ht : 0<‖u‖^6 := pow_pos (by linarith) 6
  have hc : (249682520631353/16384000000000000:ℝ)*‖u‖^6<((2541/8192:ℝ)/16)*‖u‖^6 :=
    mul_lt_mul_of_pos_right (by norm_num) ht
  by_contra! h
  have hh := mul_le_mul_of_nonneg_left h
    (mul_nonneg (by norm_num : (0:ℝ)≤2541/8192) ht.le)
  nlinarith

theorem negative_root_bounds (u : ℂ) (hu : 4≤‖u‖) (hzero : negativePolynomial u=0) :
    ‖u‖<8 ∧ 27<‖u^2-(5/2:ℂ)*u-2‖ := by
  apply negative_disk_bounds u (7301/1000:ℝ) (by norm_num) (by norm_num)
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using negative_outer_disk u hu hzero

#print axioms negative_outer_disk
#print axioms negative_root_bounds

/-- Outside the radius-four disk, a root lies in this small rational disk. -/
theorem positive_outer_disk (u : ℂ) (hu : 4≤‖u‖) (hzero : positivePolynomial u=0) :
    ‖u+(9993/2000:ℂ)‖<1/16 := by
  have he := positive_error_bound u hu
  rw [hzero,zero_sub,norm_neg] at he
  have hl := positive_model_lower u hu
  have ht : 0<‖u‖^6 := pow_pos (by linarith) 6
  have hc : (2930818612741349503696141/1024000000000000000000000000:ℝ)*‖u‖^6<((2685375/8388608:ℝ)/16)*‖u‖^6 :=
    mul_lt_mul_of_pos_right (by norm_num) ht
  by_contra! h
  have hh := mul_le_mul_of_nonneg_left h
    (mul_nonneg (by norm_num : (0:ℝ)≤2685375/8388608) ht.le)
  nlinarith

theorem positive_root_bounds (u : ℂ) (hu : 4≤‖u‖) (hzero : positivePolynomial u=0) :
    ‖u‖<8 ∧ 27<‖u^2-(5/2:ℂ)*u-2‖ := by
  apply negative_disk_bounds u (9993/2000:ℝ) (by norm_num) (by norm_num)
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using positive_outer_disk u hu hzero

#print axioms positive_outer_disk
#print axioms positive_root_bounds
end QuantitativeArithmeticSmallLevelThirtyFiveGapOne
end
end

/-! ## ThirtyFiveGapOnePhysical -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex
open QuantitativeArithmeticSmallLevelThirtyFiveGapOne

theorem physical_four_nine_bounds (m : ℕ) (s : ℂ)
    (hu : ‖(primeParameter 2 m s)^2‖<8) : ‖(primeParameter 3 m s)^2‖<27 := by
  have hx : ‖(primeParameter 2 m s)^2‖=(4:ℝ)^(s.re-(m:ℝ)) := by
    convert primeParameter_pow_norm 2 m 2 (by decide) s using 1
    norm_num
  have hy : ‖(primeParameter 3 m s)^2‖=(9:ℝ)^(s.re-(m:ℝ)) := by
    convert primeParameter_pow_norm 3 m 2 (by decide) s using 1
    norm_num
  have h4 : (4:ℝ)^(3/2:ℝ)=8 := by
    rw [show (3/2:ℝ)=(1/2:ℝ)*(3:ℕ) by norm_num,
      Real.rpow_mul (by norm_num),Real.rpow_natCast,← Real.sqrt_eq_rpow]
    norm_num
  have h9 : (9:ℝ)^(3/2:ℝ)=27 := by
    rw [show (3/2:ℝ)=(1/2:ℝ)*(3:ℕ) by norm_num,
      Real.rpow_mul (by norm_num),Real.rpow_natCast,← Real.sqrt_eq_rpow]
    norm_num
  rw [hx,← h4] at hu
  have hα := (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ)<4)).mp hu
  rw [hy,← h9]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<9) hα

/-- The one-step degree-seven obstruction cannot vanish at the physical
prime powers satisfying the first reduced row. -/
theorem physical_negative_polynomial_ne_zero (m : ℕ) (s : ℂ)
    (hu : 4≤‖(primeParameter 2 m s)^2‖)
    (hy : (primeParameter 3 m s)^2=(primeParameter 2 m s)^4-
      (5/2:ℂ)*(primeParameter 2 m s)^2-2) :
    negativePolynomial ((primeParameter 2 m s)^2)≠0 := by
  intro hzero
  obtain ⟨hu8,hY⟩ := negative_root_bounds ((primeParameter 2 m s)^2) hu hzero
  have hy27 := physical_four_nine_bounds m s hu8
  have he : ((primeParameter 2 m s)^2)^2-(5/2:ℂ)*(primeParameter 2 m s)^2-2=
      (primeParameter 3 m s)^2 := by rw [hy]; ring
  rw [he] at hY
  linarith

#print axioms physical_negative_polynomial_ne_zero

/-- The one-step degree-seven obstruction cannot vanish at the physical
prime powers satisfying the first reduced row. -/
theorem physical_positive_polynomial_ne_zero (m : ℕ) (s : ℂ)
    (hu : 4≤‖(primeParameter 2 m s)^2‖)
    (hy : (primeParameter 3 m s)^2=(primeParameter 2 m s)^4-
      (5/2:ℂ)*(primeParameter 2 m s)^2-2) :
    positivePolynomial ((primeParameter 2 m s)^2)≠0 := by
  intro hzero
  obtain ⟨hu8,hY⟩ := positive_root_bounds ((primeParameter 2 m s)^2) hu hzero
  have hy27 := physical_four_nine_bounds m s hu8
  have he : ((primeParameter 2 m s)^2)^2-(5/2:ℂ)*(primeParameter 2 m s)^2-2=
      (primeParameter 3 m s)^2 := by rw [hy]; ring
  rw [he] at hY
  linarith

#print axioms physical_positive_polynomial_ne_zero

#print axioms physical_four_nine_bounds
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveGapOneObstruction -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex
open QuantitativeArithmeticSmallLevelThirtyFiveGapOne

theorem physical_minus_four_ne_zero (m : ℕ) (s : ℂ)
    (hy : (primeParameter 3 m s)^2=(primeParameter 2 m s)^4-
      (5/2:ℂ)*(primeParameter 2 m s)^2-2) :
    (primeParameter 2 m s)^2+4≠0 := by
  intro h
  have he : (primeParameter 2 m s)^2= -4 := by linear_combination h
  have hx : ‖(primeParameter 2 m s)^2‖=(4:ℝ)^(s.re-(m:ℝ)) := by
    convert primeParameter_pow_norm 2 m 2 (by decide) s using 1
    norm_num
  rw [he] at hx
  norm_num at hx
  have hα : s.re-(m:ℝ)=1 := by
    apply (Real.rpow_right_inj (by norm_num : (0:ℝ)<4) (by norm_num : (4:ℝ)≠1)).mp
    simpa only [Real.rpow_one] using hx.symm
  have hy9 : ‖(primeParameter 3 m s)^2‖=9 := by
    have hh := primeParameter_pow_norm 3 m 2 (by decide) s
    norm_num [hα] at hh
    simpa only [norm_pow] using hh
  have hy24 : (primeParameter 3 m s)^2=24 := by
    rw [hy,show (primeParameter 2 m s)^4=((primeParameter 2 m s)^2)^2 by ring,he]
    norm_num
  rw [hy24] at hy9
  norm_num at hy9

theorem gap_one_linear_factors (u : ℂ) (hu : 4≤‖u‖) :
    u≠0 ∧ 2*u-3≠0 ∧ u+2≠0 ∧ 3*u-2≠0 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro h; rw [h] at hu; norm_num at hu
  · intro h
    have he : u=3/2 := by linear_combination (1/2:ℂ)*h
    rw [he] at hu
    norm_num at hu
  · intro h
    have he : u= -2 := by linear_combination h
    rw [he] at hu
    norm_num at hu
  · intro h
    have he : u=2/3 := by linear_combination (1/3:ℂ)*h
    rw [he] at hu
    norm_num at hu

/-- The three already available negative-sign residual rows are incompatible
with the one-step physical locus. Their original-source linkage is separate. -/
theorem negative_gap_one_residuals_impossible (m : ℕ) (s z w : ℂ)
    (hu : 4≤‖(primeParameter 2 m s)^2‖)
    (hy : (primeParameter 3 m s)^2=(primeParameter 2 m s)^4-
      (5/2:ℂ)*(primeParameter 2 m s)^2-2)
    (h3 : negativeRow3 ((primeParameter 2 m s)^2) z w=0)
    (h164 : negativeRow164 ((primeParameter 2 m s)^2) z w=0)
    (h21 : negativeRow21 ((primeParameter 2 m s)^2) z w=0) : False := by
  have hd := negative_residual_determinant _ z w h3 h164 h21
  obtain ⟨h0,h2,_,_⟩ := gap_one_linear_factors _ hu
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h0) (pow_ne_zero 2 h2))
    (physical_negative_polynomial_ne_zero m s hu hy)) hd

/-- The positive-sign residuals have one extra root u=-4; the prime-power
relation excludes it as well. -/
theorem positive_gap_one_residuals_impossible (m : ℕ) (s z w : ℂ)
    (hu : 4≤‖(primeParameter 2 m s)^2‖)
    (hy : (primeParameter 3 m s)^2=(primeParameter 2 m s)^4-
      (5/2:ℂ)*(primeParameter 2 m s)^2-2)
    (h14 : positiveRow14 ((primeParameter 2 m s)^2) z w=0)
    (h164 : positiveRow164 ((primeParameter 2 m s)^2) z w=0)
    (h16 : positiveRow16 ((primeParameter 2 m s)^2) z w=0) : False := by
  have hd := positive_residual_determinant _ z w h14 h164 h16
  obtain ⟨_,_,h2,h3⟩ := gap_one_linear_factors _ hu
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (physical_minus_four_ne_zero m s hy)
      (pow_ne_zero 2 h2)) (pow_ne_zero 2 h3))
    (physical_positive_polynomial_ne_zero m s hu hy)) hd

#print axioms physical_minus_four_ne_zero
#print axioms gap_one_linear_factors
#print axioms negative_gap_one_residuals_impossible
#print axioms positive_gap_one_residuals_impossible
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveGapOneReducedKernel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex QuantitativeArithmeticSmallLevelThirtyFiveGapOne

theorem negative_gap_one_coordinate_zero (m : ℕ) (s z w a b : ℂ) (v : Fin 210 → ℂ)
    (hw : w≠0) (hu : 4≤‖(primeParameter 2 m s)^2‖)
    (ha : a= -primeParameter 2 m s/2-2/primeParameter 2 m s)
    (h42 : v 42=0) (h192 : v 192=0)
    (hA : negativeRowsAConclusion (primeParameter 2 m s) (primeParameter 3 m s) z w a b v)
    (hB : negativeRowsBConclusion (primeParameter 2 m s) (primeParameter 3 m s) z w a b v) : v 84=0 := by
  let x := primeParameter 2 m s
  let y := primeParameter 3 m s
  have hx : x≠0 := primeParameter_ne_zero 2 m (by decide) s
  have hy0 : y≠0 := primeParameter_ne_zero 3 m (by decide) s
  change a= -x/2-2/x at ha
  by_contra h84
  change negativeRowsAConclusion x y z w a b v at hA
  change negativeRowsBConclusion x y z w a b v at hB
  obtain ⟨_,h3,_,_,_⟩ := hA
  obtain ⟨_,_,h21,_,h45,_,h104,_,h159,_,h164⟩ := hB
  simp only [h42,h192,mul_zero,zero_add,add_zero] at h104 h3 h164 h21 h45 h159
  have he : (x^4-2*x^2+x*a-y^2)*v 84=0 := by
    convert h45 using 1 <;> ring
  have ht : ((x^4+x*a-y*b-1)/y^2)*v 84=0 := by
    convert h159 using 1 <;> field_simp [hy0] <;> ring
  obtain ⟨hY,hb⟩ := gap_one_parameter_relations x y a b (v 84) hx hy0 h84 ha he ht
  have hbase : negativeBaseA x y z w a b*v 24+negativeBaseB x y z w a b*v 84=0 := by
    convert h104 using 1 <;> dsimp only [negativeBaseA,negativeBaseB]
      <;> field_simp [hx,hy0,hw] <;> ring
  have hr3 : negativeCoeff3A x y z w a b*v 24+negativeCoeff3B x y z w a b*v 84=0 := by
    convert h3 using 1 <;> dsimp only [negativeCoeff3A,negativeCoeff3B]
      <;> field_simp [hx,hy0,hw] <;> ring
  have hR3 : negativeRow3 (x^2) z w=0 :=
    (mul_eq_zero.mp (negative_homogeneous_residual_3 x y z w a b hx hy0 hw ha hb hY
      (v 24) (v 84) hbase hr3)).resolve_right h84
  have hr164 : negativeCoeff164A x y z w a b*v 24+negativeCoeff164B x y z w a b*v 84=0 := by
    convert h164 using 1 <;> dsimp only [negativeCoeff164A,negativeCoeff164B]
      <;> field_simp [hx,hy0,hw] <;> ring
  have hR164 : negativeRow164 (x^2) z w=0 :=
    (mul_eq_zero.mp (negative_homogeneous_residual_164 x y z w a b hx hy0 hw ha hb hY
      (v 24) (v 84) hbase hr164)).resolve_right h84
  have hr21 : negativeCoeff21A x y z w a b*v 24+negativeCoeff21B x y z w a b*v 84=0 := by
    convert h21 using 1 <;> dsimp only [negativeCoeff21A,negativeCoeff21B]
      <;> field_simp [hx,hy0,hw] <;> ring
  have hR21 : negativeRow21 (x^2) z w=0 :=
    (mul_eq_zero.mp (negative_homogeneous_residual_21 x y z w a b hx hy0 hw ha hb hY
      (v 24) (v 84) hbase hr21)).resolve_right h84
  exact negative_gap_one_residuals_impossible m s z w hu hY hR3 hR164 hR21

#print axioms negative_gap_one_coordinate_zero

theorem positive_gap_one_coordinate_zero (m : ℕ) (s z w a b : ℂ) (v : Fin 210 → ℂ)
    (hw : w≠0) (hu : 4≤‖(primeParameter 2 m s)^2‖)
    (ha : a= -primeParameter 2 m s/2-2/primeParameter 2 m s)
    (h42 : v 42=0) (h192 : v 192=0)
    (hP : positiveRowsConclusion (primeParameter 2 m s) (primeParameter 3 m s) z w a b v) : v 84=0 := by
  let x := primeParameter 2 m s
  let y := primeParameter 3 m s
  have hx : x≠0 := primeParameter_ne_zero 2 m (by decide) s
  have hy0 : y≠0 := primeParameter_ne_zero 3 m (by decide) s
  change a= -x/2-2/x at ha
  by_contra h84
  change positiveRowsConclusion x y z w a b v at hP
  obtain ⟨_,h3,_,h14,h16,_,_,h45,_,_,h159,_,h164⟩ := hP
  simp only [h42,h192,mul_zero,zero_add,add_zero] at h3 h14 h164 h16 h45 h159
  have he : (x^4-2*x^2+x*a-y^2)*v 84=0 := by
    convert h45 using 1 <;> ring
  have ht : ((x^4+x*a-y*b-1)/y^2)*v 84=0 := by
    convert h159 using 1 <;> field_simp [hy0] <;> ring
  obtain ⟨hY,hb⟩ := gap_one_parameter_relations x y a b (v 84) hx hy0 h84 ha he ht
  have hbase : positiveBaseA x y z w a b*v 24+positiveBaseB x y z w a b*v 84=0 := by
    convert h3 using 1 <;> dsimp only [positiveBaseA,positiveBaseB]
      <;> field_simp [hx,hy0,hw] <;> ring
  have hr14 : positiveCoeff14A x y z w a b*v 24+positiveCoeff14B x y z w a b*v 84=0 := by
    convert h14 using 1 <;> dsimp only [positiveCoeff14A,positiveCoeff14B]
      <;> field_simp [hx,hy0,hw] <;> ring
  have hR14 : positiveRow14 (x^2) z w=0 :=
    (mul_eq_zero.mp (positive_homogeneous_residual_14 x y z w a b hx hy0 hw ha hb hY
      (v 24) (v 84) hbase hr14)).resolve_right h84
  have hr164 : positiveCoeff164A x y z w a b*v 24+positiveCoeff164B x y z w a b*v 84=0 := by
    convert h164 using 1 <;> dsimp only [positiveCoeff164A,positiveCoeff164B]
      <;> field_simp [hx,hy0,hw] <;> ring
  have hR164 : positiveRow164 (x^2) z w=0 :=
    (mul_eq_zero.mp (positive_homogeneous_residual_164 x y z w a b hx hy0 hw ha hb hY
      (v 24) (v 84) hbase hr164)).resolve_right h84
  have hr16 : positiveCoeff16A x y z w a b*v 24+positiveCoeff16B x y z w a b*v 84=0 := by
    convert h16 using 1 <;> dsimp only [positiveCoeff16A,positiveCoeff16B]
      <;> field_simp [hx,hy0,hw] <;> ring
  have hR16 : positiveRow16 (x^2) z w=0 :=
    (mul_eq_zero.mp (positive_homogeneous_residual_16 x y z w a b hx hy0 hw ha hb hY
      (v 24) (v 84) hbase hr16)).resolve_right h84
  exact positive_gap_one_residuals_impossible m s z w hu hY hR14 hR164 hR16

#print axioms positive_gap_one_coordinate_zero
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalGapOneFour -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars
open scoped Topology

theorem original_gap_one_four_zero {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re) (hx : 2≤‖primeParameter 2 m s‖)
    (ha : (Real.sqrt 2:ℂ)*f 2= -primeParameter 2 m s/2-2/primeParameter 2 m s) : v 24=0 ∧ v 42=0 ∧ v 84=0 ∧ v 192=0 := by
  have hP := shifted_p_ne_zero (primeParameter 2 m s) 2 (by norm_num) hx
  have hH := shifted_h_ne_zero (primeParameter 2 m s) 2 (by norm_num) hx
  dsimp only at hH
  simp only [Complex.ofReal_ofNat] at hP hH
  rw [← ha] at hP hH
  have hu : 4≤‖(primeParameter 2 m s)^2‖ := by
    rw [norm_pow]
    nlinarith [norm_nonneg (primeParameter 2 m s)]
  have h192 := original_all_sign_leading_exclusion hm hf ε hε hlaw BG G hG hGF s v hv hshift hs
  have h42 : v 42=0 := by
    have h := original_all_sign_row119 hm hf ε hε hlaw BG G hG hGF s v hv hshift
    have hn : 1+primeParameter 2 m s*((Real.sqrt 2:ℂ)*f 2)+(primeParameter 2 m s)^2≠0 := by
      convert hP using 1 <;> ring
    exact (mul_eq_zero.mp h).resolve_left hn
  have hu5 : -badFive f=1 ∨ -badFive f= -1 := by
    rcases badFive_sign hf.toEulerData with h|h <;> simp [h]
  have hu7 : -badSeven f=1 ∨ -badSeven f= -1 := by
    rcases badSeven_sign hf.toEulerData with h|h <;> simp [h]
  have hp := phaseRoot_sign m hε
  change ε*I^(2*m)=1 ∨ ε*I^(2*m)= -1 at hp
  have hsign : ε*I^(2*m)=(-badFive f)*(-badSeven f) ∨
      ε*I^(2*m)= -(-badFive f)*(-badSeven f) := by
    rcases hp with hp|hp <;> rcases hu5 with h5|h5 <;> rcases hu7 with h7|h7 <;>
      rw [hp,h5,h7] <;> norm_num
  have hw : (-badSeven f)*primeParameter 7 m s≠0 :=
    mul_ne_zero (by rcases hu7 with h|h <;> rw [h] <;> norm_num)
      (primeParameter_ne_zero 7 m (by decide) s)
  rcases hsign with hpos|hneg
  · have hrows := original_positive_rows hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hpos (by simp) (by simp)
      BG G hG hGF s v hv hshift
    have hrowsCopy := hrows
    obtain ⟨_,h3,_,_,_,_,_,_,_,_,_,_,_⟩ := hrows
    have h84 := positive_gap_one_coordinate_zero m s
      ((-badFive f)*primeParameter 5 m s) ((-badSeven f)*primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v hw hu ha h42 h192 hrowsCopy
    have h24 : v 24=0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hH
      simp only [h42,h84,h192,mul_zero,zero_add,add_zero] at h3
      convert h3 using 1 <;> ring
    exact ⟨h24,h42,h84,h192⟩
  · have hB := original_signed_negative_rows_b hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hneg (by simp) (by simp)
      BG G hG hGF s v hv hshift
    have hA := original_signed_negative_rows_a hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hneg (by simp) (by simp)
      BG G hG hGF s v hv hshift
    have h84 := negative_gap_one_coordinate_zero m s
      ((-badFive f)*primeParameter 5 m s) ((-badSeven f)*primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v hw hu ha h42 h192 hA hB
    obtain ⟨_,h3,_,_,_⟩ := hA
    have h24 : v 24=0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hH
      simp only [h42,h84,h192,mul_zero,zero_add,add_zero] at h3
      convert h3 using 1 <;> ring
    exact ⟨h24,h42,h84,h192⟩

#print axioms original_gap_one_four_zero
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalGapOneSix -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars
open scoped Topology

theorem original_gap_one_six_zero {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re) (hx : 2≤‖primeParameter 2 m s‖)
    (ha : (Real.sqrt 2:ℂ)*f 2= -primeParameter 2 m s/2-2/primeParameter 2 m s) : v 24=0 ∧ v 42=0 ∧ v 84=0 ∧ v 128=0 ∧ v 158=0 ∧ v 192=0 := by
  obtain ⟨h24,h42,h84,h192⟩ := original_gap_one_four_zero hm hf ε hε hlaw
    BG G hG hGF s v hv hshift hs hx ha
  have finish : ∀ z w : ℂ,
      positiveLastPairReducedConclusion (primeParameter 2 m s) (primeParameter 3 m s)
        z w ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v → v 128=0 ∧ v 158=0 := by
    intro z w hrows
    obtain ⟨h67,h148⟩ := hrows
    apply shifted_last_pair_zero (primeParameter 2 m s) ((Real.sqrt 2:ℂ)*f 2)
      (v 128) (v 158) 2 (by norm_num) hx (by simpa only [Complex.ofReal_ofNat] using ha)
    · convert h67 using 1 <;> ring
    · convert h148 using 1 <;> ring
  have hu5 : -badFive f=1 ∨ -badFive f= -1 := by
    rcases badFive_sign hf.toEulerData with h|h <;> simp [h]
  have hu7 : -badSeven f=1 ∨ -badSeven f= -1 := by
    rcases badSeven_sign hf.toEulerData with h|h <;> simp [h]
  have hp := phaseRoot_sign m hε
  change ε*I^(2*m)=1 ∨ ε*I^(2*m)= -1 at hp
  have hsign : ε*I^(2*m)=(-badFive f)*(-badSeven f) ∨
      ε*I^(2*m)= -(-badFive f)*(-badSeven f) := by
    rcases hp with hp|hp <;> rcases hu5 with h5|h5 <;> rcases hu7 with h7|h7 <;>
      rw [hp,h5,h7] <;> norm_num
  have hpair : v 128=0 ∧ v 158=0 := by
    apply finish ((-badFive f)*primeParameter 5 m s) ((-badSeven f)*primeParameter 7 m s)
    rcases hsign with hpos|hneg
    · exact original_positive_last_pair_reduced_rows hm hf ε hε hlaw
        (-badFive f) (-badSeven f) hu5 hu7 hpos (by simp) (by simp)
        BG G hG hGF s v hv hshift h24 h42 h84 h192
    · exact original_negative_last_pair_reduced_rows hm hf ε hε hlaw
        (-badFive f) (-badSeven f) hu5 hu7 hneg (by simp) (by simp)
        BG G hG hGF s v hv hshift h24 h42 h84 h192
  exact ⟨h24,h42,h84,hpair.1,hpair.2,h192⟩

#print axioms original_gap_one_six_zero
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalGapOneExclusion -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open QuantitativeArithmeticSmallLevelThirtyFiveShiftedScalars
open scoped Topology

theorem original_gap_one_exclusion {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ) (v : Fin 210 → ℂ) (hv : IsLeadingVector G s v)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re) (hx : 2≤‖primeParameter 2 m s‖)
    (ha : (Real.sqrt 2:ℂ)*f 2= -primeParameter 2 m s/2-2/primeParameter 2 m s) : False := by
  obtain ⟨h24,h42,h84,h128,h158,h192⟩ := original_gap_one_six_zero hm hf ε hε hlaw
    BG G hG hGF s v hv hshift hs hx ha
  have hu5 : -badFive f=1 ∨ -badFive f= -1 := by
    rcases badFive_sign hf.toEulerData with h|h <;> simp [h]
  have hu7 : -badSeven f=1 ∨ -badSeven f= -1 := by
    rcases badSeven_sign hf.toEulerData with h|h <;> simp [h]
  have hp := phaseRoot_sign m hε
  change ε*I^(2*m)=1 ∨ ε*I^(2*m)= -1 at hp
  have hsign : ε*I^(2*m)=(-badFive f)*(-badSeven f) ∨
      ε*I^(2*m)= -(-badFive f)*(-badSeven f) := by
    rcases hp with hp|hp <;> rcases hu5 with h5|h5 <;> rcases hu7 with h7|h7 <;>
      rw [hp,h5,h7] <;> norm_num
  apply hv.1
  rcases hsign with hpos|hneg
  · exact original_positive_grid_recovery hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hpos (by simp) (by simp)
      BG G hG hGF s v hv hshift h24 h42 h84 h128 h158 h192
  · exact original_negative_grid_recovery hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hneg (by simp) (by simp)
      BG G hG hGF s v hv hshift h24 h42 h84 h128 h158 h192

#print axioms original_gap_one_exclusion
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalChiThreePositiveShiftTail -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex
open QuantitativeArithmeticUniversalPoleVector
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic

/-- Every strictly positive integer shift of a possible quadratic-twist pole
is regular on the complete additive grid. All inputs are original hypotheses. -/
theorem original_chi3_positive_shift_tail {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      ∃ BG : ℝ, ∃ G : ℂ → Fin 210 → ℂ,
        (∀ i z, MeromorphicNFAt (fun s => G s i) z) ∧
        (∀ z, BG<z.re → G z=gridVector (2*m) f z) ∧
        (∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          ∀ n : ℕ, 0<n → ∀ j, AnalyticAt ℂ (fun z => G z j) (s+(n:ℂ))) := by
  obtain ⟨ε,hε,hlaw,BG,G,hG,hGF,hlarge⟩ := original_chi3_shift_tail hm hf
  refine ⟨ε,hε,hlaw,BG,G,hG,hGF,?_⟩
  intro s hs hden n hn j
  by_cases hn2 : 2≤n
  · exact hlarge s hs hden n hn2 j
  have hn1 : n=1 := by omega
  subst n
  simp only [Nat.cast_one]
  apply (hG j _).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hj
  obtain ⟨v,hv⟩ := exists_leading_vector G (s+1)
    (fun i => (hG i _).meromorphicAt) ⟨j,hj⟩
  have hshift : ∀ a : ℕ, 0<a → ∀ i,
      0≤meromorphicOrderAt (fun z => G z i) ((s+1)+a) := by
    intro a ha i
    have hh := hlarge s hs hden (1+a) (by omega) i
    have he : s+((1+a:ℕ):ℂ)=(s+1)+(a:ℂ) := by push_cast; ring
    rw [he] at hh
    exact hh.meromorphicOrderAt_nonneg
  have hs1 : (m:ℝ)≤(s+1).re := by simp only [add_re,one_re]; linarith
  have hx : 2≤‖primeParameter 2 m (s+1)‖ := by
    rw [primeParameter_norm 2 m (by decide)]
    have hα : (1:ℝ)≤(s+1).re-(m:ℝ) := by simp only [add_re,one_re]; linarith
    simpa only [Real.rpow_one,Nat.cast_ofNat] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hα
  have ha : (Real.sqrt 2:ℂ)*f 2= -primeParameter 2 m (s+1)/2-2/primeParameter 2 m (s+1) := by
    simpa only [Nat.cast_one,pow_one,Complex.ofReal_ofNat] using chi3_shifted_candidate m 1 f s hden
  exact original_gap_one_exclusion hm hf ε hε hlaw BG G hG hGF (s+1) v hv hshift hs1 hx ha

#print axioms original_chi3_positive_shift_tail
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalNegativeThreeOrders -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

theorem chi3_candidate_polynomial (m : ℕ) (f : ℕ → ℂ) (s : ℂ)
    (hden : QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0) :
    1+((Real.sqrt 2:ℂ)*f 2)*primeParameter 2 m s+(primeParameter 2 m s)^2=0 := by
  rw [chi3_denominator_normalized] at hden
  have hx := primeParameter_ne_zero 2 m (by decide) s
  linear_combination (norm := (field_simp [hx]; ring)) (primeParameter 2 m s)^2*hden

/-- Three of the four closed-system coordinates now have bounded pole
orders at every actual chi3 candidate; no Laurent-vector premise is used. -/
theorem original_negative_three_orders {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hproduct : ε*I^(2*m)*badFive f*badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re)
    (hden : QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0) :
    (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 42) s ∧
    (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 84) s ∧
    (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 192) s := by
  have h5 := badFive_sign hf.toEulerData
  have h7 := badSeven_sign hf.toEulerData
  have hu5 : -badFive f=1 ∨ -badFive f= -1 := by rcases h5 with h|h <;> simp [h]
  have hu7 : -badSeven f=1 ∨ -badSeven f= -1 := by rcases h7 with h|h <;> simp [h]
  have h5sq : (badFive f)^2=1 := by rcases h5 with h|h <;> rw [h] <;> norm_num
  have h7sq : (badSeven f)^2=1 := by rcases h7 with h|h <;> rw [h] <;> norm_num
  have hphase : ε*I^(2*m)= -(-badFive f)*(-badSeven f) := by
    linear_combination (badFive f*badSeven f)*hproduct-
      (ε*I^(2*m)*(badSeven f)^2)*h5sq-(ε*I^(2*m))*h7sq
  have hP := chi3_candidate_polynomial m f s hden
  exact ⟨negative_coordinate42_order_ge_neg_one hm hf ε hε hlaw
    (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
    BG G hG hGF s hshift hs hP,
    negative_coordinate84_order_ge_neg_two hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
      BG G hG hGF s hshift hs hP,
    QuantitativeArithmeticSmallLevelThirtyFiveChiThree.coordinate192_order_ge_neg_two
      hm hf ε hε hlaw BG G hG hGF s hshift⟩

/-- A grid constructed solely from the original Euler/Fricke input has
these three-coordinate order bounds in the negative-product sign class. -/
theorem original_negative_three_orders_grid {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      ∃ BG : ℝ, ∃ G : ℂ → Fin 210 → ℂ,
        (∀ i z, MeromorphicNFAt (fun s => G s i) z) ∧
        (∀ z, BG<z.re → G z=gridVector (2*m) f z) ∧
        (∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          ∀ n : ℕ, 0<n → ∀ j, AnalyticAt ℂ (fun z => G z j) (s+(n:ℂ))) ∧
        (ε*I^(2*m)*badFive f*badSeven f= -1 → ∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 42) s ∧
          (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 84) s ∧
          (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 192) s) := by
  obtain ⟨ε,hε,hlaw,BG,G,hG,hGF,htail⟩ := original_chi3_positive_shift_tail hm hf
  refine ⟨ε,hε,hlaw,BG,G,hG,hGF,htail,?_⟩
  intro hproduct s hs hden
  exact original_negative_three_orders hm hf ε hε hlaw hproduct BG G hG hGF s
    (fun n hn j => (htail s hs hden n hn j).meromorphicOrderAt_nonneg) hs hden

#print axioms chi3_candidate_polynomial
#print axioms original_negative_three_orders
#print axioms original_negative_three_orders_grid
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalPositiveThreeOrders -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

/-- Three of the four closed-system coordinates now have bounded pole
orders at every actual chi3 candidate; no Laurent-vector premise is used. -/
theorem original_positive_three_orders {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hproduct : ε*I^(2*m)*badFive f*badSeven f= 1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re)
    (hden : QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0) :
    (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 42) s ∧
    (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 84) s ∧
    (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 192) s := by
  have h5 := badFive_sign hf.toEulerData
  have h7 := badSeven_sign hf.toEulerData
  have hu5 : -badFive f=1 ∨ -badFive f= -1 := by rcases h5 with h|h <;> simp [h]
  have hu7 : -badSeven f=1 ∨ -badSeven f= -1 := by rcases h7 with h|h <;> simp [h]
  have h5sq : (badFive f)^2=1 := by rcases h5 with h|h <;> rw [h] <;> norm_num
  have h7sq : (badSeven f)^2=1 := by rcases h7 with h|h <;> rw [h] <;> norm_num
  have hphase : ε*I^(2*m)= (-badFive f)*(-badSeven f) := by
    linear_combination (badFive f*badSeven f)*hproduct-
      (ε*I^(2*m)*(badSeven f)^2)*h5sq-(ε*I^(2*m))*h7sq
  have hP := chi3_candidate_polynomial m f s hden
  exact ⟨positive_coordinate42_order_ge_neg_one hm hf ε hε hlaw
    (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
    BG G hG hGF s hshift hs hP,
    positive_coordinate84_order_ge_neg_two hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
      BG G hG hGF s hshift hs hP,
    QuantitativeArithmeticSmallLevelThirtyFiveChiThree.coordinate192_order_ge_neg_two
      hm hf ε hε hlaw BG G hG hGF s hshift⟩

/-- A grid constructed solely from the original Euler/Fricke input has
these three-coordinate order bounds in the positive-product sign class. -/
theorem original_positive_three_orders_grid {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      ∃ BG : ℝ, ∃ G : ℂ → Fin 210 → ℂ,
        (∀ i z, MeromorphicNFAt (fun s => G s i) z) ∧
        (∀ z, BG<z.re → G z=gridVector (2*m) f z) ∧
        (∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          ∀ n : ℕ, 0<n → ∀ j, AnalyticAt ℂ (fun z => G z j) (s+(n:ℂ))) ∧
        (ε*I^(2*m)*badFive f*badSeven f= 1 → ∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 42) s ∧
          (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 84) s ∧
          (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 192) s) := by
  obtain ⟨ε,hε,hlaw,BG,G,hG,hGF,htail⟩ := original_chi3_positive_shift_tail hm hf
  refine ⟨ε,hε,hlaw,BG,G,hG,hGF,htail,?_⟩
  intro hproduct s hs hden
  exact original_positive_three_orders hm hf ε hε hlaw hproduct BG G hG hGF s
    (fun n hn j => (htail s hs hden n hn j).meromorphicOrderAt_nonneg) hs hden

#print axioms original_positive_three_orders
#print axioms original_positive_three_orders_grid
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveAnalyticPivotProperties -/
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFivePositiveAnalyticShortRows
open Complex

def reducedPivot24 (x y z w a b : ℂ) (v : Fin 210 → ℂ) : ℂ :=
 x^2*reduced0 x y z w a b v+y^2*reduced163 x y z w a b v

def pivot24C24 (x y z w a b : ℂ) : ℂ :=
  (-2 + (-1)*y*b + (-1)*y^(2:ℕ) + x*a + (-1)*x*y*a*b + (-1)*x*y^(2:ℕ)*a + x^(2:ℕ) + (-2)*x^(2:ℕ)*a^(2:ℕ) + (-4)*x^(3:ℕ)*a + (-1)*x^(3:ℕ)*a^(3:ℕ) + x^(3:ℕ)*y*a*b + x^(3:ℕ)*y^(2:ℕ)*a + (-2)*x^(4:ℕ)*a^(2:ℕ) + x^(4:ℕ)*y*b + x^(4:ℕ)*y^(2:ℕ) + x^(5:ℕ)*a + x^(5:ℕ)*a^(3:ℕ) + x^(6:ℕ) + (3)*x^(6:ℕ)*a^(2:ℕ) + (2)*x^(7:ℕ)*a)

def pivot24C42 (x y z w a b : ℂ) : ℂ :=
  ((-2 + (-2)*z + (-1)*y*b + (-1)*y^(2:ℕ) + (10)*x*a + (-5)*x*z*a + (-1)*x*y*a*b + (-7)*x*y^(2:ℕ)*a + (-1)*x^(2:ℕ) + (10)*x^(2:ℕ)*a^(2:ℕ) + (-3)*x^(2:ℕ)*z + x^(2:ℕ)*z*a^(2:ℕ) + (-2)*x^(2:ℕ)*y^(2:ℕ) + (-3)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-16)*x^(3:ℕ)*a + (3)*x^(3:ℕ)*a^(3:ℕ) + (4)*x^(3:ℕ)*z*a + (3)*x^(3:ℕ)*z*a^(3:ℕ) + (4)*x^(3:ℕ)*y*a*b + (2)*x^(3:ℕ)*y^(2:ℕ)*a + (-1)*x^(4:ℕ) + (-14)*x^(4:ℕ)*a^(2:ℕ) + (3)*x^(4:ℕ)*z + (5)*x^(4:ℕ)*z*a^(2:ℕ) + x^(4:ℕ)*z*a^(4:ℕ) + (2)*x^(4:ℕ)*y*b + (6)*x^(4:ℕ)*y*a^(2:ℕ)*b + x^(4:ℕ)*y^(2:ℕ) + (5)*x^(5:ℕ)*a + (-4)*x^(5:ℕ)*a^(3:ℕ) + (3)*x^(5:ℕ)*z*a + (4)*x^(5:ℕ)*y*a*b + (4)*x^(5:ℕ)*y*a^(3:ℕ)*b + (-2)*x^(5:ℕ)*y^(2:ℕ)*a + (-3)*x^(5:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (7)*x^(6:ℕ) + (5)*x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ)*z + (-2)*x^(6:ℕ)*z*a^(2:ℕ) + (-1)*x^(6:ℕ)*z*a^(4:ℕ) + x^(6:ℕ)*y*a^(2:ℕ)*b + x^(6:ℕ)*y*a^(4:ℕ)*b + (-1)*x^(6:ℕ)*y^(2:ℕ) + (-3)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1)*x^(6:ℕ)*y^(2:ℕ)*a^(4:ℕ) + (7)*x^(7:ℕ)*a + (-1)*x^(7:ℕ)*a^(3:ℕ) + (-1)*x^(7:ℕ)*z*a + (-2)*x^(7:ℕ)*z*a^(3:ℕ) + (-3)*x^(7:ℕ)*y*a*b + (-2)*x^(7:ℕ)*y*a^(3:ℕ)*b + x^(7:ℕ)*y^(2:ℕ)*a + x^(7:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-3)*x^(8:ℕ) + (-1)*x^(8:ℕ)*a^(4:ℕ) + (-1)*x^(8:ℕ)*z*a^(2:ℕ) + (-1)*x^(8:ℕ)*y*b + (-5)*x^(8:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(8:ℕ)*y*a^(4:ℕ)*b + x^(8:ℕ)*y^(2:ℕ) + (4)*x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) + x^(8:ℕ)*y^(2:ℕ)*a^(4:ℕ) + (-5)*x^(9:ℕ)*a + x^(9:ℕ)*a^(3:ℕ) + (-2)*x^(9:ℕ)*y*a*b + (-2)*x^(9:ℕ)*y*a^(3:ℕ)*b + (2)*x^(9:ℕ)*y^(2:ℕ)*a + (2)*x^(9:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-2)*x^(10:ℕ) + (-1)*x^(10:ℕ)*a^(2:ℕ) + x^(10:ℕ)*a^(4:ℕ) + (-1)*x^(10:ℕ)*y*a^(2:ℕ)*b + x^(10:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2)*x^(11:ℕ)*a + x^(11:ℕ)*a^(3:ℕ))/(w))

def pivot24C84 (x y z w a b : ℂ) : ℂ :=
  ((1 + (-1)*w + (-1)*z + (2)*x*a + x*y*a*b + (-3)*x*y^(2:ℕ)*a + x^(2:ℕ) + (-1)*x^(2:ℕ)*a^(2:ℕ) + (-1)*x^(2:ℕ)*w + (-2)*x^(2:ℕ)*z + (3)*x^(2:ℕ)*z*a^(2:ℕ) + x^(2:ℕ)*y*b + x^(2:ℕ)*y^(2:ℕ) + (-1)*x^(2:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-11)*x^(3:ℕ)*a + (-2)*x^(3:ℕ)*w*a + (2)*x^(3:ℕ)*z*a + x^(3:ℕ)*z*a^(3:ℕ) + (4)*x^(3:ℕ)*y^(2:ℕ)*a + (-3)*x^(4:ℕ)*a^(2:ℕ) + (-1)*x^(4:ℕ)*w*a^(2:ℕ) + (2)*x^(4:ℕ)*z + (-3)*x^(4:ℕ)*z*a^(2:ℕ) + (2)*x^(4:ℕ)*y*a^(2:ℕ)*b + (3)*x^(4:ℕ)*y^(2:ℕ) + (2)*x^(4:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (7)*x^(5:ℕ)*a + (-2)*x^(5:ℕ)*a^(3:ℕ) + x^(5:ℕ)*w*a + (-3)*x^(5:ℕ)*z*a + (-2)*x^(5:ℕ)*z*a^(3:ℕ) + x^(5:ℕ)*y*a*b + x^(5:ℕ)*y*a^(3:ℕ)*b + (3)*x^(5:ℕ)*y^(2:ℕ)*a + (3)*x^(6:ℕ) + (-1)*x^(6:ℕ)*a^(2:ℕ) + (-1)*x^(6:ℕ)*a^(4:ℕ) + x^(6:ℕ)*w + x^(6:ℕ)*w*a^(2:ℕ) + (-2)*x^(6:ℕ)*z*a^(2:ℕ) + (-1)*x^(6:ℕ)*y*b + (-2)*x^(6:ℕ)*y*a^(2:ℕ)*b + (2)*x^(6:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-2)*x^(7:ℕ)*a^(3:ℕ) + x^(7:ℕ)*w*a + x^(7:ℕ)*z*a^(3:ℕ) + (-4)*x^(7:ℕ)*y*a*b + (-2)*x^(7:ℕ)*y*a^(3:ℕ)*b + x^(7:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (-3)*x^(8:ℕ) + (3)*x^(8:ℕ)*a^(2:ℕ) + x^(8:ℕ)*a^(4:ℕ) + (2)*x^(8:ℕ)*z*a^(2:ℕ) + (-1)*x^(8:ℕ)*y*b + (-2)*x^(8:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(8:ℕ)*y^(2:ℕ) + (-1)*x^(8:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (5)*x^(9:ℕ)*a^(3:ℕ) + x^(9:ℕ)*z*a + x^(9:ℕ)*y*a*b + x^(9:ℕ)*y*a^(3:ℕ)*b + (-3)*x^(9:ℕ)*y^(2:ℕ)*a + (-1)*x^(9:ℕ)*y^(2:ℕ)*a^(3:ℕ) + (2)*x^(10:ℕ)*a^(2:ℕ) + x^(10:ℕ)*y*b + (2)*x^(10:ℕ)*y*a^(2:ℕ)*b + (-1)*x^(10:ℕ)*y^(2:ℕ) + (-2)*x^(10:ℕ)*y^(2:ℕ)*a^(2:ℕ) + (-1)*x^(11:ℕ)*a + (-1)*x^(11:ℕ)*a^(3:ℕ) + x^(11:ℕ)*y*a*b + (-1)*x^(11:ℕ)*y^(2:ℕ)*a + (-1)*x^(12:ℕ)*a^(2:ℕ))/(w))

def pivot24C192 (x y z w a b : ℂ) : ℂ :=
  (-3 + y*b + (-2)*x*a + (3)*x*z*a + x^(2:ℕ)*z*a^(2:ℕ) + (-3)*x^(3:ℕ)*z*a + (2)*x^(4:ℕ) + (-1)*x^(4:ℕ)*a^(2:ℕ) + (-1)*x^(4:ℕ)*z + (-2)*x^(4:ℕ)*z*a^(2:ℕ) + x^(5:ℕ)*a + x^(6:ℕ) + x^(6:ℕ)*a^(2:ℕ) + x^(6:ℕ)*z + x^(6:ℕ)*z*a^(2:ℕ) + x^(7:ℕ)*a + x^(7:ℕ)*z*a)

theorem pivot24_decomposition (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hx : x≠0) (hy : y≠0) (hw : w≠0) :
    reducedPivot24 x y z w a b v=
      pivot24C24 x y z w a b*v 24+
      pivot24C42 x y z w a b*v 42+
      pivot24C84 x y z w a b*v 84+
      pivot24C192 x y z w a b*v 192 := by
  dsimp [reducedPivot24,reduced0,reduced163,pivot24C24,pivot24C42,pivot24C84,pivot24C192]
  field_simp [hx,hy,hw]
  ring

theorem pivot24_coefficient (x y z w a b : ℂ) (hx : x≠0)
    (hP : 1+a*x+x^2=0) : pivot24C24 x y z w a b= -4 := by
  have ha : a= -x-1/x := by
    linear_combination (norm := (field_simp [hx]; ring)) hP/x
  unfold pivot24C24
  rw [ha]
  field_simp [hx]
  ring

theorem pivot24C24_analytic (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0) :
    AnalyticAt ℂ (fun t => pivot24C24 (X t) (Y t) (Z t) (W t) a b) s := by
  unfold pivot24C24
  fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])

theorem pivot24C42_analytic (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0) :
    AnalyticAt ℂ (fun t => pivot24C42 (X t) (Y t) (Z t) (W t) a b) s := by
  unfold pivot24C42
  fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])

theorem pivot24C84_analytic (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0) :
    AnalyticAt ℂ (fun t => pivot24C84 (X t) (Y t) (Z t) (W t) a b) s := by
  unfold pivot24C84
  fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])

theorem pivot24C192_analytic (X Y Z W : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0) :
    AnalyticAt ℂ (fun t => pivot24C192 (X t) (Y t) (Z t) (W t) a b) s := by
  unfold pivot24C192
  fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])

#print axioms pivot24_coefficient
#print axioms pivot24C24_analytic
#print axioms pivot24C42_analytic
#print axioms pivot24C84_analytic
#print axioms pivot24C192_analytic
end QuantitativeArithmeticSmallLevelThirtyFivePositiveAnalyticShortRows
end
end

/-! ## ThirtyFiveOriginalPositiveAnalyticRowPivot24 -/
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFivePositiveAnalyticShortRows
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

theorem analytic_signed_positive_rowPivot24 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun t => reducedPivot24 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have h0 := analytic_signed_positive_row0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  have h163 := analytic_signed_positive_row163 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
  exact (h0.mul_analytic ((primeParameter_analytic 2 m (by decide) s).fun_pow 2)).add
    (h163.mul_analytic ((primeParameter_analytic 3 m (by decide) s).fun_pow 2))

#print axioms analytic_signed_positive_rowPivot24
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveFourthOrder -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFivePositiveAnalyticShortRows
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

theorem positive_coordinate24_order_lower {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hP : 1+((Real.sqrt 2:ℂ)*f 2)*primeParameter 2 m s+(primeParameter 2 m s)^2=0)
    (β : WithTop ℤ) (hβ : β≤0)
    (h42 : β≤meromorphicOrderAt (fun t => G t 42) s)
    (h84 : β≤meromorphicOrderAt (fun t => G t 84) s)
    (h192 : β≤meromorphicOrderAt (fun t => G t 192) s) :
    β≤meromorphicOrderAt (fun t => G t 24) s := by
  have hrow := analytic_signed_positive_rowPivot24 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7
    BG G hG hGF s hshift
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  simp only [pivot24_decomposition _ _ _ _ _ _ _
    (primeParameter_ne_zero 2 m (by decide) _)
    (primeParameter_ne_zero 3 m (by decide) _)
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) _))] at hrow
  have hx := primeParameter_analytic 2 m (by decide) s
  have hy := primeParameter_analytic 3 m (by decide) s
  have hz := (analyticAt_const (v:=u5)).mul (primeParameter_analytic 5 m (by decide) s)
  have hw := (analyticAt_const (v:=u7)).mul (primeParameter_analytic 7 m (by decide) s)
  have hx0 := primeParameter_ne_zero 2 m (by decide) s
  have hy0 := primeParameter_ne_zero 3 m (by decide) s
  have hz0 := mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s)
  have hw0 := mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)
  have hc24 := pivot24C24_analytic (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s hx hy hz hw hx0 hy0 hz0 hw0
  have hc42 := pivot24C42_analytic (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s hx hy hz hw hx0 hy0 hz0 hw0
  have hc84 := pivot24C84_analytic (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s hx hy hz hw hx0 hy0 hz0 hw0
  have hc192 := pivot24C192_analytic (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s hx hy hz hw hx0 hy0 hz0 hw0
  have hc0 : pivot24C24 (primeParameter 2 m s) (primeParameter 3 m s)
      (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3)≠0 := by
    rw [pivot24_coefficient _ _ _ _ _ _ hx0 hP]
    norm_num
  exact four_row_order_lower hc24 hc42 hc84 hc192 hc0
    (hG 42 s).meromorphicAt (hG 84 s).meromorphicAt (hG 192 s).meromorphicAt
    hβ h42 h84 h192 hrow

#print axioms positive_coordinate24_order_lower
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalPositiveFourOrders -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

/-- All four closed-system coordinates now have bounded pole
orders at every actual chi3 candidate; no Laurent-vector premise is used. -/
theorem original_positive_four_orders {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hproduct : ε*I^(2*m)*badFive f*badSeven f= 1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re)
    (hden : QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0) :
    (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 24) s ∧
    (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 42) s ∧
    (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 84) s ∧
    (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 192) s := by
  have h5 := badFive_sign hf.toEulerData
  have h7 := badSeven_sign hf.toEulerData
  have hu5 : -badFive f=1 ∨ -badFive f= -1 := by rcases h5 with h|h <;> simp [h]
  have hu7 : -badSeven f=1 ∨ -badSeven f= -1 := by rcases h7 with h|h <;> simp [h]
  have h5sq : (badFive f)^2=1 := by rcases h5 with h|h <;> rw [h] <;> norm_num
  have h7sq : (badSeven f)^2=1 := by rcases h7 with h|h <;> rw [h] <;> norm_num
  have hphase : ε*I^(2*m)= (-badFive f)*(-badSeven f) := by
    linear_combination (badFive f*badSeven f)*hproduct-
      (ε*I^(2*m)*(badSeven f)^2)*h5sq-(ε*I^(2*m))*h7sq
  have hP := chi3_candidate_polynomial m f s hden
  obtain ⟨h42,h84,h192⟩ := original_positive_three_orders hm hf ε hε hlaw hproduct
    BG G hG hGF s hshift hs hden
  have h42two : (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 42) s := by
    apply le_trans ?_ h42
    change ((-2:ℤ):WithTop ℤ)≤((-1:ℤ):WithTop ℤ)
    exact WithTop.coe_le_coe.mpr (by omega)
  refine ⟨positive_coordinate24_order_lower hm hf ε hε hlaw
    (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
    BG G hG hGF s hshift hP (-2) ?_ h42two h84 h192,h42,h84,h192⟩
  change ((-2:ℤ):WithTop ℤ)≤((0:ℤ):WithTop ℤ)
  exact WithTop.coe_le_coe.mpr (by omega)

/-- A grid constructed solely from the original Euler/Fricke input has
these four-coordinate order bounds in the positive-product sign class. -/
theorem original_positive_four_orders_grid {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      ∃ BG : ℝ, ∃ G : ℂ → Fin 210 → ℂ,
        (∀ i z, MeromorphicNFAt (fun s => G s i) z) ∧
        (∀ z, BG<z.re → G z=gridVector (2*m) f z) ∧
        (∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          ∀ n : ℕ, 0<n → ∀ j, AnalyticAt ℂ (fun z => G z j) (s+(n:ℂ))) ∧
        (ε*I^(2*m)*badFive f*badSeven f= 1 → ∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 24) s ∧
    (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 42) s ∧
          (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 84) s ∧
          (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 192) s) := by
  obtain ⟨ε,hε,hlaw,BG,G,hG,hGF,htail⟩ := original_chi3_positive_shift_tail hm hf
  refine ⟨ε,hε,hlaw,BG,G,hG,hGF,htail,?_⟩
  intro hproduct s hs hden
  exact original_positive_four_orders hm hf ε hε hlaw hproduct BG G hG hGF s
    (fun n hn j => (htail s hs hden n hn j).meromorphicOrderAt_nonneg) hs hden

#print axioms original_positive_four_orders
#print axioms original_positive_four_orders_grid
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveFourResidues -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open scoped Topology

def closedFourIndex : Fin 4 → Fin 210 := ![24,42,84,192]
def closedFourExtend (v : Fin 4 → ℂ) (j : Fin 210) : ℂ :=
  if j=24 then v 0 else if j=42 then v 1 else if j=84 then v 2 else if j=192 then v 3 else 0

def IsClosedFourResidue (G : ℂ → Fin 210 → ℂ) (s : ℂ) (v : Fin 210 → ℂ) : Prop :=
  ∀ C D E J : ℂ → ℂ,
    AnalyticAt ℂ C s → AnalyticAt ℂ D s → AnalyticAt ℂ E s → AnalyticAt ℂ J s →
    HasAnalyticGerm (fun t => C t*G t 24+D t*G t 42+E t*G t 84+J t*G t 192) s →
    C s*v 24+D s*v 42+E s*v 84+J s*v 192=0

/-- Only the four selected coordinates need simple-pole bounds. Other grid
coordinates may have arbitrarily larger poles. -/
theorem exists_closed_four_residue (G : ℂ → Fin 210 → ℂ) (s : ℂ)
    (hG : ∀ j, MeromorphicAt (fun t => G t j) s)
    (hbound : ∀ j : Fin 4, (-1:WithTop ℤ)≤meromorphicOrderAt (fun t => G t (closedFourIndex j)) s) :
    ∃ v : Fin 210 → ℂ, IsClosedFourResidue G s v ∧
      ∀ j : Fin 4, v (closedFourIndex j)=0 ↔
        0≤meromorphicOrderAt (fun t => G t (closedFourIndex j)) s := by
  obtain ⟨v,hzero,hrow⟩ := exists_simple_residue_vector
    (fun t j => G t (closedFourIndex j)) s (fun j => hG (closedFourIndex j)) hbound
  have hext (j : Fin 4) : closedFourExtend v (closedFourIndex j)=v j := by
    fin_cases j <;> norm_num [closedFourExtend,closedFourIndex]
  refine ⟨closedFourExtend v,?_,fun j => by rw [hext]; exact hzero j⟩
  intro C D E J hC hD hE hJ hr
  have hc (j : Fin 4) : AnalyticAt ℂ (fun t => (![C t,D t,E t,J t] : Fin 4 → ℂ) j) s := by
    fin_cases j
    · exact hC
    · exact hD
    · exact hE
    · exact hJ
  have hg : HasAnalyticGerm
      (fun t => ∑ j : Fin 4, (![C t,D t,E t,J t] : Fin 4 → ℂ) j*G t (closedFourIndex j)) s := by
    apply hr.congr
    exact Filter.Eventually.of_forall (fun t => by norm_num [closedFourIndex,Fin.sum_univ_succ]; ring)
  have h := hrow (fun t => ![C t,D t,E t,J t]) hc hg
  norm_num [Fin.sum_univ_succ] at h
  simpa only [closedFourExtend,ite_true,show (42:Fin 210)≠24 by decide,
    show (84:Fin 210)≠24 by decide,show (84:Fin 210)≠42 by decide,
    show (192:Fin 210)≠24 by decide,show (192:Fin 210)≠42 by decide,
    show (192:Fin 210)≠84 by decide,ite_false,add_assoc] using h

#print axioms exists_closed_four_residue
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveClosedResidueRowBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFivePositiveAnalyticShortRows
open scoped Topology

theorem positive_closed_residue_row0 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced0 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced0 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => ((1 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*a^(2:ℕ) + (3)*(X t)^(5:ℕ)*a + (X t)^(5:ℕ)*a^(3:ℕ) + (2)*(X t)^(6:ℕ)*a^(2:ℕ))/((X t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((4 + (-4)*(Z t) + (-2)*(Y t)*b + (-4)*(Y t)^(2:ℕ) + (6)*(X t)*a + (-2)*(X t)*(Y t)*a*b + (-4)*(X t)*(Y t)^(2:ℕ)*a + (-11)*(X t)^(2:ℕ) + (4)*(X t)^(2:ℕ)*a^(2:ℕ) + (4)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-18)*(X t)^(3:ℕ)*a + (5)*(X t)^(3:ℕ)*(Z t)*a + (2)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (4)*(X t)^(3:ℕ)*(Y t)*a*b + (4)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (8)*(X t)^(4:ℕ) + (-10)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (2)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (4)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (14)*(X t)^(5:ℕ)*a + (-3)*(X t)^(5:ℕ)*a^(3:ℕ) + (-2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(6:ℕ) + (6)*(X t)^(6:ℕ)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(4:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (-4)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-4)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-3)*(X t)^(7:ℕ)*(Y t)*a*b + (-4)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (3)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ) + (-2)*(X t)^(8:ℕ)*a^(2:ℕ) + (-3)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)*a^(4:ℕ)*b + (3)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (-4)*(X t)^(9:ℕ)*a + (2)*(X t)^(9:ℕ)*a^(3:ℕ) + (-1)*(X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*a^(4:ℕ))/((X t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((2 + (-2)*(Z t) + (-2)*(Y t)^(2:ℕ) + (2)*(X t)*(Z t)*a + (-2)*(X t)*(Y t)^(2:ℕ)*a + (-5)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(W t) + (2)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-5)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(W t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Y t)*a*b + (3)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (6)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(W t) + (X t)^(4:ℕ)*(Z t) + (-4)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (5)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (2)*(X t)^(5:ℕ)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Y t)*a*b + (-3)*(X t)^(6:ℕ) + (X t)^(6:ℕ)*(W t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Y t)*b + (-3)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(7:ℕ)*a + (2)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (4)*(X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*a^(4:ℕ) + (X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*b + (X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-3)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(9:ℕ)*a + (3)*(X t)^(9:ℕ)*a^(3:ℕ) + (2)*(X t)^(9:ℕ)*(Y t)*a*b + (X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(11:ℕ)*a^(3:ℕ))/((X t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => ((-2 + (2)*(Z t) + (2)*(X t)*(Z t)*a + (2)*(X t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Z t) + (X t)^(3:ℕ)*a + (-3)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(5:ℕ)*a + (2)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ))/((X t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => ((1 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*a^(2:ℕ) + (3)*(X t)^(5:ℕ)*a + (X t)^(5:ℕ)*a^(3:ℕ) + (2)*(X t)^(6:ℕ)*a^(2:ℕ))/((X t)^(2:ℕ)))) (fun t => ((4 + (-4)*(Z t) + (-2)*(Y t)*b + (-4)*(Y t)^(2:ℕ) + (6)*(X t)*a + (-2)*(X t)*(Y t)*a*b + (-4)*(X t)*(Y t)^(2:ℕ)*a + (-11)*(X t)^(2:ℕ) + (4)*(X t)^(2:ℕ)*a^(2:ℕ) + (4)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-18)*(X t)^(3:ℕ)*a + (5)*(X t)^(3:ℕ)*(Z t)*a + (2)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (4)*(X t)^(3:ℕ)*(Y t)*a*b + (4)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (8)*(X t)^(4:ℕ) + (-10)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (2)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (4)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (14)*(X t)^(5:ℕ)*a + (-3)*(X t)^(5:ℕ)*a^(3:ℕ) + (-2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(6:ℕ) + (6)*(X t)^(6:ℕ)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(4:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (-4)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-4)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-3)*(X t)^(7:ℕ)*(Y t)*a*b + (-4)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (3)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ) + (-2)*(X t)^(8:ℕ)*a^(2:ℕ) + (-3)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)*a^(4:ℕ)*b + (3)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (-4)*(X t)^(9:ℕ)*a + (2)*(X t)^(9:ℕ)*a^(3:ℕ) + (-1)*(X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*a^(4:ℕ))/((X t)^(2:ℕ)*(W t)))) (fun t => ((2 + (-2)*(Z t) + (-2)*(Y t)^(2:ℕ) + (2)*(X t)*(Z t)*a + (-2)*(X t)*(Y t)^(2:ℕ)*a + (-5)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(W t) + (2)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-5)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(W t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Y t)*a*b + (3)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (6)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(W t) + (X t)^(4:ℕ)*(Z t) + (-4)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (5)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (2)*(X t)^(5:ℕ)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Y t)*a*b + (-3)*(X t)^(6:ℕ) + (X t)^(6:ℕ)*(W t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Y t)*b + (-3)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(7:ℕ)*a + (2)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (4)*(X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*a^(4:ℕ) + (X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*b + (X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-3)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(9:ℕ)*a + (3)*(X t)^(9:ℕ)*a^(3:ℕ) + (2)*(X t)^(9:ℕ)*(Y t)*a*b + (X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(11:ℕ)*a^(3:ℕ))/((X t)^(2:ℕ)*(W t)))) (fun t => ((-2 + (2)*(Z t) + (2)*(X t)*(Z t)*a + (2)*(X t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Z t) + (X t)^(3:ℕ)*a + (-3)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(5:ℕ)*a + (2)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ))/((X t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced0]
        ring))
  simpa only [reduced0,zero_mul,zero_add,add_zero] using h

#print axioms positive_closed_residue_row0

theorem positive_closed_residue_row13 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced13 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced13 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (((2)*(Z t) + (Y t)*(Z t)*b + (Y t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(3:ℕ)*(Z t)*a)/((X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => (((-5)*(Z t) + (2)*(Z t)*(W t) + (2)*(Z t)^(2:ℕ) + (Y t)*(Z t)*b + (Y t)^(2:ℕ)*(Z t) + (-5)*(X t)*(Z t)*a + (X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)*(Y t)*(Z t)*a*b + (3)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(2:ℕ)*(Z t) + (-3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (6)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-3)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-5)*(X t)^(4:ℕ)*(Z t) + (2)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*(Z t)*b + (-3)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-3)*(X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(6:ℕ)*(Z t) + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ))/((X t)^(2:ℕ)*(Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => (((-1)*(Z t) + (Z t)*(W t) + (-1)*(X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)*(Y t)*(Z t)*a*b + (X t)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Z t)*(W t) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (5)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*(W t)*a + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-3)*(X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (3)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*(Z t)*b + (X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ))/((X t)^(2:ℕ)*(Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (((3)*(Z t) + (-1)*(X t)*(Z t)^(2:ℕ)*a + (X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)^(2:ℕ)*a)/((X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (((2)*(Z t) + (Y t)*(Z t)*b + (Y t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(3:ℕ)*(Z t)*a)/((X t)^(2:ℕ)*(Y t)^(2:ℕ)))) (fun t => (((-5)*(Z t) + (2)*(Z t)*(W t) + (2)*(Z t)^(2:ℕ) + (Y t)*(Z t)*b + (Y t)^(2:ℕ)*(Z t) + (-5)*(X t)*(Z t)*a + (X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)*(Y t)*(Z t)*a*b + (3)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(2:ℕ)*(Z t) + (-3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (6)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-3)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-5)*(X t)^(4:ℕ)*(Z t) + (2)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*(Z t)*b + (-3)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-3)*(X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(6:ℕ)*(Z t) + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ))/((X t)^(2:ℕ)*(Y t)^(2:ℕ)*(W t)))) (fun t => (((-1)*(Z t) + (Z t)*(W t) + (-1)*(X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)*(Y t)*(Z t)*a*b + (X t)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Z t)*(W t) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (5)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*(W t)*a + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-3)*(X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (3)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*(Z t)*b + (X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ))/((X t)^(2:ℕ)*(Y t)^(2:ℕ)*(W t)))) (fun t => (((3)*(Z t) + (-1)*(X t)*(Z t)^(2:ℕ)*a + (X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)^(2:ℕ)*a)/((X t)^(2:ℕ)*(Y t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced13]
        ring))
  simpa only [reduced13,zero_mul,zero_add,add_zero] using h

#print axioms positive_closed_residue_row13

theorem positive_closed_residue_row14 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced14 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced14 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (-2 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((6 + (-2)*(W t) + (-2)*(Z t) + (3)*(X t)*a + (-1)*(X t)*(Z t)*a + (-1)*(X t)*(Y t)*a*b + (-2)*(X t)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(2:ℕ) + (3)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-5)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(3:ℕ)*(Y t)*a*b + (3)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (3)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(5:ℕ)*a + (2)*(X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (2)*(X t)^(6:ℕ) + (-1)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*a^(3:ℕ))/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((1 + (-1)*(W t) + (-1)*(X t)*a + (X t)*(Z t)*a + (-1)*(X t)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(W t) + (-1)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(W t)*a + (X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (-1)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(8:ℕ)*a^(2:ℕ))/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (-3 + (X t)*(Z t)*a + (-1)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (-2 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a)) (fun t => ((6 + (-2)*(W t) + (-2)*(Z t) + (3)*(X t)*a + (-1)*(X t)*(Z t)*a + (-1)*(X t)*(Y t)*a*b + (-2)*(X t)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(2:ℕ) + (3)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-5)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(3:ℕ)*(Y t)*a*b + (3)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (3)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(5:ℕ)*a + (2)*(X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (2)*(X t)^(6:ℕ) + (-1)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*a^(3:ℕ))/((W t)))) (fun t => ((1 + (-1)*(W t) + (-1)*(X t)*a + (X t)*(Z t)*a + (-1)*(X t)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(W t) + (-1)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(W t)*a + (X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (-1)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(8:ℕ)*a^(2:ℕ))/((W t)))) (fun t => (-3 + (X t)*(Z t)*a + (-1)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a)) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced14]
        ring))
  simpa only [reduced14,zero_mul,zero_add,add_zero] using h

#print axioms positive_closed_residue_row14

theorem positive_closed_residue_row150 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced150 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced150 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => (((-2)*(Y t)*b + (-2)*(Y t)^(2:ℕ) + (2)*(X t)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (0:ℂ)) (fun t => (((-2)*(Y t)*b + (-2)*(Y t)^(2:ℕ) + (2)*(X t)*a)/((Y t)^(2:ℕ)))) (fun t => (0:ℂ)) (fun t => (0:ℂ)) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced150]
        ring))
  simpa only [reduced150,zero_mul,zero_add,add_zero] using h

#print axioms positive_closed_residue_row150

theorem positive_closed_residue_row159 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced159 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced159 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((-2 + (Y t)^(2:ℕ) + (-1)*(X t)*a + (-2)*(X t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((-1 + (-1)*(Y t)*b + (X t)*a + (X t)^(4:ℕ))/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (0:ℂ)) (fun t => ((-2 + (Y t)^(2:ℕ) + (-1)*(X t)*a + (-2)*(X t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a)/((Y t)^(2:ℕ)))) (fun t => ((-1 + (-1)*(Y t)*b + (X t)*a + (X t)^(4:ℕ))/((Y t)^(2:ℕ)))) (fun t => (0:ℂ)) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced159]
        ring))
  simpa only [reduced159,zero_mul,zero_add,add_zero] using h

#print axioms positive_closed_residue_row159

theorem positive_closed_residue_row163 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced163 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced163 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => ((-3 + (X t)*a + (-1)*(X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1)*(X t)^(4:ℕ) + (-3)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(5:ℕ)*a + (X t)^(6:ℕ) + (X t)^(6:ℕ)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((-6 + (2)*(Z t) + (Y t)*b + (3)*(Y t)^(2:ℕ) + (4)*(X t)*a + (-5)*(X t)*(Z t)*a + (X t)*(Y t)*a*b + (-3)*(X t)*(Y t)^(2:ℕ)*a + (10)*(X t)^(2:ℕ) + (6)*(X t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Z t) + (-3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*b + (-5)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(3:ℕ)*a + (3)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-9)*(X t)^(4:ℕ) + (-4)*(X t)^(4:ℕ)*a^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Z t) + (3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*a^(4:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (2)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-9)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (3)*(X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (4)*(X t)^(5:ℕ)*(Y t)*a*b + (3)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (8)*(X t)^(6:ℕ) + (-1)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t) + (X t)^(6:ℕ)*(Y t)*b + (5)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)*a^(4:ℕ)*b + (-2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (11)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*a^(3:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(8:ℕ) + (2)*(X t)^(8:ℕ)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*a^(4:ℕ) + (-1)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*b + (-2)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*a^(3:ℕ) + (-2)*(X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ) + (X t)^(10:ℕ)*a^(2:ℕ) + (-1)*(X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(11:ℕ)*a + (X t)^(11:ℕ)*a^(3:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((-1 + (-1)*(W t) + (Z t) + (2)*(Y t)^(2:ℕ) + (2)*(X t)*a + (-2)*(X t)*(Z t)*a + (X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (6)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-6)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(W t)*a + (3)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-6)*(X t)^(4:ℕ) + (-2)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(W t) + (-1)*(X t)^(4:ℕ)*(W t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(W t)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (6)*(X t)^(6:ℕ) + (-1)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*a^(4:ℕ) + (X t)^(6:ℕ)*(W t) + (-3)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*b + (X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*a + (-4)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(W t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a + (-2)*(X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-3)*(X t)^(8:ℕ) + (-1)*(X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(8:ℕ)*(Y t)*b + (-3)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(9:ℕ)*a + (2)*(X t)^(9:ℕ)*a^(3:ℕ) + (X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (4)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*(Y t)*b + (X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(11:ℕ)*a + (X t)^(11:ℕ)*(Y t)*a*b + (-1)*(X t)^(11:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(12:ℕ)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => ((-1 + (-2)*(Z t) + (Y t)*b + (-2)*(X t)*a + (X t)*(Z t)*a + (-2)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a + (X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(5:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(6:ℕ) + (X t)^(6:ℕ)*(Z t) + (X t)^(7:ℕ)*a + (X t)^(7:ℕ)*(Z t)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => ((-3 + (X t)*a + (-1)*(X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1)*(X t)^(4:ℕ) + (-3)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(5:ℕ)*a + (X t)^(6:ℕ) + (X t)^(6:ℕ)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*a)/((Y t)^(2:ℕ)))) (fun t => ((-6 + (2)*(Z t) + (Y t)*b + (3)*(Y t)^(2:ℕ) + (4)*(X t)*a + (-5)*(X t)*(Z t)*a + (X t)*(Y t)*a*b + (-3)*(X t)*(Y t)^(2:ℕ)*a + (10)*(X t)^(2:ℕ) + (6)*(X t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Z t) + (-3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*b + (-5)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(3:ℕ)*a + (3)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-9)*(X t)^(4:ℕ) + (-4)*(X t)^(4:ℕ)*a^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Z t) + (3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*a^(4:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (2)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-9)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (3)*(X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (4)*(X t)^(5:ℕ)*(Y t)*a*b + (3)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (8)*(X t)^(6:ℕ) + (-1)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t) + (X t)^(6:ℕ)*(Y t)*b + (5)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)*a^(4:ℕ)*b + (-2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (11)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*a^(3:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(8:ℕ) + (2)*(X t)^(8:ℕ)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*a^(4:ℕ) + (-1)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*b + (-2)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*a^(3:ℕ) + (-2)*(X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ) + (X t)^(10:ℕ)*a^(2:ℕ) + (-1)*(X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(11:ℕ)*a + (X t)^(11:ℕ)*a^(3:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => ((-1 + (-1)*(W t) + (Z t) + (2)*(Y t)^(2:ℕ) + (2)*(X t)*a + (-2)*(X t)*(Z t)*a + (X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (6)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-6)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(W t)*a + (3)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-6)*(X t)^(4:ℕ) + (-2)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(W t) + (-1)*(X t)^(4:ℕ)*(W t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(W t)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (6)*(X t)^(6:ℕ) + (-1)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*a^(4:ℕ) + (X t)^(6:ℕ)*(W t) + (-3)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*b + (X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*a + (-4)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(W t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a + (-2)*(X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-3)*(X t)^(8:ℕ) + (-1)*(X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(8:ℕ)*(Y t)*b + (-3)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(9:ℕ)*a + (2)*(X t)^(9:ℕ)*a^(3:ℕ) + (X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (4)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*(Y t)*b + (X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(11:ℕ)*a + (X t)^(11:ℕ)*(Y t)*a*b + (-1)*(X t)^(11:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(12:ℕ)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => ((-1 + (-2)*(Z t) + (Y t)*b + (-2)*(X t)*a + (X t)*(Z t)*a + (-2)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a + (X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(5:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(6:ℕ) + (X t)^(6:ℕ)*(Z t) + (X t)^(7:ℕ)*a + (X t)^(7:ℕ)*(Z t)*a)/((Y t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced163]
        ring))
  simpa only [reduced163,zero_mul,zero_add,add_zero] using h

#print axioms positive_closed_residue_row163

theorem positive_closed_residue_row164 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced164 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced164 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => ((1 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-3)*(X t)*a + (-4)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a + (2)*(X t)^(4:ℕ))/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((7 + (-6)*(Z t) + (-2)*(Y t)*b + (-4)*(Y t)^(2:ℕ) + (4)*(X t)*a + (-1)*(X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (-11)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (4)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-7)*(X t)^(3:ℕ)*a + (2)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (5)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (11)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t) + (2)*(X t)^(4:ℕ)*(Y t)*b + (5)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (6)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (X t)^(6:ℕ) + (-2)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*a^(3:ℕ) + (-1)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(8:ℕ) + (X t)^(8:ℕ)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((2 + (-1)*(Z t) + (-2)*(Y t)^(2:ℕ) + (-1)*(X t)*a + (-1)*(X t)*(W t)*a + (3)*(X t)*(Z t)*a + (-5)*(X t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(W t) + (X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(W t)*a + (-3)*(X t)^(3:ℕ)*(Z t)*a + (3)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (8)*(X t)^(4:ℕ) + (-5)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(W t) + (-2)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Y t)*a*b + (4)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(6:ℕ) + (-1)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t) + (-3)*(X t)^(6:ℕ)*(Y t)*b + (-1)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (5)*(X t)^(7:ℕ)*a + (X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(9:ℕ)*a)/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => ((-2 + (2)*(Z t) + (-1)*(Y t)*b + (-1)*(X t)*a + (-2)*(X t)^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*(Z t))/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => ((1 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-3)*(X t)*a + (-4)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a + (2)*(X t)^(4:ℕ))/((Y t)^(2:ℕ)))) (fun t => ((7 + (-6)*(Z t) + (-2)*(Y t)*b + (-4)*(Y t)^(2:ℕ) + (4)*(X t)*a + (-1)*(X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (-11)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (4)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-7)*(X t)^(3:ℕ)*a + (2)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (5)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (11)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t) + (2)*(X t)^(4:ℕ)*(Y t)*b + (5)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (6)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (X t)^(6:ℕ) + (-2)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*a^(3:ℕ) + (-1)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(8:ℕ) + (X t)^(8:ℕ)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => ((2 + (-1)*(Z t) + (-2)*(Y t)^(2:ℕ) + (-1)*(X t)*a + (-1)*(X t)*(W t)*a + (3)*(X t)*(Z t)*a + (-5)*(X t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(W t) + (X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(W t)*a + (-3)*(X t)^(3:ℕ)*(Z t)*a + (3)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (8)*(X t)^(4:ℕ) + (-5)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(W t) + (-2)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Y t)*a*b + (4)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(6:ℕ) + (-1)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t) + (-3)*(X t)^(6:ℕ)*(Y t)*b + (-1)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (5)*(X t)^(7:ℕ)*a + (X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(9:ℕ)*a)/((Y t)^(2:ℕ)*(W t)))) (fun t => ((-2 + (2)*(Z t) + (-1)*(Y t)*b + (-1)*(X t)*a + (-2)*(X t)^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*(Z t))/((Y t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced164]
        ring))
  simpa only [reduced164,zero_mul,zero_add,add_zero] using h

#print axioms positive_closed_residue_row164

theorem positive_closed_residue_row16 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced16 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced16 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => ((3 + (-3)*(X t)*a + (X t)^(2:ℕ) + (X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (3)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*a^(3:ℕ) + (X t)^(4:ℕ) + (3)*(X t)^(4:ℕ)*a^(2:ℕ) + (2)*(X t)^(5:ℕ)*a)/((X t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((-1 + (2)*(W t) + (-2)*(Z t) + (-3)*(Y t)*b + (-2)*(Y t)^(2:ℕ) + (-4)*(X t)*a + (X t)*(W t)*a + (8)*(X t)*(Z t)*a + (X t)*(Y t)*a*b + (5)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ) + (-8)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (5)*(X t)^(3:ℕ)*a + (-3)*(X t)^(3:ℕ)*a^(3:ℕ) + (X t)^(3:ℕ)*(Z t)*a + (-2)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(4:ℕ) + (4)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (-3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(4:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (-5)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-5)*(X t)^(5:ℕ)*(Y t)*a*b + (-4)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-5)*(X t)^(6:ℕ) + (-1)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (-6)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)*a^(4:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (5)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (-7)*(X t)^(7:ℕ)*a + (2)*(X t)^(7:ℕ)*a^(3:ℕ) + (-2)*(X t)^(7:ℕ)*(Y t)*a*b + (-2)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ) + (-1)*(X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*a^(4:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(9:ℕ)*a + (X t)^(9:ℕ)*a^(3:ℕ))/((X t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => (((W t) + (-2)*(Z t) + (-1)*(Y t)*b + (-2)*(Y t)^(2:ℕ) + (3)*(X t)*(Z t)*a + (2)*(X t)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(2:ℕ) + (X t)^(2:ℕ)*(Z t) + (-2)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (4)*(X t)^(3:ℕ)*a + (2)*(X t)^(3:ℕ)*(W t)*a + (-3)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(W t) + (X t)^(4:ℕ)*(W t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (-2)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(5:ℕ)*a + (2)*(X t)^(5:ℕ)*a^(3:ℕ) + (X t)^(5:ℕ)*(W t)*a + (X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(5:ℕ)*(Y t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-4)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(6:ℕ) + (4)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*a^(4:ℕ) + (2)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-3)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(7:ℕ)*a + (4)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)*a + (2)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (-4)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*b + (2)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*a^(3:ℕ) + (X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(10:ℕ)*a^(2:ℕ))/((X t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => ((1 + (-1)*(W t) + (2)*(Z t) + (X t)*a + (-2)*(X t)*(Z t)*a + (3)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(5:ℕ)*a + (X t)^(5:ℕ)*(Z t)*a)/((X t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => ((3 + (-3)*(X t)*a + (X t)^(2:ℕ) + (X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (3)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*a^(3:ℕ) + (X t)^(4:ℕ) + (3)*(X t)^(4:ℕ)*a^(2:ℕ) + (2)*(X t)^(5:ℕ)*a)/((X t)^(2:ℕ)))) (fun t => ((-1 + (2)*(W t) + (-2)*(Z t) + (-3)*(Y t)*b + (-2)*(Y t)^(2:ℕ) + (-4)*(X t)*a + (X t)*(W t)*a + (8)*(X t)*(Z t)*a + (X t)*(Y t)*a*b + (5)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ) + (-8)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (5)*(X t)^(3:ℕ)*a + (-3)*(X t)^(3:ℕ)*a^(3:ℕ) + (X t)^(3:ℕ)*(Z t)*a + (-2)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(4:ℕ) + (4)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (-3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(4:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (-5)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-5)*(X t)^(5:ℕ)*(Y t)*a*b + (-4)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-5)*(X t)^(6:ℕ) + (-1)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (-6)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)*a^(4:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (5)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (-7)*(X t)^(7:ℕ)*a + (2)*(X t)^(7:ℕ)*a^(3:ℕ) + (-2)*(X t)^(7:ℕ)*(Y t)*a*b + (-2)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ) + (-1)*(X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*a^(4:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(9:ℕ)*a + (X t)^(9:ℕ)*a^(3:ℕ))/((X t)^(2:ℕ)*(W t)))) (fun t => (((W t) + (-2)*(Z t) + (-1)*(Y t)*b + (-2)*(Y t)^(2:ℕ) + (3)*(X t)*(Z t)*a + (2)*(X t)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(2:ℕ) + (X t)^(2:ℕ)*(Z t) + (-2)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (4)*(X t)^(3:ℕ)*a + (2)*(X t)^(3:ℕ)*(W t)*a + (-3)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(W t) + (X t)^(4:ℕ)*(W t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (-2)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(5:ℕ)*a + (2)*(X t)^(5:ℕ)*a^(3:ℕ) + (X t)^(5:ℕ)*(W t)*a + (X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(5:ℕ)*(Y t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-4)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(6:ℕ) + (4)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*a^(4:ℕ) + (2)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-3)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(7:ℕ)*a + (4)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)*a + (2)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (-4)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*b + (2)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*a^(3:ℕ) + (X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(10:ℕ)*a^(2:ℕ))/((X t)^(2:ℕ)*(W t)))) (fun t => ((1 + (-1)*(W t) + (2)*(Z t) + (X t)*a + (-2)*(X t)*(Z t)*a + (3)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(5:ℕ)*a + (X t)^(5:ℕ)*(Z t)*a)/((X t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced16]
        ring))
  simpa only [reduced16,zero_mul,zero_add,add_zero] using h

#print axioms positive_closed_residue_row16

theorem positive_closed_residue_row18 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced18 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced18 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (((-2)*(Z t) + (-1)*(Y t)*(Z t)*b + (-1)*(Y t)^(2:ℕ)*(Z t) + (2)*(X t)*(Z t)*a + (X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-2)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(5:ℕ)*(Z t)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => (((6)*(Z t) + (-1)*(Z t)*(W t) + (-1)*(Z t)^(2:ℕ) + (2)*(Y t)*(Z t)*b + (3)*(X t)*(Z t)*a + (-4)*(X t)*(Z t)^(2:ℕ)*a + (-3)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (6)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-5)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-2)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(3:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-5)*(X t)^(4:ℕ)*(Z t) + (2)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-3)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(5:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (3)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (3)*(X t)^(6:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*(Z t)*b + (4)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-3)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (5)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (X t)^(7:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(8:ℕ)*(Z t) + (-1)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Z t)*a^(3:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => (((Z t) + (Y t)*(Z t)*b + (Y t)^(2:ℕ)*(Z t) + (-1)*(X t)*(Z t)*a + (-1)*(X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(2:ℕ)*(Z t) + (-2)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (-2)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*(W t)*a + (3)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (-2)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*(W t) + (X t)^(4:ℕ)*(Z t)^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (2)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (3)*(X t)^(6:ℕ)*(Z t) + (-4)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*(Z t)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (3)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-2)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Y t)*(Z t)*a*b + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(10:ℕ)*(Z t)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (((-1)*(Z t) + (Z t)*(W t) + (-1)*(Z t)^(2:ℕ) + (X t)*(Z t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (((-2)*(Z t) + (-1)*(Y t)*(Z t)*b + (-1)*(Y t)^(2:ℕ)*(Z t) + (2)*(X t)*(Z t)*a + (X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-2)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(5:ℕ)*(Z t)*a)/((Y t)^(2:ℕ)))) (fun t => (((6)*(Z t) + (-1)*(Z t)*(W t) + (-1)*(Z t)^(2:ℕ) + (2)*(Y t)*(Z t)*b + (3)*(X t)*(Z t)*a + (-4)*(X t)*(Z t)^(2:ℕ)*a + (-3)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (6)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-5)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-2)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(3:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-5)*(X t)^(4:ℕ)*(Z t) + (2)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-3)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(5:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (3)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (3)*(X t)^(6:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*(Z t)*b + (4)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-3)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (5)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (X t)^(7:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(8:ℕ)*(Z t) + (-1)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Z t)*a^(3:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => (((Z t) + (Y t)*(Z t)*b + (Y t)^(2:ℕ)*(Z t) + (-1)*(X t)*(Z t)*a + (-1)*(X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(2:ℕ)*(Z t) + (-2)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (-2)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*(W t)*a + (3)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (-2)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*(W t) + (X t)^(4:ℕ)*(Z t)^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (2)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (3)*(X t)^(6:ℕ)*(Z t) + (-4)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*(Z t)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (3)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-2)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Y t)*(Z t)*a*b + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(10:ℕ)*(Z t)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => (((-1)*(Z t) + (Z t)*(W t) + (-1)*(Z t)^(2:ℕ) + (X t)*(Z t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a)/((Y t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced18]
        ring))
  simpa only [reduced18,zero_mul,zero_add,add_zero] using h

#print axioms positive_closed_residue_row18

theorem positive_closed_residue_row19 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced19 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced19 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (((3)*(Z t) + (-2)*(X t)*(Z t)*a + (-3)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*(Z t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-2)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(5:ℕ)*(Z t)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => (((6)*(Z t) + (-1)*(Z t)*(W t) + (-7)*(Z t)^(2:ℕ) + (-4)*(Y t)*(Z t)*b + (-4)*(Y t)^(2:ℕ)*(Z t) + (7)*(X t)*(Z t)*a + (-2)*(X t)*(Y t)*(Z t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (-16)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*(Z t)*b + (4)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-12)*(X t)^(3:ℕ)*(Z t)*a + (4)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(3:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (5)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (11)*(X t)^(4:ℕ)*(Z t) + (-4)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)*(Z t)*b + (4)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (9)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(6:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*(Z t)*b + (-2)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ)*(Z t) + (X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(9:ℕ)*(Z t)*a + (X t)^(9:ℕ)*(Z t)*a^(3:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => (((Z t) + (-2)*(Z t)^(2:ℕ) + (-1)*(Y t)*(Z t)*b + (-3)*(Y t)^(2:ℕ)*(Z t) + (X t)*(Z t)*a + (3)*(X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (-6)*(X t)^(2:ℕ)*(Z t) + (-2)*(X t)^(2:ℕ)*(Z t)*(W t) + (2)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*(Z t)*b + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-2)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*(W t)*a + (-3)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (2)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (8)*(X t)^(4:ℕ)*(Z t) + (-2)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*(W t) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)*(Z t)*b + (X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-3)*(X t)^(6:ℕ)*(Z t) + (-2)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(6:ℕ)*(Y t)*(Z t)*b + (-2)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (4)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*(Z t)*b + (X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(9:ℕ)*(Z t)*a + (X t)^(9:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(10:ℕ)*(Z t)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (((-1)*(Z t) + (-1)*(Z t)*(W t) + (3)*(Z t)^(2:ℕ) + (X t)*(Z t)^(2:ℕ)*a + (X t)^(2:ℕ)*(Z t) + (-3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*(Z t)*a + (-2)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)^(2:ℕ) + (X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)^(2:ℕ)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (((3)*(Z t) + (-2)*(X t)*(Z t)*a + (-3)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*(Z t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-2)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(5:ℕ)*(Z t)*a)/((Y t)^(2:ℕ)))) (fun t => (((6)*(Z t) + (-1)*(Z t)*(W t) + (-7)*(Z t)^(2:ℕ) + (-4)*(Y t)*(Z t)*b + (-4)*(Y t)^(2:ℕ)*(Z t) + (7)*(X t)*(Z t)*a + (-2)*(X t)*(Y t)*(Z t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (-16)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*(Z t)*b + (4)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-12)*(X t)^(3:ℕ)*(Z t)*a + (4)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(3:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (5)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (11)*(X t)^(4:ℕ)*(Z t) + (-4)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)*(Z t)*b + (4)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (9)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(6:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*(Z t)*b + (-2)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ)*(Z t) + (X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(9:ℕ)*(Z t)*a + (X t)^(9:ℕ)*(Z t)*a^(3:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => (((Z t) + (-2)*(Z t)^(2:ℕ) + (-1)*(Y t)*(Z t)*b + (-3)*(Y t)^(2:ℕ)*(Z t) + (X t)*(Z t)*a + (3)*(X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (-6)*(X t)^(2:ℕ)*(Z t) + (-2)*(X t)^(2:ℕ)*(Z t)*(W t) + (2)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*(Z t)*b + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-2)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*(W t)*a + (-3)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (2)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (8)*(X t)^(4:ℕ)*(Z t) + (-2)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*(W t) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)*(Z t)*b + (X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-3)*(X t)^(6:ℕ)*(Z t) + (-2)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(6:ℕ)*(Y t)*(Z t)*b + (-2)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (4)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*(Z t)*b + (X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(9:ℕ)*(Z t)*a + (X t)^(9:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(10:ℕ)*(Z t)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => (((-1)*(Z t) + (-1)*(Z t)*(W t) + (3)*(Z t)^(2:ℕ) + (X t)*(Z t)^(2:ℕ)*a + (X t)^(2:ℕ)*(Z t) + (-3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*(Z t)*a + (-2)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)^(2:ℕ) + (X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)^(2:ℕ)*a)/((Y t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced19]
        ring))
  simpa only [reduced19,zero_mul,zero_add,add_zero] using h

#print axioms positive_closed_residue_row19

theorem positive_closed_residue_row3 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced3 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced3 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (-3 + (X t)^(2:ℕ) + (X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(3:ℕ)*a)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((-7 + (6)*(Z t) + (Y t)*b + (3)*(Y t)^(2:ℕ) + (-5)*(X t)*a + (3)*(X t)*(Z t)*a + (3)*(X t)*(Y t)*a*b + (X t)*(Y t)^(2:ℕ)*a + (8)*(X t)^(2:ℕ) + (-3)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (6)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (-3)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(5:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Y t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(6:ℕ) + (X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(7:ℕ)*a + (X t)^(7:ℕ)*a^(3:ℕ))/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((-1 + (-1)*(W t) + (2)*(Z t) + (2)*(Y t)^(2:ℕ) + (-1)*(X t)*(Z t)*a + (X t)*(Y t)*a*b + (X t)*(Y t)^(2:ℕ)*a + (4)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(W t) + (-1)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(W t)*a + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (-3)*(X t)^(4:ℕ) + (X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)*b + (-1)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(5:ℕ)*a + (X t)^(5:ℕ)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*b + (X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(7:ℕ)*a + (X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(8:ℕ)*a^(2:ℕ))/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (-1 + (-2)*(Z t) + (-1)*(X t)*(Z t)*a + (X t)^(2:ℕ)*(Z t) + (X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Z t)*a)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (-3 + (X t)^(2:ℕ) + (X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(3:ℕ)*a)) (fun t => ((-7 + (6)*(Z t) + (Y t)*b + (3)*(Y t)^(2:ℕ) + (-5)*(X t)*a + (3)*(X t)*(Z t)*a + (3)*(X t)*(Y t)*a*b + (X t)*(Y t)^(2:ℕ)*a + (8)*(X t)^(2:ℕ) + (-3)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (6)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (-3)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(5:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Y t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(6:ℕ) + (X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(7:ℕ)*a + (X t)^(7:ℕ)*a^(3:ℕ))/((W t)))) (fun t => ((-1 + (-1)*(W t) + (2)*(Z t) + (2)*(Y t)^(2:ℕ) + (-1)*(X t)*(Z t)*a + (X t)*(Y t)*a*b + (X t)*(Y t)^(2:ℕ)*a + (4)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(W t) + (-1)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(W t)*a + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (-3)*(X t)^(4:ℕ) + (X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)*b + (-1)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(5:ℕ)*a + (X t)^(5:ℕ)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*b + (X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(7:ℕ)*a + (X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(8:ℕ)*a^(2:ℕ))/((W t)))) (fun t => (-1 + (-2)*(Z t) + (-1)*(X t)*(Z t)*a + (X t)^(2:ℕ)*(Z t) + (X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Z t)*a)) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced3]
        ring))
  simpa only [reduced3,zero_mul,zero_add,add_zero] using h

#print axioms positive_closed_residue_row3

theorem positive_closed_residue_row45 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced45 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced45 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => (1 + (-1)*(Y t)*b + (-2)*(Y t)^(2:ℕ) + (3)*(X t)*a + (-2)*(X t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((-1)*(Y t)^(2:ℕ) + (X t)*a + (-2)*(X t)^(2:ℕ) + (X t)^(4:ℕ))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => ((-1)*(W t) + (Z t)*(W t))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (0:ℂ)) (fun t => (1 + (-1)*(Y t)*b + (-2)*(Y t)^(2:ℕ) + (3)*(X t)*a + (-2)*(X t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a)) (fun t => ((-1)*(Y t)^(2:ℕ) + (X t)*a + (-2)*(X t)^(2:ℕ) + (X t)^(4:ℕ))) (fun t => ((-1)*(W t) + (Z t)*(W t))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced45]
        ring))
  simpa only [reduced45,zero_mul,zero_add,add_zero] using h

#print axioms positive_closed_residue_row45

theorem positive_closed_residue_row53 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced53 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced53 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((-4 + (-2)*(Y t)*b + (Y t)^(2:ℕ) + (X t)*(Y t)*a*b + (X t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ))/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((-1 + (-1)*(Y t)*b + (2)*(X t)*a + (X t)*(Y t)*a*b + (2)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)*b + (-3)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (X t)^(5:ℕ)*a)/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (-1 + (-1)*(W t))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (0:ℂ)) (fun t => ((-4 + (-2)*(Y t)*b + (Y t)^(2:ℕ) + (X t)*(Y t)*a*b + (X t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ))/((W t)))) (fun t => ((-1 + (-1)*(Y t)*b + (2)*(X t)*a + (X t)*(Y t)*a*b + (2)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)*b + (-3)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (X t)^(5:ℕ)*a)/((W t)))) (fun t => (-1 + (-1)*(W t))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced53]
        ring))
  simpa only [reduced53,zero_mul,zero_add,add_zero] using h

#print axioms positive_closed_residue_row53

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalPositiveClosedResidueRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFivePositiveAnalyticShortRows
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

theorem original_positive_closed_residue_rows {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (U : ℂ → ℂ) (hU : AnalyticAt ℂ U s) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v) :
    positiveRowsConclusion (primeParameter 2 m s) (primeParameter 3 m s)
      (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  have h0 := positive_closed_residue_row0 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_positive_row0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h3 := positive_closed_residue_row3 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_positive_row3 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h13 := positive_closed_residue_row13 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_positive_row13 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h14 := positive_closed_residue_row14 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_positive_row14 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h16 := positive_closed_residue_row16 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_positive_row16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h18 := positive_closed_residue_row18 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_positive_row18 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h19 := positive_closed_residue_row19 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_positive_row19 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h45 := positive_closed_residue_row45 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_positive_row45 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h53 := positive_closed_residue_row53 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_positive_row53 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h150 := positive_closed_residue_row150 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_positive_row150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h159 := positive_closed_residue_row159 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_positive_row159 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h163 := positive_closed_residue_row163 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_positive_row163 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h164 := positive_closed_residue_row164 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_positive_row164 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  exact ⟨h0,h3,h13,h14,h16,h18,h19,h45,h53,h150,h159,h163,h164⟩

#print axioms original_positive_closed_residue_rows
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveClosedRowsScale -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

theorem positive_rows_scale (x y z w a b c : ℂ) (v : Fin 210 → ℂ)
    (h : positiveRowsConclusion x y z w a b v) :
    positiveRowsConclusion x y z w a b (fun j => c*v j) := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩
  unfold positiveRowsConclusion
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · linear_combination c*h0
  · linear_combination c*h1
  · linear_combination c*h2
  · linear_combination c*h3
  · linear_combination c*h4
  · linear_combination c*h5
  · linear_combination c*h6
  · linear_combination c*h7
  · linear_combination c*h8
  · linear_combination c*h9
  · linear_combination c*h10
  · linear_combination c*h11
  · linear_combination c*h12

#print axioms positive_rows_scale
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveClosedKernel -/
section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan

/-- Positive-product closed-row kernel, with no global leading-vector premise.
Consequently this algebraic obstruction can be applied at any Laurent order. -/
theorem closed_positive_physical_kernel (m : ℕ) (s u5 u7 a b : ℂ)
    (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (v : Fin 210 → ℂ) (hs : (m:ℝ)≤s.re)
    (he : 1+primeParameter 2 m s*a+(primeParameter 2 m s)^2=0)
    (hRows : positiveRowsConclusion (primeParameter 2 m s) (primeParameter 3 m s)
      (u5*primeParameter 5 m s) (u7*primeParameter 7 m s) a b v) : v 192=0 := by
  let x := primeParameter 2 m s
  let y := primeParameter 3 m s
  let z := u5*primeParameter 5 m s
  let w := u7*primeParameter 7 m s
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  have hx : x≠0 := primeParameter_ne_zero 2 m (by decide) s
  have hy : y≠0 := primeParameter_ne_zero 3 m (by decide) s
  have hz0 : z≠0 := mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s)
  have hw : w≠0 := mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)
  change 1+x*a+x^2=0 at he
  change positiveRowsConclusion x y z w a b v at hRows
  by_cases hz : z=1
  · rw [hz] at hRows
    by_cases hw1 : w+1=0
    · have hw' : w= -1 := by linear_combination hw1
      have hcenter := signed_prime_five_seven_center m s u5 u7 hu5 hu7 hz hw'
      have hp2 : x=1 := by simp only [x,primeParameter,hcenter,Complex.cpow_zero]
      have hp3 : y=1 := by simp only [y,primeParameter,hcenter,Complex.cpow_zero]
      rw [hp2] at he
      have ha : a= -2 := by linear_combination he
      rw [hp2,hp3,hw',ha] at hRows
      exact positive_rows_signed_central b v hRows
    · exact positive_z_one_rows x y w a b v hx hy hw hw1
        (signed_prime_five_one_C_ne_zero m s u5 hu5 hz) he hRows
  by_contra hr
  let v' : Fin 210 → ℂ := fun j => (v 192)⁻¹*v j
  have h192 : v' 192=1 := by simp [v',hr]
  have hr' : v' 192≠0 := by rw [h192]; norm_num
  have hRows' := positive_rows_scale x y z w a b (v 192)⁻¹ v hRows
  obtain ⟨hp,h1,hcrow⟩ := positive_rows_branch_parameter x y z w a b v' hy hw hz hr' he hRows'
  have hwrel := positive_rows_all_branch_w x y z w a b v' hw hr' he hp h1 hcrow hRows'
  have hC : x^4-3*x^2-y^2-1≠0 := by
    have hn : (x^4-3*x^2-y^2-1)*(v' 84+v' 42)≠0 := by
      rw [hcrow]
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hw) (sub_ne_zero.mpr hz)) hr'
    exact (mul_ne_zero_iff.mp hn).1
  have ha : a= -x-1/x := by
    linear_combination (norm := (field_simp [hx]; ring)) (1/x)*he
  have hb : b=(x^4-x^2-2)/y := by
    linear_combination (norm := (field_simp [hy]; ring)) -(1/y)*hp
  by_cases hA : x^4+y^2-1=0
  · exact positive_a0_normalized_exclusion x y z w a b v' hx hy hz0 hw hz
      ha hb hA hC hwrel hcrow h192 hRows'
  have h42 : v' 42=0 := by
    apply (mul_eq_zero.mp h1).resolve_left
    intro hh
    apply hA
    linear_combination hp+hh
  obtain ⟨h0,h1,h2,h3⟩ := positive_generic_normalized_inputs x y z w a b v'
    hx hy hz0 hw ha hb hC hwrel hcrow h192 h42 hRows'
  let X := x^2
  let Y := y^2
  have hC' : X^2-Y-3*X-1≠0 := by
    convert hC using 1 <;> dsimp [X,Y] <;> ring
  have hXm : X+1≠0 := by
    intro h
    have hx' : X= -1 := by linear_combination h
    change positiveGenericInput0 X Y z=0 at h0
    rw [hx'] at h0
    have hz3 := positive_generic_minus_one Y z hz h0
    exact signed_prime_two_minus_one_not_three m s u5 hu5 hx' hz3
  have hfactor := mul_ne_zero hC' hXm
  have hP := (mul_eq_zero.mp (positive_generic_p15_certificate X Y z h0 h1 h2 h3)).resolve_left hfactor
  have hQ := sub_eq_zero.mp ((mul_eq_zero.mp
    (positive_generic_y_certificate X Y z h0 h1 h2 h3)).resolve_left hfactor)
  have hR := sub_eq_zero.mp ((mul_eq_zero.mp
    (positive_generic_z_certificate X Y z h0 h1 h2 h3)).resolve_left hfactor)
  obtain ⟨hxN,hyN,hyxN⟩ := physical_parameters m s hs
  change 1≤‖X‖ at hxN
  change 1≤‖Y‖ at hyN
  change ‖Y‖≤‖X‖^2 at hyxN
  have hzN : 1≤‖z‖ := by
    dsimp [z]
    rw [sign_mul_norm u5 _ hu5,primeParameter_norm 5 m (by decide)]
    exact Real.one_le_rpow (by norm_num) (sub_nonneg.mpr hs)
  rw [hQ] at hyN hyxN
  rw [hR] at hzN
  exact QuantitativeArithmeticSmallLevelThirtyFivePositiveRootDisks.positive_no_physical_root
    X hP hxN hyN hyxN hzN

#print axioms closed_positive_physical_kernel
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFivePositiveDoublePoleRemoval -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFivePositiveAnalyticShortRows
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

theorem positive_coordinate84_simple_of_coordinate192_simple {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re)
    (hP : 1+((Real.sqrt 2:ℂ)*f 2)*primeParameter 2 m s+(primeParameter 2 m s)^2=0)
    (h192 : (-1:WithTop ℤ)≤meromorphicOrderAt (fun t => G t 192) s) :
    (-1:WithTop ℤ)≤meromorphicOrderAt (fun t => G t 84) s := by
  by_cases hpivot : shortPivotK m ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s≠0 ∨
      shortPivotL m ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s≠0
  · exact positive_coordinate84_order_ge_neg_one_of_pivot hm hf ε hε hlaw u5 u7 hu5 hu7
      hphase h5 h7 BG G hG hGF s hshift hs hP hpivot
  push Not at hpivot
  obtain ⟨hK,hL⟩ := hpivot
  let X := primeParameter 2 m
  let Y := primeParameter 3 m
  let Z : ℂ → ℂ := fun t => u5*primeParameter 5 m t
  let W : ℂ → ℂ := fun t => u7*primeParameter 7 m t
  let a : ℂ := (Real.sqrt 2:ℂ)*f 2
  let b : ℂ := (Real.sqrt 3:ℂ)*f 3
  have hx : AnalyticAt ℂ X s := primeParameter_analytic 2 m (by decide) s
  have hy : AnalyticAt ℂ Y s := primeParameter_analytic 3 m (by decide) s
  have hz : AnalyticAt ℂ Z s := analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s)
  have hw : AnalyticAt ℂ W s := analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)
  have hA : (X s)^4+(Y s)^2-1=0 := by
    dsimp [shortPivotK] at hK
    dsimp [shortPivotL] at hL
    linear_combination hL-hK
  let C : ℂ → ℂ := fun t => -(Y t)^2+X t*a-2*(X t)^2+(X t)^4
  let D : ℂ → ℂ := fun t => 1-Y t*b-2*(Y t)^2+3*X t*a-2*(X t)^2-(X t)^3*a
  let E : ℂ → ℂ := fun t => -W t+Z t*W t
  have hC : AnalyticAt ℂ C s := by dsimp [C]; fun_prop
  have hD : AnalyticAt ℂ D s := by dsimp [D]; fun_prop
  have hE : AnalyticAt ℂ E s := by dsimp [E]; fun_prop
  have hC0 : C s≠0 := by
    intro hzero
    apply a0_third_pivot m s hs hA
    change -(Y s)^2+X s*a-2*(X s)^2+(X s)^4=0 at hzero
    change 1+a*X s+(X s)^2=0 at hP
    linear_combination hzero-hP+hA
  have h42 := positive_coordinate42_order_ge_neg_one hm hf ε hε hlaw u5 u7 hu5 hu7
    hphase h5 h7 BG G hG hGF s hshift hs hP
  have hrow := analytic_signed_positive_row45 hm hf ε hε hlaw u5 u7 hu5 hu7
    hphase h5 h7 BG G hG hGF s hshift
  have hr : HasAnalyticGerm
      (fun t => C t*G t 84+D t*G t 42+E t*G t 192+0*G t 42) s := by
    apply hrow.congr
    exact Filter.Eventually.of_forall (fun t => by dsimp [C,D,E,X,Y,Z,W,a,b,reduced45]; ring)
  apply four_row_order_lower hC hD hE analyticAt_const hC0
    (hG 42 s).meromorphicAt (hG 192 s).meromorphicAt (hG 42 s).meromorphicAt
    ?_ h42 h192 h42 hr
  change ((-1:ℤ):WithTop ℤ)≤((0:ℤ):WithTop ℤ)
  exact WithTop.coe_le_coe.mpr (by omega)

#print axioms positive_coordinate84_simple_of_coordinate192_simple
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalPositiveChiThreeRegular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

/-- The actual chi3 coordinate is regular in the positive-product sign class.
The residue argument is performed on the closed four-coordinate family only. -/
theorem original_positive_chi3_coordinate_regular {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hproduct : ε*I^(2*m)*badFive f*badSeven f= 1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re)
    (hden : QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0) :
    AnalyticAt ℂ (fun z => G z 192) s := by
  obtain ⟨h24,h42,h84,h192⟩ := original_positive_four_orders hm hf ε hε hlaw hproduct
    BG G hG hGF s hshift hs hden
  have h5 := badFive_sign hf.toEulerData
  have h7 := badSeven_sign hf.toEulerData
  have hu5 : -badFive f=1 ∨ -badFive f= -1 := by rcases h5 with h|h <;> simp [h]
  have hu7 : -badSeven f=1 ∨ -badSeven f= -1 := by rcases h7 with h|h <;> simp [h]
  have h5sq : (badFive f)^2=1 := by rcases h5 with h|h <;> rw [h] <;> norm_num
  have h7sq : (badSeven f)^2=1 := by rcases h7 with h|h <;> rw [h] <;> norm_num
  have hphase : ε*I^(2*m)= (-badFive f)*(-badSeven f) := by
    linear_combination (badFive f*badSeven f)*hproduct-
      (ε*I^(2*m)*(badSeven f)^2)*h5sq-(ε*I^(2*m))*h7sq
  have hP := chi3_candidate_polynomial m f s hden
  have hker (U : ℂ → ℂ) (hU : AnalyticAt ℂ U s) (v : Fin 210 → ℂ)
      (hv : IsClosedFourResidue (fun t i => U t*G t i) s v) : v 192=0 := by
    have hA := original_positive_closed_residue_rows hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
      BG G hG hGF s hshift U hU v hv
    apply closed_positive_physical_kernel m s (-badFive f) (-badSeven f)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) hu5 hu7 v hs ?_ hA
    simpa only [mul_comm] using hP
  have h42two : (-2:WithTop ℤ)≤meromorphicOrderAt (fun t => G t 42) s := by
    apply le_trans ?_ h42
    change ((-2:ℤ):WithTop ℤ)≤((-1:ℤ):WithTop ℤ)
    exact WithTop.coe_le_coe.mpr (by omega)
  have hfour (j : Fin 4) : (-2:WithTop ℤ)≤
      meromorphicOrderAt (fun t => G t (closedFourIndex j)) s := by
    fin_cases j
    · exact h24
    · exact h42two
    · exact h84
    · exact h192
  let R : ℂ → Fin 210 → ℂ := fun t j => (t-s)*G t j
  have hR (j : Fin 210) : MeromorphicAt (fun t => R t j) s :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt.mul (hG j s).meromorphicAt
  have h192simple : (-1:WithTop ℤ)≤meromorphicOrderAt (fun t => G t 192) s := by
    obtain ⟨v,hv,hzero⟩ := exists_closed_four_residue R s hR
      (fun j => regularized_order_ge_neg_one (hG (closedFourIndex j) s).meromorphicAt (hfour j))
    have hv0 := hker (fun t => t-s) (analyticAt_id.sub analyticAt_const) v hv
    have hr0 := (hzero (3:Fin 4)).mp hv0
    exact (regularized_order_nonneg_iff (hG 192 s).meromorphicAt).mp hr0
  have h84simple := positive_coordinate84_simple_of_coordinate192_simple hm hf ε hε hlaw
    (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
    BG G hG hGF s hshift hs hP h192simple
  have hb0 : (-1:WithTop ℤ)≤0 := by
    change ((-1:ℤ):WithTop ℤ)≤((0:ℤ):WithTop ℤ)
    exact WithTop.coe_le_coe.mpr (by omega)
  have h24simple := positive_coordinate24_order_lower hm hf ε hε hlaw
    (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
    BG G hG hGF s hshift hP (-1) hb0 h42 h84simple h192simple
  have hsimple (j : Fin 4) : (-1:WithTop ℤ)≤
      meromorphicOrderAt (fun t => G t (closedFourIndex j)) s := by
    fin_cases j
    · exact h24simple
    · exact h42
    · exact h84simple
    · exact h192simple
  obtain ⟨v,hv,hzero⟩ := exists_closed_four_residue G s (fun j => (hG j s).meromorphicAt) hsimple
  have hv' : IsClosedFourResidue (fun t i => (1:ℂ)*G t i) s v := by
    simpa only [one_mul] using hv
  have hv0 := hker (fun _ => 1) analyticAt_const v hv'
  exact (hG 192 s).meromorphicOrderAt_nonneg_iff_analyticAt.mp ((hzero (3:Fin 4)).mp hv0)

#print axioms original_positive_chi3_coordinate_regular
/-- Original Euler and entire Fricke input supplies one coherent grid whose
chi3 coordinate has no right-halfplane candidate poles in positive-product signs. -/
theorem original_positive_chi3_regular_grid {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      ∃ BG : ℝ, ∃ G : ℂ → Fin 210 → ℂ,
        (∀ i z, MeromorphicNFAt (fun s => G s i) z) ∧
        (∀ z, BG<z.re → G z=gridVector (2*m) f z) ∧
        (∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          ∀ n : ℕ, 0<n → ∀ j, AnalyticAt ℂ (fun z => G z j) (s+(n:ℂ))) ∧
        (ε*I^(2*m)*badFive f*badSeven f= 1 → ∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          AnalyticAt ℂ (fun z => G z 192) s) := by
  obtain ⟨ε,hε,hlaw,BG,G,hG,hGF,htail⟩ := original_chi3_positive_shift_tail hm hf
  refine ⟨ε,hε,hlaw,BG,G,hG,hGF,htail,?_⟩
  intro hproduct s hs hden
  exact original_positive_chi3_coordinate_regular hm hf ε hε hlaw hproduct BG G hG hGF s
    (fun n hn j => (htail s hs hden n hn j).meromorphicOrderAt_nonneg) hs hden

#print axioms original_positive_chi3_regular_grid
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalAnalyticRowPivot24 -/
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRows
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

theorem analytic_signed_negative_rowPivot24 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
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
    HasAnalyticGerm (fun t => reducedPivot24 (primeParameter 2 m t) (primeParameter 3 m t)
      (u5*primeParameter 5 m t) (u7*primeParameter 7 m t)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) (G t)) s := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  apply analytic_reducedPivot24 (primeParameter 2 m) (primeParameter 3 m)
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
  · exact analytic_short_source_2852 hm hf ε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift
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
  · exact analytic_short_source_3238 hm hf BG G hG hGF s
  · exact analytic_short_source_3242 hm hf BG G hG hGF s
  · exact analytic_short_source_3250 hm hf BG G hG hGF s
  · exact analytic_short_source_3262 hm hf BG G hG hGF s
  · exact analytic_short_source_3292 hm hf BG G hG hGF s
  · exact analytic_short_source_3302 hm hf BG G hG hGF s
  · exact analytic_short_source_3304 hm hf BG G hG hGF s
  · exact analytic_short_source_3310 hm hf BG G hG hGF s
  · exact analytic_short_source_3358 hm hf BG G hG hGF s
  · exact analytic_short_source_3362 hm hf BG G hG hGF s
  · exact analytic_short_source_3364 hm hf BG G hG hGF s
  · exact analytic_short_source_3392 hm hf BG G hG hGF s
  · exact analytic_short_source_3426 hm hf BG G hG hGF s
  · exact analytic_short_source_3432 hm hf BG G hG hGF s
  · exact analytic_short_source_3476 hm hf BG G hG hGF s
  · exact analytic_short_source_3478 hm hf BG G hG hGF s

#print axioms analytic_signed_negative_rowPivot24
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveNegativeFourthOrder -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRows
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

theorem negative_coordinate24_order_lower {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hP : 1+((Real.sqrt 2:ℂ)*f 2)*primeParameter 2 m s+(primeParameter 2 m s)^2=0)
    (β : WithTop ℤ) (hβ : β≤0)
    (h42 : β≤meromorphicOrderAt (fun t => G t 42) s)
    (h84 : β≤meromorphicOrderAt (fun t => G t 84) s)
    (h192 : β≤meromorphicOrderAt (fun t => G t 192) s) :
    β≤meromorphicOrderAt (fun t => G t 24) s := by
  have hrow := analytic_signed_negative_rowPivot24 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7
    BG G hG hGF s hshift
  simp only [pivot24_decomposition] at hrow
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  have hx := primeParameter_analytic 2 m (by decide) s
  have hy := primeParameter_analytic 3 m (by decide) s
  have hz := (analyticAt_const (v:=u5)).mul (primeParameter_analytic 5 m (by decide) s)
  have hw := (analyticAt_const (v:=u7)).mul (primeParameter_analytic 7 m (by decide) s)
  have hx0 := primeParameter_ne_zero 2 m (by decide) s
  have hy0 := primeParameter_ne_zero 3 m (by decide) s
  have hz0 := mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s)
  have hw0 := mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)
  have hc24 := pivot24C24_analytic (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s hx hy hz hw hx0 hy0 hz0 hw0
  have hc42 := pivot24C42_analytic (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s hx hy hz hw hx0 hy0 hz0 hw0
  have hc84 := pivot24C84_analytic (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s hx hy hz hw hx0 hy0 hz0 hw0
  have hc192 := pivot24C192_analytic (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t)
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s hx hy hz hw hx0 hy0 hz0 hw0
  have hc0 : pivot24C24 (primeParameter 2 m s) (primeParameter 3 m s)
      (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3)≠0 := by
    rw [pivot24_coefficient _ _ _ _ _ _ hx0 hP]
    norm_num
  exact four_row_order_lower hc24 hc42 hc84 hc192 hc0
    (hG 42 s).meromorphicAt (hG 84 s).meromorphicAt (hG 192 s).meromorphicAt
    hβ h42 h84 h192 hrow

#print axioms negative_coordinate24_order_lower
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalNegativeFourOrders -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

/-- All four closed-system coordinates now have bounded pole
orders at every actual chi3 candidate; no Laurent-vector premise is used. -/
theorem original_negative_four_orders {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hproduct : ε*I^(2*m)*badFive f*badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re)
    (hden : QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0) :
    (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 24) s ∧
    (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 42) s ∧
    (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 84) s ∧
    (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 192) s := by
  have h5 := badFive_sign hf.toEulerData
  have h7 := badSeven_sign hf.toEulerData
  have hu5 : -badFive f=1 ∨ -badFive f= -1 := by rcases h5 with h|h <;> simp [h]
  have hu7 : -badSeven f=1 ∨ -badSeven f= -1 := by rcases h7 with h|h <;> simp [h]
  have h5sq : (badFive f)^2=1 := by rcases h5 with h|h <;> rw [h] <;> norm_num
  have h7sq : (badSeven f)^2=1 := by rcases h7 with h|h <;> rw [h] <;> norm_num
  have hphase : ε*I^(2*m)= -(-badFive f)*(-badSeven f) := by
    linear_combination (badFive f*badSeven f)*hproduct-
      (ε*I^(2*m)*(badSeven f)^2)*h5sq-(ε*I^(2*m))*h7sq
  have hP := chi3_candidate_polynomial m f s hden
  obtain ⟨h42,h84,h192⟩ := original_negative_three_orders hm hf ε hε hlaw hproduct
    BG G hG hGF s hshift hs hden
  have h42two : (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 42) s := by
    apply le_trans ?_ h42
    change ((-2:ℤ):WithTop ℤ)≤((-1:ℤ):WithTop ℤ)
    exact WithTop.coe_le_coe.mpr (by omega)
  refine ⟨negative_coordinate24_order_lower hm hf ε hε hlaw
    (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
    BG G hG hGF s hshift hP (-2) ?_ h42two h84 h192,h42,h84,h192⟩
  change ((-2:ℤ):WithTop ℤ)≤((0:ℤ):WithTop ℤ)
  exact WithTop.coe_le_coe.mpr (by omega)

/-- A grid constructed solely from the original Euler/Fricke input has
these four-coordinate order bounds in the negative-product sign class. -/
theorem original_negative_four_orders_grid {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      ∃ BG : ℝ, ∃ G : ℂ → Fin 210 → ℂ,
        (∀ i z, MeromorphicNFAt (fun s => G s i) z) ∧
        (∀ z, BG<z.re → G z=gridVector (2*m) f z) ∧
        (∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          ∀ n : ℕ, 0<n → ∀ j, AnalyticAt ℂ (fun z => G z j) (s+(n:ℂ))) ∧
        (ε*I^(2*m)*badFive f*badSeven f= -1 → ∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 24) s ∧
    (-1:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 42) s ∧
          (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 84) s ∧
          (-2:WithTop ℤ)≤meromorphicOrderAt (fun z => G z 192) s) := by
  obtain ⟨ε,hε,hlaw,BG,G,hG,hGF,htail⟩ := original_chi3_positive_shift_tail hm hf
  refine ⟨ε,hε,hlaw,BG,G,hG,hGF,htail,?_⟩
  intro hproduct s hs hden
  exact original_negative_four_orders hm hf ε hε hlaw hproduct BG G hG hGF s
    (fun n hn j => (htail s hs hden n hn j).meromorphicOrderAt_nonneg) hs hden

#print axioms original_negative_four_orders
#print axioms original_negative_four_orders_grid
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveClosedResidueRowBundleV4 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
@[expose] public noncomputable section
/-! Consolidated certificate family; original declaration bodies retained. -/
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRows
open scoped Topology

theorem closed_residue_row0 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced0 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced0 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => ((1 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*a^(2:ℕ) + (3)*(X t)^(5:ℕ)*a + (X t)^(5:ℕ)*a^(3:ℕ) + (2)*(X t)^(6:ℕ)*a^(2:ℕ))/((X t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((-4 + (4)*(Z t) + (2)*(Y t)*b + (4)*(Y t)^(2:ℕ) + (-6)*(X t)*a + (2)*(X t)*(Y t)*a*b + (4)*(X t)*(Y t)^(2:ℕ)*a + (7)*(X t)^(2:ℕ) + (-4)*(X t)^(2:ℕ)*a^(2:ℕ) + (-4)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Y t)*b + (-5)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (18)*(X t)^(3:ℕ)*a + (-5)*(X t)^(3:ℕ)*(Z t)*a + (-2)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (-8)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(4:ℕ) + (14)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t) + (-2)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(4:ℕ)*(Y t)*b + (2)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-10)*(X t)^(5:ℕ)*a + (3)*(X t)^(5:ℕ)*a^(3:ℕ) + (2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (4)*(X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (5)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (3)*(X t)^(6:ℕ) + (-14)*(X t)^(6:ℕ)*a^(2:ℕ) + (2)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(4:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (-2)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (5)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (6)*(X t)^(7:ℕ)*a + (-6)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-3)*(X t)^(7:ℕ)*(Y t)*a*b + (-4)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (3)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ) + (6)*(X t)^(8:ℕ)*a^(2:ℕ) + (-3)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)*a^(4:ℕ)*b + (3)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (-4)*(X t)^(9:ℕ)*a + (4)*(X t)^(9:ℕ)*a^(3:ℕ) + (-1)*(X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*a^(4:ℕ))/((X t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((-2 + (2)*(Z t) + (2)*(Y t)^(2:ℕ) + (-2)*(X t)*(Z t)*a + (2)*(X t)*(Y t)^(2:ℕ)*a + (5)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(W t) + (-2)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (7)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(W t)*a + (X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Y t)*a*b + (-3)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-4)*(X t)^(4:ℕ) + (X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(W t) + (-1)*(X t)^(4:ℕ)*(Z t) + (4)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-11)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (2)*(X t)^(5:ℕ)*(W t)*a + (X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Y t)*a*b + (4)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(6:ℕ) + (-8)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(W t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Y t)*b + (-3)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (8)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(8:ℕ) + (8)*(X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*a^(4:ℕ) + (-1)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*b + (X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-3)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-5)*(X t)^(9:ℕ)*a + (3)*(X t)^(9:ℕ)*a^(3:ℕ) + (2)*(X t)^(9:ℕ)*(Y t)*a*b + (X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-4)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(11:ℕ)*a^(3:ℕ))/((X t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => ((-2 + (2)*(Z t) + (2)*(X t)*(Z t)*a + (2)*(X t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Z t) + (X t)^(3:ℕ)*a + (-3)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(5:ℕ)*a + (2)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ))/((X t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => ((1 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*a^(2:ℕ) + (3)*(X t)^(5:ℕ)*a + (X t)^(5:ℕ)*a^(3:ℕ) + (2)*(X t)^(6:ℕ)*a^(2:ℕ))/((X t)^(2:ℕ)))) (fun t => ((-4 + (4)*(Z t) + (2)*(Y t)*b + (4)*(Y t)^(2:ℕ) + (-6)*(X t)*a + (2)*(X t)*(Y t)*a*b + (4)*(X t)*(Y t)^(2:ℕ)*a + (7)*(X t)^(2:ℕ) + (-4)*(X t)^(2:ℕ)*a^(2:ℕ) + (-4)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Y t)*b + (-5)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (18)*(X t)^(3:ℕ)*a + (-5)*(X t)^(3:ℕ)*(Z t)*a + (-2)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (-8)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(4:ℕ) + (14)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t) + (-2)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(4:ℕ)*(Y t)*b + (2)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-10)*(X t)^(5:ℕ)*a + (3)*(X t)^(5:ℕ)*a^(3:ℕ) + (2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (4)*(X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (5)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (3)*(X t)^(6:ℕ) + (-14)*(X t)^(6:ℕ)*a^(2:ℕ) + (2)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(4:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (-2)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (5)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (6)*(X t)^(7:ℕ)*a + (-6)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-3)*(X t)^(7:ℕ)*(Y t)*a*b + (-4)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (3)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ) + (6)*(X t)^(8:ℕ)*a^(2:ℕ) + (-3)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)*a^(4:ℕ)*b + (3)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (-4)*(X t)^(9:ℕ)*a + (4)*(X t)^(9:ℕ)*a^(3:ℕ) + (-1)*(X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*a^(4:ℕ))/((X t)^(2:ℕ)*(W t)))) (fun t => ((-2 + (2)*(Z t) + (2)*(Y t)^(2:ℕ) + (-2)*(X t)*(Z t)*a + (2)*(X t)*(Y t)^(2:ℕ)*a + (5)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(W t) + (-2)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (7)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(W t)*a + (X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Y t)*a*b + (-3)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-4)*(X t)^(4:ℕ) + (X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(W t) + (-1)*(X t)^(4:ℕ)*(Z t) + (4)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-11)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (2)*(X t)^(5:ℕ)*(W t)*a + (X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Y t)*a*b + (4)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(6:ℕ) + (-8)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(W t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Y t)*b + (-3)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (8)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(8:ℕ) + (8)*(X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*a^(4:ℕ) + (-1)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*b + (X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-3)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-5)*(X t)^(9:ℕ)*a + (3)*(X t)^(9:ℕ)*a^(3:ℕ) + (2)*(X t)^(9:ℕ)*(Y t)*a*b + (X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-4)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(11:ℕ)*a^(3:ℕ))/((X t)^(2:ℕ)*(W t)))) (fun t => ((-2 + (2)*(Z t) + (2)*(X t)*(Z t)*a + (2)*(X t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Z t) + (X t)^(3:ℕ)*a + (-3)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(5:ℕ)*a + (2)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ))/((X t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced0]
        ring))
  simpa only [reduced0,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row0

theorem closed_residue_row104 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced104 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced104 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (-5 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((-2 + (-2)*(W t) + (-4)*(Z t) + (-4)*(Y t)*b + (-6)*(Y t)^(2:ℕ) + (8)*(X t)*a + (-2)*(X t)*(Z t)*a + (4)*(X t)*(Y t)*a*b + (-2)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-4)*(X t)^(3:ℕ)*a + (2)*(X t)^(3:ℕ)*(Y t)*a*b + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (4)*(X t)^(4:ℕ) + (-2)*(X t)^(4:ℕ)*a^(2:ℕ))/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => (((-2)*(W t) + (-2)*(Z t) + (-2)*(Y t)^(2:ℕ) + (4)*(X t)*a + (2)*(X t)*(Y t)*a*b + (-2)*(X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (2)*(X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-6)*(X t)^(3:ℕ)*a + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (4)*(X t)^(4:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)*b + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(5:ℕ)*a)/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (-4 + (-2)*(Z t) + (-1)*(X t)^(2:ℕ))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (-5 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ))) (fun t => ((-2 + (-2)*(W t) + (-4)*(Z t) + (-4)*(Y t)*b + (-6)*(Y t)^(2:ℕ) + (8)*(X t)*a + (-2)*(X t)*(Z t)*a + (4)*(X t)*(Y t)*a*b + (-2)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-4)*(X t)^(3:ℕ)*a + (2)*(X t)^(3:ℕ)*(Y t)*a*b + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (4)*(X t)^(4:ℕ) + (-2)*(X t)^(4:ℕ)*a^(2:ℕ))/((W t)))) (fun t => (((-2)*(W t) + (-2)*(Z t) + (-2)*(Y t)^(2:ℕ) + (4)*(X t)*a + (2)*(X t)*(Y t)*a*b + (-2)*(X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (2)*(X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-6)*(X t)^(3:ℕ)*a + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (4)*(X t)^(4:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)*b + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(5:ℕ)*a)/((W t)))) (fun t => (-4 + (-2)*(Z t) + (-1)*(X t)^(2:ℕ))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced104]
        ring))
  simpa only [reduced104,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row104

theorem closed_residue_row13 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced13 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced13 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (((-2)*(Z t) + (-1)*(Y t)*(Z t)*b + (-1)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(3:ℕ)*(Z t)*a)/((X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => (((-5)*(Z t) + (-2)*(Z t)*(W t) + (2)*(Z t)^(2:ℕ) + (-1)*(Y t)*(Z t)*b + (-1)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)*(Z t)*a + (X t)*(Z t)^(2:ℕ)*a + (3)*(X t)*(Y t)*(Z t)*a*b + (X t)*(Y t)^(2:ℕ)*(Z t)*a + (-3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (X t)^(2:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-4)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (4)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (-5)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(4:ℕ)*(Z t) + (4)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*(Z t)*b + (3)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-3)*(X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(6:ℕ)*(Z t) + (-3)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ))/((X t)^(2:ℕ)*(Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => (((-1)*(Z t) + (-1)*(Z t)*(W t) + (2)*(X t)*(Z t)*a + (-1)*(X t)*(Z t)^(2:ℕ)*a + (X t)*(Y t)*(Z t)*a*b + (X t)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)*(W t) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*(Z t)*b + (X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*(W t)*a + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-3)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(6:ℕ)*(Z t) + (-3)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(8:ℕ)*(Z t)*a^(2:ℕ))/((X t)^(2:ℕ)*(Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (((-3)*(Z t) + (X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a)/((X t)^(2:ℕ)*(Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (((-2)*(Z t) + (-1)*(Y t)*(Z t)*b + (-1)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(3:ℕ)*(Z t)*a)/((X t)^(2:ℕ)*(Y t)^(2:ℕ)))) (fun t => (((-5)*(Z t) + (-2)*(Z t)*(W t) + (2)*(Z t)^(2:ℕ) + (-1)*(Y t)*(Z t)*b + (-1)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)*(Z t)*a + (X t)*(Z t)^(2:ℕ)*a + (3)*(X t)*(Y t)*(Z t)*a*b + (X t)*(Y t)^(2:ℕ)*(Z t)*a + (-3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (X t)^(2:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-4)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (4)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (-5)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(4:ℕ)*(Z t) + (4)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*(Z t)*b + (3)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-3)*(X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(6:ℕ)*(Z t) + (-3)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ))/((X t)^(2:ℕ)*(Y t)^(2:ℕ)*(W t)))) (fun t => (((-1)*(Z t) + (-1)*(Z t)*(W t) + (2)*(X t)*(Z t)*a + (-1)*(X t)*(Z t)^(2:ℕ)*a + (X t)*(Y t)*(Z t)*a*b + (X t)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)*(W t) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*(Z t)*b + (X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*(W t)*a + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-3)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(6:ℕ)*(Z t) + (-3)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(8:ℕ)*(Z t)*a^(2:ℕ))/((X t)^(2:ℕ)*(Y t)^(2:ℕ)*(W t)))) (fun t => (((-3)*(Z t) + (X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a)/((X t)^(2:ℕ)*(Y t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced13]
        ring))
  simpa only [reduced13,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row13

theorem closed_residue_row14 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced14 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced14 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (-2 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((-4 + (-2)*(W t) + (2)*(Z t) + (-3)*(X t)*a + (X t)*(Z t)*a + (X t)*(Y t)*a*b + (2)*(X t)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(2:ℕ) + (-3)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)*b + (-3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (5)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-4)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ) + (5)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (3)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(5:ℕ)*a + (2)*(X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (2)*(X t)^(6:ℕ) + (-3)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*a^(3:ℕ))/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((-1 + (-1)*(W t) + (X t)*a + (-1)*(X t)*(Z t)*a + (X t)*(Y t)^(2:ℕ)*a + (X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(W t) + (X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (4)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(W t)*a + (X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(6:ℕ) + (-3)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (-1)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(8:ℕ)*a^(2:ℕ))/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (-3 + (X t)*(Z t)*a + (-1)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (-2 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a)) (fun t => ((-4 + (-2)*(W t) + (2)*(Z t) + (-3)*(X t)*a + (X t)*(Z t)*a + (X t)*(Y t)*a*b + (2)*(X t)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(2:ℕ) + (-3)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)*b + (-3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (5)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-4)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ) + (5)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (3)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(5:ℕ)*a + (2)*(X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (2)*(X t)^(6:ℕ) + (-3)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*a^(3:ℕ))/((W t)))) (fun t => ((-1 + (-1)*(W t) + (X t)*a + (-1)*(X t)*(Z t)*a + (X t)*(Y t)^(2:ℕ)*a + (X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(W t) + (X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (4)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(W t)*a + (X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(6:ℕ) + (-3)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (-1)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(8:ℕ)*a^(2:ℕ))/((W t)))) (fun t => (-3 + (X t)*(Z t)*a + (-1)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a)) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced14]
        ring))
  simpa only [reduced14,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row14

theorem closed_residue_row150 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced150 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced150 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => (((-2)*(Y t)*b + (-2)*(Y t)^(2:ℕ) + (2)*(X t)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (0:ℂ)) (fun t => (((-2)*(Y t)*b + (-2)*(Y t)^(2:ℕ) + (2)*(X t)*a)/((Y t)^(2:ℕ)))) (fun t => (0:ℂ)) (fun t => (0:ℂ)) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced150]
        ring))
  simpa only [reduced150,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row150

theorem closed_residue_row159 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced159 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced159 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((-2 + (Y t)^(2:ℕ) + (-1)*(X t)*a + (-2)*(X t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((-1 + (-1)*(Y t)*b + (X t)*a + (X t)^(4:ℕ))/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (0:ℂ)) (fun t => ((-2 + (Y t)^(2:ℕ) + (-1)*(X t)*a + (-2)*(X t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a)/((Y t)^(2:ℕ)))) (fun t => ((-1 + (-1)*(Y t)*b + (X t)*a + (X t)^(4:ℕ))/((Y t)^(2:ℕ)))) (fun t => (0:ℂ)) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced159]
        ring))
  simpa only [reduced159,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row159

theorem closed_residue_row163 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced163 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced163 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => ((-3 + (X t)*a + (-1)*(X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1)*(X t)^(4:ℕ) + (-3)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(5:ℕ)*a + (X t)^(6:ℕ) + (X t)^(6:ℕ)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((2 + (-2)*(Z t) + (-3)*(Y t)*b + (-5)*(Y t)^(2:ℕ) + (5)*(X t)*(Z t)*a + (3)*(X t)*(Y t)*a*b + (X t)*(Y t)^(2:ℕ)*a + (-8)*(X t)^(2:ℕ) + (-6)*(X t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-8)*(X t)^(3:ℕ)*a + (-3)*(X t)^(3:ℕ)*a^(3:ℕ) + (X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (9)*(X t)^(4:ℕ) + (2)*(X t)^(4:ℕ)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Z t) + (-3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(4:ℕ) + (-3)*(X t)^(4:ℕ)*(Y t)*b + (-5)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (11)*(X t)^(5:ℕ)*a + (5)*(X t)^(5:ℕ)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (3)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-7)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(6:ℕ) + (5)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t) + (3)*(X t)^(6:ℕ)*(Y t)*b + (5)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)*a^(4:ℕ)*b + (2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (-7)*(X t)^(7:ℕ)*a + (-3)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(7:ℕ)*(Y t)*a*b + (2)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (3)*(X t)^(8:ℕ) + (-6)*(X t)^(8:ℕ)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*a^(4:ℕ) + (X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*b + (-2)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (5)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*a^(3:ℕ) + (-2)*(X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ) + (3)*(X t)^(10:ℕ)*a^(2:ℕ) + (-1)*(X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(11:ℕ)*a + (X t)^(11:ℕ)*a^(3:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((1 + (-1)*(W t) + (-1)*(Z t) + (-2)*(Y t)^(2:ℕ) + (2)*(X t)*(Z t)*a + (X t)*(Y t)*a*b + (X t)*(Y t)^(2:ℕ)*a + (-4)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(3:ℕ)*(W t)*a + (-3)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (8)*(X t)^(4:ℕ) + (4)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(W t) + (-1)*(X t)^(4:ℕ)*(W t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (4)*(X t)^(5:ℕ)*a + (X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(W t)*a + (2)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-4)*(X t)^(6:ℕ) + (-3)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*a^(4:ℕ) + (X t)^(6:ℕ)*(W t) + (3)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*b + (X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-6)*(X t)^(7:ℕ)*a + (-4)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(W t)*a + (X t)^(7:ℕ)*(Z t)*a + (-2)*(X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (4)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (3)*(X t)^(8:ℕ) + (-1)*(X t)^(8:ℕ)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(8:ℕ)*(Y t)*b + (-3)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (7)*(X t)^(9:ℕ)*a + (2)*(X t)^(9:ℕ)*a^(3:ℕ) + (-1)*(X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(10:ℕ) + (4)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*(Y t)*b + (X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(11:ℕ)*a + (X t)^(11:ℕ)*(Y t)*a*b + (-1)*(X t)^(11:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(12:ℕ)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => ((-1 + (-2)*(Z t) + (Y t)*b + (-2)*(X t)*a + (X t)*(Z t)*a + (-2)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a + (X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(5:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(6:ℕ) + (X t)^(6:ℕ)*(Z t) + (X t)^(7:ℕ)*a + (X t)^(7:ℕ)*(Z t)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => ((-3 + (X t)*a + (-1)*(X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1)*(X t)^(4:ℕ) + (-3)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(5:ℕ)*a + (X t)^(6:ℕ) + (X t)^(6:ℕ)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*a)/((Y t)^(2:ℕ)))) (fun t => ((2 + (-2)*(Z t) + (-3)*(Y t)*b + (-5)*(Y t)^(2:ℕ) + (5)*(X t)*(Z t)*a + (3)*(X t)*(Y t)*a*b + (X t)*(Y t)^(2:ℕ)*a + (-8)*(X t)^(2:ℕ) + (-6)*(X t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-8)*(X t)^(3:ℕ)*a + (-3)*(X t)^(3:ℕ)*a^(3:ℕ) + (X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (9)*(X t)^(4:ℕ) + (2)*(X t)^(4:ℕ)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Z t) + (-3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(4:ℕ) + (-3)*(X t)^(4:ℕ)*(Y t)*b + (-5)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (11)*(X t)^(5:ℕ)*a + (5)*(X t)^(5:ℕ)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (3)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-7)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(6:ℕ) + (5)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t) + (3)*(X t)^(6:ℕ)*(Y t)*b + (5)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)*a^(4:ℕ)*b + (2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (-7)*(X t)^(7:ℕ)*a + (-3)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(7:ℕ)*(Y t)*a*b + (2)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (3)*(X t)^(8:ℕ) + (-6)*(X t)^(8:ℕ)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*a^(4:ℕ) + (X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*b + (-2)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (5)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*a^(3:ℕ) + (-2)*(X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ) + (3)*(X t)^(10:ℕ)*a^(2:ℕ) + (-1)*(X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(11:ℕ)*a + (X t)^(11:ℕ)*a^(3:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => ((1 + (-1)*(W t) + (-1)*(Z t) + (-2)*(Y t)^(2:ℕ) + (2)*(X t)*(Z t)*a + (X t)*(Y t)*a*b + (X t)*(Y t)^(2:ℕ)*a + (-4)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(3:ℕ)*(W t)*a + (-3)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (8)*(X t)^(4:ℕ) + (4)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(W t) + (-1)*(X t)^(4:ℕ)*(W t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (4)*(X t)^(5:ℕ)*a + (X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(W t)*a + (2)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-4)*(X t)^(6:ℕ) + (-3)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*a^(4:ℕ) + (X t)^(6:ℕ)*(W t) + (3)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*b + (X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-6)*(X t)^(7:ℕ)*a + (-4)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(W t)*a + (X t)^(7:ℕ)*(Z t)*a + (-2)*(X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (4)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (3)*(X t)^(8:ℕ) + (-1)*(X t)^(8:ℕ)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(8:ℕ)*(Y t)*b + (-3)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (7)*(X t)^(9:ℕ)*a + (2)*(X t)^(9:ℕ)*a^(3:ℕ) + (-1)*(X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(10:ℕ) + (4)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*(Y t)*b + (X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(11:ℕ)*a + (X t)^(11:ℕ)*(Y t)*a*b + (-1)*(X t)^(11:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(12:ℕ)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => ((-1 + (-2)*(Z t) + (Y t)*b + (-2)*(X t)*a + (X t)*(Z t)*a + (-2)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a + (X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(5:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(6:ℕ) + (X t)^(6:ℕ)*(Z t) + (X t)^(7:ℕ)*a + (X t)^(7:ℕ)*(Z t)*a)/((Y t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced163]
        ring))
  simpa only [reduced163,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row163

theorem closed_residue_row164 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced164 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced164 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => ((1 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-3)*(X t)*a + (-4)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a + (2)*(X t)^(4:ℕ))/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((-7 + (6)*(Z t) + (2)*(Y t)*b + (4)*(Y t)^(2:ℕ) + (-8)*(X t)*a + (-1)*(X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (3)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Z t) + (-3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-5)*(X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-8)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (13)*(X t)^(3:ℕ)*a + (-2)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (3)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)*a^(3:ℕ)*b + (-6)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-3)*(X t)^(4:ℕ) + (3)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (4)*(X t)^(4:ℕ)*(Y t)*b + (5)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-8)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (5)*(X t)^(6:ℕ) + (-4)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (4)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*a^(3:ℕ) + (-1)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(8:ℕ) + (X t)^(8:ℕ)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((-2 + (Z t) + (2)*(Y t)^(2:ℕ) + (X t)*a + (-1)*(X t)*(W t)*a + (-3)*(X t)*(Z t)*a + (5)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(W t) + (-1)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (5)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(W t)*a + (3)*(X t)^(3:ℕ)*(Z t)*a + (3)*(X t)^(3:ℕ)*(Y t)*a*b + (-4)*(X t)^(4:ℕ) + (-3)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(W t) + (2)*(X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)*b + (3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-7)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Y t)*a*b + (4)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (5)*(X t)^(6:ℕ) + (-1)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t) + (-3)*(X t)^(6:ℕ)*(Y t)*b + (-1)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (7)*(X t)^(7:ℕ)*a + (-2)*(X t)^(8:ℕ) + (X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(9:ℕ)*a)/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => ((-2 + (2)*(Z t) + (-1)*(Y t)*b + (-1)*(X t)*a + (-2)*(X t)^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*(Z t))/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => ((1 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-3)*(X t)*a + (-4)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a + (2)*(X t)^(4:ℕ))/((Y t)^(2:ℕ)))) (fun t => ((-7 + (6)*(Z t) + (2)*(Y t)*b + (4)*(Y t)^(2:ℕ) + (-8)*(X t)*a + (-1)*(X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (3)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Z t) + (-3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-5)*(X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-8)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (13)*(X t)^(3:ℕ)*a + (-2)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (3)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)*a^(3:ℕ)*b + (-6)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-3)*(X t)^(4:ℕ) + (3)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (4)*(X t)^(4:ℕ)*(Y t)*b + (5)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-8)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (5)*(X t)^(6:ℕ) + (-4)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (4)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*a^(3:ℕ) + (-1)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(8:ℕ) + (X t)^(8:ℕ)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => ((-2 + (Z t) + (2)*(Y t)^(2:ℕ) + (X t)*a + (-1)*(X t)*(W t)*a + (-3)*(X t)*(Z t)*a + (5)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(W t) + (-1)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (5)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(W t)*a + (3)*(X t)^(3:ℕ)*(Z t)*a + (3)*(X t)^(3:ℕ)*(Y t)*a*b + (-4)*(X t)^(4:ℕ) + (-3)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(W t) + (2)*(X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)*b + (3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-7)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Y t)*a*b + (4)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (5)*(X t)^(6:ℕ) + (-1)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t) + (-3)*(X t)^(6:ℕ)*(Y t)*b + (-1)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (7)*(X t)^(7:ℕ)*a + (-2)*(X t)^(8:ℕ) + (X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(9:ℕ)*a)/((Y t)^(2:ℕ)*(W t)))) (fun t => ((-2 + (2)*(Z t) + (-1)*(Y t)*b + (-1)*(X t)*a + (-2)*(X t)^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*(Z t))/((Y t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced164]
        ring))
  simpa only [reduced164,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row164

theorem closed_residue_row16 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced16 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced16 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => ((3 + (-3)*(X t)*a + (X t)^(2:ℕ) + (X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (3)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*a^(3:ℕ) + (X t)^(4:ℕ) + (3)*(X t)^(4:ℕ)*a^(2:ℕ) + (2)*(X t)^(5:ℕ)*a)/((X t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((-3 + (2)*(W t) + (2)*(Z t) + (Y t)*b + (6)*(Y t)^(2:ℕ) + (X t)*(W t)*a + (-8)*(X t)*(Z t)*a + (-3)*(X t)*(Y t)*a*b + (-3)*(X t)*(Y t)^(2:ℕ)*a + (8)*(X t)^(2:ℕ) + (8)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t) + (-3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(3:ℕ)*a + (3)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Z t)*a + (2)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(3:ℕ)*(Y t)*a*b + (5)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-8)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t) + (3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*a^(4:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (-3)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (6)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(5:ℕ)*a + (-5)*(X t)^(5:ℕ)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Y t)*a*b + (-4)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (7)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(6:ℕ) + (X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (-6)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)*a^(4:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (5)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (-1)*(X t)^(7:ℕ)*a + (4)*(X t)^(7:ℕ)*a^(3:ℕ) + (-2)*(X t)^(7:ℕ)*(Y t)*a*b + (-2)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ) + (X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*a^(4:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(9:ℕ)*a + (X t)^(9:ℕ)*a^(3:ℕ))/((X t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((-2 + (W t) + (2)*(Z t) + (-1)*(Y t)*b + (2)*(Y t)^(2:ℕ) + (-3)*(X t)*(Z t)*a + (-2)*(X t)*(Y t)^(2:ℕ)*a + (5)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t) + (2)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-6)*(X t)^(3:ℕ)*a + (2)*(X t)^(3:ℕ)*(W t)*a + (3)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-4)*(X t)^(4:ℕ) + (-5)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(W t) + (X t)^(4:ℕ)*(W t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (-2)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(5:ℕ)*a + (X t)^(5:ℕ)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(5:ℕ)*(Y t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(6:ℕ) + (6)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*a^(4:ℕ) + (-2)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-3)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(7:ℕ)*a + (4)*(X t)^(7:ℕ)*a^(3:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)*a + (2)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (-4)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ) + (-1)*(X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*b + (2)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*a^(3:ℕ) + (X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(10:ℕ)*a^(2:ℕ))/((X t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => ((1 + (-1)*(W t) + (2)*(Z t) + (X t)*a + (-2)*(X t)*(Z t)*a + (3)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(5:ℕ)*a + (X t)^(5:ℕ)*(Z t)*a)/((X t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => ((3 + (-3)*(X t)*a + (X t)^(2:ℕ) + (X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (3)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*a^(3:ℕ) + (X t)^(4:ℕ) + (3)*(X t)^(4:ℕ)*a^(2:ℕ) + (2)*(X t)^(5:ℕ)*a)/((X t)^(2:ℕ)))) (fun t => ((-3 + (2)*(W t) + (2)*(Z t) + (Y t)*b + (6)*(Y t)^(2:ℕ) + (X t)*(W t)*a + (-8)*(X t)*(Z t)*a + (-3)*(X t)*(Y t)*a*b + (-3)*(X t)*(Y t)^(2:ℕ)*a + (8)*(X t)^(2:ℕ) + (8)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t) + (-3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(3:ℕ)*a + (3)*(X t)^(3:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Z t)*a + (2)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(3:ℕ)*(Y t)*a*b + (5)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-8)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t) + (3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*a^(4:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (-3)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (6)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(5:ℕ)*a + (-5)*(X t)^(5:ℕ)*a^(3:ℕ) + (X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Y t)*a*b + (-4)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (7)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(6:ℕ) + (X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*b + (-6)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)*a^(4:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (5)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (-1)*(X t)^(7:ℕ)*a + (4)*(X t)^(7:ℕ)*a^(3:ℕ) + (-2)*(X t)^(7:ℕ)*(Y t)*a*b + (-2)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ) + (X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*a^(4:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(9:ℕ)*a + (X t)^(9:ℕ)*a^(3:ℕ))/((X t)^(2:ℕ)*(W t)))) (fun t => ((-2 + (W t) + (2)*(Z t) + (-1)*(Y t)*b + (2)*(Y t)^(2:ℕ) + (-3)*(X t)*(Z t)*a + (-2)*(X t)*(Y t)^(2:ℕ)*a + (5)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t) + (2)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-6)*(X t)^(3:ℕ)*a + (2)*(X t)^(3:ℕ)*(W t)*a + (3)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-4)*(X t)^(4:ℕ) + (-5)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(W t) + (X t)^(4:ℕ)*(W t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (-2)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(5:ℕ)*a + (X t)^(5:ℕ)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(5:ℕ)*(Y t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(6:ℕ) + (6)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*a^(4:ℕ) + (-2)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-3)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(7:ℕ)*a + (4)*(X t)^(7:ℕ)*a^(3:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)*a + (2)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (-4)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ) + (-1)*(X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*b + (2)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*a^(3:ℕ) + (X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(10:ℕ)*a^(2:ℕ))/((X t)^(2:ℕ)*(W t)))) (fun t => ((1 + (-1)*(W t) + (2)*(Z t) + (X t)*a + (-2)*(X t)*(Z t)*a + (3)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Z t)*a + (X t)^(4:ℕ) + (X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(5:ℕ)*a + (X t)^(5:ℕ)*(Z t)*a)/((X t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced16]
        ring))
  simpa only [reduced16,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row16

theorem closed_residue_row19 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced19 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced19 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (((-3)*(Z t) + (2)*(X t)*(Z t)*a + (3)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (2)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(5:ℕ)*(Z t)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => (((8)*(Z t) + (Z t)*(W t) + (-7)*(Z t)^(2:ℕ) + (-2)*(Y t)*(Z t)*b + (-8)*(Y t)^(2:ℕ)*(Z t) + (11)*(X t)*(Z t)*a + (-3)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (-8)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (5)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (8)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-18)*(X t)^(3:ℕ)*(Z t)*a + (4)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(3:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (7)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (3)*(X t)^(4:ℕ)*(Z t) + (-8)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)^(2:ℕ) + (-4)*(X t)^(4:ℕ)*(Y t)*(Z t)*b + (-4)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (11)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-5)*(X t)^(6:ℕ)*(Z t) + (9)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*(Z t)*b + (2)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-5)*(X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (X t)^(7:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(8:ℕ)*(Z t) + (-3)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Z t)*a^(3:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => (((Z t) + (-2)*(Z t)^(2:ℕ) + (Y t)*(Z t)*b + (-3)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)*(Z t)*a + (3)*(X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (-8)*(X t)^(2:ℕ)*(Z t) + (2)*(X t)^(2:ℕ)*(Z t)*(W t) + (2)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (4)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-6)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*(W t)*a + (-3)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (-2)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (6)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*(W t) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (11)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (2)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (-4)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-5)*(X t)^(6:ℕ)*(Z t) + (4)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(6:ℕ)*(Y t)*(Z t)*b + (2)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-8)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(8:ℕ)*(Z t) + (-4)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Y t)*(Z t)*a*b + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(10:ℕ)*(Z t)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (((Z t) + (Z t)*(W t) + (-3)*(Z t)^(2:ℕ) + (-1)*(X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (X t)^(3:ℕ)*(Z t)*a + (2)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a)/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (((-3)*(Z t) + (2)*(X t)*(Z t)*a + (3)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (2)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(5:ℕ)*(Z t)*a)/((Y t)^(2:ℕ)))) (fun t => (((8)*(Z t) + (Z t)*(W t) + (-7)*(Z t)^(2:ℕ) + (-2)*(Y t)*(Z t)*b + (-8)*(Y t)^(2:ℕ)*(Z t) + (11)*(X t)*(Z t)*a + (-3)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (-8)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (5)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (8)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-18)*(X t)^(3:ℕ)*(Z t)*a + (4)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(3:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (7)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (3)*(X t)^(4:ℕ)*(Z t) + (-8)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)^(2:ℕ) + (-4)*(X t)^(4:ℕ)*(Y t)*(Z t)*b + (-4)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (11)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-5)*(X t)^(6:ℕ)*(Z t) + (9)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*(Z t)*b + (2)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-5)*(X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (X t)^(7:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(8:ℕ)*(Z t) + (-3)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Z t)*a^(3:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => (((Z t) + (-2)*(Z t)^(2:ℕ) + (Y t)*(Z t)*b + (-3)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)*(Z t)*a + (3)*(X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (-8)*(X t)^(2:ℕ)*(Z t) + (2)*(X t)^(2:ℕ)*(Z t)*(W t) + (2)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (4)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-6)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*(W t)*a + (-3)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (-2)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (6)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*(W t) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (11)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (2)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (-4)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-5)*(X t)^(6:ℕ)*(Z t) + (4)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(6:ℕ)*(Y t)*(Z t)*b + (2)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-8)*(X t)^(7:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(8:ℕ)*(Z t) + (-4)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Y t)*(Z t)*a*b + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(10:ℕ)*(Z t)*a^(2:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => (((Z t) + (Z t)*(W t) + (-3)*(Z t)^(2:ℕ) + (-1)*(X t)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (X t)^(3:ℕ)*(Z t)*a + (2)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a)/((Y t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced19]
        ring))
  simpa only [reduced19,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row19

theorem closed_residue_row21 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced21 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced21 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (-3 + (2)*(X t)*a + (3)*(X t)^(2:ℕ) + (X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(3:ℕ)*a + (-1)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-2)*(X t)^(5:ℕ)*a)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((5 + (W t) + (-7)*(Z t) + (-3)*(Y t)*b + (-6)*(Y t)^(2:ℕ) + (9)*(X t)*a + (-1)*(X t)*(Y t)*a*b + (-2)*(X t)*(Y t)^(2:ℕ)*a + (-8)*(X t)^(2:ℕ) + (3)*(X t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (5)*(X t)^(2:ℕ)*(Y t)*b + (8)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-17)*(X t)^(3:ℕ)*a + (4)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (7)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(4:ℕ) + (-8)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (-4)*(X t)^(4:ℕ)*(Y t)*b + (-4)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (11)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Y t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-5)*(X t)^(6:ℕ) + (9)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*b + (2)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-5)*(X t)^(7:ℕ)*a + (X t)^(7:ℕ)*a^(3:ℕ) + (2)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (2)*(X t)^(8:ℕ) + (-3)*(X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*a^(3:ℕ))/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => (((-2)*(Z t) + (-3)*(Y t)^(2:ℕ) + (3)*(X t)*(Z t)*a + (-1)*(X t)*(Y t)^(2:ℕ)*a + (-7)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(W t) + (2)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-6)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(W t)*a + (-3)*(X t)^(3:ℕ)*(Z t)*a + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (5)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*(W t) + (-1)*(X t)^(4:ℕ)*(Z t) + (-2)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)*b + (-1)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (11)*(X t)^(5:ℕ)*a + (X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Y t)*a*b + (-4)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-5)*(X t)^(6:ℕ) + (4)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(6:ℕ)*(Y t)*b + (2)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-8)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(8:ℕ) + (-4)*(X t)^(8:ℕ)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*b + (-1)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*(Y t)*a*b + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(10:ℕ)*a^(2:ℕ))/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => ((-3)*(Z t) + (-1)*(X t)*(Z t)*a + (-1)*(X t)^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t) + (X t)^(3:ℕ)*a + (2)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (-3 + (2)*(X t)*a + (3)*(X t)^(2:ℕ) + (X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(3:ℕ)*a + (-1)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-2)*(X t)^(5:ℕ)*a)) (fun t => ((5 + (W t) + (-7)*(Z t) + (-3)*(Y t)*b + (-6)*(Y t)^(2:ℕ) + (9)*(X t)*a + (-1)*(X t)*(Y t)*a*b + (-2)*(X t)*(Y t)^(2:ℕ)*a + (-8)*(X t)^(2:ℕ) + (3)*(X t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t) + (3)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (5)*(X t)^(2:ℕ)*(Y t)*b + (8)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-17)*(X t)^(3:ℕ)*a + (4)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (7)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(4:ℕ) + (-8)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t) + (-4)*(X t)^(4:ℕ)*(Y t)*b + (-4)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (11)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Y t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-1)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-5)*(X t)^(6:ℕ) + (9)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*b + (2)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-5)*(X t)^(7:ℕ)*a + (X t)^(7:ℕ)*a^(3:ℕ) + (2)*(X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (2)*(X t)^(8:ℕ) + (-3)*(X t)^(8:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*a^(3:ℕ))/((W t)))) (fun t => (((-2)*(Z t) + (-3)*(Y t)^(2:ℕ) + (3)*(X t)*(Z t)*a + (-1)*(X t)*(Y t)^(2:ℕ)*a + (-7)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(W t) + (2)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-6)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(W t)*a + (-3)*(X t)^(3:ℕ)*(Z t)*a + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (5)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*(W t) + (-1)*(X t)^(4:ℕ)*(Z t) + (-2)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)*b + (-1)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (11)*(X t)^(5:ℕ)*a + (X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Y t)*a*b + (-4)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-5)*(X t)^(6:ℕ) + (4)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(6:ℕ)*(Y t)*b + (2)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-8)*(X t)^(7:ℕ)*a + (-1)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Y t)*a*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(8:ℕ) + (-4)*(X t)^(8:ℕ)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*b + (-1)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*(Y t)*a*b + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(10:ℕ)*a^(2:ℕ))/((W t)))) (fun t => ((-3)*(Z t) + (-1)*(X t)*(Z t)*a + (-1)*(X t)^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Z t) + (X t)^(3:ℕ)*a + (2)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a)) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced21]
        ring))
  simpa only [reduced21,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row21

theorem closed_residue_row26 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced26 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced26 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (((-3)*(Z t) + (2)*(X t)*(Z t)*a + (X t)*(Y t)*(Z t)*a*b + (X t)*(Y t)^(2:ℕ)*(Z t)*a + (3)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*(Z t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(4:ℕ)*(Z t) + (3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ))/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => (((7)*(Z t) + (-2)*(Z t)*(W t) + (-6)*(Z t)^(2:ℕ) + (-1)*(Y t)*(Z t)*b + (-6)*(Y t)^(2:ℕ)*(Z t) + (12)*(X t)*(Z t)*a + (-1)*(X t)*(Z t)*(W t)*a + (-4)*(X t)*(Z t)^(2:ℕ)*a + (X t)*(Y t)*(Z t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(2:ℕ)*(Z t) + (4)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (4)*(X t)^(3:ℕ)*(Z t)*a + (3)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-5)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (-2)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(4:ℕ) + (X t)^(4:ℕ)*(Y t)*(Z t)*b + (-2)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-4)*(X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (3)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (9)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t) + (-7)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(4:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*(Z t)*b + (-5)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(4:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (8)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(4:ℕ) + (2)*(X t)^(7:ℕ)*(Z t)*a + (-2)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-3)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (-5)*(X t)^(7:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (3)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (4)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ)*(Z t) + (4)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Z t)*a^(4:ℕ) + (-3)*(X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)*(Z t)*a^(4:ℕ)*b + (3)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(4:ℕ) + (-4)*(X t)^(9:ℕ)*(Z t)*a + (4)*(X t)^(9:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(9:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(10:ℕ)*(Z t)*a^(4:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => (((2)*(Z t) + (-1)*(Z t)*(W t) + (-2)*(Z t)^(2:ℕ) + (Y t)*(Z t)*b + (-2)*(Y t)^(2:ℕ)*(Z t) + (2)*(X t)*(Z t)*a + (X t)*(Z t)^(2:ℕ)*a + (-3)*(X t)^(2:ℕ)*(Z t) + (2)*(X t)^(2:ℕ)*(Z t)*(W t) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*(W t)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(3:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*(W t) + (X t)^(4:ℕ)*(Z t)*(W t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (3)*(X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-3)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(5:ℕ)*(Z t)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(4:ℕ) + (X t)^(6:ℕ)*(Z t)*(W t)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*(Z t)*a + (3)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-4)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ)*(Z t) + (4)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Z t)*a^(4:ℕ) + (-1)*(X t)^(8:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*(Z t)*b + (2)*(X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-4)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-5)*(X t)^(9:ℕ)*(Z t)*a + (2)*(X t)^(9:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(9:ℕ)*(Y t)*(Z t)*a*b + (X t)^(9:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-2)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-4)*(X t)^(10:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(10:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(11:ℕ)*(Z t)*a^(3:ℕ))/((Y t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (((-1)*(Z t) + (Z t)*(W t) + (-2)*(Z t)^(2:ℕ) + (X t)*(Z t)*a + (3)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)^(2:ℕ) + (2)*(X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ))/((Y t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (((-3)*(Z t) + (2)*(X t)*(Z t)*a + (X t)*(Y t)*(Z t)*a*b + (X t)*(Y t)^(2:ℕ)*(Z t)*a + (3)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*(Z t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (X t)^(4:ℕ)*(Z t) + (3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ))/((Y t)^(2:ℕ)))) (fun t => (((7)*(Z t) + (-2)*(Z t)*(W t) + (-6)*(Z t)^(2:ℕ) + (-1)*(Y t)*(Z t)*b + (-6)*(Y t)^(2:ℕ)*(Z t) + (12)*(X t)*(Z t)*a + (-1)*(X t)*(Z t)*(W t)*a + (-4)*(X t)*(Z t)^(2:ℕ)*a + (X t)*(Y t)*(Z t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(2:ℕ)*(Z t) + (4)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-3)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (4)*(X t)^(3:ℕ)*(Z t)*a + (3)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-5)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (-2)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(4:ℕ) + (X t)^(4:ℕ)*(Y t)*(Z t)*b + (-2)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (4)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t) + (3)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-4)*(X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (3)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-3)*(X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (9)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t) + (-7)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(4:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*(Z t)*b + (-5)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(4:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (8)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(4:ℕ) + (2)*(X t)^(7:ℕ)*(Z t)*a + (-2)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-3)*(X t)^(7:ℕ)*(Y t)*(Z t)*a*b + (-5)*(X t)^(7:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (3)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (4)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ)*(Z t) + (4)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Z t)*a^(4:ℕ) + (-3)*(X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)*(Z t)*a^(4:ℕ)*b + (3)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(4:ℕ) + (-4)*(X t)^(9:ℕ)*(Z t)*a + (4)*(X t)^(9:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(9:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(10:ℕ)*(Z t)*a^(4:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => (((2)*(Z t) + (-1)*(Z t)*(W t) + (-2)*(Z t)^(2:ℕ) + (Y t)*(Z t)*b + (-2)*(Y t)^(2:ℕ)*(Z t) + (2)*(X t)*(Z t)*a + (X t)*(Z t)^(2:ℕ)*a + (-3)*(X t)^(2:ℕ)*(Z t) + (2)*(X t)^(2:ℕ)*(Z t)*(W t) + (X t)^(2:ℕ)*(Z t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*(Z t)*b + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*(W t)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(3:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-3)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*(W t) + (X t)^(4:ℕ)*(Z t)*(W t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)^(2:ℕ) + (3)*(X t)^(4:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*(Z t)*b + (-1)*(X t)^(4:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-3)*(X t)^(5:ℕ)*(Z t)*a + (-1)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(5:ℕ)*(Z t)*(W t)*a + (-1)*(X t)^(5:ℕ)*(Y t)*(Z t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)*a^(4:ℕ) + (X t)^(6:ℕ)*(Z t)*(W t)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(6:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-2)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*(Z t)*a + (3)*(X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(7:ℕ)*(Z t)^(2:ℕ)*a + (-1)*(X t)^(7:ℕ)*(Z t)^(2:ℕ)*a^(3:ℕ) + (-4)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-2)*(X t)^(8:ℕ)*(Z t) + (4)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(8:ℕ)*(Z t)*a^(4:ℕ) + (-1)*(X t)^(8:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (X t)^(8:ℕ)*(Y t)*(Z t)*b + (2)*(X t)^(8:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t) + (-4)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-5)*(X t)^(9:ℕ)*(Z t)*a + (2)*(X t)^(9:ℕ)*(Z t)*a^(3:ℕ) + (2)*(X t)^(9:ℕ)*(Y t)*(Z t)*a*b + (X t)^(9:ℕ)*(Y t)*(Z t)*a^(3:ℕ)*b + (-2)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(3:ℕ) + (-4)*(X t)^(10:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(10:ℕ)*(Y t)*(Z t)*a^(2:ℕ)*b + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(11:ℕ)*(Z t)*a^(3:ℕ))/((Y t)^(2:ℕ)*(W t)))) (fun t => (((-1)*(Z t) + (Z t)*(W t) + (-2)*(Z t)^(2:ℕ) + (X t)*(Z t)*a + (3)*(X t)^(2:ℕ)*(Z t) + (-1)*(X t)^(2:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)^(2:ℕ) + (2)*(X t)^(5:ℕ)*(Z t)*a + (2)*(X t)^(5:ℕ)*(Z t)^(2:ℕ)*a + (X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Z t)^(2:ℕ)*a^(2:ℕ))/((Y t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced26]
        ring))
  simpa only [reduced26,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row26

theorem closed_residue_row3 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced3 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced3 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (-3 + (X t)^(2:ℕ) + (X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(3:ℕ)*a)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((3 + (-6)*(Z t) + (-3)*(Y t)*b + (-5)*(Y t)^(2:ℕ) + (9)*(X t)*a + (-3)*(X t)*(Z t)*a + (X t)*(Y t)*a*b + (-3)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ) + (3)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-8)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(3:ℕ)*(Y t)*a*b + (3)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(4:ℕ) + (-6)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (-3)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(5:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Y t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(6:ℕ) + (3)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(7:ℕ)*a + (X t)^(7:ℕ)*a^(3:ℕ))/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((1 + (-1)*(W t) + (-2)*(Z t) + (-2)*(Y t)^(2:ℕ) + (2)*(X t)*a + (X t)*(Z t)*a + (X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(W t) + (X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-7)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(W t)*a + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)*b + (-1)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (5)*(X t)^(5:ℕ)*a + (X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(6:ℕ) + (3)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*b + (X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(7:ℕ)*a + (X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(8:ℕ)*a^(2:ℕ))/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (-1 + (-2)*(Z t) + (-1)*(X t)*(Z t)*a + (X t)^(2:ℕ)*(Z t) + (X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Z t)*a)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (-3 + (X t)^(2:ℕ) + (X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(3:ℕ)*a)) (fun t => ((3 + (-6)*(Z t) + (-3)*(Y t)*b + (-5)*(Y t)^(2:ℕ) + (9)*(X t)*a + (-3)*(X t)*(Z t)*a + (X t)*(Y t)*a*b + (-3)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ) + (3)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (3)*(X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-8)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Z t)*a + (X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(3:ℕ)*(Y t)*a*b + (3)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(4:ℕ) + (-6)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)*b + (-3)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (3)*(X t)^(5:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Y t)*a*b + (-1)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(6:ℕ) + (3)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(7:ℕ)*a + (X t)^(7:ℕ)*a^(3:ℕ))/((W t)))) (fun t => ((1 + (-1)*(W t) + (-2)*(Z t) + (-2)*(Y t)^(2:ℕ) + (2)*(X t)*a + (X t)*(Z t)*a + (X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(W t) + (X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-7)*(X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(W t)*a + (-2)*(X t)^(3:ℕ)*(Y t)*a*b + (2)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (3)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Y t)*b + (-1)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (5)*(X t)^(5:ℕ)*a + (X t)^(5:ℕ)*a^(3:ℕ) + (-1)*(X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(6:ℕ) + (3)*(X t)^(6:ℕ)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*b + (X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(7:ℕ)*a + (X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(8:ℕ)*a^(2:ℕ))/((W t)))) (fun t => (-1 + (-2)*(Z t) + (-1)*(X t)*(Z t)*a + (X t)^(2:ℕ)*(Z t) + (X t)^(3:ℕ)*a + (X t)^(3:ℕ)*(Z t)*a)) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced3]
        ring))
  simpa only [reduced3,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row3

theorem closed_residue_row45 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced45 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced45 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => (1 + (-1)*(Y t)*b + (-2)*(Y t)^(2:ℕ) + (3)*(X t)*a + (-2)*(X t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((-1)*(Y t)^(2:ℕ) + (X t)*a + (-2)*(X t)^(2:ℕ) + (X t)^(4:ℕ))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => ((W t) + (-1)*(Z t)*(W t))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (0:ℂ)) (fun t => (1 + (-1)*(Y t)*b + (-2)*(Y t)^(2:ℕ) + (3)*(X t)*a + (-2)*(X t)^(2:ℕ) + (-1)*(X t)^(3:ℕ)*a)) (fun t => ((-1)*(Y t)^(2:ℕ) + (X t)*a + (-2)*(X t)^(2:ℕ) + (X t)^(4:ℕ))) (fun t => ((W t) + (-1)*(Z t)*(W t))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced45]
        ring))
  simpa only [reduced45,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row45

theorem closed_residue_row53 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced53 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced53 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => (0:ℂ)) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((-4 + (-2)*(Y t)*b + (Y t)^(2:ℕ) + (X t)*(Y t)*a*b + (X t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ))/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((-1 + (-1)*(Y t)*b + (2)*(X t)*a + (X t)*(Y t)*a*b + (2)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)*b + (-3)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (X t)^(5:ℕ)*a)/((W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => (-1 + (-1)*(W t))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => (0:ℂ)) (fun t => ((-4 + (-2)*(Y t)*b + (Y t)^(2:ℕ) + (X t)*(Y t)*a*b + (X t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (2)*(X t)^(4:ℕ) + (-1)*(X t)^(4:ℕ)*a^(2:ℕ))/((W t)))) (fun t => ((-1 + (-1)*(Y t)*b + (2)*(X t)*a + (X t)*(Y t)*a*b + (2)*(X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)*b + (-3)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (X t)^(5:ℕ)*a)/((W t)))) (fun t => (-1 + (-1)*(W t))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced53]
        ring))
  simpa only [reduced53,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row53

theorem closed_residue_row9 (X Y Z W U : ℂ → ℂ) (a b s : ℂ)
    (hx : AnalyticAt ℂ X s) (hy : AnalyticAt ℂ Y s)
    (hz : AnalyticAt ℂ Z s) (hw : AnalyticAt ℂ W s) (hu : AnalyticAt ℂ U s)
    (hx0 : X s≠0) (hy0 : Y s≠0) (hz0 : Z s≠0) (hw0 : W s≠0)
    (G : ℂ → Fin 210 → ℂ) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v)
    (hg : HasAnalyticGerm (fun t => reduced9 (X t) (Y t) (Z t) (W t) a b (G t)) s) :
    reduced9 (X s) (Y s) (Z s) (W s) a b v=0 := by
  have h0 : AnalyticAt ℂ (fun t => ((-2 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-1)*(X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-5)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*a^(3:ℕ) + (-3)*(X t)^(4:ℕ) + (-3)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(5:ℕ)*a + (X t)^(6:ℕ) + (X t)^(6:ℕ)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*a)/((X t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h1 : AnalyticAt ℂ (fun t => ((-6 + (W t) + (3)*(Z t) + (-11)*(X t)*a + (8)*(X t)*(Z t)*a + (2)*(X t)*(Y t)*a*b + (4)*(X t)*(Y t)^(2:ℕ)*a + (-8)*(X t)^(2:ℕ) + (-9)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(W t) + (8)*(X t)^(2:ℕ)*(Z t) + (2)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(3:ℕ)*a + (-3)*(X t)^(3:ℕ)*a^(3:ℕ) + (-2)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (-5)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (7)*(X t)^(4:ℕ) + (8)*(X t)^(4:ℕ)*a^(2:ℕ) + (-3)*(X t)^(4:ℕ)*(Z t) + (-5)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(4:ℕ) + (-4)*(X t)^(4:ℕ)*(Y t)*b + (3)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-9)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-6)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (13)*(X t)^(5:ℕ)*a + (5)*(X t)^(5:ℕ)*a^(3:ℕ) + (-4)*(X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (4)*(X t)^(5:ℕ)*(Y t)*a*b + (4)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-10)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(6:ℕ) + (2)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t) + (4)*(X t)^(6:ℕ)*(Y t)*b + (7)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)*a^(4:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-6)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (-7)*(X t)^(7:ℕ)*a + (-4)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (3)*(X t)^(7:ℕ)*(Y t)*a*b + (2)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (5)*(X t)^(8:ℕ) + (-7)*(X t)^(8:ℕ)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*a^(4:ℕ) + (X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*b + (-2)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (5)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*a^(3:ℕ) + (-2)*(X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ) + (3)*(X t)^(10:ℕ)*a^(2:ℕ) + (-1)*(X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(11:ℕ)*a + (X t)^(11:ℕ)*a^(3:ℕ))/((X t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h2 : AnalyticAt ℂ (fun t => ((-2 + (-2)*(X t)*a + (-1)*(X t)*(W t)*a + (X t)*(Z t)*a + (2)*(X t)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(2:ℕ)*(W t) + (2)*(X t)^(2:ℕ)*(Z t) + (-2)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (7)*(X t)^(3:ℕ)*a + (-2)*(X t)^(3:ℕ)*(W t)*a + (-4)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (7)*(X t)^(4:ℕ) + (5)*(X t)^(4:ℕ)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(W t) + (-1)*(X t)^(4:ℕ)*(W t)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Y t)*b + (2)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*(W t)*a + (4)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (3)*(X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(6:ℕ) + (-7)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*a^(4:ℕ) + (X t)^(6:ℕ)*(W t) + (X t)^(6:ℕ)*(Z t) + (3)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*b + (4)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (3)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-6)*(X t)^(7:ℕ)*a + (-4)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(W t)*a + (X t)^(7:ℕ)*(Z t)*a + (-4)*(X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (6)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (5)*(X t)^(8:ℕ) + (-1)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-3)*(X t)^(8:ℕ)*(Y t)*b + (-3)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (8)*(X t)^(9:ℕ)*a + (2)*(X t)^(9:ℕ)*a^(3:ℕ) + (-1)*(X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(10:ℕ) + (4)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*(Y t)*b + (X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(11:ℕ)*a + (X t)^(11:ℕ)*(Y t)*a*b + (-1)*(X t)^(11:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(12:ℕ)*a^(2:ℕ))/((X t)^(2:ℕ)*(W t)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h3 : AnalyticAt ℂ (fun t => ((-2 + (-3)*(X t)*a + (2)*(X t)*(Z t)*a + (-2)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-3)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(5:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(6:ℕ) + (X t)^(6:ℕ)*(Z t) + (X t)^(7:ℕ)*a + (X t)^(7:ℕ)*(Z t)*a)/((X t)^(2:ℕ)))) s := by
    fun_prop (disch := norm_num [hx0,hy0,hz0,hw0])
  have h := hv (fun t => ((-2 + (-1)*(Y t)*b + (-1)*(Y t)^(2:ℕ) + (-1)*(X t)*(Y t)*a*b + (-1)*(X t)*(Y t)^(2:ℕ)*a + (X t)^(2:ℕ) + (-1)*(X t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(2:ℕ)*(Y t)*b + (-1)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (-5)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*a^(3:ℕ) + (-3)*(X t)^(4:ℕ) + (-3)*(X t)^(4:ℕ)*a^(2:ℕ) + (X t)^(4:ℕ)*(Y t)*b + (X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-2)*(X t)^(5:ℕ)*a + (X t)^(6:ℕ) + (X t)^(6:ℕ)*a^(2:ℕ) + (2)*(X t)^(7:ℕ)*a)/((X t)^(2:ℕ)))) (fun t => ((-6 + (W t) + (3)*(Z t) + (-11)*(X t)*a + (8)*(X t)*(Z t)*a + (2)*(X t)*(Y t)*a*b + (4)*(X t)*(Y t)^(2:ℕ)*a + (-8)*(X t)^(2:ℕ) + (-9)*(X t)^(2:ℕ)*a^(2:ℕ) + (X t)^(2:ℕ)*(W t) + (8)*(X t)^(2:ℕ)*(Z t) + (2)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(2:ℕ)*(Y t)*b + (X t)^(2:ℕ)*(Y t)*a^(2:ℕ)*b + (3)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(3:ℕ)*a + (-3)*(X t)^(3:ℕ)*a^(3:ℕ) + (-2)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (-1)*(X t)^(3:ℕ)*(Y t)*a*b + (-5)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (7)*(X t)^(4:ℕ) + (8)*(X t)^(4:ℕ)*a^(2:ℕ) + (-3)*(X t)^(4:ℕ)*(Z t) + (-5)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(4:ℕ) + (-4)*(X t)^(4:ℕ)*(Y t)*b + (3)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-9)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-6)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (13)*(X t)^(5:ℕ)*a + (5)*(X t)^(5:ℕ)*a^(3:ℕ) + (-4)*(X t)^(5:ℕ)*(Z t)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (4)*(X t)^(5:ℕ)*(Y t)*a*b + (4)*(X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (-10)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(5:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-1)*(X t)^(6:ℕ) + (2)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Z t) + (4)*(X t)^(6:ℕ)*(Y t)*b + (7)*(X t)^(6:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(6:ℕ)*(Y t)*a^(4:ℕ)*b + (X t)^(6:ℕ)*(Y t)^(2:ℕ) + (-6)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(4:ℕ) + (-7)*(X t)^(7:ℕ)*a + (-4)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(Z t)*a + (X t)^(7:ℕ)*(Z t)*a^(3:ℕ) + (3)*(X t)^(7:ℕ)*(Y t)*a*b + (2)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (5)*(X t)^(8:ℕ) + (-7)*(X t)^(8:ℕ)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*a^(4:ℕ) + (X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(8:ℕ)*(Y t)*b + (-2)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ) + (X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (5)*(X t)^(9:ℕ)*a + (-1)*(X t)^(9:ℕ)*a^(3:ℕ) + (-2)*(X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)*a^(3:ℕ)*b + (2)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(9:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (-2)*(X t)^(10:ℕ) + (3)*(X t)^(10:ℕ)*a^(2:ℕ) + (-1)*(X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-2)*(X t)^(11:ℕ)*a + (X t)^(11:ℕ)*a^(3:ℕ))/((X t)^(2:ℕ)*(W t)))) (fun t => ((-2 + (-2)*(X t)*a + (-1)*(X t)*(W t)*a + (X t)*(Z t)*a + (2)*(X t)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(2:ℕ)*(W t) + (2)*(X t)^(2:ℕ)*(Z t) + (-2)*(X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Y t)^(2:ℕ) + (X t)^(2:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (7)*(X t)^(3:ℕ)*a + (-2)*(X t)^(3:ℕ)*(W t)*a + (-4)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a^(3:ℕ) + (X t)^(3:ℕ)*(Y t)*a*b + (-1)*(X t)^(3:ℕ)*(Y t)^(2:ℕ)*a + (7)*(X t)^(4:ℕ) + (5)*(X t)^(4:ℕ)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(W t) + (-1)*(X t)^(4:ℕ)*(W t)*a^(2:ℕ) + (-2)*(X t)^(4:ℕ)*(Z t) + (X t)^(4:ℕ)*(Y t)*b + (2)*(X t)^(4:ℕ)*(Y t)*a^(2:ℕ)*b + (-2)*(X t)^(4:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(4:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (X t)^(5:ℕ)*a + (-1)*(X t)^(5:ℕ)*(W t)*a + (4)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(5:ℕ)*(Z t)*a^(3:ℕ) + (3)*(X t)^(5:ℕ)*(Y t)*a*b + (X t)^(5:ℕ)*(Y t)*a^(3:ℕ)*b + (X t)^(5:ℕ)*(Y t)^(2:ℕ)*a + (-3)*(X t)^(6:ℕ) + (-7)*(X t)^(6:ℕ)*a^(2:ℕ) + (-1)*(X t)^(6:ℕ)*a^(4:ℕ) + (X t)^(6:ℕ)*(W t) + (X t)^(6:ℕ)*(Z t) + (3)*(X t)^(6:ℕ)*(Z t)*a^(2:ℕ) + (X t)^(6:ℕ)*(Y t)*b + (4)*(X t)^(6:ℕ)*(Y t)^(2:ℕ) + (3)*(X t)^(6:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-6)*(X t)^(7:ℕ)*a + (-4)*(X t)^(7:ℕ)*a^(3:ℕ) + (X t)^(7:ℕ)*(W t)*a + (X t)^(7:ℕ)*(Z t)*a + (-4)*(X t)^(7:ℕ)*(Y t)*a*b + (-1)*(X t)^(7:ℕ)*(Y t)*a^(3:ℕ)*b + (6)*(X t)^(7:ℕ)*(Y t)^(2:ℕ)*a + (X t)^(7:ℕ)*(Y t)^(2:ℕ)*a^(3:ℕ) + (5)*(X t)^(8:ℕ) + (-1)*(X t)^(8:ℕ)*(Z t)*a^(2:ℕ) + (-3)*(X t)^(8:ℕ)*(Y t)*b + (-3)*(X t)^(8:ℕ)*(Y t)*a^(2:ℕ)*b + (X t)^(8:ℕ)*(Y t)^(2:ℕ) + (2)*(X t)^(8:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (8)*(X t)^(9:ℕ)*a + (2)*(X t)^(9:ℕ)*a^(3:ℕ) + (-1)*(X t)^(9:ℕ)*(Z t)*a + (-1)*(X t)^(9:ℕ)*(Y t)*a*b + (-1)*(X t)^(9:ℕ)*(Y t)^(2:ℕ)*a + (-2)*(X t)^(10:ℕ) + (4)*(X t)^(10:ℕ)*a^(2:ℕ) + (X t)^(10:ℕ)*(Y t)*b + (X t)^(10:ℕ)*(Y t)*a^(2:ℕ)*b + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ) + (-1)*(X t)^(10:ℕ)*(Y t)^(2:ℕ)*a^(2:ℕ) + (-3)*(X t)^(11:ℕ)*a + (X t)^(11:ℕ)*(Y t)*a*b + (-1)*(X t)^(11:ℕ)*(Y t)^(2:ℕ)*a + (-1)*(X t)^(12:ℕ)*a^(2:ℕ))/((X t)^(2:ℕ)*(W t)))) (fun t => ((-2 + (-3)*(X t)*a + (2)*(X t)*(Z t)*a + (-2)*(X t)^(2:ℕ) + (2)*(X t)^(2:ℕ)*(Z t) + (X t)^(2:ℕ)*(Z t)*a^(2:ℕ) + (-2)*(X t)^(3:ℕ)*a + (-1)*(X t)^(3:ℕ)*(Z t)*a + (-1)*(X t)^(4:ℕ)*a^(2:ℕ) + (-3)*(X t)^(4:ℕ)*(Z t) + (-1)*(X t)^(4:ℕ)*(Z t)*a^(2:ℕ) + (-1)*(X t)^(5:ℕ)*a + (-2)*(X t)^(5:ℕ)*(Z t)*a + (X t)^(6:ℕ) + (X t)^(6:ℕ)*(Z t) + (X t)^(7:ℕ)*a + (X t)^(7:ℕ)*(Z t)*a)/((X t)^(2:ℕ)))) h0 h1 h2 h3
    (by
      apply (hg.mul_analytic hu).congr
      exact Filter.Eventually.of_forall (fun t => by
        dsimp [reduced9]
        ring))
  simpa only [reduced9,zero_mul,zero_add,add_zero] using h

#print axioms closed_residue_row9

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalClosedResidueRowsA -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRows
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

theorem original_closed_residue_rows_a {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (U : ℂ → ℂ) (hU : AnalyticAt ℂ U s) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v) :
    negativeRowsAConclusion (primeParameter 2 m s) (primeParameter 3 m s)
      (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  have h0 := closed_residue_row0 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row0 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h3 := closed_residue_row3 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row3 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h9 := closed_residue_row9 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row9 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h13 := closed_residue_row13 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row13 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h14 := closed_residue_row14 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row14 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  exact ⟨h0,h3,h9,h13,h14⟩

#print axioms original_closed_residue_rows_a
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalClosedResidueRowsB -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRows
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

theorem original_closed_residue_rows_b {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (U : ℂ → ℂ) (hU : AnalyticAt ℂ U s) (v : Fin 210 → ℂ)
    (hv : IsClosedFourResidue (fun t i => U t*G t i) s v) :
    negativeRowsBConclusion (primeParameter 2 m s) (primeParameter 3 m s)
      (u5*primeParameter 5 m s) (u7*primeParameter 7 m s)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) v := by
  have hu5n : u5≠0 := by rcases hu5 with rfl|rfl <;> norm_num
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  have h16 := closed_residue_row16 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row16 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h19 := closed_residue_row19 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row19 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h21 := closed_residue_row21 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row21 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h26 := closed_residue_row26 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row26 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h45 := closed_residue_row45 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row45 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h53 := closed_residue_row53 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row53 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h104 := closed_residue_row104 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row104 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h150 := closed_residue_row150 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row150 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h159 := closed_residue_row159 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row159 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h163 := closed_residue_row163 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row163 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  have h164 := closed_residue_row164 (primeParameter 2 m) (primeParameter 3 m)
    (fun t => u5*primeParameter 5 m t) (fun t => u7*primeParameter 7 m t) U
    ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s
    (primeParameter_analytic 2 m (by decide) s) (primeParameter_analytic 3 m (by decide) s)
    (analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s))
    (analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)) hU
    (primeParameter_ne_zero 2 m (by decide) s) (primeParameter_ne_zero 3 m (by decide) s)
    (mul_ne_zero hu5n (primeParameter_ne_zero 5 m (by decide) s))
    (mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)) G v hv
    (analytic_signed_negative_row164 hm hf ε hε hlaw u5 u7 hu5 hu7 hphase h5 h7 BG G hG hGF s hshift)
  exact ⟨h16,h19,h21,h26,h45,h53,h104,h150,h159,h163,h164⟩

#print axioms original_closed_residue_rows_b
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveClosedRowsBranch -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate

/-- These consequences depend only on the closed four-coordinate equations,
not on being a leading vector of the entire 210-coordinate system. -/
theorem closed_negative_branch_parameter (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hy : y≠0) (hw : w≠0) (hz : z≠1) (hr : v 192≠0)
    (he : 1+x*a+x^2=0) (hB : negativeRowsBConclusion x y z w a b v) :
    x^4-x^2-y*b-2=0 ∧ (y*b+x^2+y^2+1)*v 42=0 ∧
      (x^4-3*x^2-y^2-1)*(v 84+v 42)=w*(z-1)*v 192 := by
  rcases hB with ⟨h16,h19,h21,h26,h45,h53,h104,h150,h159,h163,h164⟩
  apply negative_branch_parameter x y z w a b (v 42) (v 84) (v 192) hy hw hz hr he
  · linear_combination h45
  · linear_combination (norm := (field_simp [hy]; ring)) h150
  · linear_combination (norm := (field_simp [hy]; ring)) h159

theorem closed_negative_all_branch (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hy : y≠0) (hw : w≠0) (hz : z≠1) (hr : v 192≠0)
    (he : 1+x*a+x^2=0) (hB : negativeRowsBConclusion x y z w a b v) :
    x^4-x^2-y*b-2=0 ∧ w=x^2*z-x^2-1 ∧
      x^4-3*x^2-y^2-1≠0 ∧ v 84+v 42≠0 := by
  obtain ⟨hp,h1,hc⟩ := closed_negative_branch_parameter x y z w a b v hy hw hz hr he hB
  have hwrel := negative_rows_b_all_branch_w x y z w a b v hw hr he hp h1 hc hB
  have hn : (x^4-3*x^2-y^2-1)*(v 84+v 42)≠0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero hw (sub_ne_zero.mpr hz)) hr
  exact ⟨hp,hwrel,(mul_ne_zero_iff.mp hn).1,(mul_ne_zero_iff.mp hn).2⟩

theorem closed_negative_regular_branch (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hy : y≠0) (hw : w≠0) (hz : z≠1) (hr : v 192≠0)
    (he : 1+x*a+x^2=0) (hB : negativeRowsBConclusion x y z w a b v)
    (hA : x^4+y^2-1≠0) :
    v 42=0 ∧ w=x^2*z-x^2-1 ∧ x^4-3*x^2-y^2-1≠0 ∧ v 84≠0 := by
  obtain ⟨hp,h1,hc⟩ := closed_negative_branch_parameter x y z w a b v hy hw hz hr he hB
  obtain ⟨hu,hct,hC,ht⟩ := negative_branch_regular x y z w b (v 42) (v 84) (v 192)
    hw hz hr hA hp h1 hc
  exact ⟨hu,(closed_negative_all_branch x y z w a b v hy hw hz hr he hB).2.1,hC,ht⟩

#print axioms closed_negative_branch_parameter
#print axioms closed_negative_all_branch
#print axioms closed_negative_regular_branch
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveClosedRowsScale -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

theorem negative_rows_a_scale (x y z w a b c : ℂ) (v : Fin 210 → ℂ)
    (h : negativeRowsAConclusion x y z w a b v) :
    negativeRowsAConclusion x y z w a b (fun j => c*v j) := by
  rcases h with ⟨h0,h1,h2,h3,h4⟩
  unfold negativeRowsAConclusion
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · linear_combination c*h0
  · linear_combination c*h1
  · linear_combination c*h2
  · linear_combination c*h3
  · linear_combination c*h4

#print axioms negative_rows_a_scale

theorem negative_rows_b_scale (x y z w a b c : ℂ) (v : Fin 210 → ℂ)
    (h : negativeRowsBConclusion x y z w a b v) :
    negativeRowsBConclusion x y z w a b (fun j => c*v j) := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  unfold negativeRowsBConclusion
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · linear_combination c*h0
  · linear_combination c*h1
  · linear_combination c*h2
  · linear_combination c*h3
  · linear_combination c*h4
  · linear_combination c*h5
  · linear_combination c*h6
  · linear_combination c*h7
  · linear_combination c*h8
  · linear_combination c*h9
  · linear_combination c*h10

#print axioms negative_rows_b_scale

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveClosedRowsNormalize -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

theorem closed_negative_generic_normalization (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hx : x≠0) (hy : y≠0) (hw : w≠0) (hz : z≠1) (hr : v 192≠0)
    (he : 1+x*a+x^2=0)
    (hAr : negativeRowsAConclusion x y z w a b v)
    (hBr : negativeRowsBConclusion x y z w a b v)
    (hA : x^4+y^2-1≠0) :
    ∃ v', v' 84=1 ∧ v' 42=0 ∧ v' 192=(x^4-3*x^2-y^2-1)/(w*(z-1)) ∧
      negativeRowsAConclusion x y z w a b v' ∧
      negativeRowsBConclusion x y z w a b v' ∧
      a= -x-1/x ∧ b=(x^4-x^2-2)/y ∧ w=x^2*z-x^2-1 := by
  obtain ⟨hu,hwrel,hC,ht⟩ := closed_negative_regular_branch x y z w a b v hy hw hz hr he hBr hA
  let v' : Fin 210 → ℂ := fun j => (v 84)⁻¹*v j
  have h84 : v' 84=1 := by simp [v',ht]
  have h42 : v' 42=0 := by simp [v',hu]
  have hr' : v' 192≠0 := mul_ne_zero (inv_ne_zero ht) hr
  have hAr' := negative_rows_a_scale x y z w a b (v 84)⁻¹ v hAr
  have hBr' := negative_rows_b_scale x y z w a b (v 84)⁻¹ v hBr
  obtain ⟨hp,h1,hc⟩ := closed_negative_branch_parameter x y z w a b v' hy hw hz hr' he hBr'
  rw [h42,h84,add_zero,mul_one] at hc
  have hz' : z-1≠0 := sub_ne_zero.mpr hz
  refine ⟨v',h84,h42,?_,hAr',hBr',?_,?_,hwrel⟩
  · linear_combination (norm := (field_simp [hw,hz']; ring)) -(1/(w*(z-1)))*hc
  · linear_combination (norm := (field_simp [hx]; ring)) (1/x)*he
  · linear_combination (norm := (field_simp [hy]; ring)) -(1/y)*hp

theorem closed_negative_a0_normalization (x y z w a b : ℂ) (v : Fin 210 → ℂ)
    (hx : x≠0) (hy : y≠0) (hw : w≠0) (hz : z≠1) (hr : v 192≠0)
    (he : 1+x*a+x^2=0)
    (hAr : negativeRowsAConclusion x y z w a b v)
    (hBr : negativeRowsBConclusion x y z w a b v)
    (hA : x^4+y^2-1=0) :
    ∃ v', v' 192=1 ∧ v' 84=w*(z-1)/(2*x^4-3*x^2-2)-v' 42 ∧
      negativeRowsAConclusion x y z w a b v' ∧
      negativeRowsBConclusion x y z w a b v' ∧
      a= -x-1/x ∧ b=(x^4-x^2-2)/y ∧ w=x^2*z-x^2-1 ∧ 2*x^4-3*x^2-2≠0 := by
  let v' : Fin 210 → ℂ := fun j => (v 192)⁻¹*v j
  have h192 : v' 192=1 := by simp [v',hr]
  have hr' : v' 192≠0 := by rw [h192]; norm_num
  have hAr' := negative_rows_a_scale x y z w a b (v 192)⁻¹ v hAr
  have hBr' := negative_rows_b_scale x y z w a b (v 192)⁻¹ v hBr
  obtain ⟨hp,hwrel,hC,_⟩ := closed_negative_all_branch x y z w a b v' hy hw hz hr' he hBr'
  obtain ⟨_,_,hc⟩ := closed_negative_branch_parameter x y z w a b v' hy hw hz hr' he hBr'
  have hc0 : 2*x^4-3*x^2-2≠0 := by
    intro hh; apply hC; linear_combination hh-hA
  have hcnorm : -2-x^2*3+x^4*2≠0 := by
    convert hc0 using 1; ring
  rw [h192,mul_one] at hc
  refine ⟨v',h192,?_,hAr',hBr',?_,?_,hwrel,hc0⟩
  · linear_combination (norm := (field_simp [hc0]; ring_nf; field_simp [hcnorm]; ring))
      (1/(2*x^4-3*x^2-2))*(hc+(v' 84+v' 42)*hA)
  · linear_combination (norm := (field_simp [hx]; ring)) (1/x)*he
  · linear_combination (norm := (field_simp [hy]; ring)) -(1/y)*hp

#print axioms closed_negative_generic_normalization
#print axioms closed_negative_a0_normalization
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveClosedRowsKernel -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open QuantitativeArithmeticSmallLevelThirtyFiveJetCertificate

/-- A kernel statement for the closed four coordinates alone. It applies
at any Laurent order, without a global leading-vector hypothesis. -/
theorem closed_negative_physical_kernel (m : ℕ) (s u5 u7 a b : ℂ)
    (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (v : Fin 210 → ℂ) (hs : (m:ℝ)≤s.re)
    (he : 1+primeParameter 2 m s*a+(primeParameter 2 m s)^2=0)
    (hAr : negativeRowsAConclusion (primeParameter 2 m s) (primeParameter 3 m s)
      (u5*primeParameter 5 m s) (u7*primeParameter 7 m s) a b v)
    (hBr : negativeRowsBConclusion (primeParameter 2 m s) (primeParameter 3 m s)
      (u5*primeParameter 5 m s) (u7*primeParameter 7 m s) a b v) : v 192=0 := by
  have hu7n : u7≠0 := by rcases hu7 with rfl|rfl <;> norm_num
  let x := primeParameter 2 m s
  let y := primeParameter 3 m s
  let z := u5*primeParameter 5 m s
  let w := u7*primeParameter 7 m s
  have hx : x≠0 := primeParameter_ne_zero 2 m (by decide) s
  have hy : y≠0 := primeParameter_ne_zero 3 m (by decide) s
  have hw : w≠0 := mul_ne_zero hu7n (primeParameter_ne_zero 7 m (by decide) s)
  change 1+x*a+x^2=0 at he
  change negativeRowsAConclusion x y z w a b v at hAr
  change negativeRowsBConclusion x y z w a b v at hBr
  by_cases hz : z=1
  · rw [hz] at hBr
    by_cases hw1 : w+1=0
    · have hw' : w= -1 := by linear_combination hw1
      have hcenter := signed_prime_five_seven_center m s u5 u7 hu5 hu7 hz hw'
      have hp2 : x=1 := by simp only [x,primeParameter,hcenter,Complex.cpow_zero]
      have hp3 : y=1 := by simp only [y,primeParameter,hcenter,Complex.cpow_zero]
      rw [hp2] at he
      have ha : a= -2 := by linear_combination he
      rw [hp2,hp3,hw',ha] at hBr
      exact negative_rows_b_signed_central b v hBr
    · exact negative_z_one_rows x y w a b v hx hy hw hw1
        (signed_prime_five_one_C_ne_zero m s u5 hu5 hz) he hBr
  by_contra hr
  by_cases hA : x^4+y^2-1=0
  · obtain ⟨v',h192,h84,hAr',hBr',ha,hb,hwrel,hc⟩ :=
      closed_negative_a0_normalization x y z w a b v hx hy hw hz hr he hAr hBr hA
    have h4 := a0_first_pivot m s hA
    have hQ := a0_second_pivot m s hA
    have hM := signed_a0_mixed_pivot m s u5 u7 hu5 hu7 hs hA hwrel
    have h := a0_polynomial_consequence x y z w a b v' hx hy hw
      hc h192 h84 ha hb hwrel hA h4 hQ hM hAr' hBr'
    exact (mul_ne_zero (sub_ne_zero.mpr hz) h4) h
  obtain ⟨v',h84,h42,h192,hAr',hBr',ha,hb,hwrel⟩ :=
    closed_negative_generic_normalization x y z w a b v hx hy hw hz hr he hAr hBr hA
  by_cases hD : x^4-x^2+y^2+3=0
  · have hC : x^4-3*x^2-y^2-1≠0 :=
      (closed_negative_all_branch x y z w a b v hy hw hz hr he hBr).2.2.1
    have hX : x^2-1≠0 := by
      intro h; apply hC; linear_combination 2*(x^2-1)*h-hD
    have hpivot := d0_second_pivot_ne_zero m s hD
    have hc := d0_polynomial_consequence x y z w a b v' hx hy hw hz
      h84 h42 h192 ha hb hwrel hD hX hpivot hAr' hBr'
    have hQ : x^4+2=0 := (mul_eq_zero.mp hc).resolve_left (sub_ne_zero.mpr hz)
    have hN := generic_normalized_row104 x y z w a b v' hx hy hw hz
      h84 h42 h192 ha hb hwrel hBr'
    have hT := d0_quartic_row104 x y z (v' 24) hN hD hQ
    exact quartic_norm_contradiction (x^2) z
      (by simpa only [← pow_mul] using hQ)
      (by rw [sign_mul_norm u5 _ hu5]; exact quartic_prime_five_norm m s hQ) hT
  · obtain ⟨h0,h1,h2⟩ := negative_generic_polynomials x y z w a b v'
      hx hy hw hz h84 h42 h192 ha hb hwrel hAr' hBr'
    obtain ⟨hP,hQ⟩ := generic_elimination (x^2) (y^2) z h0 h1 h2 hz
      (by simpa only [← pow_mul] using hD)
    obtain ⟨hxnorm,hynorm,hyxnorm⟩ := physical_parameters m s hs
    change 1≤‖y^2‖ at hynorm
    change ‖y^2‖≤‖x^2‖^2 at hyxnorm
    rw [hQ] at hynorm hyxnorm
    exact QuantitativeArithmeticSmallLevelThirtyFiveRootDisks.generic_no_physical_root
      (x^2) hP hxnorm hynorm hyxnorm

#print axioms closed_negative_physical_kernel
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveNegativeDoublePoleRemoval -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveAnalyticShortRows
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

theorem negative_coordinate84_simple_of_coordinate192_simple {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (u5 u7 : ℂ) (hu5 : u5=1 ∨ u5= -1) (hu7 : u7=1 ∨ u7= -1)
    (hphase : ε*I^(2*m)= -u5*u7) (h5 : badFive f= -u5) (h7 : badSeven f= -u7)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re)
    (hP : 1+((Real.sqrt 2:ℂ)*f 2)*primeParameter 2 m s+(primeParameter 2 m s)^2=0)
    (h192 : (-1:WithTop ℤ)≤meromorphicOrderAt (fun t => G t 192) s) :
    (-1:WithTop ℤ)≤meromorphicOrderAt (fun t => G t 84) s := by
  by_cases hpivot : shortPivotK m ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s≠0 ∨
      shortPivotL m ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) s≠0
  · exact negative_coordinate84_order_ge_neg_one_of_pivot hm hf ε hε hlaw u5 u7 hu5 hu7
      hphase h5 h7 BG G hG hGF s hshift hs hP hpivot
  push Not at hpivot
  obtain ⟨hK,hL⟩ := hpivot
  let X := primeParameter 2 m
  let Y := primeParameter 3 m
  let Z : ℂ → ℂ := fun t => u5*primeParameter 5 m t
  let W : ℂ → ℂ := fun t => u7*primeParameter 7 m t
  let a : ℂ := (Real.sqrt 2:ℂ)*f 2
  let b : ℂ := (Real.sqrt 3:ℂ)*f 3
  have hx : AnalyticAt ℂ X s := primeParameter_analytic 2 m (by decide) s
  have hy : AnalyticAt ℂ Y s := primeParameter_analytic 3 m (by decide) s
  have hz : AnalyticAt ℂ Z s := analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s)
  have hw : AnalyticAt ℂ W s := analyticAt_const.mul (primeParameter_analytic 7 m (by decide) s)
  have hA : (X s)^4+(Y s)^2-1=0 := by
    dsimp [shortPivotK] at hK
    dsimp [shortPivotL] at hL
    linear_combination hL-hK
  let C : ℂ → ℂ := fun t => -(Y t)^2+X t*a-2*(X t)^2+(X t)^4
  let D : ℂ → ℂ := fun t => 1-Y t*b-2*(Y t)^2+3*X t*a-2*(X t)^2-(X t)^3*a
  let E : ℂ → ℂ := fun t => W t-Z t*W t
  have hC : AnalyticAt ℂ C s := by dsimp [C]; fun_prop
  have hD : AnalyticAt ℂ D s := by dsimp [D]; fun_prop
  have hE : AnalyticAt ℂ E s := by dsimp [E]; fun_prop
  have hC0 : C s≠0 := by
    intro hzero
    apply a0_third_pivot m s hs hA
    change -(Y s)^2+X s*a-2*(X s)^2+(X s)^4=0 at hzero
    change 1+a*X s+(X s)^2=0 at hP
    linear_combination hzero-hP+hA
  have h42 := negative_coordinate42_order_ge_neg_one hm hf ε hε hlaw u5 u7 hu5 hu7
    hphase h5 h7 BG G hG hGF s hshift hs hP
  have hrow := analytic_signed_negative_row45 hm hf ε hε hlaw u5 u7 hu5 hu7
    hphase h5 h7 BG G hG hGF s hshift
  have hr : HasAnalyticGerm
      (fun t => C t*G t 84+D t*G t 42+E t*G t 192+0*G t 42) s := by
    apply hrow.congr
    exact Filter.Eventually.of_forall (fun t => by dsimp [C,D,E,X,Y,Z,W,a,b,reduced45]; ring)
  apply four_row_order_lower hC hD hE analyticAt_const hC0
    (hG 42 s).meromorphicAt (hG 192 s).meromorphicAt (hG 42 s).meromorphicAt
    ?_ h42 h192 h42 hr
  change ((-1:ℤ):WithTop ℤ)≤((0:ℤ):WithTop ℤ)
  exact WithTop.coe_le_coe.mpr (by omega)

#print axioms negative_coordinate84_simple_of_coordinate192_simple
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalNegativeChiThreeRegular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

/-- The actual chi3 coordinate is regular in the negative-product sign class.
The residue argument is performed on the closed four-coordinate family only. -/
theorem original_negative_chi3_coordinate_regular {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (hproduct : ε*I^(2*m)*badFive f*badSeven f= -1)
    (BG : ℝ) (G : ℂ → Fin 210 → ℂ)
    (hG : ∀ i z, MeromorphicNFAt (fun s => G s i) z)
    (hGF : ∀ z, BG<z.re → G z=gridVector (2*m) f z)
    (s : ℂ)
    (hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n))
    (hs : (m:ℝ)≤s.re)
    (hden : QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0) :
    AnalyticAt ℂ (fun z => G z 192) s := by
  obtain ⟨h24,h42,h84,h192⟩ := original_negative_four_orders hm hf ε hε hlaw hproduct
    BG G hG hGF s hshift hs hden
  have h5 := badFive_sign hf.toEulerData
  have h7 := badSeven_sign hf.toEulerData
  have hu5 : -badFive f=1 ∨ -badFive f= -1 := by rcases h5 with h|h <;> simp [h]
  have hu7 : -badSeven f=1 ∨ -badSeven f= -1 := by rcases h7 with h|h <;> simp [h]
  have h5sq : (badFive f)^2=1 := by rcases h5 with h|h <;> rw [h] <;> norm_num
  have h7sq : (badSeven f)^2=1 := by rcases h7 with h|h <;> rw [h] <;> norm_num
  have hphase : ε*I^(2*m)= -(-badFive f)*(-badSeven f) := by
    linear_combination (badFive f*badSeven f)*hproduct-
      (ε*I^(2*m)*(badSeven f)^2)*h5sq-(ε*I^(2*m))*h7sq
  have hP := chi3_candidate_polynomial m f s hden
  have hker (U : ℂ → ℂ) (hU : AnalyticAt ℂ U s) (v : Fin 210 → ℂ)
      (hv : IsClosedFourResidue (fun t i => U t*G t i) s v) : v 192=0 := by
    have hA := original_closed_residue_rows_a hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
      BG G hG hGF s hshift U hU v hv
    have hB := original_closed_residue_rows_b hm hf ε hε hlaw
      (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
      BG G hG hGF s hshift U hU v hv
    apply closed_negative_physical_kernel m s (-badFive f) (-badSeven f)
      ((Real.sqrt 2:ℂ)*f 2) ((Real.sqrt 3:ℂ)*f 3) hu5 hu7 v hs ?_ hA hB
    simpa only [mul_comm] using hP
  have h42two : (-2:WithTop ℤ)≤meromorphicOrderAt (fun t => G t 42) s := by
    apply le_trans ?_ h42
    change ((-2:ℤ):WithTop ℤ)≤((-1:ℤ):WithTop ℤ)
    exact WithTop.coe_le_coe.mpr (by omega)
  have hfour (j : Fin 4) : (-2:WithTop ℤ)≤
      meromorphicOrderAt (fun t => G t (closedFourIndex j)) s := by
    fin_cases j
    · exact h24
    · exact h42two
    · exact h84
    · exact h192
  let R : ℂ → Fin 210 → ℂ := fun t j => (t-s)*G t j
  have hR (j : Fin 210) : MeromorphicAt (fun t => R t j) s :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt.mul (hG j s).meromorphicAt
  have h192simple : (-1:WithTop ℤ)≤meromorphicOrderAt (fun t => G t 192) s := by
    obtain ⟨v,hv,hzero⟩ := exists_closed_four_residue R s hR
      (fun j => regularized_order_ge_neg_one (hG (closedFourIndex j) s).meromorphicAt (hfour j))
    have hv0 := hker (fun t => t-s) (analyticAt_id.sub analyticAt_const) v hv
    have hr0 := (hzero (3:Fin 4)).mp hv0
    exact (regularized_order_nonneg_iff (hG 192 s).meromorphicAt).mp hr0
  have h84simple := negative_coordinate84_simple_of_coordinate192_simple hm hf ε hε hlaw
    (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
    BG G hG hGF s hshift hs hP h192simple
  have hb0 : (-1:WithTop ℤ)≤0 := by
    change ((-1:ℤ):WithTop ℤ)≤((0:ℤ):WithTop ℤ)
    exact WithTop.coe_le_coe.mpr (by omega)
  have h24simple := negative_coordinate24_order_lower hm hf ε hε hlaw
    (-badFive f) (-badSeven f) hu5 hu7 hphase (by simp) (by simp)
    BG G hG hGF s hshift hP (-1) hb0 h42 h84simple h192simple
  have hsimple (j : Fin 4) : (-1:WithTop ℤ)≤
      meromorphicOrderAt (fun t => G t (closedFourIndex j)) s := by
    fin_cases j
    · exact h24simple
    · exact h42
    · exact h84simple
    · exact h192simple
  obtain ⟨v,hv,hzero⟩ := exists_closed_four_residue G s (fun j => (hG j s).meromorphicAt) hsimple
  have hv' : IsClosedFourResidue (fun t i => (1:ℂ)*G t i) s v := by
    simpa only [one_mul] using hv
  have hv0 := hker (fun _ => 1) analyticAt_const v hv'
  exact (hG 192 s).meromorphicOrderAt_nonneg_iff_analyticAt.mp ((hzero (3:Fin 4)).mp hv0)

#print axioms original_negative_chi3_coordinate_regular
/-- Original Euler and entire Fricke input supplies one coherent grid whose
chi3 coordinate has no right-halfplane candidate poles in negative-product signs. -/
theorem original_negative_chi3_regular_grid {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      ∃ BG : ℝ, ∃ G : ℂ → Fin 210 → ℂ,
        (∀ i z, MeromorphicNFAt (fun s => G s i) z) ∧
        (∀ z, BG<z.re → G z=gridVector (2*m) f z) ∧
        (∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          ∀ n : ℕ, 0<n → ∀ j, AnalyticAt ℂ (fun z => G z j) (s+(n:ℂ))) ∧
        (ε*I^(2*m)*badFive f*badSeven f= -1 → ∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          AnalyticAt ℂ (fun z => G z 192) s) := by
  obtain ⟨ε,hε,hlaw,BG,G,hG,hGF,htail⟩ := original_chi3_positive_shift_tail hm hf
  refine ⟨ε,hε,hlaw,BG,G,hG,hGF,htail,?_⟩
  intro hproduct s hs hden
  exact original_negative_chi3_coordinate_regular hm hf ε hε hlaw hproduct BG G hG hGF s
    (fun n hn j => (htail s hs hden n hn j).meromorphicOrderAt_nonneg) hs hden

#print axioms original_negative_chi3_regular_grid
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveOriginalChiThreeRegular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology

/-- Original Euler and entire Fricke input supplies one coherent grid whose
chi3 coordinate has no right-halfplane candidate poles for every sign. -/
theorem original_chi3_regular_grid {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      ∃ BG : ℝ, ∃ G : ℂ → Fin 210 → ℂ,
        (∀ i z, MeromorphicNFAt (fun s => G s i) z) ∧
        (∀ z, BG<z.re → G z=gridVector (2*m) f z) ∧
        (∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          ∀ n : ℕ, 0<n → ∀ j, AnalyticAt ℂ (fun z => G z j) (s+(n:ℂ))) ∧
        (∀ s : ℂ, (m:ℝ)≤s.re →
          QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0 →
          AnalyticAt ℂ (fun z => G z 192) s) := by
  obtain ⟨ε,hε,hlaw,BG,G,hG,hGF,htail⟩ := original_chi3_positive_shift_tail hm hf
  refine ⟨ε,hε,hlaw,BG,G,hG,hGF,htail,?_⟩
  intro s hs hden
  have hp := phaseRoot_sign m hε
  change ε*I^(2*m)=1 ∨ ε*I^(2*m)= -1 at hp
  have h5 := badFive_sign hf.toEulerData
  have h7 := badSeven_sign hf.toEulerData
  have hsign : ε*I^(2*m)*badFive f*badSeven f=1 ∨ ε*I^(2*m)*badFive f*badSeven f= -1 := by
    rcases hp with hp|hp <;> rcases h5 with h5|h5 <;> rcases h7 with h7|h7 <;>
      rw [hp,h5,h7] <;> norm_num
  have hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n) :=
    fun n hn j => (htail s hs hden n hn j).meromorphicOrderAt_nonneg
  rcases hsign with hpos|hneg
  · exact original_positive_chi3_coordinate_regular hm hf ε hε hlaw hpos BG G hG hGF s hshift hs hden
  · exact original_negative_chi3_coordinate_regular hm hf ε hε hlaw hneg BG G hG hGF s hshift hs hden

#print axioms original_chi3_regular_grid
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveChiThreeCoherentReflection -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiThree
open Complex SmallLevelAdditive QuantitativeArithmeticSmallLevelThirtyFiveCenters
open FinitenessOriginalFourier SmallLevelNormalized SmallLevelOriginal
open scoped ModularForm
theorem original_numerator_reflection_with_fricke (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 35 (by decide)=(ε*I^(2*m)) • fourierFunction (2*m) f ∧
      ∀ s : ℂ,
      numerator m f s=scaleTwo (2*m) s*reflectionMultiplier (2*m) ε s*
        numerator m f ((2*m:ℕ)-s) := by
  obtain ⟨χ,hχ,hlaw,hW,hc⟩ := original_centers_entire_with_fricke m hm hf
  let ε : ℂ := χ/I^(2*m)
  have hε : ε=1 ∨ ε= -1 := by
    have hi : I^(2*m)=(-1:ℂ)^m := by rw [pow_mul,I_sq]
    rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hχ with rfl|rfl <;> simp [ε,hi,h]
  have hp (positive : Bool) (s : ℂ) :=
    QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection
      (by decide : 0<1260)
      (coefficients (fullCoefficients f (2*m)) (center positive)) ε (hc positive).2.2 s
  have hW' : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 35 (by decide)=(ε*I^(2*m)) • fourierFunction (2*m) f := by
    simpa only [ε,div_mul_cancel₀ _ (pow_ne_zero _ I_ne_zero)] using hW
  refine ⟨ε,hε,hlaw,hW',fun s => ?_⟩
  have hpos := hp true s
  have hneg := hp false s
  norm_num only [center,Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat] at hpos hneg
  rw [center_conductor_factor] at hpos hneg
  unfold numerator reflectionMultiplier
  linear_combination hpos-hneg

theorem original_quadratic_functional_equation_with_fricke (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ (ε : ℂ) (bound : ℝ) (G : ℂ → ℂ), (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 35 (by decide)=(ε*I^(2*m)) • fourierFunction (2*m) f ∧
      (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) ∧
      (∀ s, G s=ε*(315:ℂ)^((m:ℂ)-s)*G ((2*m:ℕ)-s)) ∧
      (∀ s, denominator (2*m) f s≠0 → AnalyticAt ℂ G s) := by
  obtain ⟨ε,hε,hlaw,hW,hN⟩ := original_numerator_reflection_with_fricke m hm hf
  obtain ⟨B,G,hG,hagree,hpole,hgerm⟩ := original_continuation m hm hf
  have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
  have hraw (s : ℂ) : numerator m f s/denominator (2*m) f s=
      reflectionMultiplier (2*m) ε s*(numerator m f ((2*m:ℕ)-s)/denominator (2*m) f ((2*m:ℕ)-s)) := by
    rw [hN s,denominator_reflection (2*m) f s,mul_assoc,
      mul_div_mul_left _ _ (scaleTwo_ne_zero (2*m) s)]
    ring
  have hfe := QuantitativeArithmeticQuadraticTwistReflection.normal_form_reflection
    (fun s => numerator m f s/denominator (2*m) f s) G
    (reflectionMultiplier (2*m) ε) ((2*m:ℕ):ℂ) hG
    (fun s => (reflectionMultiplier_entire (2*m) ε).analyticAt s)
    (reflectionMultiplier_ne_zero (2*m) hε0) hgerm hraw
  refine ⟨ε,B,G,hε,hlaw,hW,hG,hagree,?_,hpole⟩
  intro s
  simpa only [reflectionMultiplier_even] using hfe s
#print axioms original_quadratic_functional_equation_with_fricke
end QuantitativeArithmeticSmallLevelThirtyFiveChiThree
end
end

/-! ## ThirtyFiveChiThreeFiniteOrder -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiThree
open Complex Filter Set SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelNineteen (heckeScalar oppositeScalar)
open QuantitativeArithmeticSmallLevelThirtyFiveCenters
open scoped Topology

theorem original_numerator_bound (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    FinitenessFiniteOrder.Bound (numerator m f) := by
  obtain ⟨χ,_,h⟩ := original_centers_entire m hm hf
  exact FinitenessFiniteOrderClosure.sub
    (SmallLevelMellinUnscale.finite_order_at_one (by decide : 0<1260) _ (h true).2.1)
    (SmallLevelMellinUnscale.finite_order_at_one (by decide : 0<1260) _ (h false).2.1)

theorem denominator_quadratic (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    denominator (2*m) f s=1+((Real.sqrt 2:ℂ)*f 2)*(2:ℂ)^((m:ℂ)-s)+
      ((2:ℂ)^((m:ℂ)-s))^2 := by
  have hfirst := SmallLevelTaylor.hecke_first_scalar (by decide : 0<2) m (f 2) s
  have hsecond := SmallLevelTaylor.hecke_second_scalar (by decide : 0<2) m s
  have hh : heckeScalar (2*m) f s=((Real.sqrt 2:ℂ)*f 2)*(2:ℂ)^((m:ℂ)-s) := by
    simpa only [heckeScalar,Nat.cast_mul,Nat.cast_ofNat] using hfirst
  have ho : oppositeScalar (2*m) s=1+((2:ℂ)^((m:ℂ)-s))^2 := by
    simpa only [oppositeScalar,Nat.cast_ofNat,show (2:ℂ)^2=4 by norm_num] using
      congrArg (fun z : ℂ => 1+z) hsecond
  have he : denominator (2*m) f s=heckeScalar (2*m) f s+oppositeScalar (2*m) s := by
    unfold denominator heckeScalar oppositeScalar
    ring
  rw [he,hh,ho]
  ring

theorem product_identity_of_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s, B<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) :
    ∀ s, denominator (2*m) f s*G s=numerator m f s := by
  obtain ⟨C,hC⟩ := original_hecke_identity m hf
  have hleft := (denominator_entire (2*m) f).mul hG
  have hright := original_numerator_entire m hm hf
  intro s
  have he : (fun z => denominator (2*m) f z*G z)=ᶠ[𝓝[≠] s] numerator m f := by
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

theorem finiteOrder_of_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s, B<s.re → G s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) :
    FinitenessOriginalInput.FiniteOrder G := by
  apply SmallLevelQuadraticExponential.finiteOrder_of_quadratic
    ((Real.sqrt 2:ℂ)*f 2) (m:ℂ) (original_numerator_entire m hm hf).continuous
    (FinitenessInputBounds.bound_finiteOrder (original_numerator_bound m hm hf)) hG
  intro s
  rw [← denominator_quadratic]
  exact product_identity_of_entire hm hf hG B hGF s

#print axioms original_numerator_bound
#print axioms denominator_quadratic
#print axioms product_identity_of_entire
#print axioms finiteOrder_of_entire
end QuantitativeArithmeticSmallLevelThirtyFiveChiThree
end
end

/-! ## ThirtyFiveOriginalChiThreeEntire -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
open Complex Filter Set SmallLevelAdditive SmallLevelNormalized SmallLevelOriginal
open QuantitativeArithmeticAnalyticGerm
open QuantitativeArithmeticSmallLevelThirtyFiveGridAnalytic
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan
open scoped Topology ModularForm

/-- For every sign, the actual quadratic-3 additive
combination is entire and satisfies its conductor-315 functional equation. -/
theorem original_chi3_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ (ω : ℂ) (B : ℝ) (H : ℂ → ℂ), (ω=1 ∨ ω= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ω ∧
      fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 35 (by decide)=(ω*I^(2*m)) • fourierFunction (2*m) f ∧
      Differentiable ℂ H ∧ FinitenessOriginalInput.FiniteOrder H ∧
      (∀ s, B<s.re → H s=original (2*m) f (1/3) s-original (2*m) f (-(1/3)) s) ∧
      ∀ s, H s=ω*(315:ℂ)^((m:ℂ)-s)*H ((2*m:ℕ)-s) := by
  obtain ⟨ε,hε,hlaw,BG,G,hG,hGF,htail,hregular⟩ := original_chi3_regular_grid hm hf
  obtain ⟨ω,B,H,hω,hωlaw,hW,hH,hagree,hfe,haway⟩ :=
    QuantitativeArithmeticSmallLevelThirtyFiveChiThree.original_quadratic_functional_equation_with_fricke m hm hf
  have hgrid (x : ℂ) : (fun z => G z 70-G z 140)=ᶠ[𝓝[≠] x] H := by
    apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) (max BG B) _ _ _ x (by linarith)
    · intro z _
      exact (hG 70 z).meromorphicAt.sub (hG 140 z).meromorphicAt
    · intro z _
      exact (hH z).meromorphicAt
    · intro z hz
      change G z (gridIndex 70)-G z (gridIndex (-70))=H z
      rw [hGF z (lt_of_le_of_lt (le_max_left BG B) hz),
        hagree z (lt_of_le_of_lt (le_max_right BG B) hz),gridVector_index,gridVector_index]
      norm_num [SmallLevelAdditive.grid]
  have hright (s : ℂ) (hs : (m:ℝ)≤s.re) : AnalyticAt ℂ H s := by
    by_cases hd : QuantitativeArithmeticSmallLevelThirtyFiveChiThree.denominator (2*m) f s=0
    · have h192 := hregular s hs hd
      have hshift : ∀ n : ℕ, 0<n → ∀ j, 0≤meromorphicOrderAt (fun z => G z j) (s+n) :=
        fun n hn j => (htail s hs hd n hn j).meromorphicOrderAt_nonneg
      have hrel := analytic_chi3_coordinate_relation hm hf ε hε hlaw BG G hG hGF s hshift
      have hC : AnalyticAt ℂ (fun z => 2*(ε*I^(2*m))*primeParameter 5 m z*
          primeParameter 7 m z/(primeParameter 3 m z)^2) s :=
        ((analyticAt_const.mul (primeParameter_analytic 5 m (by decide) s)).mul
          (primeParameter_analytic 7 m (by decide) s)).div
          ((primeParameter_analytic 3 m (by decide) s).pow 2)
          (pow_ne_zero _ (primeParameter_ne_zero 3 m (by decide) s))
      have hsum := hrel.add (HasAnalyticGerm.of_analytic (hC.mul h192))
      have hdiff : HasAnalyticGerm (fun z => G z 70-G z 140) s := by
        apply hsum.congr
        exact Filter.Eventually.of_forall (fun z => by dsimp only [Pi.mul_apply]; ring)
      exact (hdiff.congr (hgrid s)).analyticAt (hH s)
    · exact haway s hd
  have hentire (s : ℂ) : AnalyticAt ℂ H s := by
    by_cases hs : (m:ℝ)≤s.re
    · exact hright s hs
    · have hs' : (m:ℝ)≤(((2*m:ℕ):ℂ)-s).re := by
        norm_num [Complex.sub_re,Complex.mul_re]
        linarith
      have ha := (hright (((2*m:ℕ):ℂ)-s) hs').comp
        (f:=fun z : ℂ => ((2*m:ℕ):ℂ)-z) (analyticAt_const.sub analyticAt_id)
      have hc : AnalyticAt ℂ (fun z : ℂ => ω*(315:ℂ)^((m:ℂ)-z)) s := by
        fun_prop (disch := norm_num)
      convert hc.mul ha using 1
      funext z
      exact hfe z
  have hdiff : Differentiable ℂ H := fun s => (hentire s).differentiableAt
  exact ⟨ω,B,H,hω,hωlaw,hW,hdiff,
    QuantitativeArithmeticSmallLevelThirtyFiveChiThree.finiteOrder_of_entire hm hf hdiff B hagree,
    hagree,hfe⟩

#print axioms original_chi3_entire
end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

/-! ## ThirtyFiveChiThreeFricke -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiThree
open Complex FinitenessOriginalFourier FinitenessFourierConstruction
open SmallLevelNormalized SmallLevelOriginal
open scoped ModularForm

def quadraticFourier (k : ℕ) (f : ℕ → ℂ) (z : ℂ) : ℂ :=
  fourier (fullCoefficients f k) (z+(1/3:ℝ))-
  fourier (fullCoefficients f k) (z+(-1/3:ℝ))

/-- The quadratic-three Fourier law, retaining the same sign as the
untwisted Fricke law. All analytic continuation is derived from original input. -/
theorem original_quadratic_fricke {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 35 (by decide)=
        (ε*I^(2*m)) • fourierFunction (2*m) f ∧
      ∀ z : ℂ, 0<z.im → quadraticFourier (2*m) f z=
        (ε*I^(2*m))/(((Real.sqrt 315:ℂ)*z)^(2*m))*
          quadraticFourier (2*m) f (-1/((315:ℂ)*z)) := by
  obtain ⟨ε,B,G,hε,hlaw,hW,hent,hfinite,hGF,hFE⟩ :=
    QuantitativeArithmeticSmallLevelThirtyFiveKnownWords.original_chi3_entire hm hf
  obtain ⟨σ,_hσ,hgrowth⟩ := hf.growth
  refine ⟨ε,hε,hlaw,hW,?_⟩
  have h := QuantitativeArithmeticQuadraticTwistInversion.four_translate_fricke
    (k := 2*m) (ε := ε) (B := B)
    (by decide : 0<315) hf.zero hgrowth (1/3) 0 (-1/3) 0 G hent hfinite
    (by
      intro s hs
      rw [hGF s hs]
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
end QuantitativeArithmeticSmallLevelThirtyFiveChiThree
end
end

/-! ## ThirtyFiveChiThreeIndividual -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiThree
open Complex FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticSmallLevelThirtyFiveKnownWords

/-- The Ramanujan-three and quadratic-three equations separate into the
two individual additive equations without dividing by a Hecke eigenvalue. -/
theorem individual_laws {k : ℕ} {f : ℕ → ℂ} (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 k f ε)
    (hquad : ∀ z : ℂ, 0<z.im → quadraticFourier k f z=
      (ε*I^k)/(((Real.sqrt 315:ℂ)*z)^k)*quadraticFourier k f (-1/((315:ℂ)*z))) :
    ∀ z : ℂ, 0<z.im →
      (fourier (fullCoefficients f k) (z+1/3)=
        (ε*I^k)/(((Real.sqrt 315:ℂ)*z)^k)*
          fourier (fullCoefficients f k) (-1/((315:ℂ)*z)+1/3)) ∧
      (fourier (fullCoefficients f k) (z-1/3)=
        (ε*I^k)/(((Real.sqrt 315:ℂ)*z)^k)*
          fourier (fullCoefficients f k) (-1/((315:ℂ)*z)-1/3)) := by
  intro z hz
  have hr := hlaw 3 (by decide) z hz
  rw [show Nat.lcm 35 (3^2)=315 by decide,root_three,one_mul,
    SmallLevelThree.twist_three _ (periodic _),
    SmallLevelThree.twist_three _ (periodic _)] at hr
  norm_num only [Nat.cast_ofNat] at hr
  have hc := hquad z hz
  norm_num only [quadraticFourier,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_ofNat,Complex.ofReal_one] at hc
  simp only [sub_eq_add_neg] at hr hc ⊢
  constructor
  · linear_combination (hr+hc)/2
  · linear_combination (hr-hc)/2

#print axioms individual_laws
end QuantitativeArithmeticSmallLevelThirtyFiveChiThree
end
end

/-! ## ThirtyFiveGroupHecke -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
  FinitenessOriginalInput FinitenessOriginalFourier FinitenessFourierConstruction
  QuantitativeArithmeticRetainedReconstruction
open scoped MatrixGroups ModularForm

theorem original_hecke_two {f : ℕ → ℂ} (hf : EulerData 35 f) (m : ℕ) :
    heckeTwo ((2*m:ℕ):ℤ) (SmallLevelOriginal.fourierFunction (2*m) f)=
      (FinitenessAllLevelHeckePower.scale 2 m*f 2/2) • SmallLevelOriginal.fourierFunction (2*m) f := by
  exact SmallLevelGoodHeckeTwo.original_hecke_two (by decide : ¬2∣35) hf m

#print axioms original_hecke_two
end QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
end
end

/-! ## ThirtyFiveGroupHeckeConsequence -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
  QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
open scoped MatrixGroups ModularForm

def Cplus : SL(2,ℤ) := ⟨!![3,-1;-35,12],by decide⟩
def Cminus : SL(2,ℤ) := ⟨!![3,1;35,12],by decide⟩
def H : SL(2,ℤ) := ⟨!![41,-17;70,-29],by decide⟩

theorem branch_zero : heckeFinite 0*SpecialLinearGroup.mapGL ℝ (six⁻¹)=
    SpecialLinearGroup.mapGL ℝ Cminus*heckeInfinity := by
  rw [show six⁻¹=(⟨!![6,1;35,6],by decide⟩ : SL(2,ℤ)) by decide]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeFinite,heckeInfinity,six,Cminus,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem branch_infinity : heckeInfinity*SpecialLinearGroup.mapGL ℝ (six⁻¹)=
    SpecialLinearGroup.mapGL ℝ (Cplus⁻¹)*heckeFinite 0 := by
  rw [show Cplus⁻¹=(⟨!![12,1;35,3],by decide⟩ : SL(2,ℤ)) by decide]
  rw [show six⁻¹=(⟨!![6,1;35,6],by decide⟩ : SL(2,ℤ)) by decide]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeFinite,heckeInfinity,six,Cplus,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem branch_one : heckeFinite 1*SpecialLinearGroup.mapGL ℝ (six⁻¹)=
    SpecialLinearGroup.mapGL ℝ H*heckeFinite 1 := by
  rw [show six⁻¹=(⟨!![6,1;35,6],by decide⟩ : SL(2,ℤ)) by decide]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heckeFinite,six,H,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Fin.sum_univ_two]

/-- The extra matrix H is forced by Hecke2 once C+ and C- are invariant.
No division by the Hecke eigenvalue is involved. -/
theorem original_H (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (hp : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Cplus=
      SmallLevelOriginal.fourierFunction (2*m) f)
    (hn : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Cminus=
      SmallLevelOriginal.fourierFunction (2*m) f) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] H=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  let F := SmallLevelOriginal.fourierFunction (2*m) f
  let k : ℤ := ((2*m:ℕ):ℤ)
  let K := slashStabilizer k F
  have hb : F ∣[k] six⁻¹=F := K.inv_mem (original_six (by omega) hf)
  have hpi : F ∣[k] Cplus⁻¹=F := K.inv_mem hp
  have he := original_hecke_two hf.toEulerData m
  have hh := congrArg (fun G : ℍ → ℂ => G ∣[k] six⁻¹) he
  simp only [heckeTwo,SlashAction.add_slash,ModularForm.SL_smul_slash] at hh
  rw [hb] at hh
  have hi : (F ∣[k] heckeInfinity) ∣[k] six⁻¹=F ∣[k] heckeFinite 0 := by
    change (F ∣[k] heckeInfinity) ∣[k] SpecialLinearGroup.mapGL ℝ (six⁻¹)=_
    rw [← SlashAction.slash_mul,branch_infinity,SlashAction.slash_mul]
    change (F ∣[k] Cplus⁻¹) ∣[k] heckeFinite 0=_
    rw [hpi]
  have h0 : (F ∣[k] heckeFinite 0) ∣[k] six⁻¹=F ∣[k] heckeInfinity := by
    change (F ∣[k] heckeFinite 0) ∣[k] SpecialLinearGroup.mapGL ℝ (six⁻¹)=_
    rw [← SlashAction.slash_mul,branch_zero,SlashAction.slash_mul]
    change (F ∣[k] Cminus) ∣[k] heckeInfinity=_
    rw [hn]
  have h1 : (F ∣[k] heckeFinite 1) ∣[k] six⁻¹=(F ∣[k] H) ∣[k] heckeFinite 1 := by
    change (F ∣[k] heckeFinite 1) ∣[k] SpecialLinearGroup.mapGL ℝ (six⁻¹)=_
    rw [← SlashAction.slash_mul,branch_one,SlashAction.slash_mul]
    rfl
  have hz : (F ∣[k] H) ∣[k] heckeFinite 1=F ∣[k] heckeFinite 1 := by
    change (F ∣[k] heckeInfinity) ∣[k] six⁻¹+
      (F ∣[k] heckeFinite 0) ∣[k] six⁻¹+
      (F ∣[k] heckeFinite 1) ∣[k] six⁻¹=_ at hh
    rw [hi,h0,h1] at hh
    change (F ∣[k] heckeInfinity)+(F ∣[k] heckeFinite 0)+(F ∣[k] heckeFinite 1)=_ at he
    funext z
    have hh' := congrFun hh z
    have he' := congrFun he z
    simp only [Pi.add_apply] at hh' he'
    linear_combination hh'-he'
  have hc := congrArg (fun G : ℍ → ℂ => G ∣[k] (heckeFinite 1)⁻¹) hz
  simpa only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] using hc

#print axioms original_H
end QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
end
end

/-! ## ThirtyFiveChiThreeMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiThree
open Matrix UpperHalfPlane SmallLevelNormalized
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

theorem sqrt_three_conductor : Real.sqrt 315=3*Real.sqrt 35 := by
  rw [show (315:ℝ)=9*35 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem plus_branch : fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Cplus*translation (1/3)=
    translation (1/3)*fricke 315 (by decide) := by
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Cplus,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_three_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem minus_branch : fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Cminus*translation (-1/3)=
    translation (-1/3)*fricke 315 (by decide) := by
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Cminus,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_three_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem plus_conjugate : (fricke 35 (by decide))⁻¹*translation (1/3)*fricke 315 (by decide)*
    (translation (1/3))⁻¹=SpecialLinearGroup.mapGL ℝ Cplus := by
  calc
    _=(fricke 35 (by decide))⁻¹*(translation (1/3)*fricke 315 (by decide))*(translation (1/3))⁻¹ := by group
    _=(fricke 35 (by decide))⁻¹*(fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Cplus*translation (1/3))*(translation (1/3))⁻¹ := by rw [plus_branch]
    _=_ := by group

theorem minus_conjugate : (fricke 35 (by decide))⁻¹*translation (-1/3)*fricke 315 (by decide)*
    (translation (-1/3))⁻¹=SpecialLinearGroup.mapGL ℝ Cminus := by
  calc
    _=(fricke 35 (by decide))⁻¹*(translation (-1/3)*fricke 315 (by decide))*(translation (-1/3))⁻¹ := by group
    _=(fricke 35 (by decide))⁻¹*(fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Cminus*translation (-1/3))*(translation (-1/3))⁻¹ := by rw [minus_branch]
    _=_ := by group

#print axioms plus_conjugate
#print axioms minus_conjugate
end QuantitativeArithmeticSmallLevelThirtyFiveChiThree
end
end

/-! ## ThirtyFiveChiThreeTransformations -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiThree
open Complex Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

/-- Original Euler/Fricke input forces both denominator-three matrices,
including the zero Hecke-eigenvalue cases. -/
theorem original_C_plus_minus {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Cplus=fourierFunction (2*m) f ∧
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Cminus=fourierFunction (2*m) f := by
  obtain ⟨ε,_hε,hlaw,_hW,hquad⟩ := original_quadratic_fricke hm hf
  have hF : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients f (2*m)) z=
      (ε*Complex.I^(2*m))/(((Real.sqrt 35:ℂ)*z)^(2*m))*
        fourier (fullCoefficients f (2*m)) (-1/((35:ℂ)*z)) := by
    intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  have hind := individual_laws ε hlaw hquad
  constructor
  · have h := QuantitativeArithmeticNormalizedIndividualFricke.single_of_fricke
      35 315 (2*m) (by decide) (by decide) (1/3) _ _ hF
      (by
        intro z hz
        simpa only [Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_one,
          Complex.ofReal_ofNat] using (hind z hz).1)
    rw [plus_conjugate] at h
    exact h
  · have h := QuantitativeArithmeticNormalizedIndividualFricke.single_of_fricke
      35 315 (2*m) (by decide) (by decide) (-1/3) _ _ hF
      (by
        intro z hz
        simpa only [Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat,
          Complex.ofReal_one,sub_eq_add_neg,neg_div] using (hind z hz).2)
    rw [minus_conjugate] at h
    exact h

#print axioms original_C_plus_minus
end QuantitativeArithmeticSmallLevelThirtyFiveChiThree
end
end

/-! ## ThirtyFiveTwelveGenerators -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveTwelve
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized SmallLevelOriginal
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
open scoped MatrixGroups ModularForm

theorem original_H_unconditional {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] H=fourierFunction (2*m) f := by
  obtain ⟨hp,hn⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiThree.original_C_plus_minus hm hf
  exact original_H m hm hf hp hn

def generator : Fin 4 → SL(2,ℤ)
  | 0 => ⟨!![12,-1;-35,3],by decide⟩
  | 1 => ⟨!![12,1;35,3],by decide⟩
  | 2 => ⟨!![12,-5;-175,73],by decide⟩
  | 3 => ⟨!![12,5;175,73],by decide⟩

def center : Fin 4 → ℝ := ![1/12,-1/12,5/12,-5/12]

theorem original_generators {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (i : Fin 4) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] generator i=fourierFunction (2*m) f := by
  let K := slashStabilizer (((2*m:ℕ):ℤ)) (fourierFunction (2*m) f)
  obtain ⟨hp,hn⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiThree.original_C_plus_minus hm hf
  have hh : H∈K := original_H_unconditional hm hf
  have he : QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.row 3∈K := original_rows (by omega) hf 3
  have ht : T∈K := original_T (2*m) f
  have hu : lower 35∈K := original_lower (by decide) hf
  change generator i∈K
  fin_cases i
  · change generator 0∈K
    rw [show generator 0=Cminus⁻¹ by decide]
    exact K.inv_mem hn
  · change generator 1∈K
    rw [show generator 1=Cplus⁻¹ by decide]
    exact K.inv_mem hp
  · change generator 2∈K
    rw [show generator 2=QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.row 3*H by decide]
    exact K.mul_mem he hh
  · change generator 3∈K
    rw [show generator 3=(lower 35*QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.row 3*T)*(T⁻¹*H⁻¹*T) by decide]
    exact K.mul_mem (K.mul_mem (K.mul_mem hu he) ht)
      (K.mul_mem (K.mul_mem (K.inv_mem ht) (K.inv_mem hh)) ht)

#print axioms original_H_unconditional
#print axioms original_generators
end QuantitativeArithmeticSmallLevelThirtyFiveTwelve
end
end

/-! ## ThirtyFiveChiFourWordMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized SmallLevelOriginal
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows
open scoped MatrixGroups ModularForm

def integral : Fin 6 → SL(2,ℤ)
  | 0 => ⟨!![2,-1;-105,53],by decide⟩
  | 1 => ⟨!![2,-1;-35,18],by decide⟩
  | 2 => ⟨!![3,-2;35,-23],by decide⟩
  | 3 => Cplus
  | 4 => ⟨!![6,-5;35,-29],by decide⟩
  | 5 => ⟨!![12,-7;-245,143],by decide⟩

theorem original_integral {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (i : Fin 6) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] integral i=fourierFunction (2*m) f := by
  let K := slashStabilizer (((2*m:ℕ):ℤ)) (fourierFunction (2*m) f)
  obtain ⟨hp,hn⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiThree.original_C_plus_minus hm hf
  have hh : H∈K := QuantitativeArithmeticSmallLevelThirtyFiveTwelve.original_H_unconditional hm hf
  have he : QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.row 3∈K := original_rows (by omega) hf 3
  have ht : T∈K := original_T (2*m) f
  change integral i∈K
  fin_cases i
  · exact original_rows (by omega) hf 2
  · exact he
  · change integral 2∈K
    rw [show integral 2=Cminus*T⁻¹ by decide]
    exact K.mul_mem hn (K.inv_mem ht)
  · exact hp
  · exact original_rows (by omega) hf 6
  · change integral 5∈K
    rw [show integral 5=QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.row 3*H⁻¹ by decide]
    exact K.mul_mem he (K.inv_mem hh)

def matrix : Fin 9 → GL (Fin 2) ℝ
  | 0 => fricke 35 (by decide)
  | 1 => fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ T⁻¹
  | 2 => SpecialLinearGroup.mapGL ℝ (integral 0)
  | 3 => SpecialLinearGroup.mapGL ℝ (integral 1)
  | 4 => SpecialLinearGroup.mapGL ℝ (integral 2)
  | 5 => SpecialLinearGroup.mapGL ℝ (integral 3)
  | 6 => SpecialLinearGroup.mapGL ℝ (integral 4)
  | 7 => SpecialLinearGroup.mapGL ℝ (integral 5)
  | 8 => fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ (integral 1)

def isFricke (i : Fin 9) : Bool := i=0 || i=1 || i=8

def sign (χ : ℂ) (i : Fin 9) : ℂ := if isFricke i then χ else 1

def raw : Fin 9 → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => !![0,-1;35,0]
  | 1 => !![0,-1;35,-35]
  | 2 => !![2,-1;-105,53]
  | 3 => !![2,-1;-35,18]
  | 4 => !![3,-2;35,-23]
  | 5 => !![3,-1;-35,12]
  | 6 => !![6,-5;35,-29]
  | 7 => !![12,-7;-245,143]
  | 8 => !![35,-18;70,-35]

def scale (i : Fin 9) : ℝ := if isFricke i then 1/Real.sqrt 35 else 1

theorem matrix_det (i : Fin 9) : (GeneralLinearGroup.det (matrix i):ℝ)=1 := by
  have hd : (fricke 35 (by decide)).val.det=1 := fricke_det 35 (by decide)
  fin_cases i <;> simp [matrix,hd]

theorem sign_cases {χ : ℂ} (hχ : χ=1 ∨ χ= -1) (i : Fin 9) :
    sign χ i=1 ∨ sign χ i= -1 := by
  unfold sign
  split_ifs
  · exact hχ
  · exact Or.inl rfl

theorem original_matrix_actions {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (i : Fin 9) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] matrix i=
      sign (ε*Complex.I^(2*m)) i • fourierFunction (2*m) f := by
  obtain ⟨_hχ,hW⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<35) m ε hε hlaw
  have hi (j : Fin 6) : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      SpecialLinearGroup.mapGL ℝ (integral j)=fourierFunction (2*m) f := original_integral hm hf j
  have ht : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] T⁻¹=fourierFunction (2*m) f :=
    (slashStabilizer (((2*m:ℕ):ℤ)) (fourierFunction (2*m) f)).inv_mem (original_T (2*m) f)
  change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ T⁻¹=
    fourierFunction (2*m) f at ht
  fin_cases i
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 35 (by decide)=
      (ε*Complex.I^(2*m)) • fourierFunction (2*m) f
    exact hW
  · change _ ∣[_] (fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ T⁻¹)=
      (ε*Complex.I^(2*m)) • _
    rw [SlashAction.slash_mul,hW,det_one_smul _ (by simp)]
    rw [ht]
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (integral 0)=1 • _
    rw [one_smul]
    exact hi 0
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (integral 1)=1 • _
    rw [one_smul]
    exact hi 1
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (integral 2)=1 • _
    rw [one_smul]
    exact hi 2
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (integral 3)=1 • _
    rw [one_smul]
    exact hi 3
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (integral 4)=1 • _
    rw [one_smul]
    exact hi 4
  · change fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] SpecialLinearGroup.mapGL ℝ (integral 5)=1 • _
    rw [one_smul]
    exact hi 5
  · change _ ∣[_] (fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ (integral 1))=
      (ε*Complex.I^(2*m)) • _
    rw [SlashAction.slash_mul,hW,det_one_smul _ (by simp)]
    rw [hi 1]

#print axioms original_integral
#print axioms original_matrix_actions
end QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
end
end

/-! ## ThirtyFiveChiFourRawRates -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem raw_det_pos (i : Fin 9) : 0<(raw i).det := by fin_cases i <;> decide

theorem scale_pos (i : Fin 9) : 0<scale i := by
  unfold scale
  split_ifs
  · exact one_div_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  · norm_num

theorem raw_coordinates (i : Fin 9) (a b : Fin 2) :
    (matrix i).val a b=scale i*(raw i a b:ℝ) := by
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hT : T⁻¹=(⟨!![1,-1;0,1],by decide⟩ : SL(2,ℤ)) := by decide
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [matrix,integral,raw,scale,isFricke,fricke,SmallLevelNormalized.matrix,
      QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke.Cplus,hT,
      GeneralLinearGroup.mkOfDetNeZero,SpecialLinearGroup.toGL,
      SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith [ht]

theorem scale_squared_det (i : Fin 9) : (scale i)^2*((raw i).det:ℝ)=1 := by
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> norm_num [scale,isFricke,raw,Matrix.det_fin_two,ht,hn]

def coordA (i : Fin 9) : ℝ := (matrix i).val 0 0
def coordB (i : Fin 9) : ℝ := (matrix i).val 0 1
def coordC (i : Fin 9) : ℝ := (matrix i).val 1 0
def coordD (i : Fin 9) : ℝ := (matrix i).val 1 1

theorem coordinate_det (i : Fin 9) : coordA i*coordD i-coordB i*coordC i=1 := by
  have hd := matrix_det i
  change (matrix i).val.det=1 at hd
  simpa only [Matrix.det_fin_two,coordA,coordB,coordC,coordD] using hd

def rawDen (i : Fin 9) (t : ℤ) : ℤ := raw i 1 0*t+raw i 1 1*420

def rawNumer (i : Fin 9) (t : ℤ) : ℤ := raw i 0 0*t+raw i 0 1*420

def rate (i : Fin 9) (t : ℤ) : ℚ := (rawDen i t:ℚ)^2/((raw i).det*420^2)

def derivative (i : Fin 9) (t : ℤ) : ℚ := (raw i 1 0:ℚ)*rawDen i t/((raw i).det*420)

theorem coordDen_raw (i : Fin 9) (t : ℤ) :
    coordC i*((t:ℝ)/420)+coordD i=scale i*((rawDen i t:ℝ)/420) := by
  simp only [coordC,coordD,raw_coordinates,rawDen,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
  ring

theorem rate_eq (i : Fin 9) (t : ℤ) :
    (coordC i*((t:ℝ)/420)+coordD i)^2=(rate i t:ℝ) := by
  rw [coordDen_raw]
  have hd : ((raw i).det:ℝ)≠0 := by exact_mod_cast (raw_det_pos i).ne'
  have hs := scale_squared_det i
  norm_num only [rate,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_intCast,Rat.cast_ofNat]
  field_simp [hd]
  linear_combination 176400*(rawDen i t:ℝ)^2*hs

theorem derivative_eq (i : Fin 9) (t : ℤ) :
    coordC i*(coordC i*((t:ℝ)/420)+coordD i)=(derivative i t:ℝ) := by
  rw [coordDen_raw]
  simp only [coordC,raw_coordinates]
  have hd : ((raw i).det:ℝ)≠0 := by exact_mod_cast (raw_det_pos i).ne'
  have hs := scale_squared_det i
  norm_num only [derivative,Rat.cast_div,Rat.cast_mul,Rat.cast_intCast,Rat.cast_ofNat]
  field_simp [hd]
  linear_combination (raw i 1 0:ℝ)*(rawDen i t:ℝ)*hs

#print axioms raw_coordinates
#print axioms rate_eq
#print axioms derivative_eq
end QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
end
end

/-! ## ThirtyFiveChiFourWordTaylor -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
open Matrix UpperHalfPlane SmallLevelNormalized Complex Set
open FinitenessOriginalFourier FinitenessFourierConstruction SmallLevelAdditive
open QuantitativeArithmeticTwoSequenceTaylor
open scoped MatrixGroups ModularForm

theorem matrix_fourier_of_slash (m : ℕ) (f : ℕ → ℂ) (χ : ℂ)
    (hχ : χ=1 ∨ χ= -1) (w : Fin 9)
    (hw : SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] matrix w=
      sign χ w • SmallLevelOriginal.fourierFunction (2*m) f)
    (z : ℂ) (hz : 0<z.im) :
    fourier (fullCoefficients f (2*m)) z=
      sign χ w/(((coordC w:ℂ)*z+(coordD w:ℂ))^(2*m))*
        fourier (fullCoefficients f (2*m))
          (((coordA w:ℂ)*z+(coordB w:ℂ))/((coordC w:ℂ)*z+(coordD w:ℂ))) := by
  have hback : SmallLevelOriginal.fourierFunction (2*m) f=
      sign χ w • (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] matrix w) := by
    rcases sign_cases hχ w with hc|hc
    · simpa only [hc,one_smul] using hw.symm
    · simpa only [hc,neg_one_smul,neg_neg] using congrArg Neg.neg hw.symm
  have h := congrFun hback ⟨z,hz⟩
  rw [Pi.smul_apply,smul_eq_mul,det_one_slash _ (matrix_det w),_root_.zpow_neg,zpow_natCast] at h
  simp only [SmallLevelOriginal.fourierFunction] at h
  rw [coe_smul_of_det_pos (by rw [matrix_det]; norm_num)] at h
  simpa only [num,denom,coordA,coordB,coordC,coordD,div_eq_mul_inv,
    mul_assoc,mul_comm,mul_left_comm] using h

theorem matrix_taylor_of_law {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε) :
    ∀ w : Fin 9, coordC w≠0 →
      ∀ j : ℝ, coordC w*j+coordD w≠0 →
      ∃ (bound : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
        AnalyticOnNhd ℂ (error M) {s : ℂ | bound-(M:ℝ)<s.re} ∧
        ∀ s : ℂ, bound<s.re →
          transform (fullCoefficients f (2*m)) j s-
            sign (ε*Complex.I^(2*m)) w*(((coordC w*j+coordD w)^2:ℝ):ℂ)^(s-(m:ℂ))*
              (∑ n∈Finset.range M, (Complex.I*((coordC w*(coordC w*j+coordD w):ℝ):ℂ))^n*
                Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n*
                transform (fullCoefficients f (2*m))
                  ((coordA w*j+coordB w)/(coordC w*j+coordD w)) (s+(n:ℂ)))=
            error M s := by
  obtain ⟨hχ,_hfricke⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law
    (by decide : 0<35) m ε hε hlaw
  intro w hC j hj
  obtain ⟨τ,_,hg⟩ := hf.growth
  have hF := matrix_fourier_of_slash m f (ε*Complex.I^(2*m)) hχ w (original_matrix_actions hm hf ε hε hlaw w)
  have hh := matrix_even_rows (polynomial_bound hf.zero hg (2*m))
    (fullCoefficients_zero hf.zero (2*m)) m
    (coordA w) (coordB w) (coordC w) (coordD w) j hC
    (by rw [coordinate_det]; norm_num) hj (sign (ε*Complex.I^(2*m)) w) (by
      simpa only [coordinate_det,Complex.ofReal_one,one_pow,mul_one] using hF)
  simpa only [coordinate_det,div_one] using hh


#print axioms matrix_taylor_of_law
end QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
end
end

/-! ## ThirtyFiveChiFourRowData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
open Matrix Complex SmallLevelAdditive
open QuantitativeArithmeticSmallLevelThirtyFiveChiFour (coordinate)

def matrixIndex : Fin 29 → Fin 9 :=
  ![0,0,0,0,0,0,0,0,0,0,0,0,1,2,2,3,3,4,4,4,4,4,4,5,5,6,6,7,8]

def source : Fin 29 → ℤ :=
  ![24,36,40,42,48,60,80,120,168,180,240,252,414,204,210,168,180,240,252,270,273,280,288,120,126,330,336,240,189]

def partner : Fin 29 → ℤ :=
  ![-210,-140,-126,-120,-105,-84,-63,-42,-30,-28,-21,-20,840,-6,0,-21,-20,40,42,60,84,0,24,-30,-28,80,84,-20,270]

def sourceIndex : Fin 29 → Fin 35 :=
  ![1,2,3,4,5,6,7,10,12,13,17,18,34,15,16,12,13,17,18,19,20,21,22,10,11,26,27,17,14]

def targetIndex : Fin 29 → Fin 35 :=
  ![16,21,23,24,25,27,28,29,30,31,32,33,0,34,0,32,33,3,4,6,8,0,1,30,31,7,8,33,19]

theorem nonaffine (i : Fin 29) : raw (matrixIndex i) 1 0≠0 := by
  fin_cases i <;> decide

theorem denominator_ne_zero (i : Fin 29) : rawDen (matrixIndex i) (source i)≠0 := by
  fin_cases i <;> decide

theorem row_closed (i : Fin 29) :
    420*rawNumer (matrixIndex i) (source i)=partner i*rawDen (matrixIndex i) (source i) := by
  fin_cases i <;> decide

theorem source_coordinate (i : Fin 29) : (coordinate (sourceIndex i)).val=source i := by
  fin_cases i <;> decide

theorem target_coordinate (i : Fin 29) : (coordinate (targetIndex i)).val=partner i%420 := by
  fin_cases i <;> decide

def gridVector (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 35) : ℂ :=
  grid k f 420 (coordinate i).val s

theorem grid_source (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 29) :
    gridVector k f s (sourceIndex i)=grid k f 420 (source i) s := by
  rw [gridVector,source_coordinate]

theorem grid_target (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 29) :
    gridVector k f s (targetIndex i)=grid k f 420 (partner i) s := by
  rw [gridVector,target_coordinate]
  exact grid_mod k f (by decide : 0<420) (partner i) s

#print axioms row_closed
#print axioms grid_target
end QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
end
end

/-! ## ThirtyFiveChiFourGridRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
open Complex Matrix Set SmallLevelAdditive SmallLevelTaylor FinitenessOriginalFourier

/-- The exact normalized matrices act on the selected rational grid points. -/
theorem row_partner (i : Fin 29) :
    (coordA (matrixIndex i)*((source i:ℝ)/420)+coordB (matrixIndex i))/
      (coordC (matrixIndex i)*((source i:ℝ)/420)+coordD (matrixIndex i))=(partner i:ℝ)/420 := by
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  fin_cases i <;>
    norm_num [coordA,coordB,coordC,coordD,raw_coordinates,matrixIndex,source,partner,
      raw,scale,isFricke] <;> field_simp [hn] <;> nlinarith [ht]

theorem row_nonaffine (i : Fin 29) : coordC (matrixIndex i)≠0 := by
  rw [coordC,raw_coordinates]
  exact mul_ne_zero (scale_pos _).ne' (by exact_mod_cast nonaffine i)

theorem row_den_ne_zero (i : Fin 29) :
    coordC (matrixIndex i)*((source i:ℝ)/420)+coordD (matrixIndex i)≠0 := by
  rw [coordDen_raw]
  exact mul_ne_zero (scale_pos _).ne'
    (div_ne_zero (by exact_mod_cast denominator_ne_zero i) (by norm_num))

def rowCoefficient (m : ℕ) (χ : ℂ) (i : Fin 29) (n : ℕ) (s : ℂ) : ℂ :=
  sign χ (matrixIndex i)*((rate (matrixIndex i) (source i):ℂ))^(s-(m:ℂ))*
    (I*(derivative (matrixIndex i) (source i):ℂ))^n*
      Ring.choose (s+(n:ℂ)-((2*m:ℕ):ℂ)) n

/-- All 29 nonaffine rows in the chi4 certificate are actual original-input
Taylor equations, with every positive shift retained on the selected grid. -/
theorem original_word_rows {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε)
    (i : Fin 29) :
    ∃ (B : ℝ) (error : ℕ → ℂ → ℂ), ∀ M : ℕ,
      AnalyticOnNhd ℂ (error M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        gridVector (2*m) f s (sourceIndex i)-
          rowCoefficient m (ε*I^(2*m)) i 0 s*gridVector (2*m) f s (targetIndex i)=
        error M s+∑ n∈Finset.range M,
          rowCoefficient m (ε*I^(2*m)) i (n+1) s*
            gridVector (2*m) f (s+((n:ℂ)+1)) (targetIndex i) := by
  obtain ⟨B,error,hrow⟩ := matrix_taylor_of_law hm hf ε hε hlaw (matrixIndex i)
    (row_nonaffine i) ((source i:ℝ)/420) (row_den_ne_zero i)
  refine ⟨B,fun M => error (M+1),?_⟩
  intro M
  constructor
  · simpa only [Nat.cast_add,Nat.cast_one] using (hrow (M+1)).1
  · intro s hs
    have he := (hrow (M+1)).2 s hs
    rw [row_partner,rate_eq,derivative_eq,Finset.sum_range_succ'] at he
    simp only [Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one,
      Nat.cast_add,Nat.cast_one,Complex.ofReal_ratCast] at he
    simp only [grid_source,grid_target,grid,original,rowCoefficient,Nat.cast_zero,add_zero,
      pow_zero,Ring.choose_zero_right,mul_one,Nat.cast_add,Nat.cast_one]
    rw [mul_add,Finset.mul_sum] at he
    simp only [mul_assoc,one_mul] at he ⊢
    linear_combination he

#print axioms row_partner
#print axioms original_word_rows
end QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows
end
end

/-! ## ThirtyFiveChiFourRamanujanRows -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan
open Complex Set MeasureTheory SmallLevelTaylor SmallLevelAdditive
open FinitenessOriginalFourier FinitenessRamanujanFourier FinitenessRamanujanSum
open FinitenessNormalizedTwistProduct
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (gridVector)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFour (coordinate)

def rowQ : Fin 2 → ℕ := ![4,5]
def rowT : Fin 2 → ℤ := ![15,21]
def rowL (i : Fin 2) : ℕ := Nat.lcm 35 ((rowQ i)^2)
def rowD : Fin 2 → ℤ := ![315,1008]
def rowPartner (i : Fin 2) : ℤ := -(rowD i/rowT i)
def entireSpecs : Fin 4 → ℕ := ![1,4,5,10]

theorem specs_valid (i : Fin 2) : 0<rowQ i ∧ rowQ i∣420 ∧ rowT i≠0 ∧
    (rowL i:ℤ)*rowD i=(420:ℤ)^2 ∧ rowT i∣rowD i := by fin_cases i <;> decide

theorem entireSpecs_valid (i : Fin 4) : 0<entireSpecs i ∧ entireSpecs i∣420 := by
  fin_cases i <;> decide

def plusRows (v : Fin 35 → ℂ) : Fin 2 → ℂ :=
  ![v 10+v 26,v 9+v 14+v 20+v 28]
def minusRows (v : Fin 35 → ℂ) : Fin 2 → ℂ :=
  ![v 8+v 23,v 2+v 10+v 15+v 22]
def entireRows (v : Fin 35 → ℂ) : Fin 4 → ℂ :=
  ![v 0,v 9+v 25,v 8+v 12+v 18+v 27,v 4+v 11+v 23+v 29]

theorem plusRows_grid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 2) :
    plusRows (gridVector k f s) i=gridSum k f 420 (rowQ i) (rowT i) s := by
  fin_cases i <;>
    norm_num [plusRows,gridVector,coordinate,gridSum,rowQ,rowT,residues,Finset.sum_filter,Finset.sum_range_succ]

theorem minusRows_grid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 2) :
    minusRows (gridVector k f s) i=gridSum k f 420 (rowQ i) (rowPartner i) s := by
  fin_cases i <;>
    norm_num [minusRows,gridVector,coordinate,gridSum,rowQ,rowPartner,rowD,rowT,
      residues,Finset.sum_filter,Finset.sum_range_succ]

theorem entireRows_grid (k : ℕ) (f : ℕ → ℂ) (s : ℂ) (i : Fin 4) :
    entireRows (gridVector k f s) i=gridSum k f 420 (entireSpecs i) 0 s := by
  fin_cases i <;>
    norm_num [entireRows,gridVector,coordinate,gridSum,entireSpecs,residues,Finset.sum_filter,Finset.sum_range_succ]

def rowCoefficient (k : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 2) (n : ℕ) (s : ℂ) : ℂ :=
  taylorRowScalar k (rowL i) ((rowT i:ℝ)/420) (root 35 f (rowQ i)*ε*I^k) n s

def rowError (k : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 2) (M : ℕ) (s : ℂ) : ℂ :=
  mellin (frickeError k (fullCoefficients (twisted f (rowQ i)) k)
    (rowL i) ((rowT i:ℝ)/420) (root 35 f (rowQ i)*ε*I^k) (M+1)) s

theorem original_taylor_rows {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε) (i : Fin 2) :
    ∃ B : ℝ, ∀ M : ℕ,
      AnalyticOnNhd ℂ (rowError (2*m) f ε i M) {s : ℂ | B-((M:ℝ)+1)<s.re} ∧
      ∀ s : ℂ, B<s.re →
        plusRows (gridVector (2*m) f s) i-
          rowCoefficient (2*m) f ε i 0 s*minusRows (gridVector (2*m) f s) i=
        rowError (2*m) f ε i M s+∑ n∈Finset.range M,
          rowCoefficient (2*m) f ε i (n+1) s*
            minusRows (gridVector (2*m) f (s+((n:ℂ)+1))) i := by
  obtain ⟨B,hB⟩ := QuantitativeArithmeticCoherentTaylor.closed_grid_taylor_rows_of_law
    (by decide : 0<35) (even_two_mul m) hf ε hlaw 420 (rowQ i) (by decide)
    (specs_valid i).1 (specs_valid i).2.1 (rowT i) (rowD i)
    (specs_valid i).2.2.1 (specs_valid i).2.2.2.1 (specs_valid i).2.2.2.2
  refine ⟨B,?_⟩
  intro M
  refine ⟨(hB M).1,?_⟩
  intro s hs
  simpa only [plusRows_grid,minusRows_grid,rowCoefficient,rowError,rowPartner,rowL,Nat.cast_ofNat] using (hB M).2 s hs

theorem original_entire_rows {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) :
    (∀ i : Fin 4, ∀ s : ℂ, AnalyticAt ℂ (ramanujanEntire 35 k f (entireSpecs i)) s) ∧
      ∃ B : ℝ, ∀ i : Fin 4, ∀ s : ℂ, B<s.re →
        ramanujanEntire 35 k f (entireSpecs i) s=entireRows (gridVector k f s) i := by
  have hh (i : Fin 4) := original_ramanujan_entire (by decide : 0<35) hk hf (entireSpecs_valid i).1
  constructor
  · exact fun i => (hh i).1
  · choose b hb using fun i => (hh i).2
    let B : ℝ := Finset.univ.sup' Finset.univ_nonempty b
    refine ⟨B,?_⟩
    intro i s hs
    have hbi : b i≤B := Finset.le_sup' b (Finset.mem_univ i)
    rw [entireRows_grid,hb i s (lt_of_le_of_lt hbi hs)]
    have hg := ramanujanAdditive_grid k f (by decide : 0<420)
      (entireSpecs_valid i).1 (entireSpecs_valid i).2 0 s
    simpa only [Int.cast_zero,zero_div,gridSum] using hg

#print axioms original_taylor_rows
#print axioms original_entire_rows
end QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan
end
end

/-! ## ThirtyFiveChiFourSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
open Complex Matrix SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (sourceIndex targetIndex gridVector)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan (plusRows minusRows entireRows)

inductive RowKind where
  | group : Fin 29 → RowKind
  | taylor : Fin 2 → RowKind
  | entire : Fin 4 → RowKind
  deriving DecidableEq

def rowKind : Fin 35 → RowKind :=
  ![.entire 0,.group 0,.group 1,.group 2,.group 3,.group 4,.group 5,.group 6,.group 7,.group 8,.group 9,.group 10,.group 11,.group 12,.group 13,.group 14,.group 15,.group 16,.group 17,.group 18,.group 19,.group 20,.group 21,.group 22,.group 23,.group 24,.group 25,.group 26,.group 27,.group 28,.entire 1,.taylor 0,.entire 2,.taylor 1,.entire 3]

def assemble (G : Fin 29 → ℂ) (T : Fin 2 → ℂ) (E : Fin 4 → ℂ) (i : Fin 35) : ℂ :=
  match rowKind i with
  | .group j => G j
  | .taylor j => T j
  | .entire j => E j

def groupCoefficient (m : ℕ) (ε : ℂ) (i : Fin 29) (n : ℕ) (s : ℂ) : ℂ :=
  QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows.rowCoefficient m (ε*I^(2*m)) i n s

def taylorCoefficient (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 2) (n : ℕ) (s : ℂ) : ℂ :=
  QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan.rowCoefficient (2*m) f ε i n s

def leadingRows (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v : Fin 35 → ℂ) : Fin 35 → ℂ :=
  assemble (fun i => v (sourceIndex i)-groupCoefficient m ε i 0 s*v (targetIndex i))
    (fun i => plusRows v i-taylorCoefficient m f ε i 0 s*minusRows v i) (entireRows v)

def shiftRows (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (v : Fin 35 → ℂ) : Fin 35 → ℂ :=
  assemble (fun i => groupCoefficient m ε i (n+1) s*v (targetIndex i))
    (fun i => taylorCoefficient m f ε i (n+1) s*minusRows v i) 0

def leadingLinear (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : (Fin 35 → ℂ) →ₗ[ℂ] (Fin 35 → ℂ) where
  toFun := leadingRows m f ε s
  map_add' := by
    intro v w
    funext i
    fin_cases i <;> simp [leadingRows,assemble,rowKind,plusRows,minusRows,entireRows] <;> ring
  map_smul' := by
    intro c v
    funext i
    fin_cases i <;> simp [leadingRows,assemble,rowKind,plusRows,minusRows,entireRows,smul_eq_mul] <;> ring

def shiftLinear (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : (Fin 35 → ℂ) →ₗ[ℂ] (Fin 35 → ℂ) where
  toFun := shiftRows m f ε n s
  map_add' := by
    intro v w
    funext i
    fin_cases i <;> simp [shiftRows,assemble,rowKind,minusRows] <;> ring
  map_smul' := by
    intro c v
    funext i
    fin_cases i <;> simp [shiftRows,assemble,rowKind,minusRows,smul_eq_mul] <;> ring

def leadingMatrix (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) : Matrix (Fin 35) (Fin 35) ℂ :=
  (leadingLinear m f ε s).toMatrix'
def shiftMatrix (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) : Matrix (Fin 35) (Fin 35) ℂ :=
  (shiftLinear m f ε n s).toMatrix'

theorem leadingMatrix_mulVec (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v : Fin 35 → ℂ) :
    leadingMatrix m f ε s *ᵥ v=leadingRows m f ε s v := LinearMap.toMatrix'_mulVec _ _
theorem shiftMatrix_mulVec (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (v : Fin 35 → ℂ) :
    shiftMatrix m f ε n s *ᵥ v=shiftRows m f ε n s v := LinearMap.toMatrix'_mulVec _ _

#print axioms leadingMatrix_mulVec
#print axioms shiftMatrix_mulVec
end QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
end
end

/-! ## ThirtyFiveChiFourEntries -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
open Complex Matrix
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (rate matrixIndex source rate_eq row_den_ne_zero)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan (specs_valid)

theorem groupCoefficient_analytic (m : ℕ) (ε : ℂ) (i : Fin 29) (n : ℕ) (s : ℂ) :
    AnalyticAt ℂ (groupCoefficient m ε i n) s := by
  have hr : (rate (matrixIndex i) (source i):ℝ)≠0 := by
    rw [← rate_eq]
    exact pow_ne_zero _ (row_den_ne_zero i)
  have hc : (rate (matrixIndex i) (source i):ℂ)≠0 := by exact_mod_cast hr
  have hp : AnalyticAt ℂ (fun z : ℂ => (rate (matrixIndex i) (source i):ℂ)^(z-(m:ℂ))) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hc]
    fun_prop
  exact ((analyticAt_const.mul hp).mul analyticAt_const).mul
    (SmallLevelTaylor.binomial_shift_analytic (2*m) n s)

theorem taylorCoefficient_analytic (m : ℕ) (f : ℕ → ℂ) (ε : ℂ) (i : Fin 2) (n : ℕ) (s : ℂ) :
  AnalyticAt ℂ (taylorCoefficient m f ε i n) s := by
  apply SmallLevelTaylor.taylorRowScalar_analytic
  · exact_mod_cast Nat.lcm_pos (by decide : 0<35) (pow_pos (specs_valid i).1 2)
  · exact div_ne_zero (by exact_mod_cast (specs_valid i).2.2.1) (by norm_num)

theorem leadingMatrix_apply (m : ℕ) (f : ℕ→ℂ) (ε s : ℂ) (i j : Fin 35) :
    leadingMatrix m f ε s i j=leadingRows m f ε s (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _
theorem shiftMatrix_apply (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (s : ℂ) (i j : Fin 35) :
    shiftMatrix m f ε n s i j=shiftRows m f ε n s (Pi.single j 1) i :=
  LinearMap.toMatrix'_apply _ _ _

theorem leadingMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε x : ℂ) (i j : Fin 35) :
    AnalyticAt ℂ (fun s => leadingMatrix m f ε s i j) x := by
  simp only [leadingMatrix_apply]
  cases hi : rowKind i with
  | group a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const.sub ((groupCoefficient_analytic m ε a 0 x).mul analyticAt_const)
  | taylor a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const.sub ((taylorCoefficient_analytic m f ε a 0 x).mul analyticAt_const)
  | entire a =>
    simp only [leadingRows,assemble,hi]
    exact analyticAt_const

theorem shiftMatrix_analytic (m : ℕ) (f : ℕ→ℂ) (ε : ℂ) (n : ℕ) (x : ℂ) (i j : Fin 35) :
    AnalyticAt ℂ (fun s => shiftMatrix m f ε n s i j) x := by
  simp only [shiftMatrix_apply]
  cases hi : rowKind i with
  | group a =>
    simp only [shiftRows,assemble,hi]
    exact (groupCoefficient_analytic m ε a (n+1) x).mul analyticAt_const
  | taylor a =>
    simp only [shiftRows,assemble,hi]
    exact (taylorCoefficient_analytic m f ε a (n+1) x).mul analyticAt_const
  | entire a =>
    simp only [shiftRows,assemble,hi,Pi.zero_apply]
    exact analyticAt_const

#print axioms leadingMatrix_analytic
#print axioms shiftMatrix_analytic
end QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
end
end

/-! ## ThirtyFiveChiFourOriginalSystem -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
open Complex Matrix Set SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (gridVector)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan (rowError entireSpecs)

/-- The full 35-coordinate system consists of actual original-input rows.
Every positive Taylor shift stays in the same 35 coordinates. -/
theorem original_matrix_system {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε) :
    ∃ B : ℝ, ∃ error : ℕ → ℂ → Fin 35 → ℂ,
      (∀ i : Fin 35, ∀ s : ℂ, B<s.re → AnalyticAt ℂ (fun z => gridVector (2*m) f z i) s) ∧
      (∀ M : ℕ, ∀ i : Fin 35, ∀ s : ℂ, B-((M:ℝ)+1)<s.re →
        AnalyticAt ℂ (fun z => error M z i) s) ∧
      ∀ M : ℕ, ∀ s : ℂ, B<s.re →
        leadingMatrix m f ε s *ᵥ gridVector (2*m) f s=
          error M s+∑ n∈Finset.range M,
            shiftMatrix m f ε n s *ᵥ gridVector (2*m) f (s+((n:ℂ)+1)) := by
  have hg (i : Fin 29) := QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows.original_word_rows
    hm hf ε hε hlaw i
  choose bG errG hG using hg
  have ht (i : Fin 2) := QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan.original_taylor_rows
    hf ε hlaw i
  choose bT hT using ht
  obtain ⟨hRE,BR,hR⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan.original_entire_rows
    (by omega : 0<2*m) hf
  obtain ⟨BF,hF⟩ := original_common_halfplane hf
  let BG : ℝ := Finset.univ.sup' Finset.univ_nonempty bG
  let BT : ℝ := Finset.univ.sup' Finset.univ_nonempty bT
  let B : ℝ := max BG (max BT (max BR BF))
  have hBG (i : Fin 29) : bG i≤B := (Finset.le_sup' bG (Finset.mem_univ i)).trans (le_max_left _ _)
  have hBT (i : Fin 2) : bT i≤B := (Finset.le_sup' bT (Finset.mem_univ i)).trans
    ((le_max_left _ _).trans (le_max_right _ _))
  have hBR : BR≤B := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hBF : BF≤B := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  let error : ℕ → ℂ → Fin 35 → ℂ := fun M s =>
    assemble (fun i => errG i M s) (fun i => rowError (2*m) f ε i M s)
      (fun i => ramanujanEntire 35 (2*m) f (entireSpecs i) s)
  refine ⟨B,error,?_,?_,?_⟩
  · intro i s hs
    exact (hF (((QuantitativeArithmeticSmallLevelThirtyFiveChiFour.coordinate i).val:ℝ)/420)
      s (lt_of_le_of_lt hBF hs)).1
  · intro M i s hs
    have hg' (j : Fin 29) : AnalyticAt ℂ (errG j M) s := by
      apply (hG j M).1 s
      change bG j-((M:ℝ)+1)<s.re
      linarith [hBG j]
    have ht' (j : Fin 2) : AnalyticAt ℂ (rowError (2*m) f ε j M) s := by
      apply (hT j M).1 s
      change bT j-((M:ℝ)+1)<s.re
      linarith [hBT j]
    cases hi : rowKind i with
    | group j => simpa only [error,assemble,hi] using hg' j
    | taylor j => simpa only [error,assemble,hi] using ht' j
    | entire j => simpa only [error,assemble,hi] using hRE j s
  · intro M s hs
    rw [leadingMatrix_mulVec]
    simp_rw [shiftMatrix_mulVec]
    funext i
    simp only [Pi.add_apply,Finset.sum_apply]
    cases hi : rowKind i with
    | group j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,groupCoefficient] using
        (hG j M).2 s (lt_of_le_of_lt (hBG j) hs)
    | taylor j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,taylorCoefficient] using
        (hT j M).2 s (lt_of_le_of_lt (hBT j) hs)
    | entire j =>
      simpa only [leadingRows,shiftRows,error,assemble,hi,Pi.zero_apply,
        Finset.sum_const_zero,add_zero] using (hR j s (lt_of_le_of_lt hBR hs)).symm

#print axioms original_matrix_system
end QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
end
end

/-! ## ThirtyFiveChiFourLaurent -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
open Complex SmallLevelTaylor FinitenessNormalizedTwistProduct
open QuantitativeArithmeticSmallLevelThirtyFiveKnownWords (fourPrimeMonomial rational_four_prime_power primeParameter)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (rate raw rawDen matrixIndex source sign isFricke)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan (rowQ rowT rowL)
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan (phaseRoot badFive root_five)

def groupPowers : Fin 29 → ℤ×ℤ×ℤ×ℤ :=
  ![(2,0,-1,-1),(0,2,-1,-1),(2,-2,1,-1),(-2,0,-1,1),(4,0,-1,-1),(0,0,1,-1),(4,-2,1,-1),(2,0,1,-1),(2,0,-1,1),(0,2,1,-1),(4,0,1,-1),(0,2,-1,1),(-2,0,-1,-1),(2,0,0,0),(-2,0,0,0),(4,0,0,0),(0,2,0,0),(0,2,0,0),(2,0,0,0),(-2,0,0,0),(-4,0,0,0),(0,-2,0,0),(0,0,0,0),(2,0,0,0),(-2,2,0,0),(-2,2,0,0),(0,0,0,0),(0,2,0,0),(-2,0,-1,1)]

theorem group_rate_certificate (i : Fin 29) :
    rate (matrixIndex i) (source i)=(2:ℚ)^(groupPowers i).1*(3:ℚ)^(groupPowers i).2.1*
      (5:ℚ)^(groupPowers i).2.2.1*(7:ℚ)^(groupPowers i).2.2.2 := by
  fin_cases i <;> norm_num [rate,rawDen,raw,matrixIndex,source,groupPowers,Matrix.det_fin_two]

def symbolicGroup (χ X Y Z W : ℂ) (i : Fin 29) : ℂ :=
  sign χ (matrixIndex i)*fourPrimeMonomial (groupPowers i) X Y Z W

theorem groupCoefficient_laurent (m : ℕ) (ε s : ℂ) (i : Fin 29) :
    groupCoefficient m ε i 0 s=symbolicGroup (phaseRoot m ε)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 5 m s) (primeParameter 7 m s) i := by
  simp only [groupCoefficient,QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows.rowCoefficient,
    Nat.cast_zero,add_zero,pow_zero,Ring.choose_zero_right,mul_one]
  rw [rational_four_prime_power _ _ (group_rate_certificate i)]
  rfl

theorem root_four (f : ℕ → ℂ) : root 35 f 4=1 := by
  have hp : (4:ℕ).primeFactors={2} := by
    rw [show (4:ℕ)=2*2 by decide,Nat.primeFactors_mul (by decide) (by decide)]
    norm_num
  norm_num [root,hp,FinitenessNormalizedTwistLocal.sign]

def taylorPowers : Fin 2 → ℤ×ℤ×ℤ×ℤ := ![(0,0,1,-1),(-4,0,0,1)]
def taylorSign (χ u : ℂ) (i : Fin 2) : ℂ := ![χ,-χ*u] i

def symbolicTaylor (χ u X Y Z W : ℂ) (i : Fin 2) : ℂ :=
  taylorSign χ u i*fourPrimeMonomial (taylorPowers i) X Y Z W

theorem taylor_rate_certificate (i : Fin 2) :
    (rowL i:ℚ)*((rowT i:ℚ)/420)^2=(2:ℚ)^(taylorPowers i).1*(3:ℚ)^(taylorPowers i).2.1*
      (5:ℚ)^(taylorPowers i).2.2.1*(7:ℚ)^(taylorPowers i).2.2.2 := by
  fin_cases i <;> norm_num [rowL,rowQ,rowT,taylorPowers]

theorem taylorCoefficient_laurent (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (i : Fin 2) :
    taylorCoefficient m f ε i 0 s=symbolicTaylor (phaseRoot m ε) (badFive f)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 5 m s) (primeParameter 7 m s) i := by
  have hsign : root 35 f (rowQ i)*ε*I^(2*m)=taylorSign (phaseRoot m ε) (badFive f) i := by
    fin_cases i
    · change root 35 f 4*ε*I^(2*m)=phaseRoot m ε
      rw [root_four]
      simp [phaseRoot]
    · change root 35 f 5*ε*I^(2*m)= -(phaseRoot m ε)*badFive f
      rw [root_five]
      unfold phaseRoot
      ring
  have hex : s-((2*m:ℕ):ℂ)/2=s-(m:ℂ) := by push_cast; ring
  have hc : (((rowL i:ℝ)*((rowT i:ℝ)/420)^2:ℝ):ℂ)=
      (((rowL i:ℚ)*((rowT i:ℚ)/420)^2:ℚ):ℂ) := by push_cast; rfl
  simp only [taylorCoefficient,QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan.rowCoefficient,
    taylorRowScalar,pow_zero,Ring.choose_zero_right,mul_one,hex,hc,hsign]
  rw [rational_four_prime_power _ _ (taylor_rate_certificate i)]
  rfl

#print axioms groupCoefficient_laurent
#print axioms taylorCoefficient_laurent
end QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
end
end

/-! ## ThirtyFiveChiFour -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour

/-- The 35 selected original-row formulas, with global Fricke sign E and
bad-five sign u. The bad-seven sign and good-prime eigenvalues do not occur.
These are explicit algebraic rows, not assumed original-input consequences. -/
def selectedRows (E u X Y Z W : ℂ) (rho : Fin 420 → ℂ) : Fin 35 → ℂ :=
  ![-- ['ginf', 0, 1, -35, 0, 0]
    ((1))*rho 0,
    -- ['g', 0, 1, -35, 0, -1, 24]
    ((1))*rho 24 + (((-1)*E*X^2)/(Z*W))*rho 210,
    -- ['g', 0, 1, -35, 0, -1, 36]
    ((1))*rho 36 + (((-1)*E*Y^2)/(Z*W))*rho 280,
    -- ['g', 0, 1, -35, 0, -1, 40]
    ((1))*rho 40 + (((-1)*E*X^2*Z)/(Y^2*W))*rho 294,
    -- ['g', 0, 1, -35, 0, -1, 42]
    ((1))*rho 42 + (((-1)*E*W)/(X^2*Z))*rho 300,
    -- ['g', 0, 1, -35, 0, -1, 48]
    ((1))*rho 48 + (((-1)*E*X^4)/(Z*W))*rho 315,
    -- ['g', 0, 1, -35, 0, -1, 60]
    ((1))*rho 60 + (((-1)*E*Z)/(W))*rho 336,
    -- ['g', 0, 1, -35, 0, -1, 80]
    ((1))*rho 80 + (((-1)*E*X^4*Z)/(Y^2*W))*rho 357,
    -- ['g', 0, 1, -35, 0, -1, 120]
    ((1))*rho 120 + (((-1)*E*X^2*Z)/(W))*rho 378,
    -- ['g', 0, 1, -35, 0, -1, 168]
    ((1))*rho 168 + (((-1)*E*X^2*W)/(Z))*rho 390,
    -- ['g', 0, 1, -35, 0, -1, 180]
    ((1))*rho 180 + (((-1)*E*Y^2*Z)/(W))*rho 392,
    -- ['g', 0, 1, -35, 0, -1, 240]
    ((1))*rho 240 + (((-1)*E*X^4*Z)/(W))*rho 399,
    -- ['g', 0, 1, -35, 0, -1, 252]
    ((1))*rho 252 + (((-1)*E*Y^2*W)/(Z))*rho 400,
    -- ['g', 0, 1, -35, 35, -1, 414]
    (((-1)*E)/(X^2*Z*W))*rho 0 + ((1))*rho 414,
    -- ['g', 2, -1, -105, 53, 1, 204]
    ((1))*rho 204 + ((-1)*X^2)*rho 414,
    -- ['g', 2, -1, -105, 53, 1, 210]
    (((-1))/(X^2))*rho 0 + ((1))*rho 210,
    -- ['g', 2, -1, -35, 18, 1, 168]
    ((1))*rho 168 + ((-1)*X^4)*rho 399,
    -- ['g', 2, -1, -35, 18, 1, 180]
    ((1))*rho 180 + ((-1)*Y^2)*rho 400,
    -- ['g', 3, -2, 35, -23, 1, 240]
    ((-1)*Y^2)*rho 40 + ((1))*rho 240,
    -- ['g', 3, -2, 35, -23, 1, 252]
    ((-1)*X^2)*rho 42 + ((1))*rho 252,
    -- ['g', 3, -2, 35, -23, 1, 270]
    (((-1))/(X^2))*rho 60 + ((1))*rho 270,
    -- ['g', 3, -2, 35, -23, 1, 273]
    (((-1))/(X^4))*rho 84 + ((1))*rho 273,
    -- ['g', 3, -2, 35, -23, 1, 280]
    (((-1))/(Y^2))*rho 0 + ((1))*rho 280,
    -- ['g', 3, -2, 35, -23, 1, 288]
    ((-1))*rho 24 + ((1))*rho 288,
    -- ['g', 3, -1, -35, 12, 1, 120]
    ((1))*rho 120 + ((-1)*X^2)*rho 390,
    -- ['g', 3, -1, -35, 12, 1, 126]
    ((1))*rho 126 + (((-1)*Y^2)/(X^2))*rho 392,
    -- ['g', 6, -5, 35, -29, 1, 330]
    (((-1)*Y^2)/(X^2))*rho 80 + ((1))*rho 330,
    -- ['g', 6, -5, 35, -29, 1, 336]
    ((-1))*rho 84 + ((1))*rho 336,
    -- ['g', 12, -7, -245, 143, 1, 240]
    ((1))*rho 240 + ((-1)*Y^2)*rho 400,
    -- ['g', 35, -18, 70, -35, -1, 189]
    ((1))*rho 189 + (((-1)*E*W)/(X^2*Z))*rho 270,
    -- ['R', 4]
    ((1))*rho 105 + ((1))*rho 315,
    -- ['F', 4, 15]
    (((-1)*E*Z)/(W))*rho 84 + ((1))*rho 120 + (((-1)*E*Z)/(W))*rho 294 + ((1))*rho 330,
    -- ['R', 5]
    ((1))*rho 84 + ((1))*rho 168 + ((1))*rho 252 + ((1))*rho 336,
    -- ['F', 5, 21]
    ((E*u*W)/(X^4))*rho 36 + ((1))*rho 105 + ((E*u*W)/(X^4))*rho 120 + ((1))*rho 189 + ((E*u*W)/(X^4))*rho 204 + ((1))*rho 273 + ((E*u*W)/(X^4))*rho 288 + ((1))*rho 357,
    -- ['R', 10]
    ((1))*rho 42 + ((1))*rho 126 + ((1))*rho 294 + ((1))*rho 378]

/-- Both Fricke signs and both ramified-five signs: the exact selected
row system annihilates the chi4 target even at singular spectral parameters.
Only geometric prime powers are required to be nonzero. -/
theorem target (E u X Y Z W : ℂ) (hE : E= -1 ∨ E=1) (hu : u= -1 ∨ u=1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (rho : Fin 420 → ℂ) (hrows : selectedRows E u X Y Z W rho=0) :
    rho 105-rho 315=0 := by
  rcases hE with rfl|rfl <;> rcases hu with rfl|rfl
  · apply target_case0 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows0, neg_mul, one_mul, neg_neg] using hrows
  · apply target_case2 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows2, neg_mul, one_mul, neg_neg] using hrows
  · apply target_case4 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows4, neg_mul, one_mul, neg_neg] using hrows
  · apply target_case6 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows6, neg_mul, one_mul, neg_neg] using hrows

#print axioms target

end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourMatrix -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Matrix

/-- All coordinates appearing in the selected rows vanish in their kernel. -/
theorem selected_kernel (E u X Y Z W : ℂ) (hE : E= -1 ∨ E=1) (hu : u= -1 ∨ u=1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (rho : Fin 420 → ℂ) (hrows : selectedRows E u X Y Z W rho=0) :
    ∀ i : Fin 35, rho (coordinate i)=0 := by
  rcases hE with rfl|rfl <;> rcases hu with rfl|rfl
  · apply selected_kernel_case0 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows0, neg_mul, one_mul, neg_neg] using hrows
  · apply selected_kernel_case2 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows2, neg_mul, one_mul, neg_neg] using hrows
  · apply selected_kernel_case4 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows4, neg_mul, one_mul, neg_neg] using hrows
  · apply selected_kernel_case6 X Y Z W hX hY hZ hW rho
    simpa only [selectedRows, selectedRows6, neg_mul, one_mul, neg_neg] using hrows

/-- Zero extension from the selected 35 coordinates to the 420-grid. -/
def embed (v : Fin 35 → ℂ) (j : Fin 420) : ℂ :=
  match j.val with
  | 0 => v 0
  | 24 => v 1
  | 36 => v 2
  | 40 => v 3
  | 42 => v 4
  | 48 => v 5
  | 60 => v 6
  | 80 => v 7
  | 84 => v 8
  | 105 => v 9
  | 120 => v 10
  | 126 => v 11
  | 168 => v 12
  | 180 => v 13
  | 189 => v 14
  | 204 => v 15
  | 210 => v 16
  | 240 => v 17
  | 252 => v 18
  | 270 => v 19
  | 273 => v 20
  | 280 => v 21
  | 288 => v 22
  | 294 => v 23
  | 300 => v 24
  | 315 => v 25
  | 330 => v 26
  | 336 => v 27
  | 357 => v 28
  | 378 => v 29
  | 390 => v 30
  | 392 => v 31
  | 399 => v 32
  | 400 => v 33
  | 414 => v 34
  | _ => 0

theorem embed_coordinate (v : Fin 35 → ℂ) (i : Fin 35) : embed v (coordinate i)=v i := by
  fin_cases i <;> rfl

def reducedRows (E u X Y Z W : ℂ) (v : Fin 35 → ℂ) : Fin 35 → ℂ :=
  selectedRows E u X Y Z W (embed v)

def selectedLinear (E u X Y Z W : ℂ) : (Fin 420 → ℂ) →ₗ[ℂ] (Fin 35 → ℂ) where
  toFun := selectedRows E u X Y Z W
  map_add' := by
    intro v w
    funext i
    fin_cases i <;> dsimp [selectedRows] <;> ring1
  map_smul' := by
    intro c v
    funext i
    fin_cases i <;> dsimp [selectedRows] <;> ring1

def embedLinear : (Fin 35 → ℂ) →ₗ[ℂ] (Fin 420 → ℂ) where
  toFun := embed
  map_add' := by
    intro v w
    funext j
    dsimp only [embed, Pi.add_apply]
    split <;> simp
  map_smul' := by
    intro c v
    funext j
    dsimp only [embed, Pi.smul_apply]
    split <;> simp

def reducedLinear (E u X Y Z W : ℂ) : (Fin 35 → ℂ) →ₗ[ℂ] (Fin 35 → ℂ) :=
  (selectedLinear E u X Y Z W).comp embedLinear

def reducedMatrix (E u X Y Z W : ℂ) : Matrix (Fin 35) (Fin 35) ℂ :=
  (reducedLinear E u X Y Z W).toMatrix'

theorem reducedMatrix_mulVec (E u X Y Z W : ℂ) (v : Fin 35 → ℂ) :
    reducedMatrix E u X Y Z W *ᵥ v=reducedRows E u X Y Z W v :=
  LinearMap.toMatrix'_mulVec _ _

/-- A 35-coordinate subsystem is nonsingular at every nonzero geometric
specialization, for both signs. There is no residual spectral locus and no
Hecke eigenvalue hypothesis. The actual analytic row realization is separate. -/
theorem reducedMatrix_det_ne_zero (E u X Y Z W : ℂ)
    (hE : E= -1 ∨ E=1) (hu : u= -1 ∨ u=1)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) :
    (reducedMatrix E u X Y Z W).det≠0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  have hz : reducedMatrix E u X Y Z W *ᵥ (v-w)=0 := by
    rw [Matrix.mulVec_sub,hvw,sub_self]
  rw [reducedMatrix_mulVec] at hz
  have he := selected_kernel E u X Y Z W hE hu hX hY hZ hW (embed (v-w)) hz
  apply sub_eq_zero.mp
  funext i
  simpa only [embed_coordinate, Pi.zero_apply] using he i

#print axioms selected_kernel
#print axioms embed_coordinate
#print axioms reducedMatrix_det_ne_zero
end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourComparison -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
open Complex Matrix
open QuantitativeArithmeticSmallLevelThirtyFiveKnownWords (fourPrimeMonomial primeParameter)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (sourceIndex targetIndex matrixIndex sign isFricke)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRamanujan (plusRows minusRows entireRows)
open QuantitativeArithmeticSmallLevelThirtyFiveChiFour (selectedRows embed reducedMatrix)
open QuantitativeArithmeticSmallLevelThirtyFiveGridRamanujan (phaseRoot phaseRoot_sign badFive badFive_sign)

def symbolicRows (χ u X Y Z W : ℂ) (v : Fin 35 → ℂ) : Fin 35 → ℂ :=
  assemble (fun i => v (sourceIndex i)-symbolicGroup χ X Y Z W i*v (targetIndex i))
    (fun i => plusRows v i-symbolicTaylor χ u X Y Z W i*minusRows v i) (entireRows v)

/-- Exact rational comparison with the already checked algebraic certificate. -/
theorem symbolic_rows (χ u X Y Z W : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0) (v : Fin 35 → ℂ) :
    symbolicRows χ u X Y Z W v=selectedRows χ u X Y Z W (embed v) := by
  funext i
  fin_cases i <;>
    norm_num [symbolicRows,assemble,rowKind,symbolicGroup,symbolicTaylor,taylorSign,
      groupPowers,taylorPowers,fourPrimeMonomial,sign,isFricke,matrixIndex,
      sourceIndex,targetIndex,plusRows,minusRows,entireRows,selectedRows,embed] <;>
    field_simp [hX,hY,hZ,hW] <;> ring

theorem actual_leading_rows (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) (v : Fin 35 → ℂ) :
    leadingRows m f ε s v=selectedRows (phaseRoot m ε) (badFive f)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 5 m s) (primeParameter 7 m s) (embed v) := by
  have he : leadingRows m f ε s v=symbolicRows (phaseRoot m ε) (badFive f)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 5 m s) (primeParameter 7 m s) v := by
    funext i
    cases hi : rowKind i <;> simp only [leadingRows,symbolicRows,assemble,hi,
      groupCoefficient_laurent,taylorCoefficient_laurent]
  rw [he]
  apply symbolic_rows <;> exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

theorem actual_leading_matrix (m : ℕ) (f : ℕ → ℂ) (ε s : ℂ) :
    leadingMatrix m f ε s=reducedMatrix (phaseRoot m ε) (badFive f)
      (primeParameter 2 m s) (primeParameter 3 m s) (primeParameter 5 m s) (primeParameter 7 m s) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [leadingMatrix_mulVec,QuantitativeArithmeticSmallLevelThirtyFiveChiFour.reducedMatrix_mulVec]
  exact actual_leading_rows m f ε s v

/-- No spectral parameters remain in this determinant: it never vanishes. -/
theorem original_leading_nonsingular {m : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1) (s : ℂ) : (leadingMatrix m f ε s).det≠0 := by
  rw [actual_leading_matrix]
  apply QuantitativeArithmeticSmallLevelThirtyFiveChiFour.reducedMatrix_det_ne_zero
    _ _ _ _ _ _ (phaseRoot_sign m hε).symm (badFive_sign hf.toEulerData).symm <;>
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

#print axioms symbolic_rows
#print axioms actual_leading_matrix
#print axioms original_leading_nonsingular
end QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
end
end

/-! ## ThirtyFiveTwelveMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveTwelve
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem sqrt_twelve_conductor : Real.sqrt 5040=12*Real.sqrt 35 := by
  rw [show (5040:ℝ)=144*35 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem fricke_branch (a : Fin 4) :
    fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ (generator a)*translation (center a)=
    translation (center a)*fricke 5040 (by decide) := by
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases a <;> apply Units.ext <;> ext i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [fricke,generator,center,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_twelve_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

#print axioms fricke_branch
end QuantitativeArithmeticSmallLevelThirtyFiveTwelve
end
end

/-! ## ThirtyFiveTwelveEntire -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveTwelve
open SmallLevelNormalized SmallLevelOriginal QuantitativeArithmeticTranslatedFricke
  Complex Filter Set MeasureTheory FinitenessPolynomialSeries FinitenessFourierConstruction
  Matrix UpperHalfPlane
open scoped Topology MatrixGroups ModularForm

def centeredMellin (m : ℕ) (f : ℕ → ℂ) (j : Fin 4) : ℂ → ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 5040
    (SmallLevelAdditive.coefficients (FinitenessOriginalFourier.fullCoefficients f (2*m)) (center j)))

/-- Four individual Fricke equations with a common original sign. -/
theorem original_centers_with_fricke {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f (χ/Complex.I^(2*m)) ∧
      fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 35 (by decide)=χ • fourierFunction (2*m) f ∧
      ∀ j : Fin 4,
      (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center j))
        ∣[((2*m:ℕ):ℤ)] fricke 5040 (by decide)=
      χ • (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center j)) := by
  obtain ⟨ε,hε,hlaw⟩ := QuantitativeArithmeticCoherentTaylor.original_coherent_law (by decide : 0<35) hf
  let χ : ℂ := ε*Complex.I^(2*m)
  obtain ⟨hχ,hF⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law (by decide : 0<35) m ε hε hlaw
  have hlawχ : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f (χ/Complex.I^(2*m)) := by
    simpa only [χ,mul_div_cancel_right₀ _ (pow_ne_zero _ Complex.I_ne_zero)] using hlaw
  refine ⟨χ,hχ,hlawχ,hF,?_⟩
  intro j
  exact translated_slash 35 5040 (2*m) (by decide) (by decide) _ χ _
    (SpecialLinearGroup.mapGL ℝ (generator j)) (by simp)
    hF (original_generators hm hf j) (fricke_branch j)

/-- Actual entire finite-order denominator-twelve Mellin transforms. -/
theorem original_centers_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f (χ/Complex.I^(2*m)) ∧
      ∀ j : Fin 4,
      Differentiable ℂ (centeredMellin m f j) ∧
      FinitenessFiniteOrder.Bound (centeredMellin m f j) ∧
      ∀ s : ℂ, centeredMellin m f j s=
        (χ/(Complex.I^(2*m)))*centeredMellin m f j ((2*m:ℕ)-s) := by
  obtain ⟨χ,hχ,hlaw,_hW,hF⟩ := original_centers_with_fricke hm hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  refine ⟨χ,hχ,hlaw,fun j => ?_⟩
  exact translated_mellin_entire 5040 (2*m) (by decide) (by omega) _
    (FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m))
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)) (center j) χ hχ
    (hF j)

#print axioms original_centers_with_fricke
#print axioms original_centers_entire
end QuantitativeArithmeticSmallLevelThirtyFiveTwelve
end
end

/-! ## ThirtyFiveChiFourNumerator -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open QuantitativeArithmeticSmallLevelThirtyFiveTwelve QuantitativeArithmeticMellinScale
  SmallLevelAdditive SmallLevelTaylor Complex Filter Set MeasureTheory
  FinitenessFourierConstruction FinitenessOriginalFourier

/-- The entire numerator before division by the Hecke polynomial. -/
def translateMellin (m : ℕ) (f : ℕ → ℂ) (r : ℝ) : ℂ → ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1 (coefficients (fullCoefficients f (2*m)) r))

def numerator (m : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  translateMellin m f (1/12) s-translateMellin m f (-1/12) s+
    translateMellin m f (5/12) s-translateMellin m f (-5/12) s

def denominator (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  1+(((3:ℝ)^(((k:ℝ)+1)/2):ℝ):ℂ)*f 3*(3:ℂ)^(-s)+(3:ℂ)^k*(9:ℂ)^(-s)

theorem original_numerator_entire (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    Differentiable ℂ (numerator m f) := by
  obtain ⟨χ,_,_,h⟩ := original_centers_entire hm hf
  have hj (j : Fin 4) : Differentiable ℂ (translateMellin m f (center j)) :=
    entire_at_one (by decide : 0<5040) _ (h j).1
  exact ((hj 0).sub (hj 1) |>.add (hj 2)).sub (hj 3)

theorem denominator_entire (k : ℕ) (f : ℕ → ℂ) : Differentiable ℂ (denominator k f) := by
  unfold denominator
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (9:ℂ)≠0)]
  fun_prop

/-- An exact original-input Hecke identity, identifying the quadratic-twist
numerator on a half-plane. No division or continuation premise is used. -/
theorem original_hecke_identity (m : ℕ) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ bound : ℝ, ∀ s : ℂ, bound<s.re →
      numerator m f s=denominator (2*m) f s*
        (original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) := by
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  obtain ⟨H,hH⟩ := original_additive_hecke hf (by decide : Nat.Prime 3) (by decide)
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
  have hp := hH (1/12) s hsH
  have hn := hH (-(1/12)) s hsH
  norm_num [Finset.sum_range_succ] at hp hn
  have h1 := hper (-(1/4))
  have h2 := hper (-(5/12))
  norm_num at h1 h2
  rw [h1] at hp
  rw [h2] at hn
  have h3 := hper (-(3/4))
  norm_num at h3
  rw [← h3] at hn
  have he (r : ℝ) : translateMellin m f r s=original (2*m) f r s := by
    unfold translateMellin
    have heq : FinitenessAllLevelAxisDecay.axis 1 (coefficients (fullCoefficients f (2*m)) r)=
        (fun y : ℝ => fourier (fullCoefficients f (2*m)) ((r:ℂ)+(y:ℂ)*I)) :=
      funext (axis_one_translate (fullCoefficients f (2*m)) r)
    rw [heq,(hB r s hsB).2]
  have hnum : numerator m f s=original (2*m) f (1/12) s-original (2*m) f (-1/12) s+
      original (2*m) f (5/12) s-original (2*m) f (-5/12) s := by
    simp only [numerator,he]
  rw [hnum]
  unfold denominator
  push_cast
  simp only [neg_div] at hp hn ⊢
  linear_combination hp-hn

#print axioms original_numerator_entire
#print axioms denominator_entire
#print axioms original_hecke_identity
end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourContinuation -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex Filter Set SmallLevelAdditive
open scoped Topology

/-- Three fixed evaluations exclude an identically zero denominator for
every complex Hecke eigenvalue, including zero. -/
theorem denominator_nonzero (k : ℕ) (f : ℕ → ℂ) : ∃ s : ℂ, denominator k f s≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  norm_num [denominator,Complex.cpow_neg,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/16:ℂ)*h0-(3/4:ℂ)*h1+(27/16:ℂ)*h2
  norm_num at hbad

/-- The actual odd additive combination modulo4 has a global meromorphic
continuation from the original hypotheses. Its only possible poles are
zeros of the explicit Hecke-3 denominator. Pole removal is still separate. -/
theorem original_continuation (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ (bound : ℝ) (G : ℂ → ℂ), (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) ∧
      (∀ s, denominator (2*m) f s≠0 → AnalyticAt ℂ G s) ∧
      (∀ x, G=ᶠ[𝓝[≠] x] (fun s => numerator m f s/denominator (2*m) f s)) := by
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  obtain ⟨H,hH⟩ := original_hecke_identity m hf
  obtain ⟨G,hG,hagree,hpole,hgerm⟩ := QuantitativeArithmeticEntireQuotient.continuation
    (numerator m f) (denominator (2*m) f)
    (fun s => original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) (max B H)
    (fun z => (original_numerator_entire m hm hf).analyticAt z)
    (fun z => (denominator_entire (2*m) f).analyticAt z)
    (denominator_nonzero (2*m) f)
    (fun z hz => (hB (1/4) z (lt_of_le_of_lt (le_max_left _ _) hz)).1.sub
      (hB (-(1/4)) z (lt_of_le_of_lt (le_max_left _ _) hz)).1)
    (fun z hz => hH z (lt_of_le_of_lt (le_max_right _ _) hz))
  exact ⟨max B H,G,hG,hagree,hpole,hgerm⟩

#print axioms denominator_nonzero
#print axioms original_continuation
end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourGridEntire -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
open Complex Matrix
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows (gridVector)

/-- The actual selected 35 additive twists all have entire continuations. -/
theorem original_entire_grid {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε) :
    ∃ B : ℝ, ∃ G : ℂ → Fin 35 → ℂ,
      (∀ i, Differentiable ℂ (fun z => G z i)) ∧
      ∀ z, B<z.re → G z=gridVector (2*m) f z := by
  obtain ⟨B,H,hF,hH,hrow⟩ := original_matrix_system hm hf ε hε hlaw
  obtain ⟨G,hG,hGF⟩ := QuantitativeArithmeticClosedEntire.closed_system_entire B
    (gridVector (2*m) f) (leadingMatrix m f ε) (shiftMatrix m f ε) H
    hF (leadingMatrix_analytic m f ε) (original_leading_nonsingular hf ε hε)
    (shiftMatrix_analytic m f ε) hH hrow
  exact ⟨B,G,hG,hGF⟩

#print axioms original_entire_grid
end QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem
end
end

/-! ## ThirtyFiveChiFourReflection -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex SmallLevelAdditive QuantitativeArithmeticSmallLevelThirtyFiveTwelve
open FinitenessOriginalFourier
def scaleThree (k : ℕ) (s : ℂ) : ℂ := (3:ℂ)^((k:ℂ)-2*s)
def reflectionMultiplier (k : ℕ) (ε s : ℂ) : ℂ := ε*(Real.sqrt 560:ℂ)^((k:ℂ)-2*s)

theorem scaleThree_ne_zero (k : ℕ) (s : ℂ) : scaleThree k s≠0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

theorem scaleThree_eq (k : ℕ) (s : ℂ) : scaleThree k s=(3:ℂ)^k*(9:ℂ)^(-s) := by
  have h4 : (9:ℂ)^(-s)=(3:ℂ)^(-2*s) := by
    have h := Complex.natCast_cpow_natCast_mul 3 2 (-s)
    norm_num only [Nat.cast_ofNat] at h
    rw [← h]
    congr 1
    ring
  rw [h4,← Complex.cpow_natCast,← Complex.cpow_add _ _ (by norm_num : (3:ℂ)≠0)]
  unfold scaleThree
  congr 1
  ring

theorem scaleThree_product (k : ℕ) (s : ℂ) : scaleThree k s*scaleThree k ((k:ℂ)-s)=1 := by
  unfold scaleThree
  rw [← Complex.cpow_add _ _ (by norm_num : (3:ℂ)≠0)]
  rw [show (k:ℂ)-2*s+((k:ℂ)-2*((k:ℂ)-s))=0 by ring,Complex.cpow_zero]

theorem center_conductor_factor (k : ℕ) (s : ℂ) :
    (Real.sqrt 5040:ℂ)^((k:ℂ)-2*s)=scaleThree k s*(Real.sqrt 560:ℂ)^((k:ℂ)-2*s) := by
  have hs : Real.sqrt 5040=3*Real.sqrt 560 := by
    rw [show (5040:ℝ)=9*560 by norm_num,Real.sqrt_mul (by norm_num)]
    norm_num
  rw [hs,Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤3) (Real.sqrt_nonneg _) _

theorem reflectionMultiplier_entire (k : ℕ) (ε : ℂ) : Differentiable ℂ (reflectionMultiplier k ε) := by
  have hn : (Real.sqrt 560:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold reflectionMultiplier
  simp_rw [Complex.cpow_def_of_ne_zero hn]
  fun_prop

theorem reflectionMultiplier_ne_zero (k : ℕ) {ε : ℂ} (hε : ε≠0) (s : ℂ) :
    reflectionMultiplier k ε s≠0 := by
  apply mul_ne_zero hε
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by norm_num)).ne'))

theorem reflectionMultiplier_even (m : ℕ) (ε s : ℂ) :
    reflectionMultiplier (2*m) ε s=ε*(560:ℂ)^((m:ℂ)-s) := by
  have hn : (Real.sqrt 560:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs : (Real.sqrt 560:ℂ)*(Real.sqrt 560:ℂ)=560 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ)≤560)
  have hp := Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg 560) (Real.sqrt_nonneg 560) ((m:ℂ)-s)
  rw [hs] at hp
  unfold reflectionMultiplier
  rw [show ((2*m:ℕ):ℂ)-2*s=((m:ℂ)-s)+((m:ℂ)-s) by push_cast; ring,
    Complex.cpow_add _ _ hn,← hp]


theorem denominator_reflection (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    denominator k f s=scaleThree k s*denominator k f ((k:ℂ)-s) := by
  have hp : scaleThree k s*(3:ℂ)^(-((k:ℂ)-s))=(3:ℂ)^(-s) := by
    unfold scaleThree
    rw [← Complex.cpow_add _ _ (by norm_num : (3:ℂ)≠0)]
    congr 1
    ring
  have hq := scaleThree_product k s
  unfold denominator
  rw [← scaleThree_eq,← scaleThree_eq]
  linear_combination -hq - (((3:ℝ)^(((k:ℝ)+1)/2):ℝ):ℂ)*f 3*hp

theorem original_numerator_reflection (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      ∀ s : ℂ, numerator m f s=scaleThree (2*m) s*reflectionMultiplier (2*m) ε s*
        numerator m f ((2*m:ℕ)-s) := by
  obtain ⟨χ,hχ,hlaw,hc⟩ := original_centers_entire hm hf
  let ε : ℂ := χ/I^(2*m)
  have hε : ε=1 ∨ ε= -1 := by
    have hi : I^(2*m)=(-1:ℂ)^m := by rw [pow_mul,I_sq]
    rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hχ with rfl|rfl <;> simp [ε,hi,h]
  have hp (j : Fin 4) (s : ℂ) :=
    QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection
      (by decide : 0<5040)
      (coefficients (fullCoefficients f (2*m)) (center j)) ε (hc j).2.2 s
  refine ⟨ε,hε,hlaw,fun s => ?_⟩
  have h0 := hp 0 s
  have h1 := hp 1 s
  have h2 := hp 2 s
  have h3 := hp 3 s
  norm_num only [center,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Nat.cast_ofNat] at h0 h1 h2 h3
  rw [center_conductor_factor] at h0 h1 h2 h3
  unfold numerator translateMellin reflectionMultiplier
  simp only [neg_div] at h0 h1 h2 h3 ⊢
  linear_combination h0-h1+h2-h3

theorem original_quadratic_functional_equation (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ (ε : ℂ) (bound : ℝ) (G : ℂ → ℂ), (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) ∧
      (∀ s, G s=ε*(560:ℂ)^((m:ℂ)-s)*G ((2*m:ℕ)-s)) ∧
      (∀ s, denominator (2*m) f s≠0 → AnalyticAt ℂ G s) := by
  obtain ⟨ε,hε,hlaw,hN⟩ := original_numerator_reflection m hm hf
  obtain ⟨B,G,hG,hagree,hpole,hgerm⟩ := original_continuation m hm hf
  have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
  have hraw (s : ℂ) : numerator m f s/denominator (2*m) f s=
      reflectionMultiplier (2*m) ε s*(numerator m f ((2*m:ℕ)-s)/denominator (2*m) f ((2*m:ℕ)-s)) := by
    rw [hN s,denominator_reflection (2*m) f s,mul_assoc,
      mul_div_mul_left _ _ (scaleThree_ne_zero (2*m) s)]
    ring
  have hfe := QuantitativeArithmeticQuadraticTwistReflection.normal_form_reflection
    (fun s => numerator m f s/denominator (2*m) f s) G
    (reflectionMultiplier (2*m) ε) ((2*m:ℕ):ℂ) hG
    (fun s => (reflectionMultiplier_entire (2*m) ε).analyticAt s)
    (reflectionMultiplier_ne_zero (2*m) hε0) hgerm hraw
  refine ⟨ε,B,G,hε,hlaw,hG,hagree,?_,hpole⟩
  intro s
  simpa only [reflectionMultiplier_even] using hfe s
#print axioms original_quadratic_functional_equation
end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourFiniteOrder -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex Filter Set SmallLevelTaylor SmallLevelAdditive
open QuantitativeArithmeticSmallLevelThirtyFiveTwelve
open scoped Topology

theorem original_numerator_bound (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    FinitenessFiniteOrder.Bound (numerator m f) := by
  obtain ⟨χ,_,_,h⟩ := original_centers_entire hm hf
  have hj (j : Fin 4) : FinitenessFiniteOrder.Bound (translateMellin m f (center j)) :=
    SmallLevelMellinUnscale.finite_order_at_one (by decide : 0<5040) _ (h j).2.1
  exact FinitenessFiniteOrderClosure.sub
    (FinitenessFiniteOrderClosure.add (FinitenessFiniteOrderClosure.sub (hj 0) (hj 1)) (hj 2)) (hj 3)

theorem denominator_quadratic (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    denominator (2*m) f s=1+((Real.sqrt 3:ℂ)*f 3)*(3:ℂ)^((m:ℂ)-s)+
      ((3:ℂ)^((m:ℂ)-s))^2 := by
  have hfirst := SmallLevelTaylor.hecke_first_scalar (by decide : 0<3) m (f 3) s
  have hsecond := SmallLevelTaylor.hecke_second_scalar (by decide : 0<3) m s
  norm_num only [Nat.cast_ofNat,show (3:ℂ)^2=9 by norm_num] at hfirst hsecond
  unfold denominator
  rw [hfirst,hsecond]

theorem product_identity_of_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s, B<s.re → G s=original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) :
    ∀ s, denominator (2*m) f s*G s=numerator m f s := by
  obtain ⟨C,hC⟩ := original_hecke_identity m hf
  have hleft := (denominator_entire (2*m) f).mul hG
  have hright := original_numerator_entire m hm hf
  intro s
  have he : (fun z => denominator (2*m) f z*G z)=ᶠ[𝓝[≠] s] numerator m f := by
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

theorem finiteOrder_of_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (B : ℝ)
    (hGF : ∀ s, B<s.re → G s=original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) :
    FinitenessOriginalInput.FiniteOrder G := by
  apply QuantitativeArithmeticQuadraticTwistQuotient.finiteOrder_of_real_quadratic
    3 (by norm_num)
    ((Real.sqrt 3:ℂ)*f 3) (m:ℂ) (original_numerator_entire m hm hf).continuous
    (FinitenessInputBounds.bound_finiteOrder (original_numerator_bound m hm hf)) hG
  intro s
  norm_num only [Complex.ofReal_ofNat]
  rw [← denominator_quadratic]
  exact product_identity_of_entire hm hf hG B hGF s

#print axioms original_numerator_bound
#print axioms denominator_quadratic
#print axioms product_identity_of_entire
#print axioms finiteOrder_of_entire
end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourEntire -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex Filter Set SmallLevelAdditive
open QuantitativeArithmeticAnalyticGerm
open scoped Topology

/-- Original-input entireness, finite order and the coherent conductor560
functional equation for the quadratic-four additive difference. -/
theorem original_chi4_entire {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ (ε : ℂ) (B : ℝ) (H : ℂ → ℂ), (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      Differentiable ℂ H ∧ FinitenessOriginalInput.FiniteOrder H ∧
      (∀ s, B<s.re → H s=original (2*m) f (1/4) s-original (2*m) f (-(1/4)) s) ∧
      ∀ s, H s=ε*(560:ℂ)^((m:ℂ)-s)*H ((2*m:ℕ)-s) := by
  obtain ⟨ε,B,H,hε,hlaw,hH,hagree,hfe,_haway⟩ := original_quadratic_functional_equation m hm hf
  obtain ⟨BG,G,hG,hGF⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem.original_entire_grid
    hm hf ε hε hlaw
  have hdiff : Differentiable ℂ (fun z => G z 9-G z 25) := (hG 9).sub (hG 25)
  have hgrid (x : ℂ) : (fun z => G z 9-G z 25)=ᶠ[𝓝[≠] x] H := by
    apply SmallLevelContinuation.halfplane_germ_identity (x.re-1) (max BG B) _ _ _ x (by linarith)
    · intro z _
      exact (hdiff.analyticAt z).meromorphicAt
    · intro z _
      exact (hH z).meromorphicAt
    · intro z hz
      change G z 9-G z 25=H z
      rw [hGF z (lt_of_le_of_lt (le_max_left BG B) hz),
        hagree z (lt_of_le_of_lt (le_max_right BG B) hz)]
      have hp := grid_mod (2*m) f (by decide : 0<420) (-105) z
      norm_num [grid] at hp
      norm_num [QuantitativeArithmeticSmallLevelThirtyFiveChiFourRows.gridVector,coordinate,grid]
      exact hp
  have hentire : Differentiable ℂ H := by
    intro s
    exact ((HasAnalyticGerm.of_analytic (hdiff.analyticAt s)).congr (hgrid s)).analyticAt (hH s) |>.differentiableAt
  exact ⟨ε,B,H,hε,hlaw,hentire,finiteOrder_of_entire hm hf hentire B hagree,hagree,hfe⟩

#print axioms original_chi4_entire
end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourFricke -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex FinitenessOriginalFourier FinitenessFourierConstruction
open SmallLevelNormalized SmallLevelOriginal
open scoped ModularForm

def quadraticFourier (k : ℕ) (f : ℕ → ℂ) (z : ℂ) : ℂ :=
  fourier (fullCoefficients f k) (z+(1/4:ℝ))-
  fourier (fullCoefficients f k) (z+(-1/4:ℝ))

/-- The quadratic-four Fourier law, retaining the same sign as the
untwisted Fricke law. All analytic continuation is derived from original input. -/
theorem original_quadratic_fricke {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 (2*m) f ε ∧
      fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 35 (by decide)=
        (ε*I^(2*m)) • fourierFunction (2*m) f ∧
      ∀ z : ℂ, 0<z.im → quadraticFourier (2*m) f z=
        (ε*I^(2*m))/(((Real.sqrt 560:ℂ)*z)^(2*m))*
          quadraticFourier (2*m) f (-1/((560:ℂ)*z)) := by
  obtain ⟨ε,B,G,hε,hlaw,hent,hfinite,hGF,hFE⟩ :=
    original_chi4_entire hm hf
  obtain ⟨_hχ,hW⟩ := QuantitativeArithmeticCoherentTaylor.fricke_sign_of_law (by decide : 0<35) m ε hε hlaw
  obtain ⟨σ,_hσ,hgrowth⟩ := hf.growth
  refine ⟨ε,hε,hlaw,hW,?_⟩
  have h := QuantitativeArithmeticQuadraticTwistInversion.four_translate_fricke
    (k := 2*m) (ε := ε) (B := B)
    (by decide : 0<560) hf.zero hgrowth (1/4) 0 (-1/4) 0 G hent hfinite
    (by
      intro s hs
      rw [hGF s hs]
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
end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourIndividual -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticSmallLevelThirtyFiveChiFourSystem (root_four)

/-- The Ramanujan-four and quadratic-four equations separate into the
two individual additive equations without dividing by a Hecke eigenvalue. -/
theorem individual_laws {k : ℕ} {f : ℕ → ℂ} (ε : ℂ)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 35 k f ε)
    (hquad : ∀ z : ℂ, 0<z.im → quadraticFourier k f z=
      (ε*I^k)/(((Real.sqrt 560:ℂ)*z)^k)*quadraticFourier k f (-1/((560:ℂ)*z))) :
    ∀ z : ℂ, 0<z.im →
      (fourier (fullCoefficients f k) (z+1/4)=
        (ε*I^k)/(((Real.sqrt 560:ℂ)*z)^k)*
          fourier (fullCoefficients f k) (-1/((560:ℂ)*z)+1/4)) ∧
      (fourier (fullCoefficients f k) (z-1/4)=
        (ε*I^k)/(((Real.sqrt 560:ℂ)*z)^k)*
          fourier (fullCoefficients f k) (-1/((560:ℂ)*z)-1/4)) := by
  intro z hz
  have hr := hlaw 4 (by decide) z hz
  rw [show Nat.lcm 35 (4^2)=560 by decide,root_four,one_mul,
    SmallLevelThirty.twist_four _ (periodic _),
    SmallLevelThirty.twist_four _ (periodic _)] at hr
  norm_num only [Nat.cast_ofNat] at hr
  have hc := hquad z hz
  norm_num only [quadraticFourier,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_ofNat,Complex.ofReal_one] at hc
  simp only [sub_eq_add_neg] at hr hc ⊢
  constructor
  · linear_combination (hr+hc)/2
  · linear_combination (hr-hc)/2

#print axioms individual_laws
end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Matrix UpperHalfPlane SmallLevelNormalized
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

def Dplus : SL(2,ℤ) := ⟨!![4,-1;-35,9],by decide⟩
def Dminus : SL(2,ℤ) := ⟨!![4,1;35,9],by decide⟩

theorem sqrt_four_conductor : Real.sqrt 560=4*Real.sqrt 35 := by
  rw [show (560:ℝ)=16*35 by norm_num,Real.sqrt_mul (by norm_num)]
  norm_num

theorem plus_branch : fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Dplus*translation (1/4)=
    translation (1/4)*fricke 560 (by decide) := by
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Dplus,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_four_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem minus_branch : fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Dminus*translation (-1/4)=
    translation (-1/4)*fricke 560 (by decide) := by
  have ht : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fricke,Dminus,translation,matrix,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,sqrt_four_conductor] <;>
    field_simp [hn] <;> norm_num [ht]

theorem plus_conjugate : (fricke 35 (by decide))⁻¹*translation (1/4)*fricke 560 (by decide)*
    (translation (1/4))⁻¹=SpecialLinearGroup.mapGL ℝ Dplus := by
  calc
    _=(fricke 35 (by decide))⁻¹*(translation (1/4)*fricke 560 (by decide))*(translation (1/4))⁻¹ := by group
    _=(fricke 35 (by decide))⁻¹*(fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Dplus*translation (1/4))*(translation (1/4))⁻¹ := by rw [plus_branch]
    _=_ := by group

theorem minus_conjugate : (fricke 35 (by decide))⁻¹*translation (-1/4)*fricke 560 (by decide)*
    (translation (-1/4))⁻¹=SpecialLinearGroup.mapGL ℝ Dminus := by
  calc
    _=(fricke 35 (by decide))⁻¹*(translation (-1/4)*fricke 560 (by decide))*(translation (-1/4))⁻¹ := by group
    _=(fricke 35 (by decide))⁻¹*(fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ Dminus*translation (-1/4))*(translation (-1/4))⁻¹ := by rw [minus_branch]
    _=_ := by group

#print axioms plus_conjugate
#print axioms minus_conjugate
end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveChiFourTransformations -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiFour
open Complex Matrix UpperHalfPlane SmallLevelNormalized SmallLevelOriginal
open FinitenessOriginalFourier FinitenessFourierConstruction
open QuantitativeArithmeticSmallLevelThirtyFiveGroupHecke
open scoped MatrixGroups ModularForm

/-- Original Euler/Fricke input forces both denominator-four matrices,
including the zero Hecke-eigenvalue cases. -/
theorem original_D_plus_minus {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Dplus=fourierFunction (2*m) f ∧
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] Dminus=fourierFunction (2*m) f := by
  obtain ⟨ε,_hε,hlaw,_hW,hquad⟩ := original_quadratic_fricke hm hf
  have hF : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients f (2*m)) z=
      (ε*Complex.I^(2*m))/(((Real.sqrt 35:ℂ)*z)^(2*m))*
        fourier (fullCoefficients f (2*m)) (-1/((35:ℂ)*z)) := by
    intro z hz
    simpa [FinitenessNormalizedTwistProduct.root,FinitenessAnalyticReconstruction.twist,
      Finset.sum_range_succ] using hlaw 1 (by decide) z hz
  have hind := individual_laws ε hlaw hquad
  constructor
  · have h := QuantitativeArithmeticNormalizedIndividualFricke.single_of_fricke
      35 560 (2*m) (by decide) (by decide) (1/4) _ _ hF
      (by
        intro z hz
        simpa only [Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_one,
          Complex.ofReal_ofNat] using (hind z hz).1)
    rw [plus_conjugate] at h
    exact h
  · have h := QuantitativeArithmeticNormalizedIndividualFricke.single_of_fricke
      35 560 (2*m) (by decide) (by decide) (-1/4) _ _ hF
      (by
        intro z hz
        simpa only [Nat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat,
          Complex.ofReal_one,sub_eq_add_neg,neg_div] using (hind z hz).2)
    rw [minus_conjugate] at h
    exact h

#print axioms original_D_plus_minus
end QuantitativeArithmeticSmallLevelThirtyFiveChiFour
end
end

/-! ## ThirtyFiveGroupData -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section

namespace QuantitativeArithmeticSmallLevelThirtyFiveGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

def kernel (i : Fin 18) : SL(2,ℤ) :=
  match i.val with
  | 0 => ⟨!![1,1;0,1],by decide⟩
  | 1 => ⟨!![1,0;35,1],by decide⟩
  | 2 => ⟨!![2,-1;-35,18],by decide⟩
  | 3 => ⟨!![6,-1;-35,6],by decide⟩
  | 4 => ⟨!![3,-1;-35,12],by decide⟩
  | 5 => ⟨!![3,1;35,12],by decide⟩
  | 6 => ⟨!![41,-17;70,-29],by decide⟩
  | 7 => ⟨!![4,-1;-35,9],by decide⟩
  | 8 => ⟨!![4,1;35,9],by decide⟩
  | 9 => ⟨!![1,0;-35,1],by decide⟩
  | 10 => ⟨!![1,-1;0,1],by decide⟩
  | 11 => ⟨!![18,1;35,2],by decide⟩
  | 12 => ⟨!![6,1;35,6],by decide⟩
  | 13 => ⟨!![12,1;35,3],by decide⟩
  | 14 => ⟨!![12,-1;-35,3],by decide⟩
  | 15 => ⟨!![-29,-2;595,41],by decide⟩
  | 16 => ⟨!![9,1;35,4],by decide⟩
  | _ => ⟨!![9,-1;-35,4],by decide⟩

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

theorem word_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 18, kernel i∈K)
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
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hl i)

def rowClass (c d : ZMod 35) : ℕ :=
  (if c.val%5=0 then 5 else (d.val%5*([0,1,3,2,4] : List ℕ).getD (c.val%5) 0)%5)*8+
  (if c.val%7=0 then 7 else (d.val%7*([0,1,4,5,2,3,6] : List ℕ).getD (c.val%7) 0)%7)

def repRow (c d : ZMod 35) : SL(2,ℤ) :=
  match rowClass c d with
  | 0 => ⟨!![0,-1;1,0],by decide⟩
  | 9 => ⟨!![0,-1;1,1],by decide⟩
  | 38 => ⟨!![0,-1;1,-1],by decide⟩
  | 18 => ⟨!![0,-1;1,2],by decide⟩
  | 29 => ⟨!![0,-1;1,-2],by decide⟩
  | 19 => ⟨!![-1,0;2,-1],by decide⟩
  | 27 => ⟨!![0,-1;1,3],by decide⟩
  | 28 => ⟨!![-1,0;-2,-1],by decide⟩
  | 20 => ⟨!![0,-1;1,-3],by decide⟩
  | 10 => ⟨!![-1,1;2,-3],by decide⟩
  | 26 => ⟨!![-1,0;3,-1],by decide⟩
  | 36 => ⟨!![0,-1;1,4],by decide⟩
  | 37 => ⟨!![-1,-1;-2,-3],by decide⟩
  | 21 => ⟨!![-1,0;-3,-1],by decide⟩
  | 11 => ⟨!![0,-1;1,-4],by decide⟩
  | 35 => ⟨!![1,1;-3,-2],by decide⟩
  | 1 => ⟨!![-1,2;2,-5],by decide⟩
  | 17 => ⟨!![-1,1;3,-4],by decide⟩
  | 13 => ⟨!![-1,0;4,-1],by decide⟩
  | 5 => ⟨!![0,-1;1,5],by decide⟩
  | 12 => ⟨!![-1,1;-3,2],by decide⟩
  | 6 => ⟨!![-1,-2;-2,-5],by decide⟩
  | 30 => ⟨!![-1,-1;-3,-4],by decide⟩
  | 34 => ⟨!![-1,0;-4,-1],by decide⟩
  | 2 => ⟨!![0,-1;1,-5],by decide⟩
  | 4 => ⟨!![1,2;-3,-5],by decide⟩
  | 46 => ⟨!![2,1;-5,-2],by decide⟩
  | 32 => ⟨!![-1,3;2,-7],by decide⟩
  | 22 => ⟨!![1,1;-4,-3],by decide⟩
  | 8 => ⟨!![-1,2;3,-7],by decide⟩
  | 44 => ⟨!![-1,0;5,-1],by decide⟩
  | 14 => ⟨!![0,-1;1,6],by decide⟩
  | 3 => ⟨!![-1,2;-3,5],by decide⟩
  | 41 => ⟨!![-2,1;-5,2],by decide⟩
  | 25 => ⟨!![-1,1;-4,3],by decide⟩
  | 43 => ⟨!![-1,0;-5,-1],by decide⟩
  | 33 => ⟨!![0,-1;1,-6],by decide⟩
  | 45 => ⟨!![2,-1;-5,3],by decide⟩
  | 40 => ⟨!![2,3;-5,-7],by decide⟩
  | 15 => ⟨!![3,1;-7,-2],by decide⟩
  | 24 => ⟨!![1,2;-4,-7],by decide⟩
  | 39 => ⟨!![2,1;-7,-3],by decide⟩
  | 16 => ⟨!![0,-1;1,7],by decide⟩
  | 42 => ⟨!![2,1;5,3],by decide⟩
  | 7 => ⟨!![3,-2;-7,5],by decide⟩
  | 23 => ⟨!![3,4;-7,-9],by decide⟩
  | 31 => ⟨!![2,-1;-7,4],by decide⟩
  | _ => 1

def edgeSRow (c d : ZMod 35) : List (Fin 37) :=
  match rowClass c d with
  | 0 => [36]
  | 9 => [10]
  | 38 => [0, 36]
  | 19 => [36]
  | 28 => [36]
  | 26 => [36]
  | 21 => [36]
  | 35 => [36]
  | 13 => [36]
  | 12 => [36]
  | 34 => [36]
  | 46 => [36]
  | 22 => [36]
  | 44 => [36]
  | 14 => [3]
  | 41 => [36]
  | 25 => [36]
  | 43 => [36]
  | 33 => [12, 36]
  | 45 => [36]
  | 15 => [36]
  | 39 => [36]
  | 16 => [7, 13, 36, 2, 0]
  | 42 => [36]
  | 7 => [36]
  | 23 => [10, 11, 4, 16]
  | 31 => [36]
  | _ => []

def edgeTRow (c d : ZMod 35) : List (Fin 37) :=
  match rowClass c d with
  | 47 => [0]
  | 19 => [10, 36]
  | 26 => [36]
  | 13 => [36]
  | 6 => [11, 9, 36, 5]
  | 30 => [13, 2, 36, 0]
  | 34 => [16, 4]
  | 4 => [14, 8, 36]
  | 44 => [17, 5]
  | 41 => [36]
  | 43 => [12]
  | 40 => [10, 6, 36]
  | 24 => [17, 36]
  | 39 => [14, 1, 36, 15, 2, 0]
  | 16 => [7, 36]
  | 42 => [13, 7]
  | 23 => [10, 11, 36, 4, 16, 3, 8]
  | _ => []

def rep (g : SL(2,ZMod 35)) : SL(2,ℤ) := repRow (g.1 1 0) (g.1 1 1)
theorem row_primitive (g : SL(2,ZMod 35)) :
    ∃ a b : ZMod 35, a*g.1 1 1-b*g.1 1 0=1 := by
  refine ⟨g.1 0 0,g.1 0 1,?_⟩
  exact (det_fin_two g.1).symm.trans g.det_coe

end QuantitativeArithmeticSmallLevelThirtyFiveGroup
end
end

/-! ## ThirtyFiveGroupEdgesSFamilyV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace QuantitativeArithmeticSmallLevelThirtyFiveGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

















































end QuantitativeArithmeticSmallLevelThirtyFiveGroup
end
end
end

/-! ## ThirtyFiveGroupEdgesTFamilyV4 -/
section
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace QuantitativeArithmeticSmallLevelThirtyFiveGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

















































end QuantitativeArithmeticSmallLevelThirtyFiveGroup
end
end
end

/-! ## ThirtyFiveGroupGenerators -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
@[expose] public section

namespace QuantitativeArithmeticSmallLevelThirtyFiveGroup
open Matrix ModularGroup SmallLevelGenerators
open scoped MatrixGroups

theorem edgeSRow_checked : ∀ c d : ZMod 35, (∃ a b : ZMod 35, a*d-b*c=1) →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 35,
    Nat.gcd (Nat.gcd c.val d.val) 35 = 1 →
    repRow c d*S*(repRow d (-c))⁻¹=word (edgeSRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeTRow_checked : ∀ c d : ZMod 35, (∃ a b : ZMod 35, a*d-b*c=1) →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d) := by
  intro c d h
  exact (by decide +kernel : ∀ c d : ZMod 35,
    Nat.gcd (Nat.gcd c.val d.val) 35 = 1 →
    repRow c d*T*(repRow c (c+d))⁻¹=word (edgeTRow c d)) c d (QuantitativeArithmeticPrimitiveResiduePair.gcd_eq_one c d h)

theorem edgeS_checked (g : SL(2,ZMod 35)) :
    rep g*S*(rep (g*reduction 35 S))⁻¹=word (edgeSRow (g.1 1 0) (g.1 1 1)) := by
  have hs : rep (g*reduction 35 S)=repRow (g.1 1 1) (-(g.1 1 0)) := by
    have hS : reduction 35 S=(⟨!![0,-1;1,0],by decide⟩ : SL(2,ZMod 35)) := by decide
    simp [rep, hS, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hs]
  exact edgeSRow_checked _ _ (row_primitive g)

theorem edgeT_checked (g : SL(2,ZMod 35)) :
    rep g*T*(rep (g*reduction 35 T))⁻¹=word (edgeTRow (g.1 1 0) (g.1 1 1)) := by
  have ht : rep (g*reduction 35 T)=repRow (g.1 1 0) (g.1 1 0+g.1 1 1) := by
    have hT : reduction 35 T=(⟨!![1,1;0,1],by decide⟩ : SL(2,ZMod 35)) := by decide
    simp [rep, hT, Matrix.mul_apply, Fin.sum_univ_two]
  rw [ht]
  exact edgeTRow_checked _ _ (row_primitive g)

theorem rep_one : rep 1=1 := by decide

theorem rep_upper (g : SL(2,ZMod 35)) (hg : g.1 1 0=0) : rep g=1 := by
  have h : ∀ d : ZMod 35, repRow 0 d=1 := by decide
  simpa only [rep, hg] using h (g.1 1 1)

theorem gamma0_mem (K : Subgroup SL(2,ℤ)) (hK : ∀ i : Fin 18, kernel i∈K)
    (hZ : (-1:SL(2,ℤ))∈K) (γ : SL(2,ℤ))
    (hγ : γ∈CongruenceSubgroup.Gamma0 35) : γ∈K := by
  apply transversal_mem (reduction 35) rep K
  · intro g
    rw [edgeS_checked]
    exact word_mem K hK hZ _
  · intro g
    rw [edgeT_checked]
    exact word_mem K hK hZ _
  · exact rep_one
  · apply rep_upper
    exact CongruenceSubgroup.Gamma0_mem.mp hγ
#print axioms gamma0_mem

end QuantitativeArithmeticSmallLevelThirtyFiveGroup
end
end

/-! ## ThirtyFiveGroupMatrices -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem conjugate_fricke (i : Fin 9) :
    SpecialLinearGroup.mapGL ℝ (kernel ⟨i.val+9,by omega⟩)*fricke 35 (by decide)=
      fricke 35 (by decide)*SpecialLinearGroup.mapGL ℝ (kernel (i.castLE (by decide))) := by
  have hs : (Real.sqrt 35)^2=35 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 35≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  fin_cases i <;>
    apply Units.ext <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [fricke,matrix,kernel,GeneralLinearGroup.mkOfDetNeZero,
      SpecialLinearGroup.toGL,SpecialLinearGroup.map_apply_coe,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] <;>
    field_simp [hn] <;> nlinarith

theorem conjugate_invariant (F : ℍ → ℂ) (k : ℤ) (g : GL (Fin 2) ℝ)
    (δ : ℂ) (hg : F ∣[k] g=δ • F) (γ κ : SL(2,ℤ))
    (hκ : SpecialLinearGroup.mapGL ℝ κ*g=g*SpecialLinearGroup.mapGL ℝ γ)
    (hγ : F ∣[k] γ=F) : F ∣[k] κ=F := by
  have hh : (F ∣[k] κ) ∣[k] g=F ∣[k] g := by
    change (F ∣[k] SpecialLinearGroup.mapGL ℝ κ) ∣[k] g=F ∣[k] g
    rw [← SlashAction.slash_mul,hκ,SlashAction.slash_mul]
    change (F ∣[k] g) ∣[k] γ=F ∣[k] g
    rw [hg,ModularForm.SL_smul_slash,hγ]
  have h := congrArg (fun G : ℍ → ℂ => G ∣[k] g⁻¹) hh
  simpa only [← SlashAction.slash_mul,mul_inv_cancel,SlashAction.slash_one] using h

theorem original_first_four {k : ℕ} (hk : 0<k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) (i : Fin 4) :
    SmallLevelOriginal.fourierFunction k f ∣[(k:ℤ)] kernel (i.castLE (by decide))=
      SmallLevelOriginal.fourierFunction k f := by
  fin_cases i
  · exact original_T k f
  · exact original_lower (by decide) hf
  · have hh := (slashStabilizer (k:ℤ) (SmallLevelOriginal.fourierFunction k f)).inv_mem
      (original_odd (by decide) (by decide : 2*18=35+1) (by decide) hf)
    exact hh
  · exact QuantitativeArithmeticSmallLevelThirtyFiveGroupOriginalRows.original_six hk hf

/-- Only the five displayed additional invariances are assumed. The first
four generators and all nine Fricke conjugates follow from original input. -/
theorem original_kernel (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (hextra : ∀ i : Fin 5,
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel ⟨i.val+4,by omega⟩=
        SmallLevelOriginal.fourierFunction (2*m) f) (i : Fin 18) :
    SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel i=
      SmallLevelOriginal.fourierFunction (2*m) f := by
  have hbase (j : Fin 9) :
      SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel (j.castLE (by decide))=
        SmallLevelOriginal.fourierFunction (2*m) f := by
    by_cases hj : j.val<4
    · exact original_first_four (by omega) hf ⟨j.val,hj⟩
    · have hh := hextra ⟨j.val-4,by omega⟩
      have heq : (⟨(j.val-4)+4,by omega⟩ : Fin 18)=j.castLE (by decide) := by
        apply Fin.ext
        simp only [Fin.val_castLE]
        omega
      simpa only [heq] using hh
  obtain ⟨χ,_,hχ⟩ := original_fricke_sign (by decide : 0<35) m hf
  by_cases hi : i.val<9
  · exact hbase ⟨i.val,hi⟩
  · have hh := conjugate_invariant _ _ _ χ hχ _ _
      (conjugate_fricke ⟨i.val-9,by omega⟩) (hbase ⟨i.val-9,by omega⟩)
    have heq : (⟨(i.val-9)+9,by omega⟩ : Fin 18)=i := by
      apply Fin.ext
      change (i.val-9)+9=i.val
      omega
    simpa only [heq] using hh

#print axioms original_first_four
#print axioms original_kernel
end QuantitativeArithmeticSmallLevelThirtyFiveGroup
end
end

/-! ## ThirtyFiveModular -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveGroup
open Matrix UpperHalfPlane ModularGroup SmallLevelGenerators SmallLevelOriginal
open scoped MatrixGroups ModularForm

/-- All eighteen group generators are forced by the original hypotheses.
The chi3 and chi4 analytic continuations have been proved internally. -/
theorem original_all_generators {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f) (i : Fin 18) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] kernel i=fourierFunction (2*m) f := by
  obtain ⟨hCp,hCm⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiThree.original_C_plus_minus hm hf
  obtain ⟨hDp,hDm⟩ := QuantitativeArithmeticSmallLevelThirtyFiveChiFour.original_D_plus_minus hm hf
  have hH := QuantitativeArithmeticSmallLevelThirtyFiveTwelve.original_H_unconditional hm hf
  apply original_kernel m hm hf _ i
  intro j
  fin_cases j
  · exact hCp
  · exact hCm
  · exact hH
  · exact hDp
  · exact hDm

theorem original_gamma0 {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 (2*m) f)
    (γ : SL(2,ℤ)) (hγ : γ∈CongruenceSubgroup.Gamma0 35) :
    fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] γ=fourierFunction (2*m) f := by
  exact gamma0_mem (slashStabilizer ((2*m:ℕ):ℤ) (fourierFunction (2*m) f))
    (original_all_generators hm hf) (SmallLevelThirtySix.slash_neg_one_even _ m) γ hγ

/-- The level35 converse theorem, from the literal original Euler-product
and entire Fricke hypotheses, including holomorphy at every cusp. -/
theorem level_thirty_five {k : ℕ} (hk : 0<k) (heven : Even k) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) : IsModular 35 k f := by
  obtain ⟨m,hm⟩ := heven
  have hkm : k=2*m := by omega
  rw [hkm] at hf ⊢
  exact modular_of_transformations (by decide) hf (original_gamma0 (by omega) hf)

#print axioms original_all_generators
#print axioms original_gamma0
#print axioms level_thirty_five
end QuantitativeArithmeticSmallLevelThirtyFiveGroup
end
end

/-! ## ThirtyFivePoleResidual -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelThirtyFivePole

open Complex Filter Set
open scoped Topology

def badProduct (f : ℕ → ℂ) : ℂ :=
  (Real.sqrt 5:ℂ)*f 5*((Real.sqrt 7:ℂ)*f 7)

/-- The product in the level-35 residual has norm one for actual original
Euler data, with no new root-sign assumptions. -/
theorem badProduct_norm {f : ℕ → ℂ} (hf : FinitenessOriginalInput.EulerData 35 f) :
    ‖badProduct f‖=1 := by
  have h5 := FinitenessOriginalTwistLocal.bad_root_sign hf
    (by decide : Nat.Prime 5) (by decide) (by decide)
  have h7 := FinitenessOriginalTwistLocal.bad_root_sign hf
    (by decide : Nat.Prime 7) (by decide) (by decide)
  norm_num only [Nat.cast_ofNat] at h5 h7
  have he : badProduct f=(-f 5*Real.sqrt 5)*(-f 7*Real.sqrt 7) := by
    unfold badProduct
    ring
  rw [he]
  rcases h5 with h5|h5 <;> rcases h7 with h7|h7 <;> rw [h5,h7] <;> norm_num

/-- Exponential form of the numerator 35^(s-k/2)-sigma5*sigma7.
No finite-grid identity for this residual is asserted by this definition. -/
def residual (f : ℕ → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((Real.log 35:ℂ)*(z-(k:ℂ)/2))-badProduct f

theorem residual_cpow (f : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    residual f k z=(35:ℂ)^(z-(k:ℂ)/2)-badProduct f := by
  have hl : Complex.log (35:ℂ)=(Real.log 35:ℂ) := by
    simp
  rw [residual,Complex.cpow_def_of_ne_zero (by norm_num : (35:ℂ)≠0),hl]

theorem residual_analytic (f : ℕ → ℂ) (k : ℕ) (x : ℂ) :
    AnalyticAt ℂ (residual f k) x := by
  unfold residual
  fun_prop

theorem original_residual_central {k : ℕ} {f : ℕ → ℂ} {z : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) (hz : residual f k z=0) :
    z.re=(k:ℝ)/2 := by
  apply SmallLevelPoleGrid.exponential_zero_central
    (α:=Real.log 35) (s:=badProduct f)
    (Real.log_pos (by norm_num : (1:ℝ)<35)).ne' (badProduct_norm hf.toEulerData)
  have hh := sub_eq_zero.mp hz
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat]
    using hh

/-- The residual cannot vanish identically, including when either good-prime
Hecke eigenvalue is zero. -/
theorem original_residual_not_identically_zero {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) :
    ∃ z : ℂ, residual f k z≠0 := by
  refine ⟨(((k:ℝ)/2+1:ℝ):ℂ),?_⟩
  intro hz
  have h := original_residual_central hf hz
  simp only [Complex.ofReal_re] at h
  linarith

/-- Once the finite row certificate shows that the residual kills the whole
leading vector, its nonzero value forces the pole onto the central line. -/
theorem central_of_residual_kernel {ι : Type*} {k : ℕ} {f : ℕ → ℂ} {z : ℂ}
    (hf : FinitenessOriginalInput.IsSolution 35 k f) (v : ι → ℂ) (hv : v≠0)
    (hrow : ∀ i, residual f k z*v i=0) : z.re=(k:ℝ)/2 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  apply original_residual_central hf
  exact (mul_eq_zero.mp (hrow i)).resolve_right hi

#print axioms badProduct_norm
#print axioms residual_cpow
#print axioms residual_analytic
#print axioms original_residual_central
#print axioms original_residual_not_identically_zero
#print axioms central_of_residual_kernel

end SmallLevelThirtyFivePole
end
end
