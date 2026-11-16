module
public meta import SmallLevelCertificateBatchCommandV1
public import QuantitativeArithmeticLevelThirtyFivePoleAlgebraV4
-- Bounded certificate elaboration.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

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

certificate_batch {
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
}

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

certificate_batch {
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

}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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

}

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

certificate_batch {
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

}

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

certificate_batch {
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

}

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

certificate_batch {
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
}

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

certificate_batch {
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

}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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

}

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

certificate_batch {
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
}

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

certificate_batch {
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

}

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

certificate_batch {
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
}

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
certificate_batch {
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
}

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

certificate_batch {
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

}

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

certificate_batch {
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
}

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
certificate_batch {
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
}

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

certificate_batch {
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
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

