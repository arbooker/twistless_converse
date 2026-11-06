module

public import QuantitativeArithmeticEntireQuotientV1
public import QuantitativeArithmeticMellinScaleV1
public import QuantitativeArithmeticQuadraticTwistReflectionTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenGridSystemTheoryV4
public import QuantitativeArithmeticSmallLevelNineteenTenthFrickeV1
public import QuantitativeArithmeticTranslatedFrickeTheoryV4
public import SmallLevelAdditiveTheoryV4
public import SmallLevelTaylorTheoryV4

/-! Consolidated chapter: QuantitativeArithmeticSmallLevelNineteen. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSmallLevelNineteenCentersV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteen
open Complex MeasureTheory FinitenessFourierConstruction SmallLevelAdditive
open QuantitativeArithmeticTranslatedFricke
open scoped ModularForm

def center (positive : Bool) : ℝ := if positive then 1/10 else -(1/10)

def centeredMellin (m : ℕ) (f : ℕ → ℂ) (positive : Bool) : ℂ → ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1900
    (coefficients (FinitenessOriginalFourier.fullCoefficients f (2*m)) (center positive)))

def centerEntire (m : ℕ) (f : ℕ → ℂ) (positive : Bool) : ℂ → ℂ :=
  mellin (FinitenessAllLevelAxisDecay.axis 1
    (coefficients (FinitenessOriginalFourier.fullCoefficients f (2*m)) (center positive)))

/-- Entire finite-order Mellin continuations of both individual tenth twists,
with one common functional-equation sign, from original input alone. -/
theorem original_centers_entire (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    ∃ χ : ℂ, (χ=1 ∨ χ= -1) ∧ ∀ positive : Bool,
      Differentiable ℂ (centeredMellin m f positive) ∧
      FinitenessFiniteOrder.Bound (centeredMellin m f positive) ∧
      ∀ s : ℂ, centeredMellin m f positive s=
        (χ/(Complex.I^(2*m)))*centeredMellin m f positive ((2*m:ℕ)-s) := by
  obtain ⟨χ,hχ,hp,hn⟩ := original_tenth_fricke m hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  refine ⟨χ,hχ,fun positive => ?_⟩
  apply translated_mellin_entire 1900 (2*m) (by decide) (by omega) _
    (FinitenessOriginalFourier.polynomial_bound hf.zero hg (2*m))
    (FinitenessOriginalFourier.fullCoefficients_zero hf.zero (2*m)) (center positive) χ hχ
  change ((SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
    SmallLevelNormalized.translation (center positive)) ∣[((2*m:ℕ):ℤ)]
    SmallLevelNormalized.fricke 1900 (by decide)) = χ •
    (SmallLevelOriginal.fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)]
      SmallLevelNormalized.translation (center positive))
  cases positive
  · simpa only [center,Bool.false_eq_true,ite_false,neg_div] using hn
  · exact hp

/-- The unscaled continuations agree with the actual additive Dirichlet
series in a common initial half-plane. -/
theorem original_center_continuations (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    (∀ positive : Bool, Differentiable ℂ (centerEntire m f positive)) ∧
    ∃ B : ℝ, ∀ positive : Bool, ∀ s : ℂ, B<s.re →
      centerEntire m f positive s=SmallLevelAdditive.original (2*m) f (center positive) s := by
  obtain ⟨χ,_,he⟩ := original_centers_entire m hm hf
  refine ⟨fun positive => QuantitativeArithmeticMellinScale.entire_at_one (by decide : 0<1900)
    _ (he positive).1,?_⟩
  obtain ⟨B,hB⟩ := SmallLevelAdditive.original_common_halfplane hf
  refine ⟨B,fun positive s hs => ?_⟩
  have haxis : FinitenessAllLevelAxisDecay.axis 1
      (coefficients (FinitenessOriginalFourier.fullCoefficients f (2*m)) (center positive)) =
      (fun t : ℝ => fourier (FinitenessOriginalFourier.fullCoefficients f (2*m))
        ((center positive:ℂ)+(t:ℂ)*I)) := funext (axis_one_translate _ _)
  unfold centerEntire
  rw [haxis]
  exact (hB (center positive) s hs).2

#print axioms original_centers_entire
#print axioms original_center_continuations
end QuantitativeArithmeticSmallLevelNineteen
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenHeckeV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteen
open Complex SmallLevelAdditive

def evenOne (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  original k f (1/5) s+original k f (-1/5) s

def evenTwo (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  original k f (2/5) s+original k f (-2/5) s

def tenthSum (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  original k f (1/10) s+original k f (-1/10) s

def heckeScalar (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  (((2:ℝ)^(((k:ℝ)+1)/2):ℝ):ℂ)*f 2*(2:ℂ)^(-s)

def oppositeScalar (k : ℕ) (s : ℂ) : ℂ := 1+(2:ℂ)^k*(4:ℂ)^(-s)

theorem original_add_int (k : ℕ) (f : ℕ → ℂ) (r : ℝ) (n : ℤ) (s : ℂ) :
    original k f (r+(n:ℝ)) s=original k f r s := transform_add_int _ r n s

theorem period_three_fifths (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    original k f (3/5) s=original k f (-2/5) s := by
  convert original_add_int k f (-2/5) 1 s using 1; norm_num

theorem period_four_fifths (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    original k f (4/5) s=original k f (-1/5) s := by
  convert original_add_int k f (-1/5) 1 s using 1; norm_num

/-- The literal original Hecke2 relation closes the two even fifth-sums
against the already entire tenth-sum, including when f₂ vanishes. -/
theorem original_even_hecke {k : ℕ} {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 k f) :
    ∃ B : ℝ, ∀ s : ℂ, B<s.re →
      heckeScalar k f s*evenOne k f s=
        oppositeScalar k s*evenTwo k f s+tenthSum k f s := by
  obtain ⟨B,hB⟩ := SmallLevelTaylor.original_additive_hecke hf
    (by decide : Nat.Prime 2) (by decide : ¬2∣19)
  refine ⟨B,fun s hs => ?_⟩
  have hp := hB (1/10) s hs
  have hn := hB (-1/10) s hs
  norm_num [Finset.sum_range_succ] at hp hn
  rw [period_three_fifths] at hp
  unfold heckeScalar evenOne oppositeScalar evenTwo tenthSum
  simp only [neg_div] at hp hn ⊢
  linear_combination -hp-hn

/-- The actual modulus-five Ramanujan sum is the sum of the two even
classes; this identity holds even for the totalized Dirichlet series. -/
theorem ramanujan_five (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    SmallLevelTaylor.ramanujanAdditive k f 5 0 s=evenOne k f s+evenTwo k f s := by
  unfold SmallLevelTaylor.ramanujanAdditive FinitenessRamanujanSum.residues
  rw [show (Finset.range 5).filter (fun a => Nat.Coprime a 5)={1,2,3,4} by decide]
  norm_num
  rw [period_three_fifths,period_four_fifths]
  unfold evenOne evenTwo
  ring

#print axioms original_even_hecke
#print axioms ramanujan_five
end QuantitativeArithmeticSmallLevelNineteen
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenChiFiveV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteen
open Complex SmallLevelAdditive SmallLevelTaylor Filter Set
open scoped Topology

/-- The even quadratic additive combination, equal to the Gauss-factor
multiple of the chi5 twist in its original convergence half-plane. -/
def quadraticCombination (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  evenOne k f s-evenTwo k f s

def denominator (k : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  heckeScalar k f s+oppositeScalar k s

def numerator (m : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  (oppositeScalar (2*m) s-heckeScalar (2*m) f s)*ramanujanEntire 19 (2*m) f 5 s+
    2*(centerEntire m f true s+centerEntire m f false s)

theorem denominator_entire (k : ℕ) (f : ℕ → ℂ) : Differentiable ℂ (denominator k f) := by
  unfold denominator heckeScalar oppositeScalar
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by norm_num : (4:ℂ)≠0)]
  fun_prop

theorem denominator_nonzero (k : ℕ) (f : ℕ → ℂ) : ∃ s : ℂ, denominator k f s≠0 := by
  by_contra hw
  push Not at hw
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  norm_num [denominator,heckeScalar,oppositeScalar,Complex.cpow_neg,Complex.cpow_natCast] at h0 h1 h2
  have hbad : (1:ℂ)=0 := by
    linear_combination (1/3:ℂ)*h0-2*h1+(8/3:ℂ)*h2
  norm_num at hbad

theorem original_numerator_entire (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) : Differentiable ℂ (numerator m f) := by
  have he := (original_center_continuations m hm hf).1
  have hr : Differentiable ℂ (ramanujanEntire 19 (2*m) f 5) := by
    intro s
    exact ((original_ramanujan_entire (by decide : 0<19) (by omega) hf (by decide : 0<5)).1 s).differentiableAt
  have hc : Differentiable ℂ (fun s => oppositeScalar (2*m) s-heckeScalar (2*m) f s) := by
    unfold heckeScalar oppositeScalar
    simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
      Complex.cpow_def_of_ne_zero (by norm_num : (4:ℂ)≠0)]
    fun_prop
  exact (hc.mul hr).add (((he true).add (he false)).const_mul 2)

/-- Actual original-input numerator identity, before any quotient or
meromorphic continuation. No restriction on the complex Hecke eigenvalue. -/
theorem original_quotient_identity (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    ∃ bound : ℝ, ∀ s : ℂ, bound<s.re →
      numerator m f s=denominator (2*m) f s*quadraticCombination (2*m) f s := by
  obtain ⟨Bc,hc⟩ := (original_center_continuations m hm hf).2
  obtain ⟨Bh,hh⟩ := original_even_hecke hf
  obtain ⟨Br,hr⟩ := (original_ramanujan_entire (by decide : 0<19) (by omega) hf (by decide : 0<5)).2
  refine ⟨max Bc (max Bh Br),fun s hs => ?_⟩
  have hcs := lt_of_le_of_lt (le_max_left Bc (max Bh Br)) hs
  have hhs : Bh<s.re := lt_of_le_of_lt ((le_max_left Bh Br).trans (le_max_right Bc _)) hs
  have hrs : Br<s.re := lt_of_le_of_lt ((le_max_right Bh Br).trans (le_max_right Bc _)) hs
  have hb : centerEntire m f true s+centerEntire m f false s=tenthSum (2*m) f s := by
    rw [hc true s hcs,hc false s hcs]
    simp only [center,ite_true,Bool.false_eq_true,ite_false,tenthSum,neg_div]
  unfold numerator
  rw [hb,hr s hrs,ramanujan_five]
  unfold denominator quadraticCombination
  linear_combination -2*(hh s hhs)

/-- The original even quadratic combination modulo5 has a global
normal-form meromorphic continuation. Its only possible poles lie on the
explicit Hecke2 denominator. Pole removal is not claimed here. -/
theorem original_quadratic_continuation (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    ∃ (bound : ℝ) (G : ℂ → ℂ), (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=quadraticCombination (2*m) f s) ∧
      (∀ s, denominator (2*m) f s≠0 → AnalyticAt ℂ G s) ∧
      (∀ x, G=ᶠ[𝓝[≠] x] (fun s => numerator m f s/denominator (2*m) f s)) := by
  obtain ⟨B,hB⟩ := original_common_halfplane hf
  obtain ⟨H,hH⟩ := original_quotient_identity m hm hf
  have hinit (z : ℂ) (hz : max B H<z.re) : AnalyticAt ℂ (quadraticCombination (2*m) f) z := by
    have hs := lt_of_le_of_lt (le_max_left B H) hz
    exact ((hB (1/5) z hs).1.add (hB (-1/5) z hs).1).sub
      ((hB (2/5) z hs).1.add (hB (-2/5) z hs).1)
  obtain ⟨G,hG,hagree,hpole,hgerm⟩ := QuantitativeArithmeticEntireQuotient.continuation
    (numerator m f) (denominator (2*m) f) (quadraticCombination (2*m) f) (max B H)
    (fun z => (original_numerator_entire m hm hf).analyticAt z)
    (fun z => (denominator_entire (2*m) f).analyticAt z)
    (denominator_nonzero (2*m) f) hinit
    (fun z hz => hH z (lt_of_le_of_lt (le_max_right _ _) hz))
  exact ⟨max B H,G,hG,hagree,hpole,hgerm⟩

#print axioms denominator_nonzero
#print axioms original_quotient_identity
#print axioms original_quadratic_continuation
end QuantitativeArithmeticSmallLevelNineteen
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenReflectionLawsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteen
open Complex MeasureTheory SmallLevelNormalized SmallLevelOriginal
open FinitenessFourierConstruction FinitenessOriginalFourier FinitenessRamanujanFourier
open FinitenessNormalizedTwistProduct FinitenessAllLevelAxisDecay SmallLevelAdditive
open scoped MatrixGroups ModularForm

/-- The Ramanujan5 root is trivial at level19. -/
theorem root_five (f : ℕ → ℂ) : root 19 f 5=1 := by
  simp [root,(by decide : Nat.Prime 5).primeFactors,FinitenessNormalizedTwistLocal.sign]

/-- Coherent untwisted and tenth-twist Mellin signs are derived from one
original functional-equation sign; no uniqueness-of-sign premise is used. -/
theorem original_scaled_reflections (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      (∀ positive : Bool, ∀ s : ℂ, centeredMellin m f positive s=
        ε*centeredMellin m f positive ((2*m:ℕ)-s)) ∧
      (∀ s : ℂ, mellin (axis 475 (fullCoefficients (twisted f 5) (2*m))) s=
        ε*mellin (axis 475 (fullCoefficients (twisted f 5) (2*m))) ((2*m:ℕ)-s)) := by
  obtain ⟨ε,hε,hlaw⟩ := FinitenessOriginalTwistedContinuations.coherent_solution_laws (by decide : 0<19) hf
  obtain ⟨τ,_,hg⟩ := hf.growth
  let χ : ℂ := ε*I^(2*m)
  have hχ : χ=1 ∨ χ= -1 := by
    have hi : I^(2*m)=(-1:ℂ)^m := by rw [pow_mul,I_sq]
    rcases neg_one_pow_eq_or ℂ m with h|h <;> rcases hε with rfl|rfl <;> simp [χ,hi,h]
  have hfr : fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 19 (by decide)=
      χ • fourierFunction (2*m) f := by
    have h := fricke_law 19 (2*m) (by decide) (fourier (fullCoefficients f (2*m))) χ (by
      intro z hz
      simpa [χ,root,FinitenessAnalyticReconstruction.twist,Finset.sum_range_succ] using hlaw 1 (by decide) z hz)
    change fourierFunction (2*m) f=χ • (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] fricke 19 (by decide)) at h
    rcases hχ with hc|hc
    · rw [hc] at h ⊢
      simpa using h.symm
    · rw [hc] at h ⊢
      simpa only [neg_one_smul,neg_neg] using congrArg Neg.neg h.symm
  have hcent (positive : Bool) :
      (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center positive)) ∣[((2*m:ℕ):ℤ)]
        fricke 1900 (by decide)=χ • (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (center positive)) := by
    obtain ⟨hn,hp⟩ := original_tenth_matrices hf
    cases positive
    · change (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (-(1/10))) ∣[((2*m:ℕ):ℤ)] _=_
      rw [show (-(1/10):ℝ)= -1/10 by ring,← SlashAction.slash_mul,tenth_negative_factor,
        SlashAction.slash_mul,SlashAction.slash_mul]
      change ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] tenthMinus) ∣[((2*m:ℕ):ℤ)] _)
        ∣[((2*m:ℕ):ℤ)] _=_
      rw [hn,hfr,det_one_smul _ (translation_det _)]
      simp [center,neg_div]
    · change (fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] translation (1/10)) ∣[((2*m:ℕ):ℤ)] _=_
      rw [← SlashAction.slash_mul,tenth_positive_factor,SlashAction.slash_mul,SlashAction.slash_mul]
      change ((fourierFunction (2*m) f ∣[((2*m:ℕ):ℤ)] tenthPlus) ∣[((2*m:ℕ):ℤ)] _)
        ∣[((2*m:ℕ):ℤ)] _=_
      rw [hp,hfr,det_one_smul _ (translation_det _)]
      simp [center]
  refine ⟨ε,hε,?_,?_⟩
  · intro positive s
    have h := QuantitativeArithmeticTranslatedFricke.translated_mellin_entire 1900 (2*m)
      (by decide) (by omega) _ (polynomial_bound hf.zero hg (2*m))
      (fullCoefficients_zero hf.zero (2*m)) (center positive) χ hχ (hcent positive)
    change mellin (axis 1900 (coefficients (fullCoefficients f (2*m)) (center positive))) s =
      ε*mellin (axis 1900 (coefficients (fullCoefficients f (2*m)) (center positive))) ((2*m:ℕ)-s)
    simpa only [χ,mul_div_cancel_right₀ _ (pow_ne_zero _ I_ne_zero)] using h.2.2 s
  · have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
    have hfr5 : ∀ z : ℂ, 0<z.im → fourier (fullCoefficients (twisted f 5) (2*m)) z=
        (ε*I^(2*m))/(((Real.sqrt 475:ℂ)*z)^(2*m))*
          fourier (fullCoefficients (twisted f 5) (2*m)) (-1/((475:ℂ)*z)) := by
      intro z hz
      have href : 0<(-1/((475:ℂ)*z)).im :=
        FinitenessComplexGeometry.reflected_im_pos (by norm_num : (0:ℝ)<475) hz
      simpa only [fourier_twisted hf.zero hg 5 (2*m) hz,
        fourier_twisted hf.zero hg 5 (2*m) href,show Nat.lcm 19 (5^2)=475 by decide,
        root_five,one_mul,mul_assoc,Nat.cast_ofNat] using hlaw 5 (by decide) z hz
    exact (FinitenessAllLevelMellinPair.mellin_entire (by decide : 0<475) (by omega) _
      (polynomial_bound (twisted_zero hf.zero 5) (twisted_growth hg 5) (2*m))
      (fullCoefficients_zero (twisted_zero hf.zero 5) (2*m)) ε hε0 hfr5).2.2

/-- Both entire pieces of the quadratic-twist numerator have coherent
unnormalized Mellin reflection laws. -/
theorem original_unscaled_reflections (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    ∃ ε : ℂ, (ε=1 ∨ ε= -1) ∧
      (∀ positive : Bool, ∀ s : ℂ, centerEntire m f positive s=
        ε*(Real.sqrt 1900:ℂ)^((2*m:ℕ)-2*s)*centerEntire m f positive ((2*m:ℕ)-s)) ∧
      (∀ s : ℂ, SmallLevelTaylor.ramanujanEntire 19 (2*m) f 5 s=
        ε*(Real.sqrt 475:ℂ)^((2*m:ℕ)-2*s)*
          SmallLevelTaylor.ramanujanEntire 19 (2*m) f 5 ((2*m:ℕ)-s)) := by
  obtain ⟨ε,hε,hc,hr⟩ := original_scaled_reflections m hm hf
  refine ⟨ε,hε,fun positive => QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection
    (by decide : 0<1900) _ ε (hc positive),?_⟩
  intro s
  have h := QuantitativeArithmeticQuadraticTwistReflection.unscaled_reflection
    (by decide : 0<475) _ ε hr s
  have haxis : axis 1 (fullCoefficients (twisted f 5) (2*m)) =
      (fun y : ℝ => fourier (fullCoefficients (twisted f 5) (2*m)) ((y:ℂ)*I)) := by
    funext y
    simp [axis]
  rw [haxis] at h
  simpa only [SmallLevelTaylor.ramanujanEntire,Nat.cast_ofNat] using h

#print axioms original_scaled_reflections
#print axioms original_unscaled_reflections
end QuantitativeArithmeticSmallLevelNineteen
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenReflectionAlgebraV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteen
open Complex SmallLevelTaylor Filter Set
open scoped Topology

def scaleTwo (k : ℕ) (s : ℂ) : ℂ := (2:ℂ)^((k:ℂ)-2*s)
def reflectionMultiplier (k : ℕ) (ε s : ℂ) : ℂ := ε*(Real.sqrt 475:ℂ)^((k:ℂ)-2*s)

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

theorem heckeScalar_reflection (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    heckeScalar k f s=scaleTwo k s*heckeScalar k f ((k:ℂ)-s) := by
  have hp : scaleTwo k s*(2:ℂ)^(-((k:ℂ)-s))=(2:ℂ)^(-s) := by
    unfold scaleTwo
    rw [← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    ring
  unfold heckeScalar
  rw [← hp]
  ring

theorem oppositeScalar_reflection (k : ℕ) (s : ℂ) :
    oppositeScalar k s=scaleTwo k s*oppositeScalar k ((k:ℂ)-s) := by
  have hp := scaleTwo_product k s
  unfold oppositeScalar
  rw [← scaleTwo_eq,← scaleTwo_eq]
  linear_combination -hp

theorem denominator_reflection (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    denominator k f s=scaleTwo k s*denominator k f ((k:ℂ)-s) := by
  unfold denominator
  rw [heckeScalar_reflection k f s,oppositeScalar_reflection k s]
  ring

theorem center_conductor_factor (k : ℕ) (s : ℂ) :
    (Real.sqrt 1900:ℂ)^((k:ℂ)-2*s)=scaleTwo k s*(Real.sqrt 475:ℂ)^((k:ℂ)-2*s) := by
  have hs : Real.sqrt 1900=2*Real.sqrt 475 := by
    rw [show (1900:ℝ)=4*475 by norm_num,Real.sqrt_mul (by norm_num)]
    norm_num
  rw [hs,Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤2) (Real.sqrt_nonneg _) _

theorem reflectionMultiplier_entire (k : ℕ) (ε : ℂ) : Differentiable ℂ (reflectionMultiplier k ε) := by
  have hn : (Real.sqrt 475:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold reflectionMultiplier
  simp_rw [Complex.cpow_def_of_ne_zero hn]
  fun_prop

theorem reflectionMultiplier_ne_zero (k : ℕ) {ε : ℂ} (hε : ε≠0) (s : ℂ) :
    reflectionMultiplier k ε s≠0 := by
  apply mul_ne_zero hε
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by norm_num)).ne'))

theorem reflectionMultiplier_even (m : ℕ) (ε s : ℂ) :
    reflectionMultiplier (2*m) ε s=ε*(475:ℂ)^((m:ℂ)-s) := by
  have hn : (Real.sqrt 475:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs : (Real.sqrt 475:ℂ)*(Real.sqrt 475:ℂ)=475 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ)≤475)
  have hp := Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg 475) (Real.sqrt_nonneg 475) ((m:ℂ)-s)
  rw [hs] at hp
  unfold reflectionMultiplier
  rw [show ((2*m:ℕ):ℂ)-2*s=((m:ℂ)-s)+((m:ℂ)-s) by push_cast; ring,
    Complex.cpow_add _ _ hn,← hp]

/-- The entire numerator and denominator transform with the same auxiliary
Hecke factor; it cancels without assuming either is nonzero at the point. -/
theorem numerator_reflection (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (hc : ∀ positive : Bool, ∀ s : ℂ, centerEntire m f positive s=
      ε*(Real.sqrt 1900:ℂ)^((2*m:ℕ)-2*s)*centerEntire m f positive ((2*m:ℕ)-s))
    (hr : ∀ s : ℂ, ramanujanEntire 19 (2*m) f 5 s=
      ε*(Real.sqrt 475:ℂ)^((2*m:ℕ)-2*s)*ramanujanEntire 19 (2*m) f 5 ((2*m:ℕ)-s))
    (s : ℂ) : numerator m f s=scaleTwo (2*m) s*reflectionMultiplier (2*m) ε s*
      numerator m f ((2*m:ℕ)-s) := by
  unfold numerator
  rw [oppositeScalar_reflection (2*m) s,heckeScalar_reflection (2*m) f s,
    hr s,hc true s,hc false s,center_conductor_factor (2*m) s]
  unfold reflectionMultiplier
  ring

theorem raw_quotient_reflection (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (hN : ∀ s : ℂ, numerator m f s=scaleTwo (2*m) s*reflectionMultiplier (2*m) ε s*
      numerator m f ((2*m:ℕ)-s)) (s : ℂ) :
    numerator m f s/denominator (2*m) f s=reflectionMultiplier (2*m) ε s*
      (numerator m f ((2*m:ℕ)-s)/denominator (2*m) f ((2*m:ℕ)-s)) := by
  rw [hN s,denominator_reflection (2*m) f s,mul_assoc,
    mul_div_mul_left _ _ (scaleTwo_ne_zero (2*m) s)]
  ring

#print axioms denominator_reflection
#print axioms numerator_reflection
#print axioms raw_quotient_reflection
end QuantitativeArithmeticSmallLevelNineteen
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenReflectionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteen
open Complex SmallLevelAdditive Filter Set
open scoped Topology

/-- The original level19 Euler input yields a global meromorphic continuation
of the actual quadratic additive combination, with its exact conductor475
functional equation. This includes exceptional denominator zeros. Poles
are still permitted, so this is not the modularity theorem. -/
theorem original_quadratic_functional_equation (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    ∃ (ε : ℂ) (bound : ℝ) (G : ℂ → ℂ), (ε=1 ∨ ε= -1) ∧
      (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=quadraticCombination (2*m) f s) ∧
      (∀ s, G s=ε*(475:ℂ)^((m:ℂ)-s)*G ((2*m:ℕ)-s)) ∧
      (∀ s, denominator (2*m) f s≠0 → AnalyticAt ℂ G s) ∧
      (∀ x, G=ᶠ[𝓝[≠] x] (fun s => numerator m f s/denominator (2*m) f s)) := by
  obtain ⟨ε,hε,hc,hr⟩ := original_unscaled_reflections m hm hf
  obtain ⟨bound,G,hG,hagree,hpole,hgerm⟩ := original_quadratic_continuation m hm hf
  have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
  have hN := numerator_reflection m f ε hc hr
  have hfe := QuantitativeArithmeticQuadraticTwistReflection.normal_form_reflection
    (fun s => numerator m f s/denominator (2*m) f s) G
    (reflectionMultiplier (2*m) ε) ((2*m:ℕ):ℂ) hG
    (fun s => (reflectionMultiplier_entire (2*m) ε).analyticAt s)
    (reflectionMultiplier_ne_zero (2*m) hε0) hgerm
    (raw_quotient_reflection m f ε hN)
  refine ⟨ε,bound,G,hε,hG,hagree,?_,hpole,hgerm⟩
  intro s
  simpa only [reflectionMultiplier_even] using hfe s

#print axioms original_quadratic_functional_equation
end QuantitativeArithmeticSmallLevelNineteen
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenPoleGapV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteen
open Complex

/-- The normalized Hecke parameter, with the positive square root convention. -/
def poleParameter (f : ℕ → ℂ) : ℂ := (2:ℂ)^((1:ℂ)/2)*f 2

def poleCoordinate (m : ℕ) (s : ℂ) : ℂ := (2:ℂ)^(s-(m:ℂ))

theorem poleCoordinate_ne_zero (m : ℕ) (s : ℂ) : poleCoordinate m s≠0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

theorem denominator_normalized (m : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    denominator (2*m) f s*poleCoordinate m s^2=
      poleCoordinate m s^2+poleParameter f*poleCoordinate m s+1 := by
  have hn : (2:ℂ)≠0 := by norm_num
  have hs : poleCoordinate m s^2=(2:ℂ)^(2*(s-(m:ℂ))) := by
    unfold poleCoordinate
    rw [pow_two,← Complex.cpow_add _ _ hn]
    congr 1
    ring
  have hc : heckeScalar (2*m) f s*poleCoordinate m s^2=
      poleParameter f*poleCoordinate m s := by
    rw [hs]
    unfold heckeScalar poleParameter poleCoordinate
    rw [Complex.ofReal_cpow (by norm_num : (0:ℝ)≤2)]
    push_cast
    have hp : (2:ℂ)^(((2*(m:ℂ)+1)/2))*(2:ℂ)^(-s)*(2:ℂ)^(2*(s-(m:ℂ)))=
        (2:ℂ)^((1:ℂ)/2)*(2:ℂ)^(s-(m:ℂ)) := by
      rw [← Complex.cpow_add _ _ hn,← Complex.cpow_add _ _ hn,← Complex.cpow_add _ _ hn]
      congr 1
      ring
    linear_combination f 2*hp
  have hd : scaleTwo (2*m) s*poleCoordinate m s^2=1 := by
    rw [hs]
    unfold scaleTwo
    rw [← Complex.cpow_add _ _ hn]
    convert Complex.cpow_zero (2:ℂ) using 1
    congr 1
    push_cast
    ring
  unfold denominator oppositeScalar
  rw [← scaleTwo_eq]
  linear_combination hc+hd

/-- Every actual denominator zero satisfies the normalized Hecke quadratic. -/
theorem denominator_zero_quadratic (m : ℕ) (f : ℕ → ℂ) (s : ℂ)
    (h : denominator (2*m) f s=0) :
    poleCoordinate m s^2+poleParameter f*poleCoordinate m s+1=0 := by
  rw [← denominator_normalized,h,zero_mul]

theorem poleCoordinate_shift (m n : ℕ) (s : ℂ) :
    poleCoordinate m (s+(n:ℂ))=(2:ℂ)^n*poleCoordinate m s := by
  unfold poleCoordinate
  rw [← Complex.cpow_natCast,← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
  congr 1
  ring

/-- Exact gap equation at the integer translate of a denominator zero.
No restrictions on the Hecke eigenvalue or on the zero multiplicity occur. -/
theorem denominator_zero_gap (m n : ℕ) (f : ℕ → ℂ) (s : ℂ)
    (h : denominator (2*m) f s=0) :
    poleParameter f*poleCoordinate m (s+(n:ℂ))=
      -poleCoordinate m (s+(n:ℂ))^2/(2:ℂ)^n-(2:ℂ)^n := by
  have he := denominator_zero_quadratic m f s h
  have hn : (2:ℂ)^n≠0 := pow_ne_zero _ (by norm_num)
  rw [poleCoordinate_shift]
  field_simp
  linear_combination he

/-- Arithmetic endpoint of the generic polynomial certificate: its values
X=4 and A=-3 cannot satisfy the actual denominator gap equation. -/
theorem denominator_gap_excludes_four (m n : ℕ) (f : ℕ → ℂ) (s : ℂ)
    (h : denominator (2*m) f s=0)
    (hx : poleCoordinate m (s+(n:ℂ))^2=4)
    (ha : poleParameter f*poleCoordinate m (s+(n:ℂ))= -3) : False := by
  have he := denominator_zero_gap m n f s h
  rw [hx,ha] at he
  have hn : (2:ℂ)^n≠0 := pow_ne_zero _ (by norm_num)
  have hpoly : ((2:ℂ)^n)^2-3*(2:ℂ)^n+4=0 := by
    field_simp at he
    linear_combination he
  have hr : ((2:ℝ)^n)^2-3*(2:ℝ)^n+4=0 := by exact_mod_cast hpoly
  nlinarith [sq_nonneg ((2:ℝ)^n-3/2)]

#print axioms denominator_normalized
#print axioms denominator_zero_gap
#print axioms denominator_gap_excludes_four
end QuantitativeArithmeticSmallLevelNineteen
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenPoleConstraintsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteen
open Complex

theorem nonanalytic_reflected (m : ℕ) (G : ℂ → ℂ) (ε : ℂ)
    (hfe : ∀ s, G s=ε*(475:ℂ)^((m:ℂ)-s)*G ((2*m:ℕ)-s))
    (s : ℂ) (hs : ¬ AnalyticAt ℂ G s) :
    ¬ AnalyticAt ℂ G ((2*m:ℕ)-s) := by
  intro hr
  have hm : AnalyticAt ℂ (fun z : ℂ => ε*(475:ℂ)^((m:ℂ)-z)) s := by
    have he := (reflectionMultiplier_entire (2*m) ε).analyticAt s
    change AnalyticAt ℂ (fun z => reflectionMultiplier (2*m) ε z) s at he
    simpa only [reflectionMultiplier_even] using he
  have he : AnalyticAt ℂ (fun z : ℂ => ε*(475:ℂ)^((m:ℂ)-z)*G ((2*m:ℕ)-z)) s :=
    hm.mul (hr.comp (analyticAt_const.sub analyticAt_id))
  exact hs ((funext hfe) ▸ he)

/-- The actual reflection law allows a hypothetical pole to be chosen on
or to the right of the central line. -/
theorem right_halfplane_pole (m : ℕ) (G : ℂ → ℂ) (ε : ℂ)
    (hfe : ∀ s, G s=ε*(475:ℂ)^((m:ℂ)-s)*G ((2*m:ℕ)-s))
    (hpole : ∃ s, ¬ AnalyticAt ℂ G s) :
    ∃ s, (m:ℝ)≤s.re ∧ ¬ AnalyticAt ℂ G s := by
  obtain ⟨s,hs⟩ := hpole
  by_cases hr : (m:ℝ)≤s.re
  · exact ⟨s,hr,hs⟩
  · refine ⟨(2*m:ℕ)-s,?_,nonanalytic_reflected m G ε hfe s hs⟩
    have hre : (((2*m:ℕ):ℂ)-s).re=2*(m:ℝ)-s.re := by simp
    rw [hre]
    linarith

/-- The shifted coordinate is at least its real integer scale in modulus
when the original pole lies in the right half-plane. -/
theorem poleCoordinate_norm_lower (m n : ℕ) (s : ℂ) (hs : (m:ℝ)≤s.re) :
    (2:ℝ)^n≤‖poleCoordinate m (s+(n:ℂ))‖ := by
  rw [poleCoordinate_shift,norm_mul]
  have hn : ‖(2:ℂ)^n‖=(2:ℝ)^n := by simp
  rw [hn]
  have hbase : 1≤‖poleCoordinate m s‖ := by
    unfold poleCoordinate
    rw [show (2:ℂ)=((2:ℝ):ℂ) by norm_num,Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    simp only [sub_re,natCast_re]
    calc
      1=(2:ℝ)^(0:ℝ) := by rw [Real.rpow_zero]
      _≤(2:ℝ)^(s.re-(m:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]

/-- A quadratic root is confined to a closed annulus depending only on the
Hecke parameter. This uses no reality assumption on that parameter. -/
theorem denominator_zero_coordinate_bounds (m : ℕ) (f : ℕ → ℂ) (s : ℂ)
    (h : denominator (2*m) f s=0) :
    ‖poleCoordinate m s‖≤‖poleParameter f‖+1 ∧
      1≤(‖poleParameter f‖+1)*‖poleCoordinate m s‖ := by
  have he := denominator_zero_quadratic m f s h
  have ht : poleCoordinate m s^2= -(poleParameter f*poleCoordinate m s)-1 := by
    linear_combination he
  have hn : ‖poleCoordinate m s‖^2≤‖poleParameter f‖*‖poleCoordinate m s‖+1 := by
    calc
      ‖poleCoordinate m s‖^2=‖poleCoordinate m s^2‖ := (norm_pow _ _).symm
      _=‖-(poleParameter f*poleCoordinate m s)-1‖ := by rw [ht]
      _≤‖-(poleParameter f*poleCoordinate m s)‖+‖(1:ℂ)‖ := norm_sub_le _ _
      _=‖poleParameter f‖*‖poleCoordinate m s‖+1 := by simp
  have hupper : ‖poleCoordinate m s‖≤‖poleParameter f‖+1 := by
    nlinarith [norm_nonneg (poleCoordinate m s),norm_nonneg (poleParameter f)]
  refine ⟨hupper,?_⟩
  have hone : (1:ℂ)= -(poleCoordinate m s^2+poleParameter f*poleCoordinate m s) := by
    linear_combination he
  have hlow : 1≤‖poleCoordinate m s‖^2+‖poleParameter f‖*‖poleCoordinate m s‖ := by
    calc
      1=‖(1:ℂ)‖ := by simp
      _=‖poleCoordinate m s^2+poleParameter f*poleCoordinate m s‖ := by rw [hone,norm_neg]
      _≤‖poleCoordinate m s^2‖+‖poleParameter f*poleCoordinate m s‖ := norm_add_le _ _
      _=‖poleCoordinate m s‖^2+‖poleParameter f‖*‖poleCoordinate m s‖ := by simp
  by_cases ht1 : 1≤‖poleCoordinate m s‖
  · nlinarith [norm_nonneg (poleParameter f)]
  · nlinarith [norm_nonneg (poleCoordinate m s)]

/-- Full original-input reduction: any non-entire quadratic continuation has
a right-half-plane denominator zero, with its exact gap equation at every
nonnegative integer shift. This is a reduction, not pole exclusion. -/
theorem original_quadratic_pole_reduction (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 19 (2*m) f) :
    ∃ (ε : ℂ) (bound : ℝ) (G : ℂ → ℂ), (ε=1 ∨ ε= -1) ∧
      (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=quadraticCombination (2*m) f s) ∧
      (∀ s, G s=ε*(475:ℂ)^((m:ℂ)-s)*G ((2*m:ℕ)-s)) ∧
      ((∃ s, ¬ AnalyticAt ℂ G s) → ∃ s, (m:ℝ)≤s.re ∧
        ¬ AnalyticAt ℂ G s ∧ denominator (2*m) f s=0 ∧
        ∀ n : ℕ, poleParameter f*poleCoordinate m (s+(n:ℂ))=
          -poleCoordinate m (s+(n:ℂ))^2/(2:ℂ)^n-(2:ℂ)^n) := by
  obtain ⟨ε,bound,G,hε,hG,ha,hfe,hpole,_⟩ := original_quadratic_functional_equation m hm hf
  refine ⟨ε,bound,G,hε,hG,ha,hfe,?_⟩
  intro hbad
  obtain ⟨s,hs,hnot⟩ := right_halfplane_pole m G ε hfe hbad
  have hd : denominator (2*m) f s=0 := by
    by_contra hn
    exact hnot (hpole s hn)
  exact ⟨s,hs,hnot,hd,fun n => denominator_zero_gap m n f s hd⟩

#print axioms right_halfplane_pole
#print axioms poleCoordinate_norm_lower
#print axioms denominator_zero_coordinate_bounds
#print axioms original_quadratic_pole_reduction
end QuantitativeArithmeticSmallLevelNineteen
end
end

/-! ## QuantitativeArithmeticSmallLevelNineteenCentralGapV1 -/
section
set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelNineteen
open Complex
open QuantitativeArithmeticSmallLevelNineteenGridSystem

theorem poleParameter_sqrt (f : ℕ→ℂ) : poleParameter f=(Real.sqrt 2:ℂ)*f 2 := by
  unfold poleParameter
  have h := Complex.ofReal_cpow (by norm_num : (0:ℝ)≤2) (1/2:ℝ)
  rw [← Real.sqrt_eq_rpow] at h
  norm_num only [Complex.ofReal_ofNat,Complex.ofReal_div,Complex.ofReal_one] at h
  rw [← h]

/-- A point on the unit circle cannot be a positive integer shift to the
right of the critical half-plane. -/
theorem unit_parameter_gap_zero {p : ℕ} (hp : 1<p) (m n : ℕ) (s : ℂ)
    (hs : (m:ℝ)≤s.re) (hunit : ‖primeParameter p m (s+(n:ℂ))‖=1) : n=0 := by
  by_contra hn
  have hnpos : (0:ℝ)<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hre : 0<(s+(n:ℂ)-(m:ℂ)).re := by
    simp only [sub_re,add_re,natCast_re]
    linarith
  have hpR : (1:ℝ)<(p:ℝ) := by exact_mod_cast hp
  have hgt := Real.one_lt_rpow hpR hre
  have hnorm : ‖primeParameter p m (s+(n:ℂ))‖=(p:ℝ)^((s+(n:ℂ)-(m:ℂ)).re) := by
    unfold primeParameter
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ)<(p:ℝ)) _
  rw [hnorm] at hunit
  linarith

theorem central_three_gap (m n : ℕ) (f : ℕ→ℂ) (s : ℂ)
    (hs : (m:ℝ)≤s.re) (hd : denominator (2*m) f s=0)
    (hy2 : (primeParameter 3 m (s+(n:ℂ)))^2= -1) :
    n=0 ∧ (Real.sqrt 2:ℂ)*f 2= -primeParameter 2 m (s+(n:ℂ))-1/primeParameter 2 m (s+(n:ℂ)) := by
  have hunit : ‖primeParameter 3 m (s+(n:ℂ))‖=1 := by
    have h := congrArg norm hy2
    rw [norm_pow] at h
    norm_num at h
    rcases h with h|h
    · exact h
    · have hn := norm_nonneg (primeParameter 3 m (s+(n:ℂ)))
      linarith
  have hn := unit_parameter_gap_zero (by decide : 1<3) m n s hs hunit
  refine ⟨hn,?_⟩
  rw [hn,Nat.cast_zero,add_zero]
  have h := denominator_zero_quadratic m f s hd
  rw [poleParameter_sqrt] at h
  change (primeParameter 2 m s)^2+((Real.sqrt 2:ℂ)*f 2)*primeParameter 2 m s+1=0 at h
  have hx : primeParameter 2 m s≠0 := poleCoordinate_ne_zero m s
  apply (mul_right_cancel₀ hx)
  linear_combination (norm := (field_simp [hx]; ring1)) h

#print axioms poleParameter_sqrt
#print axioms unit_parameter_gap_zero
#print axioms central_three_gap
end QuantitativeArithmeticSmallLevelNineteen
end
end
