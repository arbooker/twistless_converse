module
public import QuantitativeArithmeticLevelThirtyFiveShiftExclusionV1
public meta import SmallLevelCertificateBatchCommandV1
public import QuantitativeArithmeticLevelThirtyFivePoleAlgebraV4
-- Bounded certificate elaboration.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

set_option Elab.async false

/-! ## ThirtyFiveChiThreeReflection -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyFiveChiThree
open Complex SmallLevelAdditive QuantitativeArithmeticSmallLevelThirtyFiveCenters
open FinitenessOriginalFourier
certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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

}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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

}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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

}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

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
certificate_batch {
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
}

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

certificate_batch {
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
}

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

certificate_batch {
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
}

end QuantitativeArithmeticSmallLevelThirtyFiveKnownWords
end
end

