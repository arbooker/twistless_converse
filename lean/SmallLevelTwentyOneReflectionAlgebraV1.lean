module

public import SmallLevelTwentyOneReflectionLawsV1
public import SmallLevelTwentyOneChiFiveContinuationV1
public import FinitenessFiniteOrderClosureV1
public import QuantitativeArithmeticQuadraticTwistReflectionTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFive
open Complex SmallLevelTaylor Filter Set
open QuantitativeArithmeticSmallLevelNineteen (heckeScalar oppositeScalar)
open SmallLevelTwentyOneTenthMellin
open scoped Topology

def scaleTwo (k : ℕ) (s : ℂ) : ℂ := (2:ℂ)^((k:ℂ)-2*s)
def reflectionMultiplier (k : ℕ) (ε s : ℂ) : ℂ := ε*(Real.sqrt 525:ℂ)^((k:ℂ)-2*s)

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
    (Real.sqrt 2100:ℂ)^((k:ℂ)-2*s)=scaleTwo k s*(Real.sqrt 525:ℂ)^((k:ℂ)-2*s) := by
  have hs : Real.sqrt 2100=2*Real.sqrt 525 := by
    rw [show (2100:ℝ)=4*525 by norm_num,Real.sqrt_mul (by norm_num)]
    norm_num
  rw [hs,Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤2) (Real.sqrt_nonneg _) _

theorem reflectionMultiplier_entire (k : ℕ) (ε : ℂ) : Differentiable ℂ (reflectionMultiplier k ε) := by
  have hn : (Real.sqrt 525:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold reflectionMultiplier
  simp_rw [Complex.cpow_def_of_ne_zero hn]
  fun_prop

theorem reflectionMultiplier_ne_zero (k : ℕ) {ε : ℂ} (hε : ε≠0) (s : ℂ) :
    reflectionMultiplier k ε s≠0 := by
  apply mul_ne_zero hε
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by norm_num)).ne'))

theorem reflectionMultiplier_even (m : ℕ) (ε s : ℂ) :
    reflectionMultiplier (2*m) ε s=ε*(525:ℂ)^((m:ℂ)-s) := by
  have hn : (Real.sqrt 525:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs : (Real.sqrt 525:ℂ)*(Real.sqrt 525:ℂ)=525 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ)≤525)
  have hp := Complex.mul_cpow_ofReal_nonneg (Real.sqrt_nonneg 525) (Real.sqrt_nonneg 525) ((m:ℂ)-s)
  rw [hs] at hp
  unfold reflectionMultiplier
  rw [show ((2*m:ℕ):ℂ)-2*s=((m:ℂ)-s)+((m:ℂ)-s) by push_cast; ring,
    Complex.cpow_add _ _ hn,← hp]

/-- The entire numerator and denominator transform with the same auxiliary
Hecke factor; it cancels without assuming either is nonzero at the point. -/
theorem numerator_reflection (m : ℕ) (f : ℕ → ℂ) (ε : ℂ)
    (hc : ∀ positive : Bool, ∀ s : ℂ, centerEntire m f positive s=
      ε*(Real.sqrt 2100:ℂ)^((2*m:ℕ)-2*s)*centerEntire m f (!positive) ((2*m:ℕ)-s))
    (hr : ∀ s : ℂ, ramanujanEntire 21 (2*m) f 5 s=
      ε*(Real.sqrt 525:ℂ)^((2*m:ℕ)-2*s)*ramanujanEntire 21 (2*m) f 5 ((2*m:ℕ)-s))
    (s : ℂ) : numerator m f s=scaleTwo (2*m) s*reflectionMultiplier (2*m) ε s*
      numerator m f ((2*m:ℕ)-s) := by
  unfold numerator
  rw [oppositeScalar_reflection (2*m) s,heckeScalar_reflection (2*m) f s,
    hr s,hc true s,hc false s,center_conductor_factor (2*m) s]
  simp only [Bool.not_true,Bool.not_false]
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

theorem original_numerator_bound (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    FinitenessFiniteOrder.Bound (numerator m f) := by
  obtain ⟨ε,hε,hlaw⟩ := QuantitativeArithmeticCoherentTaylor.original_coherent_law (by decide : 0<21) hf
  have hc := original_center_laws hm hf ε hε hlaw
  have hr := (original_ramanujan_five_laws hm hf ε hε hlaw).1
  have hhecke : FinitenessFiniteOrder.Bound (heckeScalar (2*m) f) :=
    FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const _)
      (SmallLevelMellinUnscale.negative_cpow_bound (by norm_num : (0:ℝ)<2))
  have hopp : FinitenessFiniteOrder.Bound (oppositeScalar (2*m)) :=
    FinitenessFiniteOrderClosure.add (FinitenessInputBounds.bound_const _)
      (FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const _)
        (SmallLevelMellinUnscale.negative_cpow_bound (by norm_num : (0:ℝ)<4)))
  exact FinitenessFiniteOrderClosure.add
    (FinitenessFiniteOrder.mul (FinitenessFiniteOrderClosure.sub hopp hhecke) hr)
    (FinitenessFiniteOrder.mul (FinitenessInputBounds.bound_const 2)
      (FinitenessFiniteOrderClosure.add (hc true).1 (hc false).1))

/-- The original chi5 additive combination has an explicit meromorphic
functional equation, with no condition on the Hecke eigenvalue. -/
theorem original_reflected_continuation (m : ℕ) (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) :
    ∃ (ε : ℂ) (bound : ℝ) (G : ℂ → ℂ), (ε=1 ∨ ε= -1) ∧
      (∀ s, MeromorphicNFAt G s) ∧
      (∀ s, bound<s.re → G s=quadraticCombination (2*m) f s) ∧
      (∀ s, denominator (2*m) f s≠0 → AnalyticAt ℂ G s) ∧
      (∀ x, G=ᶠ[𝓝[≠] x] (fun s => numerator m f s/denominator (2*m) f s)) ∧
      (∀ s, G s=ε*(525:ℂ)^((m:ℂ)-s)*G (((2*m:ℕ):ℂ)-s)) := by
  obtain ⟨ε,hε,hlaw⟩ := QuantitativeArithmeticCoherentTaylor.original_coherent_law (by decide : 0<21) hf
  obtain ⟨B,G,hG,hagree,hpole,hgerm⟩ := original_quadratic_continuation m hm hf
  have hc := original_center_laws hm hf ε hε hlaw
  have hr := (original_ramanujan_five_laws hm hf ε hε hlaw).2
  have hn := numerator_reflection m f ε (fun b => (hc b).2) hr
  have hε0 : ε≠0 := by rcases hε with rfl|rfl <;> norm_num
  have he := QuantitativeArithmeticQuadraticTwistReflection.normal_form_reflection
    (fun s => numerator m f s/denominator (2*m) f s) G
    (reflectionMultiplier (2*m) ε) (((2*m:ℕ):ℂ)) hG
    (fun s => (reflectionMultiplier_entire (2*m) ε).analyticAt s)
    (reflectionMultiplier_ne_zero (2*m) hε0) hgerm
    (raw_quotient_reflection m f ε hn)
  refine ⟨ε,B,G,hε,hG,hagree,hpole,hgerm,?_⟩
  simpa only [reflectionMultiplier_even] using he

#print axioms denominator_reflection
#print axioms numerator_reflection
#print axioms original_numerator_bound
#print axioms original_reflected_continuation
end SmallLevelTwentyOneChiFive
