module

public import QuantitativeMaassHeckeWordKernelV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- Symmetric time translation is the time-side action of a cosine wave. -/
def evenTimeTranslate (s : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (f (u-s)+f (u+s))/2

theorem evenTimeTranslate_smooth (s : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (evenTimeTranslate s f) := by
  unfold evenTimeTranslate
  fun_prop

theorem evenTimeTranslate_even (s : ℝ) (f : ℝ → ℂ) (he : Function.Even f) :
    Function.Even (evenTimeTranslate s f) := by
  intro u
  change (f (-u-s)+f (-u+s))/2=(f (u-s)+f (u+s))/2
  rw [show -u-s= -(u+s) by ring,show -u+s= -(u-s) by ring,he (u+s),he (u-s)]
  ring

theorem evenTimeTranslate_real (s : ℝ) (f : ℝ → ℂ) (hr : ∀ u,star (f u)=f u) (u : ℝ) :
    star (evenTimeTranslate s f u)=evenTimeTranslate s f u := by
  change star ((f (u-s)+f (u+s))/(2:ℂ))=(f (u-s)+f (u+s))/(2:ℂ)
  rw [star_div₀,star_add,hr,hr,star_ofNat]

theorem evenTimeTranslate_add (s : ℝ) (f g : ℝ → ℂ) :
    evenTimeTranslate s (f+g)=evenTimeTranslate s f+evenTimeTranslate s g := by
  funext u
  simp only [evenTimeTranslate,Pi.add_apply]
  ring

/-- Symmetric translation costs precisely the added absolute translation
in the time support. -/
theorem evenTimeTranslate_support (s L : ℝ) (f : ℝ → ℂ)
    (hs : Function.support f⊆Icc (-L) L) :
    Function.support (evenTimeTranslate s f)⊆Icc (-(L+|s|)) (L+|s|) := by
  intro u hu
  have hsome : f (u-s)≠0 ∨ f (u+s)≠0 := by
    by_contra hh
    push Not at hh
    exact hu (by simp only [evenTimeTranslate,hh.1,hh.2,add_zero,zero_div])
  rcases hsome with h|h
  · have hh := hs h
    constructor <;> linarith [hh.1,hh.2,le_abs_self s,neg_abs_le s]
  · have hh := hs h
    constructor <;> linarith [hh.1,hh.2,le_abs_self s,neg_abs_le s]

theorem evenTimeTranslate_compact (s : ℝ) (f : ℝ → ℂ) (hc : HasCompactSupport f) :
    HasCompactSupport (evenTimeTranslate s f) := by
  have hm : HasCompactSupport (fun u => f (u-s)) := by
    have hh : (fun u => f (u-s))=f ∘ (Homeomorph.addRight (-s)) := by
      funext u
      change f (u-s)=f (u+ -s)
      rw [sub_eq_add_neg]
    rw [hh]
    exact hc.comp_homeomorph (Homeomorph.addRight (-s))
  have hp : HasCompactSupport (fun u => f (u+s)) := hc.comp_homeomorph (Homeomorph.addRight s)
  have hh : HasCompactSupport (((fun u => f (u-s))+(fun u => f (u+s)))*(fun _ => (2:ℂ)⁻¹)) :=
    (hm.add hp).mul_right
  have he : evenTimeTranslate s f=((fun u => f (u-s))+(fun u => f (u+s)))*(fun _ => (2:ℂ)⁻¹) := by
    funext u
    exact div_eq_mul_inv _ _
  rw [he]
  exact hh

/-- Exact carrier after time translation, including its two unit phases. -/
def translatedCarrier (t s : ℝ) (A : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Complex.exp (((-t*s):ℝ)*Complex.I)*A (u-s)+
    Complex.exp (((t*s):ℝ)*Complex.I)*A (u+s))/2

theorem translatedCarrier_smooth (t s : ℝ) (A : ℝ → ℂ) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (translatedCarrier t s A) := by
  unfold translatedCarrier
  fun_prop

theorem translatedCarrier_support (t s L : ℝ) (A : ℝ → ℂ)
    (hs : Function.support A⊆Icc (-L) L) :
    Function.support (translatedCarrier t s A)⊆Icc (-(L+|s|)) (L+|s|) := by
  intro u hu
  have hsome : A (u-s)≠0 ∨ A (u+s)≠0 := by
    by_contra hh
    push Not at hh
    exact hu (by simp only [translatedCarrier,hh.1,hh.2,mul_zero,add_zero,zero_div])
  rcases hsome with h|h
  · have hh := hs h
    constructor <;> linarith [hh.1,hh.2,le_abs_self s,neg_abs_le s]
  · have hh := hs h
    constructor <;> linarith [hh.1,hh.2,le_abs_self s,neg_abs_le s]

/-- Time translation does not create frequency factors in derivatives of
the slowly varying carrier amplitude. -/
theorem translatedCarrier_iteratedDeriv (t s : ℝ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) (n : ℕ) :
    iteratedDeriv n (translatedCarrier t s A)=translatedCarrier t s (iteratedDeriv n A) := by
  funext u
  have hm : ContDiff ℝ ∞ (fun v => A (v-s)) := by fun_prop
  have hp : ContDiff ℝ ∞ (fun v => A (v+s)) := by fun_prop
  have hcm : ContDiff ℝ ∞ (fun v => Complex.exp (((-t*s):ℝ)*Complex.I)*A (v-s)) := by fun_prop
  have hcp : ContDiff ℝ ∞ (fun v => Complex.exp (((t*s):ℝ)*Complex.I)*A (v+s)) := by fun_prop
  unfold translatedCarrier
  rw [iteratedDeriv_div_const]
  rw [iteratedDeriv_fun_add (hcm.of_le (by simp)).contDiffAt (hcp.of_le (by simp)).contDiffAt]
  rw [iteratedDeriv_const_mul _ (hm.of_le (by simp)).contDiffAt,
    iteratedDeriv_const_mul _ (hp.of_le (by simp)).contDiffAt,
    iteratedDeriv_comp_sub_const,iteratedDeriv_comp_add_const]

/-- Uniform derivative bounds are unchanged by symmetric translation. -/
theorem translatedCarrier_derivative_bound (t s : ℝ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) (n : ℕ) (M : ℝ)
    (hb : ∀ u,‖iteratedDeriv n A u‖≤M) (u : ℝ) :
    ‖iteratedDeriv n (translatedCarrier t s A) u‖≤M := by
  rw [translatedCarrier_iteratedDeriv t s A hA n]
  unfold translatedCarrier
  rw [norm_div,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  calc
    _ ≤ _ := norm_add_le _ _
    _ = ‖iteratedDeriv n A (u-s)‖+‖iteratedDeriv n A (u+s)‖ := by
      simp only [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
    _ ≤ M+M := add_le_add (hb _) (hb _)
    _ = _ := by ring

/-- The phases in the translated amplitude recover the literal time translate. -/
theorem timeFrequencyShift_translatedCarrier (t s : ℝ) (A : ℝ → ℂ) :
    timeFrequencyShift t (translatedCarrier t s A)=evenTimeTranslate s (timeFrequencyShift t A) := by
  funext u
  have hm : Complex.exp (((t*(u-s)):ℝ)*Complex.I)=
      Complex.exp (((t*u):ℝ)*Complex.I)*Complex.exp (((-t*s):ℝ)*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hp : Complex.exp (((t*(u+s)):ℝ)*Complex.I)=
      Complex.exp (((t*u):ℝ)*Complex.I)*Complex.exp (((t*s):ℝ)*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [timeFrequencyShift,translatedCarrier,evenTimeTranslate,hm,hp]
  ring

/-- Exact two-frequency decomposition after applying one cosine translation. -/
theorem evenTimeTranslate_pair_carriers (t s : ℝ) (A B : ℝ → ℂ) :
    evenTimeTranslate s (timeFrequencyShift t A+timeFrequencyShift (-t) B)=
      timeFrequencyShift t (translatedCarrier t s A)+timeFrequencyShift (-t) (translatedCarrier (-t) s B) := by
  rw [evenTimeTranslate_add,timeFrequencyShift_translatedCarrier,timeFrequencyShift_translatedCarrier]

#print axioms evenTimeTranslate_smooth
#print axioms evenTimeTranslate_even
#print axioms evenTimeTranslate_real
#print axioms evenTimeTranslate_add
#print axioms evenTimeTranslate_support
#print axioms evenTimeTranslate_compact
#print axioms translatedCarrier_smooth
#print axioms translatedCarrier_support
#print axioms translatedCarrier_iteratedDeriv
#print axioms translatedCarrier_derivative_bound
#print axioms timeFrequencyShift_translatedCarrier
#print axioms evenTimeTranslate_pair_carriers

end QuantitativeMaass
