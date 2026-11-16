module

public import QuantitativeMaassHigherTimeCarrierV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

namespace QuantitativeMaass

/-- An arbitrary-order derivative bound for modulation, retaining all spectral
frequency dependence explicitly. -/
theorem timeFrequencyShift_iterated_bound (t : ℝ) (n : ℕ) (A : ℝ → ℂ)
    (hA : ContDiff ℝ ∞ A) (M : ℝ)
    (hb : ∀ k : ℕ,k≤n → ∀ u,‖iteratedDeriv k A u‖≤M) (u : ℝ) :
    ‖iteratedDeriv n (timeFrequencyShift t A) u‖≤(|t|+1)^n*M := by
  induction n generalizing A M with
  | zero =>
    simpa only [iteratedDeriv_zero,timeFrequencyShift,norm_mul,Complex.norm_exp_ofReal_mul_I,
      one_mul,pow_zero] using hb 0 le_rfl u
  | succ n ih =>
    rw [iteratedDeriv_succ',timeFrequencyShift_deriv t A hA]
    have hh := ih (timeDerivativeCarrier t A) (timeDerivativeCarrier_smooth t A hA)
      ((|t|+1)*M) (timeDerivativeCarrier_iterated_bound t A hA n M hb)
    convert hh using 1
    ring

/-- Concrete fourth-order bounds for the literal convolution-square window,
with common support and constants uniform in all window parameters. -/
theorem windowTimeSquare_four_derivative_bounds (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ B C : ℝ,0<B ∧ 0<C ∧ ∀ R : ℝ,∀ hR : 1≤R,∀ ε : ℝ,0≤ε → ε≤1 →
      ∀ t : ℝ,1≤t →
      let f := timeConvolution
        (windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε))
        (windowTimeSchwartz K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε))
      Function.support (f : ℝ → ℂ)⊆Icc (-(B*R)) (B*R) ∧
      ∀ n : ℕ,n≤4 → ∀ u,‖iteratedDeriv n (f : ℝ → ℂ) u‖≤C*R*ε^2*(t+1)^4 := by
  obtain ⟨B,C,hB,hC,hbounds⟩ := windowSquareCarrier_uniform_bounds K hc 4
  refine ⟨2*B,2*C,by positivity,by positivity,?_⟩
  intro R hR ε hε hε1 t ht
  dsimp only
  have hRp : 0<R := lt_of_lt_of_le zero_lt_one hR
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
  obtain ⟨hsA,hsB,hder⟩ := hbounds R hR ε hε hε1 t
  obtain ⟨hA,_,hBreg,_⟩ := windowSquareCarrier_regular K hc R ε t hRp
  rw [windowTimeSquare_carriers K he hc R ε t hRp hε]
  constructor
  · intro u hu
    by_contra hn
    have hn' : u∉Icc (-(2*(B*R))) (2*(B*R)) := by
      simpa only [mul_assoc] using hn
    have h0 : windowSquareCarrierPlus K R ε t u=0 := by by_contra hz;exact hn' (hsA hz)
    have h1 : windowSquareCarrierMinus K R ε t u=0 := by by_contra hz;exact hn' (hsB hz)
    exact hu (by simp only [Pi.add_apply,timeFrequencyShift,h0,h1,mul_zero,add_zero])
  · intro n hn u
    have hAn : ContDiffAt ℝ n (timeFrequencyShift t (windowSquareCarrierPlus K R ε t)) u :=
      ((timeFrequencyShift_smooth t _ hA).of_le (by simp)).contDiffAt
    have hBn : ContDiffAt ℝ n (timeFrequencyShift (-t) (windowSquareCarrierMinus K R ε t)) u :=
      ((timeFrequencyShift_smooth (-t) _ hBreg).of_le (by simp)).contDiffAt
    rw [iteratedDeriv_add hAn hBn]
    have hp := timeFrequencyShift_iterated_bound t n _ hA (C*R*ε^2)
      (fun k hk v => (hder k (hk.trans hn) v).1) u
    have hm := timeFrequencyShift_iterated_bound (-t) n _ hBreg (C*R*ε^2)
      (fun k hk v => (hder k (hk.trans hn) v).2) u
    rw [abs_neg,abs_of_pos ht0] at hm
    rw [abs_of_pos ht0] at hp
    have hpow : (t+1)^n≤(t+1)^4 := pow_le_pow_right₀ (by linarith) hn
    apply (norm_add_le _ _).trans ((add_le_add hp hm).trans ?_)
    have hmul := mul_le_mul_of_nonneg_right hpow (by positivity : 0≤C*R*ε^2)
    nlinarith

#print axioms timeFrequencyShift_iterated_bound
#print axioms windowTimeSquare_four_derivative_bounds

end QuantitativeMaass
