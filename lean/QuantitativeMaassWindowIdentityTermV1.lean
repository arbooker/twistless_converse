module

public import QuantitativeMaassSphericalFourierV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff

namespace QuantitativeMaass

def windowTimeSchwartz (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R) (a b : ℝ) :
    SchwartzMap ℝ ℂ :=
  (symmetricWindowTimeTest_compact K hc R a b hR).toSchwartzMap
    (symmetricWindowTimeTest_smooth K R a b)

/-- The actual Abel identity contribution of the squared time packet.
Identification with radial squared energy is a separate geometric theorem. -/
def windowIdentityContribution (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (R : ℝ) (hR : 0<R) (a b : ℝ) : ℂ :=
  abelProfile (evenCoshLift (timeConvolution (windowTimeSchwartz K hc R hR a b)
    (windowTimeSchwartz K hc R hR a b))) 1

/-- The scalar moving-window mass is exactly the Abel identity term. -/
theorem windowIdentityContribution_eq_mass (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (R : ℝ) (hR : 0<R) (a b : ℝ) (ha : 0<a) :
    windowIdentityContribution K hc R hR a b=(1/(4*Real.pi):ℂ)*
      ((∫ r : ℝ, (smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r)^2*
        windowPlancherelWeight r):ℝ) := by
  let f := windowTimeSchwartz K hc R hR a b
  have hf : Function.Even f := symmetricWindowTimeTest_even K he R a b
  have hr : ∀ t,star (f t)=f t := symmetricWindowTimeTest_real K he R a b
  have hfc : HasCompactSupport (f : ℝ → ℂ) := symmetricWindowTimeTest_compact K hc R a b hR
  change abelProfile (evenCoshLift (timeConvolution f f)) 1=_
  rw [abelProfile_timeSquare_diagonal f hf hr hfc]
  congr 1
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with r
  have hcos : cosinePacket f r=(smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r:ℂ) :=
    symmetricWindowTimeTest_cosinePacket K he hc R a b r hR ha
  rw [hcos]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, windowPlancherelWeight, mul_assoc]

/-- Explicit main term and error for the literal Abel identity contribution. -/
theorem windowIdentityContribution_error (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ r,0≤K r) (hm : (∫ r,K r)=1)
    (R : ℝ) (hR : 0<R) (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ‖(4*Real.pi:ℂ)*windowIdentityContribution K hc R hR a b-((b^2-a^2:ℝ):ℂ)‖ ≤
      8*(1+b)*(∫ u,|u| * K u)/R+8*(∫ u,|u|^2*K u)/R^2+2*(b-a) := by
  have hmass := (symmetric_squaredWindow_plancherel_mass a b ha hab K hK hm R hR).2
  have hscale : (4*Real.pi:ℂ)*windowIdentityContribution K hc R hR a b =
      ((∫ r : ℝ, (smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r)^2*
        windowPlancherelWeight r):ℝ) := by
    rw [windowIdentityContribution_eq_mass K he hc R hR a b ha]
    have hn : (4*Real.pi:ℂ)≠0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [← mul_assoc, mul_one_div_cancel hn, one_mul]
  rw [hscale, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hmass

/-- The original shrinking-window normalization now holds for a literal
Abel diagonal, with one constructed kernel and one constant before all windows. -/
theorem exists_uniform_window_identity_main :
    ∃ (K : SchwartzMap ℝ ℝ) (C : ℝ)
      (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))),
      0<C ∧ (∀ x,0≤K x) ∧ Function.Even K ∧ (∫ x,K x)=1 ∧
      ∀ (t ε δ R : ℝ) (hR : 0<R),1≤t → ε∈Icc (0:ℝ) 1 → 0≤δ → 2*δ≤ε →
        1≤R → 1/R≤δ →
        ‖windowIdentityContribution K hc R hR (t+δ) (t+ε-δ)-
          ((t*ε/(2*Real.pi):ℝ):ℂ)‖ ≤ C*(t*δ+1) := by
  obtain ⟨K,C,hC,hK,he,hm,hc,hbound⟩ := exists_uniform_window_plancherel_mass
  refine ⟨K,C,hc,hC,hK,he,hm,?_⟩
  intro t ε δ R hR ht hε hδ hδε hR1 hRδ
  have hb := (hbound t ε δ R ht hε hδ hδε hR1 hRδ).2
  rw [windowIdentityContribution_eq_mass K he hc R hR (t+δ) (t+ε-δ) (by linarith)]
  let I : ℝ := ∫ r : ℝ, (smoothedWindow K R
    (Icc (t+δ) (t+ε-δ)∪Icc (-(t+ε-δ)) (-(t+δ))) r)^2*windowPlancherelWeight r
  change ‖(1/(4*Real.pi):ℂ)*(I:ℂ)-((t*ε/(2*Real.pi):ℝ):ℂ)‖≤C*(t*δ+1)
  have heq : (1/(4*Real.pi):ℂ)*(I:ℂ)=((I/(4*Real.pi):ℝ):ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [heq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hb

end QuantitativeMaass

#print axioms QuantitativeMaass.windowIdentityContribution_eq_mass
#print axioms QuantitativeMaass.windowIdentityContribution_error
#print axioms QuantitativeMaass.exists_uniform_window_identity_main
