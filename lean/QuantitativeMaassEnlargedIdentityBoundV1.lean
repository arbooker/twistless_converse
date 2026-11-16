module

public import QuantitativeMaassWindowIdentityTermV1
public import QuantitativeMaassWindowMajorantV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- Uniform enlarged mass estimate for every fixed positive probability kernel. -/
theorem enlarged_window_mass_uniform (K : SchwartzMap ℝ ℝ)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ C : ℝ,0<C ∧ ∀ (t ε δ R : ℝ),1≤t → ε∈Icc (0:ℝ) 1 → 0≤δ → 2*δ≤ε →
      1≤R → 1/R≤δ →
      Integrable (fun x => (smoothedWindow K R
        (Icc (t-δ) (t+ε+δ)∪Icc (-(t+ε+δ)) (-(t-δ))) x)^2*windowPlancherelWeight x) ∧
      |(∫ x,(smoothedWindow K R
        (Icc (t-δ) (t+ε+δ)∪Icc (-(t+ε+δ)) (-(t-δ))) x)^2*windowPlancherelWeight x)/
        (4*Real.pi)-t*ε/(2*Real.pi)|≤C*(t*δ+1) := by
  let m1 : ℝ := ∫ u,|u| * K u
  let m2 : ℝ := ∫ u,|u|^2*K u
  have hm1 : 0≤m1 := integral_nonneg (fun u => mul_nonneg (abs_nonneg u) (hK u))
  have hm2 : 0≤m2 := integral_nonneg (fun u => mul_nonneg (sq_nonneg _) (hK u))
  let C : ℝ := (32*m1+8*m2+10)/(4*Real.pi)
  have hπ : 0<4*Real.pi := mul_pos (by norm_num) Real.pi_pos
  refine ⟨C,div_pos (by positivity) hπ,?_⟩
  intro t ε δ R ht hε hδ hδε hR hRδ
  have ht0 : 0<t := by linarith
  have hR0 : 0<R := by linarith
  obtain ⟨hi,hb⟩ := enlarged_squaredWindow_plancherel_mass t ε δ (by linarith [hε.2]) hε.1 hδ
    K hK hm R hR0
  refine ⟨hi,?_⟩
  have hfirst : 8*(1+t+ε+δ)*m1/R≤32*m1*(t*δ) := by
    have hcoef : 8*(1+t+ε+δ)*m1≤32*t*m1 :=
      mul_le_mul_of_nonneg_right (by nlinarith [hε.2]) hm1
    calc
      _ ≤ (32*t*m1)/R := div_le_div_of_nonneg_right hcoef hR0.le
      _ = (32*t*m1)*(1/R) := by ring
      _ ≤ (32*t*m1)*δ := mul_le_mul_of_nonneg_left hRδ (by positivity)
      _ = _ := by ring
  have hsecond : 8*m2/R^2≤8*m2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
    have hpow : 1≤R^2 := by nlinarith
    nlinarith [mul_nonneg hm2 (sub_nonneg.mpr hpow)]
  have htd : 0≤t*δ := mul_nonneg ht0.le hδ
  have herror : 8*(1+t+ε+δ)*m1/R+8*m2/R^2+4*t*δ+ε^2+2*ε*δ+2*(ε+2*δ) ≤
      (32*m1+8*m2+10)*(t*δ+1) := by
    nlinarith [mul_nonneg hm2 htd, sq_nonneg (ε-1),
      mul_nonneg (sub_nonneg.mpr hε.2) hε.1,
      mul_nonneg (sub_nonneg.mpr hε.2) hδ]
  have hfull := hb.trans herror
  have hdiv := div_le_div_of_nonneg_right hfull hπ.le
  convert hdiv using 1
  · have hid (I : ℝ) : I/(4*Real.pi)-t*ε/(2*Real.pi) =
        (I-2*t*ε)/(4*Real.pi) := by ring
    rw [hid,abs_div,abs_of_pos hπ]
  · dsimp [C]
    ring

/-- Literal enlarged-window Abel identity estimate with a constant before all
centres, widths, margins and radii. -/
theorem windowIdentityContribution_enlarged_bound (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) :
    ∃ C : ℝ,0<C ∧ ∀ (t ε δ R : ℝ) (hR : 0<R),1≤t → ε∈Icc (0:ℝ) 1 →
      0≤δ → 2*δ≤ε → 1≤R → 1/R≤δ →
      ‖windowIdentityContribution K hc R hR (t-δ) (t+ε+δ)-
        ((t*ε/(2*Real.pi):ℝ):ℂ)‖≤C*(t*δ+1) := by
  obtain ⟨C,hC,hbound⟩ := enlarged_window_mass_uniform K hK hm
  refine ⟨C,hC,?_⟩
  intro t ε δ R hR ht hε hδ hδε hR1 hRδ
  have hb := (hbound t ε δ R ht hε hδ hδε hR1 hRδ).2
  rw [windowIdentityContribution_eq_mass K he hc R hR (t-δ) (t+ε+δ) (by linarith [hε.2])]
  let I : ℝ := ∫ r : ℝ, (smoothedWindow K R
    (Icc (t-δ) (t+ε+δ)∪Icc (-(t+ε+δ)) (-(t-δ))) r)^2*windowPlancherelWeight r
  change ‖(1/(4*Real.pi):ℂ)*(I:ℂ)-((t*ε/(2*Real.pi):ℝ):ℂ)‖≤C*(t*δ+1)
  have heq : (1/(4*Real.pi):ℂ)*(I:ℂ)=((I/(4*Real.pi):ℝ):ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [heq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hb

#print axioms enlarged_window_mass_uniform
#print axioms windowIdentityContribution_enlarged_bound

end QuantitativeMaass
