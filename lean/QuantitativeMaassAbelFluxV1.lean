module

public import QuantitativeMaassAbelSmoothV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- The boundary flux whose integral supplies the radial Abel intertwining.
It vanishes at s=0 and outside a compact set. -/
def abelFlux (f : ℝ → ℂ) (q s : ℝ) : ℂ :=
  ((q:ℂ)*(s:ℂ)+(s:ℂ)^3/2)*deriv f (q+s^2)+(3/4:ℂ)*(s:ℂ)*f (q+s^2)

theorem abelFlux_smooth (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (q : ℝ) :
    ContDiff ℝ ∞ (abelFlux f q) := by
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  have hz : ContDiff ℝ ∞ (fun s : ℝ => (s:ℂ)) := Complex.ofRealCLM.contDiff
  unfold abelFlux
  fun_prop

theorem abelFlux_compact (f : ℝ → ℂ) (hc : HasCompactSupport f) (q : ℝ) :
    HasCompactSupport (abelFlux f q) :=
  (quadratic_compactSupport (deriv f) hc.deriv q).mul_left.add
    (quadratic_compactSupport f hc q).mul_left

theorem abelFlux_hasDerivAt (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (q s : ℝ) :
    HasDerivAt (abelFlux f q)
      (((2*q*s^2+s^4:ℝ):ℂ)*deriv (deriv f) (q+s^2)+
        ((q+3*s^2:ℝ):ℂ)*deriv f (q+s^2)+(3/4:ℂ)*f (q+s^2)) s := by
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  have hr := ((hasDerivAt_id s).pow 2).const_add q
  have hg := ((hf.differentiable (by simp)) (q+s^2)).hasDerivAt.scomp s hr
  have hg' := ((hf'.differentiable (by simp)) (q+s^2)).hasDerivAt.scomp s hr
  have hz := (hasDerivAt_id s).ofReal_comp
  have hp := (hz.const_mul (q:ℂ)).add ((hz.pow 3).div_const 2)
  have hd := (hp.mul hg').add ((hz.const_mul (3/4:ℂ)).mul hg)
  convert hd using 1
  · rfl
  · simp only [Function.comp_def,Pi.pow_apply,Pi.add_apply,id_eq,
      Complex.real_smul,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
    push_cast
    ring

theorem abelFlux_integral_deriv_zero (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (q : ℝ) :
    (∫ s in Ioi (0:ℝ), deriv (abelFlux f q) s)=0 := by
  rw [HasCompactSupport.integral_Ioi_deriv_eq
    ((abelFlux_smooth f hf q).of_le (by simp)) (abelFlux_compact f hc q)]
  simp only [abelFlux,Complex.ofReal_zero,mul_zero,zero_pow (by decide : 3≠0),
    zero_div,add_zero,zero_mul,neg_zero]

/-- The derivative of the cosh-coordinate time Laplacian, acting on F'. -/
def abelAuxOperator (f : ℝ → ℂ) (v : ℝ) : ℂ :=
  ((v:ℂ)^2-1)*deriv (deriv f) v+3*(v:ℂ)*deriv f v+f v

/-- Exact Abel differential identity from the proved zero boundary flux. -/
theorem abelIntegral_auxOperator (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (q : ℝ) :
    abelIntegral (abelAuxOperator f) q=
      ((q:ℂ)^2-1)*abelIntegral (deriv (deriv f)) q+
        2*(q:ℂ)*abelIntegral (deriv f) q+(1/4:ℂ)*abelIntegral f q := by
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  have hf'' := (contDiff_infty_iff_deriv.mp hf').2
  have h0 := (quadratic_integrable f hf.continuous hc q).integrableOn (s:=Ioi (0:ℝ))
  have h1 := (quadratic_integrable (deriv f) hf'.continuous hc.deriv q).integrableOn (s:=Ioi (0:ℝ))
  have h2 := (quadratic_integrable (deriv (deriv f)) hf''.continuous hc.deriv.deriv q).integrableOn (s:=Ioi (0:ℝ))
  have hflux : Integrable (deriv (abelFlux f q)) :=
    ((abelFlux_smooth f hf q).continuous_deriv (by simp)).integrable_of_hasCompactSupport
    (abelFlux_compact f hc q).deriv
  have he : abelIntegral (abelAuxOperator f) q=
      ∫ s in Ioi (0:ℝ), (((q:ℂ)^2-1)*deriv (deriv f) (q+s^2)+
        2*(q:ℂ)*deriv f (q+s^2)+(1/4:ℂ)*f (q+s^2))+deriv (abelFlux f q) s := by
    unfold abelIntegral
    apply integral_congr_ae
    filter_upwards with s
    rw [(abelFlux_hasDerivAt f hf q s).deriv]
    unfold abelAuxOperator
    push_cast
    ring
  have ha := h2.const_mul ((q:ℂ)^2-1)
  have hb := h1.const_mul (2*(q:ℂ))
  have hc₀ := h0.const_mul (1/4:ℂ)
  have hsplit₁ := integral_add ha hb
  have hsplit₂ := integral_add (ha.add hb) hc₀
  have hsplit₃ := integral_add ((ha.add hb).add hc₀) hflux.integrableOn
  simp only [Pi.add_apply] at hsplit₁ hsplit₂ hsplit₃
  rw [he,hsplit₃,hsplit₂,hsplit₁,abelFlux_integral_deriv_zero f hf hc q,add_zero,
    integral_const_mul,integral_const_mul,integral_const_mul]
  rfl

#print axioms abelFlux_hasDerivAt
#print axioms abelFlux_integral_deriv_zero
#print axioms abelIntegral_auxOperator

end QuantitativeMaass
