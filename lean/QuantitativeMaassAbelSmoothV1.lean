module

public import QuantitativeMaassAbelIntegralV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuantitativeMaass

theorem abelIntegral_deriv (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    deriv (abelIntegral f)=abelIntegral (deriv f) :=
  funext fun q => (abelIntegral_hasDerivAt f hf hc q).deriv

/-- All parameter derivatives exist; compactness supplies the domination
at each order. No assumed regularity of the Abel transform is used. -/
theorem abelIntegral_smooth (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (abelIntegral f) := by
  have hn : ∀ n : ℕ, ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ContDiff ℝ n (abelIntegral f) := by
    intro n
    induction n with
    | zero =>
      intro f hf hc
      apply contDiff_zero.mpr
      exact (show Differentiable ℝ (abelIntegral f) from
        fun q => (abelIntegral_hasDerivAt f hf hc q).differentiableAt).continuous
    | succ n ih =>
      intro f hf hc
      rw [show (↑(n+1):ℕ∞ω)=(n:ℕ∞ω)+1 from by simp,contDiff_succ_iff_deriv]
      refine ⟨fun q => (abelIntegral_hasDerivAt f hf hc q).differentiableAt,by simp,?_⟩
      rw [abelIntegral_deriv f hf hc]
      exact ih (deriv f) (contDiff_infty_iff_deriv.mp hf).2 hc.deriv
  exact contDiff_infty.mpr (fun n => hn n f hf hc)

theorem abelIntegral_zero_above (f : ℝ → ℂ) (B q : ℝ)
    (hs : Function.support f⊆Iic B) (hq : B<q) : abelIntegral f q=0 := by
  have hz (s : ℝ) : f (q+s^2)=0 := by
    by_contra hn
    have hh : q+s^2≤B := hs hn
    nlinarith [sq_nonneg s]
  simp only [abelIntegral,hz,integral_zero]

/-- The normalized radial profile corresponding to an even time test
of the form phi(t)=F(cosh t). The spectral identification remains separate. -/
def abelProfile (F : ℝ → ℂ) (q : ℝ) : ℂ :=
  -(Real.sqrt 2/Real.pi:ℂ)*abelIntegral (deriv F) q

theorem abelProfile_smooth (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) : ContDiff ℝ ∞ (abelProfile F) :=
  contDiff_const.mul (abelIntegral_smooth (deriv F) (contDiff_infty_iff_deriv.mp hF).2 hc.deriv)

theorem abelProfile_support (F : ℝ → ℂ) (B : ℝ) (hs : Function.support F⊆Iic B) :
    Function.support (abelProfile F)⊆Iic B := by
  intro q hq
  by_contra hB
  have hs' : Function.support (deriv F)⊆Iic B :=
    support_deriv_subset.trans (closure_minimal hs isClosed_Iic)
  have hz := abelIntegral_zero_above (deriv F) B q hs' (lt_of_not_ge hB)
  exact hq (by simp only [abelProfile,hz,mul_zero])

/-- The nonsingular Abel transform produces an actual compact radial
seed and hence the previously constructed quotient L2 kernel columns. -/
def abelRadialSeed (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (w : UpperHalfPlane) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) : SmoothUpperSeed :=
  radialSeed (abelProfile F) (abelProfile_smooth F hF hc) w R hR (abelProfile_support F _ hs)

#print axioms abelIntegral_smooth
#print axioms abelProfile_smooth
#print axioms abelProfile_support
#print axioms abelRadialSeed

end QuantitativeMaass
