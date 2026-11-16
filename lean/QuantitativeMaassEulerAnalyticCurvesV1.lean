module

public import QuantitativeMaassComplexEulerSeriesV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Each actual Fourier--Bessel term is holomorphic along holomorphic coordinate
curves lying in the physical complex tube. -/
theorem complexEulerTerm_differentiableOn (b : ℕ → ℂ) (r : ℝ) (σ n : ℕ)
    (X Y : ℂ → ℂ) (S : Set ℂ) (hX : DifferentiableOn ℂ X S) (hY : DifferentiableOn ℂ Y S)
    (hgap : ∀ z∈S,|(X z).im|<(Y z).re) :
    DifferentiableOn ℂ (fun z => complexEulerTerm b r σ n (X z) (Y z)) S := by
  have harg : ∀ z∈S,0<((((2*Real.pi*((n+1:ℕ):ℝ):ℝ):ℂ)*Y z)).re := by
    intro z hz
    have hy : 0<(Y z).re := (abs_nonneg _).trans_lt (hgap z hz)
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    positivity
  have hm := (principalComplexMoment_analytic 0 r).differentiableOn.comp
    (hY.const_mul ((2*Real.pi*((n+1:ℕ):ℝ):ℝ):ℂ)) harg
  have hp := (complexEulerPhase_differentiable σ (n+1)).comp_differentiableOn hX
  exact (hm.const_mul (b (n+1))).mul hp

/-- Uniform positive tube gap suffices for termwise holomorphic summation. -/
theorem complexEulerCore_differentiableOn_uniform {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (X Y : ℂ → ℂ) (S : Set ℂ) (hS : IsOpen S)
    (hX : DifferentiableOn ℂ X S) (hY : DifferentiableOn ℂ Y S)
    (a : ℝ) (ha : 0<a) (hgap : ∀ z∈S,a≤(Y z).re-|(X z).im|) :
    DifferentiableOn ℂ (fun z => complexEulerCore b r σ (X z) (Y z)) S := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    ((principalMomentMajorant_summable hb 0 0 (2*Real.pi) a (by positivity) ha).mul_left 2)
  · intro n
    apply complexEulerTerm_differentiableOn b r σ n X Y S hX hY
    intro z hz
    linarith [hgap z hz]
  · exact hS
  · intro n z hz
    exact complexEulerTerm_bound b r σ n a ha (X z) (Y z) (hgap z hz)

/-- The actual Fourier--Bessel core is holomorphic along every holomorphic
coordinate curve in the open physical tube. No uniform gap is assumed. -/
theorem complexEulerCore_analytic_curves {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (X Y : ℂ → ℂ) (S : Set ℂ) (hS : IsOpen S)
    (hX : DifferentiableOn ℂ X S) (hY : DifferentiableOn ℂ Y S)
    (hgap : ∀ z∈S,|(X z).im|<(Y z).re) :
    AnalyticOnNhd ℂ (fun z => complexEulerCore b r σ (X z) (Y z)) S := by
  apply DifferentiableOn.analyticOnNhd _ hS
  intro z hz
  let ρ := fun w => (Y w).re-|(X w).im|
  let a := ρ z/2
  have hρ : ContinuousOn ρ S :=
    (Complex.continuous_re.comp_continuousOn hY.continuousOn).sub
      (Complex.continuous_im.comp_continuousOn hX.continuousOn).abs
  have hp : 0<ρ z := sub_pos.mpr (hgap z hz)
  have ha : 0<a := by dsimp [a]; positivity
  let U := S∩ρ ⁻¹' Ioi a
  have hU : IsOpen U := hρ.isOpen_inter_preimage hS isOpen_Ioi
  have hzU : z∈U := ⟨hz,by change a<ρ z; dsimp [a]; linarith⟩
  have hd := complexEulerCore_differentiableOn_uniform hb r σ X Y U hU
    (hX.mono inter_subset_left) (hY.mono inter_subset_left) a ha
    (fun _ hw => hw.2.le)
  exact ((hd z hzU).differentiableAt (hU.mem_nhds hzU)).differentiableWithinAt

#print axioms complexEulerTerm_differentiableOn
#print axioms complexEulerCore_differentiableOn_uniform
#print axioms complexEulerCore_analytic_curves

end QuantitativeMaass
