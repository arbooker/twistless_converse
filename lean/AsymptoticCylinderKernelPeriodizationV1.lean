module

public import AsymptoticUnweightedFourierKernelV1
public import AsymptoticBergmanDecayV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticUnweightedKernel

open UpperHalfPlane

private theorem periodization_coefficient (h : ℕ) {Y : ℝ} (hY : 0 < Y) :
    ((2*h+1 : ℕ) : ℂ) / (4*Real.pi*Y) * (2*Complex.I*(Real.sqrt Y : ℂ))^(2*h+2) *
      ((-2*Real.pi*Complex.I)^(2*h+2) / ((2*h+1).factorial : ℂ)) =
      (((4*Real.pi)^(2*h+1) * Y^h / ((2*h).factorial : ℝ)) : ℂ) := by
  have hab : (2*Complex.I*(Real.sqrt Y : ℂ)) * (-2*Real.pi*Complex.I) =
      4*Real.pi*(Real.sqrt Y : ℂ) := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hp : (Real.sqrt Y : ℂ)^(2*h+2) = (Y : ℂ)^(h+1) := by
    rw [show 2*h+2=2*(h+1) by omega, pow_mul, ← Complex.ofReal_pow, Real.sq_sqrt hY.le]
  calc
    _ = (((2*h+1 : ℕ) : ℂ) / (4*Real.pi*Y)) *
        ((2*Complex.I*(Real.sqrt Y : ℂ)) * (-2*Real.pi*Complex.I))^(2*h+2) /
        ((2*h+1).factorial : ℂ) := by simp only [mul_pow]; ring
    _ = _ := by
      rw [hab, mul_pow, hp, Nat.factorial_succ]
      push_cast
      have hYn : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
      have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hn : (2 : ℂ)*h+1 ≠ 0 := by exact_mod_cast (show (2*h : ℝ)+1 ≠ 0 by positivity)
      have hf : ((2*h).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*h)
      rw [show 2*h+2=(2*h+1)+1 by omega, pow_succ, pow_succ]
      field_simp [hYn, hπ, hn, hf]
      ring

/-- The reciprocal-power periodization of the actual Fourier kernel.
The coefficient includes the flat-measure factor 1/(y v). -/
theorem fourierKernel_periodization (h : ℕ) {ε : ℝ} (hε : 0 < ε) (z u : ℍ) :
    fourierKernel h ε z u = ((2*h+1 : ℕ) : ℂ) / (4*Real.pi*z.im*u.im) *
      ∑' n : ℤ, ((2*Complex.I*(Real.sqrt (z.im*u.im) : ℂ)) /
        ((z : ℂ)-star (u : ℂ)+n))^(2*h+2) := by
  have ht : (∑' n : ℤ, ((2*Complex.I*(Real.sqrt (z.im*u.im) : ℂ)) /
      ((z : ℂ)-star (u : ℂ)+n))^(2*h+2)) =
      (2*Complex.I*(Real.sqrt (z.im*u.im) : ℂ))^(2*h+2) *
        ∑' n : ℤ, 1 / ((difference z u : ℂ)+n)^(2*h+2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [div_pow]
    simp only [difference]
    ring
  rw [ht, show 2*h+2=(2*h+1)+1 by omega,
    EisensteinSeries.qExpansion_identity (by omega : 1 ≤ 2*h+1) (difference z u),
    fourierKernel_formula h hε z u]
  have hc := periodization_coefficient h (mul_pos z.im_pos u.im_pos)
  push_cast at hc
  have he : ((2*h+1 : ℕ) : ℂ) / (4*Real.pi*z.im*u.im) *
      ((2*Complex.I*(Real.sqrt (z.im*u.im) : ℂ))^(2*h+1+1) *
        (((-2*Real.pi*Complex.I)^(2*h+1+1) / ((2*h+1).factorial : ℂ)) *
          ∑' n : ℕ, (n : ℂ)^(2*h+1) *
            Complex.exp (2*Real.pi*Complex.I*(difference z u : ℂ))^n)) =
      (((2*h+1 : ℕ) : ℂ) / (4*Real.pi*(z.im*u.im)) *
        (2*Complex.I*(Real.sqrt (z.im*u.im) : ℂ))^(2*h+2) *
        ((-2*Real.pi*Complex.I)^(2*h+2) / ((2*h+1).factorial : ℂ))) *
          ∑' n : ℕ, (n : ℂ)^(2*h+1) *
            Complex.exp (2*Real.pi*Complex.I*(difference z u : ℂ))^n := by
    rw [show 2*h+1+1=2*h+2 by omega]
    push_cast
    ring
  rw [he]
  congr 1
  simpa only [Complex.ofReal_mul] using (periodization_coefficient h (mul_pos z.im_pos u.im_pos)).symm

noncomputable def translate (z : ℍ) (n : ℤ) : ℍ :=
  ⟨(z : ℂ)+n, by simpa using z.im_pos⟩

theorem base_translate (z u : ℍ) (n : ℤ) :
    AsymptoticBergmanDecay.base (translate z n) u =
      (2*Complex.I*(Real.sqrt (z.im*u.im) : ℂ)) / ((z : ℂ)-star (u : ℂ)+n) := by
  unfold AsymptoticBergmanDecay.base translate
  simp only [UpperHalfPlane.im, Complex.add_im, Complex.intCast_im, add_zero]
  congr 1
  ring

/-- In hyperbolic measure the two height factors from the concrete
cylinder lift give precisely the manuscript's coefficient (k-1)/(4π). -/
theorem hyperbolicKernel_periodization (h : ℕ) {ε : ℝ} (hε : 0 < ε) (z u : ℍ) :
    (z.im*u.im : ℝ) * fourierKernel h ε z u =
      ((2*h+1 : ℕ) : ℂ) / (4*Real.pi) *
        ∑' n : ℤ, AsymptoticBergmanDecay.base (translate z n) u^(2*h+2) := by
  rw [fourierKernel_periodization h hε z u]
  simp_rw [base_translate]
  push_cast
  have hz : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  have hu : (u.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr u.im_pos.ne'
  field_simp

#print axioms fourierKernel_periodization
#print axioms hyperbolicKernel_periodization

end AsymptoticUnweightedKernel
