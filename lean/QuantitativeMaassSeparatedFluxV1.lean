module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section

namespace QuantitativeMaass

/-- A separated energy coefficient is bounded by its two flux components.
The frequency variables are square roots of shifted Laplace eigenvalues. -/
theorem separated_flux_coefficient {a b L : ℝ} (ha : 0≤a) (hb : 0<b)
    (hsep : L≤|a-b|) (c α β : ℂ)
    (hflux : ((a^2-b^2:ℝ):ℂ)*c=(a:ℂ)*α-β) :
    L*‖c‖≤‖α‖+‖β‖/b := by
  have hn : |a^2-b^2| *‖c‖≤a*‖α‖+‖β‖ := by
    have hh := norm_sub_le ((a:ℂ)*α) β
    rw [←hflux,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha] at hh
    exact hh
  have he : |a^2-b^2|=|a-b| *(a+b) := by
    rw [sq_sub_sq,abs_mul,abs_of_pos (by linarith : 0<a+b)]
    ring
  rw [he] at hn
  have hg := mul_le_mul_of_nonneg_right hsep (show 0≤(a+b)*‖c‖ by positivity)
  have hd : ‖β‖/b*b=‖β‖ := div_mul_cancel₀ _ hb.ne'
  have hh : (a+b)*(L*‖c‖)≤(a+b)*(‖α‖+‖β‖/b) := by
    nlinarith [mul_nonneg ha (norm_nonneg α),mul_nonneg ha (div_nonneg (norm_nonneg β) hb.le),
      mul_nonneg hb.le (norm_nonneg α)]
  exact (mul_le_mul_iff_right₀ (show 0<a+b by linarith)).mp hh

/-- Bessel bounds for both flux components give an off-band squared-mass
bound independent of the number of output eigenvectors. -/
theorem separated_flux_bessel {E F ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [Fintype ι] (u : ι → E) (v : ι → F) (hu : Orthonormal ℂ u)
    (hv : Orthonormal ℂ v) (A : E) (B : F) (a : ι → ℝ) (b L : ℝ)
    (ha : ∀ i,0≤a i) (hb : 0<b) (hL : 0<L) (hsep : ∀ i,L≤|a i-b|)
    (c : ι → ℂ)
    (hflux : ∀ i,((a i^2-b^2:ℝ):ℂ)*c i=
      (a i:ℂ)*inner ℂ (u i) A-inner ℂ (v i) B) :
    ∑ i,‖c i‖^2≤(2/L^2)*(‖A‖^2+‖B‖^2/b^2) := by
  classical
  have hp (i : ι) : L^2*‖c i‖^2≤
      2*‖inner ℂ (u i) A‖^2+2*‖inner ℂ (v i) B‖^2/b^2 := by
    have hh := separated_flux_coefficient (ha i) hb (hsep i) (c i)
      (inner ℂ (u i) A) (inner ℂ (v i) B) (hflux i)
    have hs := pow_le_pow_left₀ (show 0≤L*‖c i‖ by positivity) hh 2
    have hq := sq_nonneg (‖inner ℂ (u i) A‖-‖inner ℂ (v i) B‖/b)
    rw [mul_pow] at hs
    have he : 2*‖inner ℂ (v i) B‖^2/b^2=2*(‖inner ℂ (v i) B‖/b)^2 := by
      rw [div_pow]
      ring
    rw [he]
    nlinarith only [hs,hq]
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hp i)
  have hA : (∑ i,‖inner ℂ (u i) A‖^2)≤‖A‖^2 := by
    simpa using hu.sum_inner_products_le (s := Finset.univ) A
  have hB : (∑ i,‖inner ℂ (v i) B‖^2)≤‖B‖^2 := by
    simpa using hv.sum_inner_products_le (s := Finset.univ) B
  simp only [Finset.sum_add_distrib,←Finset.sum_div,←Finset.mul_sum] at hsum
  rw [mul_div_assoc] at hsum
  have hg := div_le_div_of_nonneg_right hB (sq_nonneg b)
  have he : (2/L^2)*(‖A‖^2+‖B‖^2/b^2)=
      (2*(‖A‖^2+‖B‖^2/b^2))/L^2 := by ring
  rw [he]
  apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
  nlinarith [hsum,hg,hA]

#print axioms separated_flux_coefficient
#print axioms separated_flux_bessel

end QuantitativeMaass
