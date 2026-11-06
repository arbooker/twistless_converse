module

public import QuantitativeArithmeticPairedMellinV1
public import QuantitativeArithmeticPrimeSmallTwistCharactersV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section

namespace QuantitativeArithmeticWeightedFourierTwist

open Complex Filter Asymptotics FinitenessOriginalInput FinitenessOriginalFourier
  FinitenessFourierConstruction

variable {ι : Type*} [Fintype ι]

def phase (n : ℕ) (r : ℝ) : ℂ :=
  Complex.exp (2*Real.pi*I*(n : ℂ)*(r : ℂ))

def coefficient (w : ι → ℂ) (r : ι → ℝ) (n : ℕ) : ℂ :=
  ∑ i, w i*phase n (r i)

def twisted (f : ℕ → ℂ) (w : ι → ℂ) (r : ι → ℝ) (n : ℕ) : ℂ :=
  f n*coefficient w r n

def translates (F : ℂ → ℂ) (w : ι → ℂ) (r : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ i, w i*F (z+(r i : ℂ))

theorem phase_norm (n : ℕ) (r : ℝ) : ‖phase n r‖=1 := by
  simp [phase,Complex.norm_exp]

theorem coefficient_bound (w : ι → ℂ) (r : ι → ℝ) (n : ℕ) :
    ‖coefficient w r n‖ ≤ ∑ i, ‖w i‖ := by
  unfold coefficient
  simpa only [norm_mul,phase_norm,mul_one] using norm_sum_le Finset.univ (fun i => w i*phase n (r i))

theorem twisted_zero {f : ℕ → ℂ} (hf0 : f 0=0) (w : ι → ℂ) (r : ι → ℝ) :
    twisted f w r 0=0 := by simp only [twisted,hf0,zero_mul]

theorem twisted_growth {f : ℕ → ℂ} {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ)) (w : ι → ℂ) (r : ι → ℝ) :
    twisted f w r =O[atTop] (fun n : ℕ => (n : ℝ)^τ) := by
  have hb : coefficient w r =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    apply IsBigO.of_bound (∑ i, ‖w i‖)
    exact Filter.Eventually.of_forall (fun n => by simpa using coefficient_bound w r n)
  unfold twisted
  simpa only [mul_one] using hf.mul hb

theorem fullCoefficients_twisted (f : ℕ → ℂ) (w : ι → ℂ) (r : ι → ℝ) (k n : ℕ) :
    fullCoefficients (twisted f w r) k n=fullCoefficients f k n*coefficient w r n := by
  unfold fullCoefficients FinitenessGrowthNormalization.normalized twisted
  ring

theorem phase_translate (n : ℕ) (r : ℝ) (z : ℂ) :
    phase n r*Complex.exp (2*Real.pi*I*(n : ℂ)*z)=
      Complex.exp (2*Real.pi*I*(n : ℂ)*(z+(r : ℂ))) := by
  rw [phase,← Complex.exp_add]
  congr 1
  ring

theorem coefficient_translate (A : ℕ → ℂ) (w : ι → ℂ) (r : ι → ℝ)
    (n : ℕ) (z : ℂ) :
    (A n*coefficient w r n)*Complex.exp (2*Real.pi*I*(n : ℂ)*z)=
      ∑ i, w i*(A n*Complex.exp (2*Real.pi*I*(n : ℂ)*(z+(r i : ℂ)))) := by
  unfold coefficient
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [show A n*(w i*phase n (r i))*Complex.exp (2*Real.pi*I*(n : ℂ)*z)=
    w i*(A n*(phase n (r i)*Complex.exp (2*Real.pi*I*(n : ℂ)*z))) by ring,
    phase_translate]

/-- Finite weighted additive twisting commutes with the actual convergent
Fourier series. The polynomial growth exponent is unchanged. -/
theorem fourier_twisted {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (w : ι → ℂ) (r : ι → ℝ) (k : ℕ) {z : ℂ} (hz : 0<z.im) :
    fourier (fullCoefficients (twisted f w r) k) z=
      translates (fourier (fullCoefficients f k)) w r z := by
  have hs : ∀ i ∈ (Finset.univ : Finset ι), Summable (fun n : ℕ =>
      w i*(fullCoefficients f k n*Complex.exp (2*Real.pi*I*(n : ℂ)*(z+(r i : ℂ))))) := by
    intro i _
    apply Summable.mul_left
    apply exp_summable (polynomial_bound hf0 hf k)
    simpa using hz
  rw [fourier_eq_exp]
  simp_rw [fullCoefficients_twisted,coefficient_translate]
  rw [Summable.tsum_finsetSum hs]
  unfold translates
  apply Finset.sum_congr rfl
  intro i _
  rw [tsum_mul_left,← fourier_eq_exp]

/-- A pair of completed finite weighted twists yields a pair of actual
weighted translation laws, with no separate analytic hypotheses on twists. -/
theorem paired_translation_law {N k : ℕ} (hN : 0<N)
    {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (w v : ι → ℂ) (r : ι → ℝ) (F G : ℂ → ℂ)
    (hhol : Differentiable ℂ F) (hfinite : FiniteOrder F)
    {c d : ℝ} (hc : ∀ s : ℂ, c<s.re → F s=completed N k (twisted f w r) s)
    (hd : ∀ s : ℂ, d<s.re → G s=completed N k (twisted f v r) s)
    {ε : ℂ} (hε : ‖ε‖=1) (hFE : ∀ s : ℂ, F s=ε*G (1-s)) :
    ∀ z : ℂ, 0<z.im → translates (fourier (fullCoefficients f k)) w r z=
      (ε*I^k)/((((Real.sqrt N : ℝ):ℂ)*z)^k)*
        translates (fourier (fullCoefficients f k)) v r (-1/((N : ℂ)*z)) := by
  have h := QuantitativeArithmeticPairedMellin.original_fricke_pair hN
    (twisted_zero hf0 w r) (twisted_zero hf0 v r)
    (twisted_growth hf w r) (twisted_growth hf v r) F G hhol hfinite hc hd hε hFE
  intro z hz
  have hz' : 0<(-1/((N : ℂ)*z)).im := by
    simpa only [Complex.ofReal_natCast] using
      FinitenessComplexGeometry.reflected_im_pos (L := (N : ℝ)) (by exact_mod_cast hN) hz
  simpa only [fourier_twisted hf0 hf w r k hz,fourier_twisted hf0 hf v r k hz'] using h z hz

#print axioms fourier_twisted
#print axioms paired_translation_law

end QuantitativeArithmeticWeightedFourierTwist
