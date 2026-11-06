module

public import FinitenessOriginalInversionV1
public import FinitenessFourierConstructionV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessOriginalFourier

open Complex Filter Asymptotics FinitenessCompletedNormalization FinitenessOriginalInversion
  FinitenessFourierConstruction FinitenessPolynomialSeries

noncomputable def fullCoefficients (f : ℕ → ℂ) (k : ℕ) : ℕ → ℂ :=
  FinitenessGrowthNormalization.normalized f (alpha k)

noncomputable def height (N : ℕ) (l : ℝ) : ℝ := Real.exp (l-Real.log N/2)

theorem fullCoefficients_zero {f : ℕ → ℂ} (hf0 : f 0=0) (k : ℕ) : fullCoefficients f k 0=0 :=
  FinitenessGrowthNormalization.normalized_zero (by simp [hf0]) _

theorem fullCoefficients_succ (f : ℕ → ℂ) (k n : ℕ) :
    fullCoefficients f k (n+1)=normalizedCoefficients f k n := by
  rw [normalizedCoefficients_eq]
  rfl

theorem polynomial_bound {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ)) (k : ℕ) : PolynomialBound (fullCoefficients f k) := by
  exact FinitenessGrowthNormalization.polynomial_bound hf0 hf (alpha k)

theorem exp_summable {a : ℕ → ℂ} (ha : PolynomialBound a) {z : ℂ} (hz : 0 < z.im) :
    Summable (fun n : ℕ => a n*Complex.exp (2*Real.pi*I*(n : ℂ)*z)) := by
  have hs := FinitenessPolynomialSeries.summable ha
    (Function.Periodic.norm_qParam_lt_one (by norm_num : (0:ℝ)<1) hz)
  apply hs.congr
  intro n
  congr 1
  rw [Function.Periodic.qParam, ofReal_one, div_one, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem exp_frequency (N : ℕ) (l : ℝ) (n : ℕ) :
    Real.exp (l+scaledFrequencies N n) = 2*Real.pi*(n+1)*height N l := by
  have hn : 0 < (n+1 : ℝ) := by positivity
  have hp : 0 < 2*Real.pi := by positivity
  have he : l+scaledFrequencies N n = (l-Real.log N/2)+Real.log (n+1)+Real.log (2*Real.pi) := by
    unfold scaledFrequencies frequencies exponent
    ring
  rw [he, Real.exp_add, Real.exp_add, Real.exp_log hn, Real.exp_log hp]
  unfold height
  ring

/-- The inverse-Mellin series is literally the original normalized Fourier
series on the imaginary axis, at y=exp(l)/sqrt(N). -/
theorem laplace_eq_fourier {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ)) (N k : ℕ) (l : ℝ) :
    laplace N k f l=fourier (fullCoefficients f k) ((height N l : ℂ)*I) := by
  have hz : 0 < (((height N l : ℂ)*I)).im := by
    simpa only [mul_I_im, ofReal_re, height] using Real.exp_pos (l-Real.log N/2)
  have hs := exp_summable (polynomial_bound hf0 hf k) hz
  rw [fourier_eq_exp, hs.tsum_eq_zero_add, fullCoefficients_zero hf0, zero_mul, zero_add]
  unfold laplace
  apply tsum_congr
  intro n
  rw [fullCoefficients_succ, exp_frequency, ofReal_exp]
  congr 2
  have hI : I*I = -1 := I_mul_I
  push_cast
  symm
  calc
    _ = (2*(Real.pi : ℂ)*((n : ℂ)+1)*(height N l : ℂ))*(I*I) := by ring
    _ = _ := by rw [hI]; ring

theorem solution_axis {N k : ℕ} (hN : 0 < N) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution N k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε = -1) ∧ ∀ l : ℝ,
      fourier (fullCoefficients f k) ((height N l : ℂ)*I) =
      (ε : ℂ)*Complex.exp (((-l*(k : ℝ) : ℝ):ℂ))*
        fourier (fullCoefficients f k) ((height N (-l) : ℂ)*I) := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  obtain ⟨ε,hε,he⟩ := FinitenessOriginalInversion.solution_inversion hN hf
  refine ⟨ε,hε,?_⟩
  intro l
  simpa only [laplace_eq_fourier hf.zero hg] using he l

#print axioms polynomial_bound
#print axioms laplace_eq_fourier
#print axioms solution_axis

end FinitenessOriginalFourier
