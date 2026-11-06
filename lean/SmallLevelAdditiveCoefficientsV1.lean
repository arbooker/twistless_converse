module

public import FinitenessAllLevelMellinDirichletV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace SmallLevelAdditive

open Complex Filter Asymptotics FinitenessPolynomialSeries FinitenessFourierConstruction

/-- The unit phase of a real translate of the original Fourier series. -/
def phase (r : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((2*Real.pi*(n:ℝ)*r:ℝ):ℂ)*Complex.I)

def coefficients (a : ℕ → ℂ) (r : ℝ) (n : ℕ) : ℂ := a n*phase r n

theorem phase_norm (r : ℝ) (n : ℕ) : ‖phase r n‖=1 := by
  simp [phase,Complex.norm_exp]

theorem coefficients_norm (a : ℕ → ℂ) (r : ℝ) (n : ℕ) :
    ‖coefficients a r n‖=‖a n‖ := by
  rw [coefficients,norm_mul,phase_norm,mul_one]

theorem coefficients_zero {a : ℕ → ℂ} (ha0 : a 0=0) (r : ℝ) :
    coefficients a r 0=0 := by simp [coefficients,ha0]

theorem coefficients_polynomial {a : ℕ → ℂ} (ha : PolynomialBound a) (r : ℝ) :
    PolynomialBound (coefficients a r) := by
  obtain ⟨C,hC,d,hd⟩ := ha
  exact ⟨C,hC,d,fun n => by simpa only [coefficients_norm] using hd n⟩

theorem coefficients_growth {a : ℕ → ℂ} {τ : ℝ}
    (ha : a=O[atTop] (fun n : ℕ => (n:ℝ)^τ)) (r : ℝ) :
    coefficients a r=O[atTop] (fun n : ℕ => (n:ℝ)^τ) := by
  have h : coefficients a r=O[atTop] a := by
    apply IsBigO.of_bound 1
    exact Filter.Eventually.of_forall (fun n => by simp [coefficients_norm])
  exact h.trans ha

/-- Translation is represented by the actual coefficient phases, including
at points where the totalized Fourier sums are not convergent. -/
theorem fourier_translate (a : ℕ → ℂ) (r : ℝ) (z : ℂ) :
    fourier (coefficients a r) z=fourier a (z+r) := by
  rw [fourier_eq_exp,fourier_eq_exp]
  apply tsum_congr
  intro n
  unfold coefficients phase
  rw [mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem axis_one_translate (a : ℕ → ℂ) (r t : ℝ) :
    FinitenessAllLevelAxisDecay.axis 1 (coefficients a r) t=
      fourier a ((r:ℂ)+(t:ℂ)*Complex.I) := by
  simp only [FinitenessAllLevelAxisDecay.axis,Nat.cast_one,Real.sqrt_one,
    div_one,fourier_translate,add_comm]

#print axioms phase_norm
#print axioms coefficients_norm
#print axioms coefficients_polynomial
#print axioms coefficients_growth
#print axioms fourier_translate
#print axioms axis_one_translate

end SmallLevelAdditive
