module

public import FinitenessRamanujanSumV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessRamanujanFourier

open Complex Filter Asymptotics FinitenessRamanujanSum FinitenessOriginalFourier
  FinitenessFourierConstruction FinitenessAnalyticReconstruction

noncomputable def twisted (f : ℕ → ℂ) (q : ℕ) (n : ℕ) : ℂ := f n*ramanujan q n

theorem twisted_zero {f : ℕ → ℂ} (hf0 : f 0=0) (q : ℕ) : twisted f q 0=0 := by
  simp only [twisted, hf0, zero_mul]

theorem twisted_growth {f : ℕ → ℂ} {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ)) (q : ℕ) :
    twisted f q =O[atTop] (fun n : ℕ => (n : ℝ)^τ) := by
  have hr : (fun n => (ramanujan q n : ℂ)) =O[atTop] (fun _ : ℕ => (1:ℝ)) := by
    apply IsBigO.of_bound (q : ℝ)
    exact Filter.Eventually.of_forall (fun n => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_one, mul_one]
        using abs_bound q n)
  unfold twisted
  simpa only [mul_one] using hf.mul hr

theorem fullCoefficients_twisted (f : ℕ → ℂ) (q k n : ℕ) :
    fullCoefficients (twisted f q) k n=fullCoefficients f k n*complexSum q n := by
  unfold fullCoefficients FinitenessGrowthNormalization.normalized twisted
  rw [ofReal_ramanujan]
  ring

theorem phase_translate (q n a : ℕ) (z : ℂ) :
    phase q n a*Complex.exp (2*Real.pi*I*(n : ℂ)*z)=
      Complex.exp (2*Real.pi*I*(n : ℂ)*(z+(a : ℂ)/q)) := by
  rw [phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem coefficient_translate (A : ℕ → ℂ) (q n : ℕ) (z : ℂ) :
    (A n*complexSum q n)*Complex.exp (2*Real.pi*I*(n : ℂ)*z)=
      ∑ a ∈ residues q, A n*Complex.exp (2*Real.pi*I*(n : ℂ)*(z+(a : ℂ)/q)) := by
  unfold complexSum
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_assoc, phase_translate]

/-- The ACTUAL primitive translation sum equals the Fourier series with
Ramanujan-twisted coefficients. Convergence justifies interchanging sums. -/
theorem fourier_twisted {f : ℕ → ℂ} (hf0 : f 0=0) {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ)) (q k : ℕ)
    {z : ℂ} (hz : 0 < z.im) :
    fourier (fullCoefficients (twisted f q) k) z =
      twist (fourier (fullCoefficients f k)) q z := by
  have hs : ∀ a ∈ residues q, Summable (fun n : ℕ => fullCoefficients f k n*
      Complex.exp (2*Real.pi*I*(n : ℂ)*(z+(a : ℂ)/q))) := by
    intro a _
    apply exp_summable (polynomial_bound hf0 hf k)
    simpa using hz
  rw [fourier_eq_exp]
  simp_rw [fullCoefficients_twisted, coefficient_translate]
  rw [Summable.tsum_finsetSum hs]
  unfold twist residues
  apply Finset.sum_congr rfl
  intro a _
  exact (fourier_eq_exp (fullCoefficients f k) (z+(a : ℂ)/q)).symm

#print axioms twisted_growth
#print axioms fourier_twisted

end FinitenessRamanujanFourier
