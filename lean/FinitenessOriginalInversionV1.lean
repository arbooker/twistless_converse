module

public import FinitenessCompletedNormalizationV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessOriginalInversion

open Complex Filter Asymptotics FinitenessOriginalInput FinitenessInputBounds
  FinitenessCompletedNormalization FinitenessMellinSeries

noncomputable def normalizedCoefficients (f : ℕ → ℂ) (k : ℕ) : ℕ → ℂ :=
  shiftedCoefficients (coefficients f) frequencies (alpha k)

noncomputable def scaledFrequencies (N : ℕ) (n : ℕ) : ℝ := frequencies n-exponent N

noncomputable def laplace (N k : ℕ) (f : ℕ → ℂ) (l : ℝ) : ℂ :=
  ∑' n, normalizedCoefficients f k n*(Real.exp (-Real.exp (l+scaledFrequencies N n)) : ℂ)

theorem normalizedCoefficients_eq (f : ℕ → ℂ) (k n : ℕ) :
    normalizedCoefficients f k n = (f (n+1) : ℂ)*((((n+1 : ℕ):ℝ)^(alpha k) : ℝ):ℂ) := by
  unfold normalizedCoefficients shiftedCoefficients coefficients frequencies
  rw [Real.rpow_def_of_pos (by positivity : 0 < ((n+1 : ℕ):ℝ)), ofReal_exp]
  congr 2
  push_cast
  ring

theorem normalized_weight (N k : ℕ) (f : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    ‖normalizedCoefficients f k n‖*Real.exp (-σ*scaledFrequencies N n) =
      Real.exp (σ*exponent N)*(‖f (n+1)‖ * Real.exp (-(σ-alpha k)*Real.log (n+1))) := by
  unfold normalizedCoefficients shiftedCoefficients coefficients scaledFrequencies frequencies
  rw [norm_mul, Complex.norm_exp, ofReal_re]
  rw [mul_assoc, ← Real.exp_add]
  calc
    _ = ‖f (n+1)‖ * Real.exp (σ*exponent N+(-(σ-alpha k)*Real.log (n+1))) := by
      congr 2
      ring
    _ = _ := by rw [Real.exp_add]; ring

theorem normalized_absolute {N k : ℕ} {f : ℕ → ℂ} {τ σ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ)) (hσ : τ+alpha k+1 < σ) :
    Summable (fun n => ‖normalizedCoefficients f k n‖*Real.exp (-σ*scaledFrequencies N n)) := by
  simp_rw [normalized_weight]
  exact (absolute_convergence hf (by linarith : τ+1 < σ-alpha k)).mul_left _

/-- Mellin inversion preserves the specified root number. Keeping the
root explicit is needed to compare different Ramanujan twists coherently. -/
theorem inversion_with_sign {N : ℕ} (hN : 0 < N) (k : ℕ) {f : ℕ → ℂ} {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ))
    (F : ℂ → ℂ) (hhol : Differentiable ℂ F) (hfinite : FiniteOrder F)
    {c : ℝ} (hc : ∀ s : ℂ, c<s.re → F s=completed N k f s)
    {ε : ℂ} (hεnorm : ‖ε‖=1) (hFE : ∀ s : ℂ, F s=ε*F (1-s)) :
    ∀ l : ℝ,
      laplace N k f l = (ε : ℂ)*Complex.exp (((-l*(k : ℝ) : ℝ):ℂ))*laplace N k f (-l) := by
  obtain ⟨σ,hσ⟩ := exists_gt (max (max 0 ((k : ℝ)/2)) (max (τ+alpha k+1) (c+alpha k)))
  have hσ0 : 0 < σ := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hσ
  have hσk : (k : ℝ)/2 < σ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hσ
  have hστ : τ+alpha k+1 < σ := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hσ
  have hσc : c+alpha k < σ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hσ
  let G := normalize F (constant N k) (exponent N) (alpha k)
  have hGhol : Differentiable ℂ G := normalize_holomorphic hhol _ _ _
  have hGfinite : FinitenessFiniteOrder.Bound G :=
    normalize_finiteOrder (finiteOrder_bound hhol.continuous hfinite) _ _ _
  have hGseries : ∀ z : ℂ, z.re=σ → G z=Gamma z*series (normalizedCoefficients f k) (scaledFrequencies N) z := by
    intro z hz
    apply normalize_series (constant_ne_zero N k)
    rw [hc _ (by simp only [sub_re, ofReal_re, hz]; linarith), completed_exponential hN]
    simp only [sub_add_cancel]
  have halpha : 1+2*alpha k=(k : ℝ) := by unfold alpha; ring
  have hGFE : ∀ z : ℂ, G z=(ε : ℂ)*G ((k : ℂ)-z) := by
    intro z
    simpa only [halpha, ofReal_natCast] using normalize_FE hFE (constant N k) (exponent N) (alpha k) z
  intro l
  exact FinitenessDirichletInversion.inversion hσ0 (by linarith : (k : ℝ)-σ < σ)
    (normalized_absolute (N := N) hf hστ) hGhol hGfinite hGseries hεnorm hGFE l

/-- The inverse-Mellin transformation law follows from the ORIGINAL
completion and individual growth. Euler products are not used here. -/
theorem inversion {N : ℕ} (hN : 0 < N) (k : ℕ) {f : ℕ → ℂ} {τ : ℝ}
    (hf : f =O[atTop] (fun n : ℕ => (n : ℝ)^τ)) (hcont : Continuation N k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε = -1) ∧ ∀ l : ℝ,
      laplace N k f l = (ε : ℂ)*Complex.exp (((-l*(k : ℝ) : ℝ):ℂ))*laplace N k f (-l) := by
  obtain ⟨F,hhol,hfinite,⟨c,hc⟩,ε,hε,hFE⟩ := hcont
  have hεnorm : ‖ε‖=1 := by rcases hε with h | h <;> simp [h]
  exact ⟨ε,hε,inversion_with_sign hN k hf F hhol hfinite hc hεnorm hFE⟩

theorem solution_inversion {N k : ℕ} (hN : 0 < N) {f : ℕ → ℂ} (hf : IsSolution N k f) :
    ∃ ε : ℂ, (ε=1 ∨ ε = -1) ∧ ∀ l : ℝ,
      laplace N k f l=(ε : ℂ)*Complex.exp (((-l*(k : ℝ) : ℝ):ℂ))*laplace N k f (-l) := by
  obtain ⟨τ,_,hg⟩ := hf.growth
  exact inversion hN k hg hf.continuation

#print axioms normalized_absolute
#print axioms inversion_with_sign
#print axioms inversion
#print axioms solution_inversion

end FinitenessOriginalInversion
