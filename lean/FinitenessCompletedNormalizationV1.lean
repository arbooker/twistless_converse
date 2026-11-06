module

public import FinitenessInputBoundsV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessCompletedNormalization

open Complex FinitenessOriginalInput FinitenessMellinSeries FinitenessFiniteOrder

noncomputable def alpha (k : ℕ) : ℝ := ((k : ℝ)-1)/2
noncomputable def exponent (N : ℕ) : ℝ := Real.log N/2-Real.log (2*Real.pi)
noncomputable def constant (N k : ℕ) : ℂ :=
  2*Complex.exp (((-Real.log N/4-alpha k*Real.log (2*Real.pi) : ℝ):ℂ))
noncomputable def coefficients (f : ℕ → ℂ) (n : ℕ) : ℂ := f (n+1)
noncomputable def frequencies (n : ℕ) : ℝ := Real.log (n+1)

theorem L_eq_series (f : ℕ → ℂ) (s : ℂ) : L f s=series (coefficients f) frequencies s := by
  unfold L series coefficients frequencies
  apply tsum_congr
  intro n
  have hn : 0 < ((n+1 : ℕ):ℝ) := by positivity
  rw [cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))]
  have hl : Complex.log ((n+1 : ℕ):ℂ)=(Real.log (n+1):ℂ) := by
    simpa only [Nat.cast_add_one, ofReal_add, ofReal_natCast, ofReal_one] using (ofReal_log hn.le).symm
  rw [hl]
  congr 2
  push_cast
  ring

theorem constant_ne_zero (N k : ℕ) : constant N k ≠ 0 :=
  mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)

/-- Literal completion from the paper, with its Gamma_C, conductor power,
and (k-1)/2 shift rewritten into the exponential Dirichlet-series form. -/
theorem completed_exponential {N : ℕ} (hN : 0 < N) (k : ℕ) (f : ℕ → ℂ) (s : ℂ) :
    completed N k f s = constant N k*Complex.exp ((exponent N : ℂ)*s)*
      Gamma (s+(alpha k : ℂ))*series (coefficients f) frequencies s := by
  have hnr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hpi : 0 < 2*Real.pi := by positivity
  have hk : ((k : ℂ)-1)/2=(alpha k : ℂ) := by unfold alpha; push_cast; rfl
  unfold completed gammaC
  rw [hk, L_eq_series,
    cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hN.ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hpi.ne')]
  have hlog : Complex.log (N : ℂ)=(Real.log N : ℂ) := by
    simp
  rw [hlog, ← ofReal_log hpi.le]
  have he : Complex.exp ((Real.log N : ℂ)*((s-1/2)/2))*
      Complex.exp ((Real.log (2*Real.pi):ℂ)*(-(s+(alpha k : ℂ)))) =
      Complex.exp (((-Real.log N/4-alpha k*Real.log (2*Real.pi):ℝ):ℂ))*
        Complex.exp ((exponent N : ℂ)*s) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold exponent
    push_cast
    ring
  calc
    _ = 2*(Complex.exp ((Real.log N : ℂ)*((s-1/2)/2))*
        Complex.exp ((Real.log (2*Real.pi):ℂ)*(-(s+(alpha k : ℂ)))))*
        Gamma (s+(alpha k : ℂ))*series (coefficients f) frequencies s := by ring
    _ = _ := by rw [he]; unfold constant; ring

/-- General shifted completion. Here a(n) must be multiplied by exp(alpha*d(n)),
which is n^((k-1)/2) in the ordinary Dirichlet-series application. -/
noncomputable def shiftedCoefficients (a : ℕ → ℂ) (d : ℕ → ℝ) (α : ℝ) (n : ℕ) : ℂ :=
  a n*Complex.exp (((α*d n : ℝ):ℂ))

noncomputable def normalize (F : ℂ → ℂ) (c : ℂ) (b α : ℝ) (z : ℂ) : ℂ :=
  (c⁻¹*Complex.exp (((b*α : ℝ):ℂ)))*F (z-(α : ℂ))

theorem normalize_finiteOrder {F : ℂ → ℂ} (hF : Bound F) (c : ℂ) (b α : ℝ) :
    Bound (normalize F c b α) := by
  have hs := FinitenessInputBounds.bound_shift hF (-(α : ℂ))
  unfold normalize
  simpa only [sub_eq_add_neg] using FinitenessFiniteOrder.mul
    (FinitenessInputBounds.bound_const (c⁻¹*Complex.exp (((b*α : ℝ):ℂ)))) hs

theorem normalize_holomorphic {F : ℂ → ℂ} (hF : Differentiable ℂ F) (c : ℂ) (b α : ℝ) :
    Differentiable ℂ (normalize F c b α) :=
  (differentiable_const _).mul (hF.comp (differentiable_id.sub (differentiable_const _)))

theorem normalize_FE {F : ℂ → ℂ} {ε : ℂ} (hFE : ∀ s : ℂ, F s=ε*F (1-s))
    (c : ℂ) (b α : ℝ) (z : ℂ) :
    normalize F c b α z=ε*normalize F c b α (((1+2*α : ℝ):ℂ)-z) := by
  unfold normalize
  rw [hFE (z-(α : ℂ))]
  have he : 1-(z-(α : ℂ))=(((1+2*α : ℝ):ℂ)-z)-(α : ℂ) := by push_cast; ring
  rw [he]
  ring

theorem normalize_series {a : ℕ → ℂ} {d : ℕ → ℝ} {F : ℂ → ℂ}
    {c : ℂ} (hc : c ≠ 0) (b α : ℝ) (z : ℂ)
    (hF : F (z-(α : ℂ))=c*Complex.exp ((b : ℂ)*(z-(α : ℂ)))*
      Gamma z*series a d (z-(α : ℂ))) :
    normalize F c b α z = Gamma z*series (shiftedCoefficients a d α) (fun n => d n-b) z := by
  unfold normalize
  rw [hF]
  unfold series
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have he : Complex.exp (((b*α : ℝ):ℂ))*Complex.exp ((b : ℂ)*(z-(α : ℂ)))*
      Complex.exp (((-d n : ℝ):ℂ)*(z-(α : ℂ))) =
      Complex.exp (((α*d n : ℝ):ℂ))*Complex.exp (((-(d n-b) : ℝ):ℂ)*z) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (c⁻¹*c)*Gamma z*a n*(Complex.exp (((b*α : ℝ):ℂ))*
        Complex.exp ((b : ℂ)*(z-(α : ℂ)))*Complex.exp (((-d n : ℝ):ℂ)*(z-(α : ℂ)))) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hc, one_mul, he]; unfold shiftedCoefficients; ring

#print axioms completed_exponential
#print axioms normalize_series
#print axioms normalize_FE

end FinitenessCompletedNormalization
