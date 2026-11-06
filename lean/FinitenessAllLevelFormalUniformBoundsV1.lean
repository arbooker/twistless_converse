module

public import FinitenessAllLevelFormalRowBoundsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelCertificateBoundary FinitenessAllLevelGlobalHeight
  QuantitativeArithmeticRetainedCertificate

variable {N Q p : ℕ} {hQ : 0 < Q}

theorem step_tail_bound (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) (χ : ℕ → ℂ) (m : ℕ)
    {B y : ℝ} (hB : 0 ≤ B) (hy : 0 < y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℂ), ‖lam‖ ≤ B → ∀ (G : ℂ → ℂ) (M : ℝ),
      0 ≤ M → (∀ w, y ≤ w.im → ‖G w‖ ≤ M) → ∀ z : ℂ,
        y ≤ z.im → z.im ≤ P.ε → ‖step A χ m lam G z‖ ≤ C * M := by
  obtain ⟨C, hC, hb⟩ := step_uniform_bound hN A χ m hB hy
  refine ⟨C, hC, fun lam hlam G M hM hG z hz hze => ?_⟩
  let H : ℂ → ℂ := fun w => if y ≤ w.im then G w else 0
  have hGH : ∀ w : ℂ, y ≤ w.im → G w = H w := by
    intro w hw
    simp only [H, ite_eq_left hw]
  have hH : ∀ w, ‖H w‖ ≤ M := by
    intro w
    by_cases hw : y ≤ w.im
    · simpa only [H, ite_eq_left hw] using hG w hw
    · simpa only [H, ite_eq_right hw, norm_zero] using hM
  have hc : y ≤ z.im / P.ρ := by
    apply (le_div_iff₀ P.rho_pos).mpr
    exact (mul_le_of_le_one_right hy.le P.rho_lt_one.le).trans hz
  rw [step_congr hN hp A P χ m lam hGH (hy.trans_le hz) hze hc]
  exact hb lam hlam H M hM hH z hz

/-- A single exponential-in-depth bound works for all input vectors and
all eigenvalues in the specified disk, on the entire positive-height tail. -/
theorem iterate_uniform_bound (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) {B y : ℝ} (hB : 0 ≤ B) (hy : 0 < y) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (n : ℕ) (lam : ℂ), ‖lam‖ ≤ B →
      ∀ (F : space (radius a)) (z : ℂ), y ≤ z.im →
        ‖iterate A a χ m lam F n z‖ ≤ D ^ n * ‖F‖ := by
  obtain ⟨C, hC, hb⟩ := step_tail_bound hN hp A P χ m hB hy
  let D := max C 1
  have hD : 1 ≤ D := le_max_right _ _
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  refine ⟨D, hD, fun n => ?_⟩
  induction n with
  | zero =>
    intro lam _ F z _
    change ‖extend F.val (Function.Periodic.qParam 1 z)‖ ≤ D ^ 0 * ‖F‖
    simpa only [pow_zero, one_mul] using
      FinitenessAllLevelDiskRestriction.norm_extend_le F (Function.Periodic.qParam 1 z)
  | succ n ih =>
    intro lam hlam F z hz
    by_cases haz : a ≤ z.im
    · simp only [iterate, ite_eq_left haz]
      exact (FinitenessAllLevelDiskRestriction.norm_extend_le F _).trans
        (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hD))
    · simp only [iterate, ite_eq_right haz]
      calc
        _ ≤ C * (D ^ n * ‖F‖) := hb lam hlam _ _ (by positivity)
          (fun w hw => ih lam hlam F w hw) z hz ((le_of_not_ge haz).trans hae)
        _ ≤ D * (D ^ n * ‖F‖) := mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity)
        _ = D ^ (n + 1) * ‖F‖ := by rw [pow_succ]; ring

/-- Actual compact-uniform boundedness of the formal continuation, with
the bound chosen before the eigenvalue and the Banach-disk input. -/
theorem formal_uniform_bound (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) {B y : ℝ} (hB : 0 ≤ B) (hy : 0 < y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℂ), ‖lam‖ ≤ B →
      ∀ (F : space (radius a)) (z : ℂ), y ≤ z.im →
        ‖formal A P a χ m lam F z‖ ≤ C * ‖F‖ := by
  obtain ⟨D, hD, hb⟩ := iterate_uniform_bound hN hp A P hae χ m hB hy
  obtain ⟨n, hn⟩ := uniform_depth hN hp A P ha hae hy
  refine ⟨D ^ n, pow_nonneg (zero_le_one.trans hD) _, fun lam hlam F z hz => ?_⟩
  rw [hn χ m lam F z hz]
  exact hb n lam hlam F z hz

theorem formalOperator_uniform_bound (hN : 0 < N) (hp : p.Prime)
    (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε) (χ : ℕ → ℂ) (m : ℕ)
    {B y : ℝ} (hB : 0 ≤ B) (hy : 0 < y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℂ), ‖lam‖ ≤ B → ∀ z : ℂ, y ≤ z.im →
      ‖formalOperator A P a χ m lam z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := formal_uniform_bound hN hp A P ha hae χ m hB hy
  refine ⟨C, hC, fun lam hlam z hz => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro F
  simpa only [formalOperator_apply] using hb lam hlam F z hz

#print axioms step_tail_bound
#print axioms iterate_uniform_bound
#print axioms formal_uniform_bound
#print axioms formalOperator_uniform_bound

end FinitenessAllLevelFormalContinuation
