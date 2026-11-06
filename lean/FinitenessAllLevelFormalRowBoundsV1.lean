module

public import FinitenessAllLevelFormalMeasurableV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex Set FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelBoundaryGeometry FinitenessAllLevelCertificateBoundary
  FinitenessAllLevelReconstruction FinitenessAllLevelGlobalHeight FinitenessAllLevelGoodTrace
  QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedReconstruction
  FinitenessAnalyticReconstruction SpanningIntegerRows

variable {N Q p : ℕ} {hQ : 0 < Q}

include hQ in
/-- Uniform bound for an individual reconstruction row, with an arbitrary
globally bounded input. The eigenvalue ranges over a closed disk. -/
theorem row_uniform_bound (hN : 0 < N) (χ : ℕ → ℂ) (m : ℕ)
    {B y : ℝ} (hB : 0 ≤ B) (hy : 0 < y) (j : Fin Q)
    (i : AugIndex N (({p} : Finset ℕ) : Set ℕ) Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℂ), ‖lam‖ ≤ B → ∀ (G : ℂ → ℂ) (M : ℝ),
      0 ≤ M → (∀ w, ‖G w‖ ≤ M) → ∀ z : ℂ, y ≤ z.im →
      ‖twoDilationRow G (2 * m) χ (firstMultiplier (fun _ => lam) m)
        (fun q => (q : ℂ) ^ (2 * m)) j z i‖ ≤ C * M := by
  cases i with
  | inl i =>
    let L : ℝ := Nat.lcm N (i.val.1 ^ 2)
    let s := (Finset.range i.val.1).filter (fun v => Nat.Coprime v i.val.1)
    have hL : 0 < L := row_level_pos hN hQ i
    have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
    let c := ‖χ i.val.1‖ / (Real.sqrt L * y) ^ (2 * m)
    have hc : 0 ≤ c := by positivity
    refine ⟨c * s.card, by positivity, fun lam _ G M hM hG z hz => ?_⟩
    have him : (z + ((i.val.2 : ℂ) - (j.val : ℂ)) / Q).im = z.im := by simp
    have hn : y ≤ ‖z + ((i.val.2 : ℂ) - (j.val : ℂ)) / Q‖ :=
      hz.trans ((le_abs_self _).trans (him ▸ Complex.abs_im_le_norm _))
    have hw : ‖χ i.val.1 / ((Real.sqrt L : ℂ) *
        (z + ((i.val.2 : ℂ) - (j.val : ℂ)) / Q)) ^ (2 * m)‖ ≤ c := by
      rw [norm_div, norm_pow, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hs.le]
      apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos (mul_pos hs hy) _)
      exact pow_le_pow_left₀ (mul_nonneg hs.le hy.le)
        (mul_le_mul_of_nonneg_left hn hs.le) _
    have ht : ‖twist G i.val.1
        (-1 / ((Nat.lcm N (i.val.1 ^ 2) : ℕ) *
          (z + ((i.val.2 : ℂ) - (j.val : ℂ)) / Q)))‖ ≤ (s.card : ℝ) * M := by
      unfold twist
      exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun v _ => hG _)).trans_eq
        (by simp [s]))
    change ‖(χ i.val.1 / ((Real.sqrt L : ℂ) *
      (z + ((i.val.2 : ℂ) - (j.val : ℂ)) / Q)) ^ (2 * m)) * _‖ ≤ _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul hw ht (norm_nonneg _) hc
  | inr i =>
    let c := ‖(i.1.val : ℂ) ^ m * (Real.sqrt i.1.val : ℂ)‖
    let d := ‖(i.1.val : ℂ) ^ (2 * m)‖
    refine ⟨c * B + d, by positivity, fun lam hlam G M hM hG z _ => ?_⟩
    have hc : ‖firstMultiplier (fun _ => lam) m i.1.val‖ ≤ c * B := by
      dsimp only [firstMultiplier]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hlam (norm_nonneg _)
    calc
      _ ≤ ‖firstMultiplier (fun _ => lam) m i.1.val‖ * ‖G _‖ + d * ‖G _‖ := by
        simpa only [twoDilationRow, norm_mul] using norm_sub_le
          (firstMultiplier (fun _ => lam) m i.1.val * G
            ((i.1.val : ℂ) * (z + ((i.2 : ℂ) - (j.val : ℂ)) / Q)))
          ((i.1.val : ℂ) ^ (2 * m) * G
            ((i.1.val : ℂ) ^ 2 * (z + ((i.2 : ℂ) - (j.val : ℂ)) / Q)))
      _ ≤ c * B * M + d * M := add_le_add
        (mul_le_mul hc (hG _) (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left (hG _) (norm_nonneg _))
      _ = _ := (add_mul _ _ _).symm

/-- One common bound covers every selected cell. It is independent of
the spatial real part, input function, and eigenvalue in the specified disk. -/
theorem step_uniform_bound (hN : 0 < N) (A : Certificate N {p} Q hQ)
    (χ : ℕ → ℂ) (m : ℕ) {B y : ℝ} (hB : 0 ≤ B) (hy : 0 < y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℂ), ‖lam‖ ≤ B → ∀ (G : ℂ → ℂ) (M : ℝ),
      0 ≤ M → (∀ w, ‖G w‖ ≤ M) → ∀ z : ℂ, y ≤ z.im →
        ‖step A χ m lam G z‖ ≤ C * M := by
  classical
  choose c hc hb using (fun j i => row_uniform_bound (hQ := hQ) hN χ m hB hy j i)
  let C : Fin Q → ℝ := fun j => ∑ i ∈ (A.coeff j).support, ‖(A.coeff j i : ℂ)‖ * c j i
  have hC (j : Fin Q) : 0 ≤ C j := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hc j i))
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun lam hlam G M hM hG z hz => ?_⟩
  let j := selector Q hQ (Function.Periodic.qParam 1 z)
  calc
    _ ≤ ∑ i ∈ (A.coeff j).support, ‖(A.coeff j i : ℂ)‖ *
        ‖twoDilationRow G (2 * m) χ (firstMultiplier (fun _ => lam) m)
          (fun q => (q : ℂ) ^ (2 * m)) j
          (line (coordinate (Function.Periodic.qParam 1 z)) z.im) i‖ := by
      simp only [step, ← norm_mul]
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ (A.coeff j).support, ‖(A.coeff j i : ℂ)‖ * (c j i * M) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact hb j i lam hlam G M hM hG _ (by simpa only [line_im] using hz)
    _ = C j * M := by simp only [C, Finset.sum_mul, mul_assoc]
    _ ≤ (∑ j, C j) * M := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ j)) hM

#print axioms row_uniform_bound
#print axioms step_uniform_bound

end FinitenessAllLevelFormalContinuation
