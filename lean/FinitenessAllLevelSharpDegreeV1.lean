module

public import FinitenessAllLevelEigenvalueDegreeV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex FinitenessAllLevelDiskAlgebra FinitenessAllLevelBoundaryCoordinates
  FinitenessAllLevelBoundaryGeometry FinitenessAllLevelCertificateBoundary
  FinitenessAllLevelPencilHeights FinitenessAllLevelReconstruction
  FinitenessAllLevelGlobalHeight FinitenessAllLevelGoodTrace FinitenessAllLevelEigenvalueDegree
  QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedReconstruction
  FinitenessAnalyticReconstruction

variable {N Q p : ℕ} {hQ : 0 < Q}

/-- The sharp eigenvalue degree depends on the number of prime-height gains,
not on the total depth of the reconstruction tree. -/
theorem iterate_sharp_degree (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (F : space (radius a)) (n j : ℕ)
    {z : ℂ} (hz : a / (p : ℝ) ^ j ≤ z.im) :
    DegreeBound (fun lam => iterate A a χ m lam F n z) j := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  induction n generalizing j z with
  | zero => exact constant (lift F z) j
  | succ n ih =>
    by_cases haz : a ≤ z.im
    · simpa only [iterate, ite_eq_left haz] using constant (lift F z) j
    cases j with
    | zero => exact False.elim (haz (by simpa using hz))
    | succ j =>
      let c : ℝ := a / (p : ℝ) ^ (j + 1)
      have hc : 0 < c := div_pos ha (pow_pos hp0 _)
      have hzpos : 0 < z.im := hc.trans_le hz
      have hze : z.im ≤ P.ε := (le_of_not_ge haz).trans hae
      have hcr : c ≤ z.im / P.ρ := by
        apply (le_div_iff₀ P.rho_pos).mpr
        exact (mul_le_of_le_one_right hc.le P.rho_lt_one.le).trans hz
      let G : ℂ → ℂ → ℂ := fun lam w => iterate A a χ m lam F n w
      let H : ℂ → ℂ → ℂ := fun lam w => if c ≤ w.im then G lam w else 0
      have hH (w : ℂ) : DegreeBound (fun lam => H lam w) (j + 1) := by
        by_cases hw : c ≤ w.im
        · simpa only [H, ite_eq_left hw] using ih (j + 1) hw
        · simpa only [H, ite_eq_right hw] using constant 0 (j + 1)
      simp only [iterate, ite_eq_right haz, step]
      apply FinitenessAllLevelEigenvalueDegree.sum
      intro i hi
      apply DegreeBound.const_mul
      let cell := selector Q hQ (Function.Periodic.qParam 1 z)
      let z' := line (coordinate (Function.Periodic.qParam 1 z)) z.im
      have him (u : ℤ) : (z' + ((u : ℂ) - (cell.val : ℂ)) / Q).im = z.im := by
        simp [z', line]
      cases i with
      | inl i =>
        have heq : (fun lam => twoDilationRow (P := {p}) (G lam) (2 * m) χ
              (firstMultiplier (fun _ => lam) m) (fun q => (q : ℂ) ^ (2 * m)) cell z' (Sum.inl i)) =
            (fun lam => twoDilationRow (P := {p}) (H lam) (2 * m) χ
              (firstMultiplier (fun _ => lam) m) (fun q => (q : ℂ) ^ (2 * m)) cell z' (Sum.inl i)) := by
          funext lam
          apply rows_agree hN hp A P hzpos hze hcr (G lam) (H lam) _ χ _ _ _ _ _ hi
          intro w hw
          simp only [H, ite_eq_left hw]
        change DegreeBound (fun lam => twoDilationRow (P := {p}) (G lam) (2 * m) χ
          (firstMultiplier (fun _ => lam) m) (fun q => (q : ℂ) ^ (2 * m)) cell z' (Sum.inl i)) (j + 1)
        rw [heq]
        simp only [twoDilationRow, frickeRow, twist]
        apply DegreeBound.const_mul
        exact FinitenessAllLevelEigenvalueDegree.sum _ _ _ (fun v _ => hH _)
      | inr i =>
        have hpi : i.1.val = p := by simpa using i.1.property
        have he : (p : ℝ) * c = a / (p : ℝ) ^ j := by
          dsimp [c]
          rw [pow_succ]
          field_simp
        have hfirst : a / (p : ℝ) ^ j ≤
            ((i.1.val : ℂ) * (z' + ((i.2 : ℂ) - (cell.val : ℂ)) / Q)).im := by
          simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero, him, hpi]
          rw [← he]
          exact mul_le_mul_of_nonneg_left hz hp0.le
        have hsecond : c ≤
            ((i.1.val : ℂ) ^ 2 * (z' + ((i.2 : ℂ) - (cell.val : ℂ)) / Q)).im := by
          rw [← ofReal_natCast, ← ofReal_pow, mul_im]
          simp only [ofReal_re, ofReal_im, zero_mul, add_zero, him, hpi]
          exact hz.trans (le_mul_of_one_le_left hzpos.le (one_le_pow₀ hp1))
        simp only [twoDilationRow, firstMultiplier]
        have hcharged := (ih j hfirst).param_mul.const_mul
          ((i.1.val : ℂ) ^ m * (Real.sqrt i.1.val : ℂ))
        have hplain := (ih (j + 1) hsecond).const_mul ((i.1.val : ℂ) ^ (2 * m))
        simpa only [mul_assoc] using hcharged.sub hplain

/-- Globally in the eigenvalue, the actual formal continuation at height
at least a/p^j is a polynomial of degree at most j. -/
theorem formal_sharp_degree (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (F : space (radius a)) (j : ℕ)
    {z : ℂ} (hz : a / (p : ℝ) ^ j ≤ z.im) :
    DegreeBound (fun lam => formal A P a χ m lam F z) j :=
  iterate_sharp_degree hN hp A P ha hae χ m F _ j hz

#print axioms iterate_sharp_degree
#print axioms formal_sharp_degree

end FinitenessAllLevelFormalContinuation
