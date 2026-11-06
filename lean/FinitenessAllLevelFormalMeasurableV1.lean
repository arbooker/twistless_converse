module

public import FinitenessAllLevelFormalOperatorAnalyticV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex Set MeasureTheory FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelBoundaryGeometry
  FinitenessAllLevelBoundarySampling FinitenessAllLevelCertificateBoundary
  FinitenessAllLevelReconstruction FinitenessAllLevelGlobalHeight
  QuantitativeArithmeticRetainedCertificate QuantitativeArithmeticRetainedReconstruction
  FinitenessAnalyticReconstruction

variable {N Q p : ℕ} {hQ : 0 < Q}

theorem lift_measurable {a : ℝ} (F : space (radius a)) : Measurable (lift F) :=
  (extend_measurable F).comp Function.Periodic.continuous_qParam.measurable

theorem row_measurable (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ)
    {G : ℂ → ℂ} (hG : Measurable G) (j : Fin Q)
    (i : SpanningIntegerRows.AugIndex N (({p} : Finset ℕ) : Set ℕ) Q) :
    Measurable (fun z => twoDilationRow G (2 * m) χ
      (FinitenessAllLevelGoodTrace.firstMultiplier (fun _ => lam) m)
      (fun q => (q : ℂ) ^ (2 * m)) j z i) := by
  cases i with
  | inl i =>
    simp only [twoDilationRow, frickeRow, twist]
    apply Measurable.mul
    · exact measurable_const.div ((measurable_const.mul
        (measurable_id.add_const _)).pow_const _)
    · apply Finset.measurable_sum
      intro v _
      exact hG.comp ((measurable_const.div
        (measurable_const.mul (measurable_id.add_const _))).add_const _)
  | inr i =>
    exact (measurable_const.mul (hG.comp
      (measurable_const.mul (measurable_id.add_const _)))).sub
      (measurable_const.mul (hG.comp
        (measurable_const.mul (measurable_id.add_const _))))

set_option maxHeartbeats 800000 in
theorem step_measurable (A : Certificate N {p} Q hQ) (χ : ℕ → ℂ) (m : ℕ)
    (lam : ℂ) {G : ℂ → ℂ} (hG : Measurable G) : Measurable (step A χ m lam G) := by
  have hline : Measurable (fun z : ℂ =>
      line (coordinate (Function.Periodic.qParam 1 z)) z.im) :=
    (Complex.continuous_ofReal.measurable.comp
      (coordinate_measurable.comp Function.Periodic.continuous_qParam.measurable)).add
      ((Complex.continuous_ofReal.measurable.comp Complex.continuous_im.measurable).mul_const I)
  have hsel : Measurable (fun z : ℂ => selector Q hQ (Function.Periodic.qParam 1 z)) := (selector_measurable Q hQ).comp Function.Periodic.continuous_qParam.measurable
  let H : Fin Q × ℂ → ℂ := fun t =>
    ∑ i ∈ (A.coeff t.1).support, (A.coeff t.1 i : ℂ) *
      twoDilationRow G (2 * m) χ
        (FinitenessAllLevelGoodTrace.firstMultiplier (fun _ => lam) m)
        (fun q => (q : ℂ) ^ (2 * m)) t.1 t.2 i
  have hj (j : Fin Q) : Measurable (fun z : ℂ => H (j, z)) := by
    dsimp only [H]
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (row_measurable χ m lam hG j i)
  have hm : Measurable H := measurable_from_prod_countable_right hj
  exact hm.comp (f := fun z : ℂ =>
    (selector Q hQ (Function.Periodic.qParam 1 z),
      line (coordinate (Function.Periodic.qParam 1 z)) z.im)) (hsel.prodMk hline)

theorem iterate_measurable (A : Certificate N {p} Q hQ) (a : ℝ) (χ : ℕ → ℂ)
    (m : ℕ) (lam : ℂ) (F : space (radius a)) (n : ℕ) :
    Measurable (iterate A a χ m lam F n) := by
  induction n with
  | zero => exact lift_measurable F
  | succ n ih =>
    exact Measurable.ite (measurableSet_le measurable_const Complex.continuous_im.measurable)
      (lift_measurable F) (step_measurable A χ m lam ih)

theorem depth_measurable (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) : Measurable (depth A P a) := by
  have h : Measurable (fun z : {z : ℂ | 0 < z.im} =>
      Nat.find (depth_exists A P a z.property)) :=
    measurable_find (fun z => depth_exists A P a z.property)
      (fun n => measurableSet_le measurable_const
        (Complex.continuous_im.measurable.comp measurable_subtype_coe))
  exact h.dite measurable_const
    (measurableSet_lt measurable_const Complex.continuous_im.measurable)

/-- The actual finite reconstruction tree is Borel measurable, including
its selected cells and depth interfaces. No spatial holomorphy is assumed. -/
theorem formal_measurable (A : Certificate N {p} Q hQ) {L : ℝ} (P : Parameters A L)
    (a : ℝ) (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a)) :
    Measurable (formal A P a χ m lam F) :=
  (measurable_from_prod_countable_right
    (f := fun t : ℕ × ℂ => iterate A a χ m lam F t.1 t.2)
    (iterate_measurable A a χ m lam F)).comp
    ((depth_measurable A P a).prodMk measurable_id)

#print axioms step_measurable
#print axioms iterate_measurable
#print axioms depth_measurable
#print axioms formal_measurable

end FinitenessAllLevelFormalContinuation
