module

public import FinitenessAllLevelFormalUniformBoundsV1
public import FinitenessAllLevelAnalyticIntegralV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelFormalContinuation

open Complex Metric Set Filter MeasureTheory FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelGlobalHeight
  QuantitativeArithmeticRetainedCertificate
open scoped Topology

variable {N Q p : ℕ} {hQ : 0 < Q}

theorem test_integrable (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (μ : Measure ℂ) {ψ : ℂ → ℂ} (hψ : Integrable ψ μ)
    {y : ℝ} (hy : 0 < y) (hs : ∀ z, ψ z ≠ 0 → y ≤ z.im)
    (lam : ℂ) (F : space (radius a)) :
    Integrable (fun z => ψ z * formal A P a χ m lam F z) μ := by
  obtain ⟨C, hC, hb⟩ := formal_uniform_bound hN hp A P ha hae χ m (norm_nonneg lam) hy
  apply (hψ.norm.const_mul (C * ‖F‖)).mono'
    (hψ.aestronglyMeasurable.mul (formal_measurable A P a χ m lam F).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro z
  change ‖ψ z * formal A P a χ m lam F z‖ ≤ (C * ‖F‖) * ‖ψ z‖
  by_cases hz : ψ z = 0
  · simp only [hz, zero_mul, norm_zero, mul_zero, le_refl]
  · rw [norm_mul, mul_comm (C * ‖F‖)]
    exact mul_le_mul_of_nonneg_left (hb lam le_rfl F z (hs z hz)) (norm_nonneg _)

/-- Each integrable test supported above a positive height gives an entire
scalar constraint for the actual formal continuation. -/
theorem test_analytic (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (μ : Measure ℂ) {ψ : ℂ → ℂ}
    (hψm : Measurable ψ) (hψ : Integrable ψ μ)
    {y : ℝ} (hy : 0 < y) (hs : ∀ z, ψ z ≠ 0 → y ≤ z.im)
    (F : space (radius a)) :
    AnalyticOnNhd ℂ (fun lam => ∫ z, ψ z * formal A P a χ m lam F z ∂μ) univ := by
  apply FinitenessAllLevelAnalyticIntegral.analytic_integral
  · intro lam
    exact hψm.mul (formal_measurable A P a χ m lam F)
  · intro z
    exact (differentiable_const _).mul (formal_differentiable A P a χ m F z)
  · intro w
    obtain ⟨C, hC, hb⟩ := formal_uniform_bound hN hp A P ha hae χ m
      (B := ‖w‖ + 2) (by positivity) hy
    refine ⟨fun z => (C * ‖F‖) * ‖ψ z‖, hψ.norm.const_mul _,
      Filter.Eventually.of_forall (fun z lam hlam => ?_)⟩
    change ‖ψ z * formal A P a χ m lam F z‖ ≤ (C * ‖F‖) * ‖ψ z‖
    by_cases hz : ψ z = 0
    · simp only [hz, zero_mul, norm_zero, mul_zero, le_refl]
    · have hl : ‖lam‖ ≤ ‖w‖ + 2 := by
        have h := mem_closedBall.mp hlam
        calc
          ‖lam‖ ≤ ‖lam - w‖ + ‖w‖ := norm_le_norm_sub_add _ _
          _ ≤ ‖w‖ + 2 := by rw [← dist_eq_norm] at *; linarith
      rw [norm_mul, mul_comm (C * ‖F‖)]
      exact mul_le_mul_of_nonneg_left (hb lam hl F z (hs z hz)) (norm_nonneg _)

def testLinear (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (μ : Measure ℂ) {ψ : ℂ → ℂ} (hψ : Integrable ψ μ)
    {y : ℝ} (hy : 0 < y) (hs : ∀ z, ψ z ≠ 0 → y ≤ z.im) (lam : ℂ) :
    space (radius a) →ₗ[ℂ] ℂ where
  toFun F := ∫ z, ψ z * formal A P a χ m lam F z ∂μ
  map_add' F G := by
    have he : (fun z => ψ z * formal A P a χ m lam (F + G) z) =
        fun z => ψ z * formal A P a χ m lam F z + ψ z * formal A P a χ m lam G z := by
      funext z
      simp only [← formalOperator_apply, map_add, mul_add]
    rw [he]
    exact integral_add (test_integrable hN hp A P ha hae χ m μ hψ hy hs lam F)
      (test_integrable hN hp A P ha hae χ m μ hψ hy hs lam G)
  map_smul' c F := by
    have he : (fun z => ψ z * formal A P a χ m lam (c • F) z) =
        fun z => c • (ψ z * formal A P a χ m lam F z) := by
      funext z
      simp only [← formalOperator_apply, map_smul, smul_eq_mul]
      ring
    rw [he, integral_smul]
    rfl

theorem test_bound (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (μ : Measure ℂ) {ψ : ℂ → ℂ} (hψ : Integrable ψ μ)
    {y : ℝ} (hy : 0 < y) (hs : ∀ z, ψ z ≠ 0 → y ≤ z.im)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ lam : ℂ, ‖lam‖ ≤ B → ∀ F : space (radius a),
      ‖testLinear hN hp A P ha hae χ m μ hψ hy hs lam F‖ ≤ D * ‖F‖ := by
  obtain ⟨C, hC, hb⟩ := formal_uniform_bound hN hp A P ha hae χ m hB hy
  refine ⟨C * ∫ z, ‖ψ z‖ ∂μ, mul_nonneg hC (integral_nonneg (fun z => norm_nonneg _)),
    fun lam hlam F => ?_⟩
  calc
    _ ≤ ∫ z, ‖ψ z * formal A P a χ m lam F z‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, (C * ‖F‖) * ‖ψ z‖ ∂μ := by
      apply integral_mono (test_integrable hN hp A P ha hae χ m μ hψ hy hs lam F).norm
        (hψ.norm.const_mul _)
      intro z
      change ‖ψ z * formal A P a χ m lam F z‖ ≤ (C * ‖F‖) * ‖ψ z‖
      by_cases hz : ψ z = 0
      · simp only [hz, zero_mul, norm_zero, mul_zero, le_refl]
      · rw [norm_mul, mul_comm (C * ‖F‖)]
        exact mul_le_mul_of_nonneg_left (hb lam hlam F z (hs z hz)) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; ring

def testCLM (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (μ : Measure ℂ) {ψ : ℂ → ℂ} (hψ : Integrable ψ μ)
    {y : ℝ} (hy : 0 < y) (hs : ∀ z, ψ z ≠ 0 → y ≤ z.im) (lam : ℂ) :
    space (radius a) →L[ℂ] ℂ :=
  let hb := test_bound hN hp A P ha hae χ m μ hψ hy hs (norm_nonneg lam)
  (testLinear hN hp A P ha hae χ m μ hψ hy hs lam).mkContinuous
    (Classical.choose hb) ((Classical.choose_spec hb).2 lam le_rfl)

#print axioms test_integrable
#print axioms test_analytic
#print axioms testLinear
#print axioms test_bound
#print axioms testCLM

end FinitenessAllLevelFormalContinuation
