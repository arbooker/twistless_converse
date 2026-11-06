module

public import FinitenessAllLevelFormalTestsV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCauchyConstraints

open Complex Metric Set Filter MeasureTheory FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelBoundaryCoordinates FinitenessAllLevelGlobalHeight
  FinitenessAllLevelFormalContinuation QuantitativeArithmeticRetainedCertificate
open scoped Topology

theorem height_lower {c z : ℂ} {R : ℝ} (hz : z ∈ closedBall c R) :
    c.im - R ≤ z.im := by
  have hd : ‖c - z‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
  have hi := (le_abs_self (c - z).im).trans (Complex.abs_im_le_norm (c - z))
  simp only [sub_im] at hi
  linarith

def transform (c : ℂ) (R : ℝ) (G : ℂ → ℂ) (w : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • G z

/-- Pointwise Cauchy identities are an exact alternative to distributional
holomorphy tests. They do not assume any analytic structure on the zero set. -/
def CauchyIdentities (G : ℂ → ℂ) : Prop :=
  ∀ c : ℂ, ∀ R : ℝ, 0 < R → R < c.im → ∀ w ∈ ball c R, transform c R G w = G w

theorem differentiableOn_of_identities {G : ℂ → ℂ}
    (hi : ∀ c : ℂ, ∀ R : ℝ, 0 < R → R < c.im → CircleIntegrable G c R)
    (he : CauchyIdentities G) : DifferentiableOn ℂ G {z : ℂ | 0 < z.im} := by
  intro w hw
  have hr : 0 < w.im / 2 := half_pos hw
  have hri : w.im / 2 < w.im := by linarith
  have hn : w ∉ sphere w |w.im / 2| := by
    simp only [mem_sphere, dist_self, abs_of_pos hr]
    exact hr.ne
  have hd : DifferentiableAt ℂ (transform w (w.im / 2) G) w :=
    ((Complex.hasDerivAt_circleIntegral_sub_inv_smul (hi w _ hr hri) hn).const_smul
      ((2 * Real.pi * I : ℂ)⁻¹)).differentiableAt
  have heq : G =ᶠ[𝓝 w] transform w (w.im / 2) G := by
    filter_upwards [ball_mem_nhds w hr] with v hv
    exact (he w _ hr hri v hv).symm
  exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt

theorem identities_of_differentiableOn {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im}) : CauchyIdentities G := by
  intro c R hR hRc w hw
  have hd : DifferentiableOn ℂ G (closedBall c R) := hG.mono (fun z hz =>
    (sub_pos.mpr hRc).trans_le (height_lower hz))
  exact (hd.mono closure_ball_subset_closedBall).diffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw

theorem formal_circleIntegrable {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a))
    (c : ℂ) {R : ℝ} (hR : 0 < R) (hRc : R < c.im) :
    CircleIntegrable (formal A P a χ m lam F) c R := by
  obtain ⟨C, _, hb⟩ := formal_uniform_bound hN hp A P ha hae χ m
    (norm_nonneg lam) (sub_pos.mpr hRc)
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C * ‖F‖)
    volume 0 (2 * Real.pi)).mono_fun'
  · exact ((formal_measurable A P a χ m lam F).comp
      (continuous_circleMap c R).measurable).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun θ => hb lam le_rfl F _
      (height_lower (sphere_subset_closedBall (circleMap_mem_sphere c hR.le θ))))

/-- For the actual formal reconstruction the Cauchy equations are
equivalent to genuine holomorphy on the whole upper half-plane. -/
theorem formal_identities_iff {N Q p : ℕ} {hQ : 0 < Q}
    (hN : 0 < N) (hp : p.Prime) (A : Certificate N {p} Q hQ)
    {L : ℝ} (P : Parameters A L) {a : ℝ} (ha : 0 < a) (hae : a ≤ P.ε)
    (χ : ℕ → ℂ) (m : ℕ) (lam : ℂ) (F : space (radius a)) :
    CauchyIdentities (formal A P a χ m lam F) ↔
      DifferentiableOn ℂ (formal A P a χ m lam F) {z : ℂ | 0 < z.im} :=
  ⟨differentiableOn_of_identities (formal_circleIntegrable hN hp A P ha hae χ m lam F),
    identities_of_differentiableOn⟩

#print axioms differentiableOn_of_identities
#print axioms identities_of_differentiableOn
#print axioms formal_circleIntegrable
#print axioms formal_identities_iff

end FinitenessAllLevelCauchyConstraints
