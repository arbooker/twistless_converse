module

public import FinitenessGammaDecayV1
public import FinitenessContourShiftV1

@[expose] public section

set_option autoImplicit false

namespace FinitenessBoundaryDecay

open Complex MeasureTheory Set FinitenessFiniteOrder FinitenessStripDecay

/-- Rapid polynomial decay on one vertical line, with constants allowed
to depend on the line, function and polynomial degree. -/
def Rapid (F : ℂ → ℂ) (σ : ℝ) : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, ∀ z : ℂ, z.re=σ → ‖z‖^n*‖F z‖ ≤ C

theorem gamma_shift {σ α : ℝ} (hσ : 0 < σ+α) :
    Rapid (fun z : ℂ => Gamma (z+(α : ℂ))) σ := by
  intro n
  refine ⟨2^(n-1)*(|σ|^n*Real.Gamma (σ+α)+Real.Gamma (σ+α+n)), ?_⟩
  intro z hz
  have hs : 0 < (z+(α : ℂ)).re := by simpa [hz] using hσ
  have h0 : ‖Gamma (z+(α : ℂ))‖ ≤ Real.Gamma (σ+α) := by
    simpa [hz] using FinitenessGammaDecay.norm_le_real hs
  have hn : |z.im|^n*‖Gamma (z+(α : ℂ))‖ ≤ Real.Gamma (σ+α+n) := by
    simpa [hz] using FinitenessGammaDecay.weighted_bound n hs
  have hp : ‖z‖^n ≤ 2^(n-1)*(|σ|^n+|z.im|^n) :=
    (pow_le_pow_left₀ (norm_nonneg _) (by simpa [hz] using norm_le_abs_re_add_abs_im z) n).trans
      (add_pow_le (abs_nonneg σ) (abs_nonneg z.im) n)
  calc
    ‖z‖^n*‖Gamma (z+(α : ℂ))‖
        ≤ (2^(n-1)*(|σ|^n+|z.im|^n))*‖Gamma (z+(α : ℂ))‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = 2^(n-1)*(|σ|^n*‖Gamma (z+(α : ℂ))‖+|z.im|^n*‖Gamma (z+(α : ℂ))‖) := by ring
    _ ≤ 2^(n-1)*(|σ|^n*Real.Gamma (σ+α)+Real.Gamma (σ+α+n)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left h0 (by positivity)) hn) (by positivity)

theorem of_norm_le {F G : ℂ → ℂ} {σ K : ℝ} (hG : Rapid G σ) (hK : 0 ≤ K)
    (hF : ∀ z : ℂ, z.re=σ → ‖F z‖ ≤ K*‖G z‖) : Rapid F σ := by
  intro n
  obtain ⟨C,hC⟩ := hG n
  refine ⟨K*C, ?_⟩
  intro z hz
  calc
    ‖z‖^n*‖F z‖ ≤ ‖z‖^n*(K*‖G z‖) := mul_le_mul_of_nonneg_left (hF z hz) (by positivity)
    _ = K*(‖z‖^n*‖G z‖) := by ring
    _ ≤ K*C := mul_le_mul_of_nonneg_left (hC z hz) hK

/-- A unit-root functional equation pays the opposite boundary. -/
theorem reflected {F : ℂ → ℂ} {σ κ : ℝ} {ε : ℂ} (hF : Rapid F σ)
    (hε : ‖ε‖=1) (hFE : ∀ z, F z=ε*F ((κ : ℂ)-z)) : Rapid F (κ-σ) := by
  intro n
  obtain ⟨C₀,h0⟩ := hF 0
  obtain ⟨Cₙ,hn⟩ := hF n
  refine ⟨2^(n-1)*(|κ|^n*C₀+Cₙ), ?_⟩
  intro z hz
  have hw : ((κ : ℂ)-z).re=σ := by simp only [sub_re, ofReal_re, hz]; ring
  have he : ‖F z‖=‖F ((κ : ℂ)-z)‖ := by rw [hFE z, norm_mul, hε, one_mul]
  have hnorm : ‖z‖ ≤ |κ|+‖(κ : ℂ)-z‖ := by
    calc
      ‖z‖ = ‖(κ : ℂ)-((κ : ℂ)-z)‖ := by congr 1; ring
      _ ≤ ‖(κ:ℂ)‖+‖(κ : ℂ)-z‖ := norm_sub_le _ _
      _ = |κ|+‖(κ : ℂ)-z‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hp : ‖z‖^n ≤ 2^(n-1)*(|κ|^n+‖(κ : ℂ)-z‖^n) := by
    apply (pow_le_pow_left₀ (norm_nonneg _) hnorm n).trans
    exact add_pow_le (abs_nonneg κ) (norm_nonneg ((κ : ℂ)-z)) n
  have hh0 : ‖F ((κ : ℂ)-z)‖ ≤ C₀ := by simpa using h0 ((κ : ℂ)-z) hw
  have hhn := hn ((κ : ℂ)-z) hw
  rw [he]
  calc
    ‖z‖^n*‖F ((κ : ℂ)-z)‖ ≤ (2^(n-1)*(|κ|^n+‖(κ : ℂ)-z‖^n))*‖F ((κ : ℂ)-z)‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = 2^(n-1)*(|κ|^n*‖F ((κ : ℂ)-z)‖+‖(κ : ℂ)-z‖^n*‖F ((κ : ℂ)-z)‖) := by ring
    _ ≤ 2^(n-1)*(|κ|^n*C₀+Cₙ) := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hh0 (by positivity)) hhn) (by positivity)

/-- Boundary decay plus finite order gives the actual integrable majorant
needed for contour shifting; no decay is assumed inside the strip. -/
theorem strip_majorant {F : ℂ → ℂ} (hhol : Differentiable ℂ F) (hF : Bound F)
    {a b : ℝ} (hab : a < b) (ha : Rapid F a) (hb : Rapid F b) :
    ∃ C₀ C₂ : ℝ,
      (∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖F z‖ ≤ C₀) ∧
      (∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im|^2*‖F z‖ ≤ C₂) := by
  obtain ⟨A₀,hA0⟩ := ha 0
  obtain ⟨B₀,hB0⟩ := hb 0
  obtain ⟨A₂,hA2⟩ := ha 2
  obtain ⟨B₂,hB2⟩ := hb 2
  refine ⟨max A₀ B₀,max A₂ B₂,?_,?_⟩
  · intro z hza hzb
    simpa only [pow_zero, one_mul] using weighted_strip hhol hF hab 0
      (fun w hw => (hA0 w hw).trans (le_max_left _ _))
      (fun w hw => (hB0 w hw).trans (le_max_right _ _)) hza hzb
  · intro z hza hzb
    exact weighted_strip hhol hF hab 2
      (fun w hw => (hA2 w hw).trans (le_max_left _ _))
      (fun w hw => (hB2 w hw).trans (le_max_right _ _)) hza hzb

theorem contour_eq {F : ℂ → ℂ} (hhol : Differentiable ℂ F) (hF : Bound F)
    {a b : ℝ} (hab : a < b) (ha : Rapid F a) (hb : Rapid F b) :
    (∫ t : ℝ, F ((a : ℂ)+(t : ℂ)*I)) = ∫ t : ℝ, F ((b : ℂ)+(t : ℂ)*I) := by
  obtain ⟨C₀,C₂,h0,h2⟩ := strip_majorant hhol hF hab ha hb
  exact FinitenessContourShift.vertical_eq hhol hab.le
    (fun _ hz₁ hz₂ => cauchy_bound h0 h2 hz₁ hz₂)
    (vertical_integrable hhol.continuous h0 h2 le_rfl hab.le)
    (vertical_integrable hhol.continuous h0 h2 hab.le le_rfl)

#print axioms gamma_shift
#print axioms reflected
#print axioms contour_eq

end FinitenessBoundaryDecay
