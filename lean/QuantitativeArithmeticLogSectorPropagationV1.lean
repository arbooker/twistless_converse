module
public import QuantitativeArithmeticGaussianStripTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticLogSector
open Complex QuantitativeArithmeticGaussianStrip

def logRay (z : ℂ) : ℂ := exp (I*z)

theorem compact_angle_decay (L : ℂ → ℂ)
    (hL : ∀ a b : ℝ,0<a → a<b → b<Real.pi →
      DiffContOnCl ℂ L (HadamardThreeLines.verticalStrip a b))
    (hg : ∀ a b : ℝ,0<a → a<b → b<Real.pi →
      ∃ C B : ℝ,0≤C ∧ 0≤B ∧ ∀ z : ℂ,a≤z.re → z.re≤b → ‖L z‖≤C*Real.exp (B*|z.im|))
    (hr : ∀ n : ℕ,∃ D : ℝ,0≤D ∧ ∀ z : ℂ,z.re=Real.pi/2 →
      ‖L z‖≤D*Real.exp (-(n:ℝ)*z.im))
    (δ : ℝ) (hδ : 0<δ) (hδπ : δ<Real.pi/2) (n : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ z : ℂ,δ≤z.re → z.re≤Real.pi-δ → 0≤z.im →
      ‖L z‖≤C*Real.exp (-(n:ℝ)*z.im) := by
  have hpi := Real.pi_pos
  obtain ⟨C₁,B₁,hC₁,hB₁,hg₁⟩ := hg (δ/2) (Real.pi/2) (by linarith) (by linarith) (by linarith)
  obtain ⟨C₂,B₂,hC₂,hB₂,hg₂⟩ := hg (Real.pi/2) (Real.pi-δ/2) (by linarith) (by linarith) (by linarith)
  obtain ⟨K₁,hK₁,h₁⟩ := exponential_right_propagation L (δ/2) (Real.pi/2) C₁ B₁
    (by linarith) hC₁ hB₁ (hL _ _ (by linarith) (by linarith) (by linarith)) hg₁ hr
    δ (by linarith) hδπ.le n
  obtain ⟨K₂,hK₂,h₂⟩ := exponential_left_propagation L (Real.pi/2) (Real.pi-δ/2) C₂ B₂
    (by linarith) hC₂ hB₂ (hL _ _ (by linarith) (by linarith) (by linarith)) hg₂ hr
    (Real.pi-δ) (by linarith) (by linarith) n
  refine ⟨max K₁ K₂,hK₁.trans (le_max_left _ _),?_⟩
  intro z hz hz' hi
  by_cases h : z.re≤Real.pi/2
  · exact (h₁ z hz h hi).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · exact (h₂ z (by linarith) hz' hi).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

theorem logarithmic_coordinates (w : ℂ) (hw : w≠0) :
    logRay (-I*log w)=w ∧ (-I*log w).re=arg w ∧ (-I*log w).im= -Real.log ‖w‖ := by
  constructor
  · unfold logRay
    rw [show I*(-I*log w)=log w by rw [← mul_assoc,mul_neg,I_mul_I,neg_neg,one_mul]]
    exact exp_log hw
  · simp [Complex.mul_re,Complex.mul_im,Complex.log_re,Complex.log_im]

/-- A strip estimate in logarithmic coordinates is a uniform flatness
estimate in every closed angular sector of the upper half-plane. -/
theorem flat_sector (F : ℂ → ℂ)
    (h : ∀ δ : ℝ,0<δ → δ<Real.pi/2 → ∀ n : ℕ,
      ∃ C : ℝ,0≤C ∧ ∀ z : ℂ,δ≤z.re → z.re≤Real.pi-δ → 0≤z.im →
        ‖F (logRay z)‖≤C*Real.exp (-(n:ℝ)*z.im))
    (δ : ℝ) (hδ : 0<δ) (hδπ : δ<Real.pi/2) (n : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ w : ℂ,w≠0 → ‖w‖≤1 → δ≤arg w → arg w≤Real.pi-δ →
      ‖F w‖≤C*‖w‖^n := by
  obtain ⟨C,hC,h⟩ := h δ hδ hδπ n
  refine ⟨C,hC,?_⟩
  intro w hw hw1 hwa hwb
  obtain ⟨he,hre,him⟩ := logarithmic_coordinates w hw
  have hi : 0≤(-I*log w).im := by
    rw [him]
    exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hw1)
  have hh := h (-I*log w) (by rwa [hre]) (by rwa [hre]) hi
  rw [he,him] at hh
  have hexp : Real.exp (-(n:ℝ)*(-Real.log ‖w‖))=‖w‖^n := by
    rw [show -(n:ℝ)*(-Real.log ‖w‖)=(n:ℝ)*Real.log ‖w‖ by ring,
      Real.exp_nat_mul,Real.exp_log (norm_pos_iff.mpr hw)]
  rwa [hexp] at hh
#print axioms compact_angle_decay
#print axioms flat_sector
end QuantitativeArithmeticLogSector
