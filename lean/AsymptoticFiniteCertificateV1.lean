module

public import AsymptoticFiniteFoldAssemblyV1
public import AsymptoticRegularCertificateV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCertificateOperators

open MeasureTheory UpperHalfPlane Set Filter
open FinitenessCertificate FinitenessGlobalHeight AsymptoticCertificateBranches
open AsymptoticCertificateOperators
open AsymptoticHyperbolicSlash (Space)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The certificate branch with only the finite fold set I retained. -/
noncomputable def finiteLowPart (hN : 0<N) (P : Parameters A) (t : ℕ)
    (m : ℕ) (v : Index A) (I : Finset ℤ) : Space →L[ℂ] Space :=
  ∑ n∈I,AsymptoticFoldedLow.term (level_pos A hN v) (inputShift A v) (outputShift A v)
    (lowCell_measurable A P.ε v) (lowStrip_measurable P.ε) P.rho_pos.le
    (outputShift_nonneg A v) (outputShift_lt_one A v).le (fun _ hz => hz.1) t m n

theorem finiteLowPart_norm_le (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 1≤t)
    (m : ℕ) (v : Index A) (I : Finset ℤ) :
    ‖finiteLowPart A hN P t m v I‖≤P.ρ^(t-1)*(3*P.ρ+16/level A v) := by
  exact
    AsymptoticFoldedLow.finite_folds_norm_le (level_pos A hN v) (inputShift A v) (outputShift A v)
    (lowCell_measurable A P.ε v) (lowStrip_measurable P.ε) P.rho_pos.le
    (outputShift_nonneg A v) (outputShift_lt_one A v).le (fun _ hz => hz.1) ht I m

noncomputable def finiteLow (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (t : ℕ)
    (I : Finset ℤ) (m : ℕ) : Space →L[ℂ] Space :=
  ∑ v : Index A,amplitude A χ v • finiteLowPart A hN P t m v I

theorem finiteLow_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) {t : ℕ} (ht : 1≤t) (I : Finset ℤ) (m : ℕ) :
    ‖finiteLow A hN P χ t I m‖≤P.ρ^(t-1)*lowConstant A P := by
  apply (norm_sum_le _ _).trans
  rw [lowConstant,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  rw [norm_smul,amplitude_norm A χ hχ]
  have hb := mul_le_mul_of_nonneg_left
    (finiteLowPart_norm_le A hN P ht m v I) (abs_nonneg (scalar A v:ℝ))
  convert hb using 1
  ring

/-- Uniformity includes every weight/root and every unit-modulus sector
multiplier, with the same finite fold set for the whole certificate. -/
theorem finiteLow_tendstoUniformly (hN : 0<N) (P : Parameters A)
    {α : Type*} (m : α → ℕ) (χ : α → ℕ → ℂ)
    (hχ : ∀ a q,q∣Q → ‖χ a q‖=1) {t : ℕ} (ht : 1≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun a => finiteLow A hN P (χ a) t I (m a))
      (fun a => low A hN P (χ a) t (m a)) atTop := by
  apply AsymptoticFiniteFoldAssembly.tendstoUniformly
    (b:=fun v n => |(scalar A v:ℝ)| *(AsymptoticFoldMajorant.majorant P.ρ (4/level A v) n^t))
  · intro v
    exact (AsymptoticFoldMajorant.power_summable_bound P.rho_pos.le (div_nonneg (by norm_num) (level_pos A hN v).le) ht).1.mul_left _
  · intro v n a
    rw [norm_smul,amplitude_norm A (χ a) (hχ a)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact AsymptoticFoldedLow.term_norm_le (level_pos A hN v) (inputShift A v) (outputShift A v)
      (lowCell_measurable A P.ε v) (lowStrip_measurable P.ε) P.rho_pos.le
      (outputShift_nonneg A v) (outputShift_lt_one A v).le (fun _ hz => hz.1) t (m a) n

#print axioms finiteLowPart_norm_le
#print axioms finiteLow_norm_le
#print axioms finiteLow_tendstoUniformly

/-- The certificate branch with only the finite fold set I retained. -/
noncomputable def finiteTerminalPart (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (m : ℕ) (v : Index A) (I : Finset ℤ) : Space →L[ℂ] Space :=
  ∑ n∈I,AsymptoticFoldedTerminal.term (level_pos A hN v) (inputShift A v) (outputShift A v)
    (lowCell_measurable A P.ε v) (highStrip_measurable P.ε) P.epsilon_pos
    (outputShift_nonneg A v) (outputShift_lt_one A v).le
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht m n

theorem finiteTerminalPart_norm_le (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (m : ℕ) (v : Index A) (I : Finset ℤ) :
    ‖finiteTerminalPart A hN P ht m v I‖≤3+4*((P.ε*level A v)^2)⁻¹ := by
  exact
    AsymptoticFoldedTerminal.finite_folds_norm_le (level_pos A hN v) (inputShift A v) (outputShift A v)
    (lowCell_measurable A P.ε v) (highStrip_measurable P.ε) P.epsilon_pos
    (outputShift_nonneg A v) (outputShift_lt_one A v).le
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht I m

noncomputable def finiteTerminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) {t : ℕ} (ht : 2≤t)
    (I : Finset ℤ) (m : ℕ) : Space →L[ℂ] Space :=
  ∑ v : Index A,amplitude A χ v • finiteTerminalPart A hN P ht m v I

theorem finiteTerminal_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (m : ℕ) :
    ‖finiteTerminal A hN P χ ht I m‖≤terminalConstant A P := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v _
  rw [norm_smul,amplitude_norm A χ hχ]
  exact mul_le_mul_of_nonneg_left
    (finiteTerminalPart_norm_le A hN P ht m v I) (abs_nonneg (scalar A v:ℝ))

/-- Uniformity includes every weight/root and every unit-modulus sector
multiplier, with the same finite fold set for the whole certificate. -/
theorem finiteTerminal_tendstoUniformly (hN : 0<N) (P : Parameters A)
    {α : Type*} (m : α → ℕ) (χ : α → ℕ → ℂ)
    (hχ : ∀ a q,q∣Q → ‖χ a q‖=1) {t : ℕ} (ht : 2≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun a => finiteTerminal A hN P (χ a) ht I (m a))
      (fun a => terminal A hN P (χ a) ht (m a)) atTop := by
  apply AsymptoticFiniteFoldAssembly.tendstoUniformly
    (b:=fun v n => |(scalar A v:ℝ)| *(AsymptoticFoldMajorant.majorant 1 ((P.ε*level A v)^2)⁻¹ n))
  · intro v
    exact (AsymptoticFoldMajorant.majorant_summable_bound zero_le_one (by positivity : 0≤((P.ε*level A v)^2)⁻¹)).1.mul_left _
  · intro v n a
    rw [norm_smul,amplitude_norm A (χ a) (hχ a)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact AsymptoticFoldedTerminal.term_norm_le (level_pos A hN v) (inputShift A v) (outputShift A v)
      (lowCell_measurable A P.ε v) (highStrip_measurable P.ε) P.epsilon_pos
      (outputShift_nonneg A v) (outputShift_lt_one A v).le
      (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht (m a) n

#print axioms finiteTerminalPart_norm_le
#print axioms finiteTerminal_norm_le
#print axioms finiteTerminal_tendstoUniformly

end AsymptoticCertificateOperators
