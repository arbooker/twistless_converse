module

public import AsymptoticFiniteFoldAssemblyV1
public import AsymptoticRegularCertificateV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularCertificate

open MeasureTheory UpperHalfPlane Set Filter AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticCertificateBranches
open AsymptoticCertificateOperators
open AsymptoticRegularFoldedLow (Space)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The certificate branch with only the finite fold set I retained. -/
noncomputable def finiteLowPart (hN : 0<N) (P : Parameters A) (t : ℕ)
    (z : ℍ) (v : Index A) (I : Finset ℤ) : Space →L[ℂ] Space :=
  ∑ n∈I,AsymptoticRegularFoldedLow.term (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell A P.ε v) (lowStrip P.ε) P.rho_pos.le
    (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v) (fun _ hz => hz.1) t n z

theorem finiteLowPart_norm_le (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 1≤t)
    (z : ℍ) (v : Index A) (I : Finset ℤ) :
    ‖finiteLowPart A hN P t z v I‖≤P.ρ^(t-1)*(3*P.ρ+16/level A v) := by
  simpa only [finiteLowPart,levelQ_cast] using
    AsymptoticRegularFoldedLow.finite_folds_norm_le (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell A P.ε v) (lowStrip P.ε) P.rho_pos.le
    (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v) (fun _ hz => hz.1) ht I z

noncomputable def finiteLow (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (t : ℕ)
    (I : Finset ℤ) (z : ℍ) : Space →L[ℂ] Space :=
  ∑ v : Index A,amplitude A χ v • finiteLowPart A hN P t z v I

theorem finiteLow_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) {t : ℕ} (ht : 1≤t) (I : Finset ℤ) (z : ℍ) :
    ‖finiteLow A hN P χ t I z‖≤P.ρ^(t-1)*lowConstant A P := by
  apply (norm_sum_le _ _).trans
  rw [lowConstant,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  rw [norm_smul,amplitude_norm A χ hχ]
  have hb := mul_le_mul_of_nonneg_left
    (finiteLowPart_norm_le A hN P ht z v I) (abs_nonneg (scalar A v:ℝ))
  convert hb using 1
  ring

/-- Uniformity includes every weight/root and every unit-modulus sector
multiplier, with the same finite fold set for the whole certificate. -/
theorem finiteLow_tendstoUniformly (hN : 0<N) (P : Parameters A)
    {α : Type*} (z : α → ℍ) (χ : α → ℕ → ℂ)
    (hχ : ∀ a q,q∣Q → ‖χ a q‖=1) {t : ℕ} (ht : 1≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun a => finiteLow A hN P (χ a) t I (z a))
      (fun a => low A hN P (χ a) t (z a)) atTop := by
  apply AsymptoticFiniteFoldAssembly.tendstoUniformly
    (b:=fun v n => |(scalar A v:ℝ)| *(AsymptoticFoldMajorant.majorant P.ρ (4/level A v) n^t))
  · intro v
    exact (AsymptoticFoldMajorant.power_summable_bound P.rho_pos.le (div_nonneg (by norm_num) (level_pos A hN v).le) ht).1.mul_left _
  · intro v n a
    rw [norm_smul,amplitude_norm A (χ a) (hχ a)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa only [levelQ_cast] using AsymptoticRegularFoldedLow.term_norm_le (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
      (lowCell A P.ε v) (lowStrip P.ε) P.rho_pos.le
      (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v) (fun _ hz => hz.1) t n (z a)

#print axioms finiteLowPart_norm_le
#print axioms finiteLow_norm_le
#print axioms finiteLow_tendstoUniformly

/-- The certificate branch with only the finite fold set I retained. -/
noncomputable def finiteTerminalPart (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (z : ℍ) (v : Index A) (I : Finset ℤ) : Space →L[ℂ] Space :=
  ∑ n∈I,AsymptoticRegularFoldedTerminal.term (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell A P.ε v) (highStrip P.ε) P.epsilon_pos
    (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht n z

theorem finiteTerminalPart_norm_le (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (z : ℍ) (v : Index A) (I : Finset ℤ) :
    ‖finiteTerminalPart A hN P ht z v I‖≤3+4*((P.ε*level A v)^2)⁻¹ := by
  simpa only [finiteTerminalPart,levelQ_cast] using
    AsymptoticRegularFoldedTerminal.finite_folds_norm_le (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell A P.ε v) (highStrip P.ε) P.epsilon_pos
    (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht I z

noncomputable def finiteTerminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) {t : ℕ} (ht : 2≤t)
    (I : Finset ℤ) (z : ℍ) : Space →L[ℂ] Space :=
  ∑ v : Index A,amplitude A χ v • finiteTerminalPart A hN P ht z v I

theorem finiteTerminal_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (z : ℍ) :
    ‖finiteTerminal A hN P χ ht I z‖≤terminalConstant A P := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v _
  rw [norm_smul,amplitude_norm A χ hχ]
  exact mul_le_mul_of_nonneg_left
    (finiteTerminalPart_norm_le A hN P ht z v I) (abs_nonneg (scalar A v:ℝ))

/-- Uniformity includes every weight/root and every unit-modulus sector
multiplier, with the same finite fold set for the whole certificate. -/
theorem finiteTerminal_tendstoUniformly (hN : 0<N) (P : Parameters A)
    {α : Type*} (z : α → ℍ) (χ : α → ℕ → ℂ)
    (hχ : ∀ a q,q∣Q → ‖χ a q‖=1) {t : ℕ} (ht : 2≤t) :
    TendstoUniformly
      (fun I : Finset ℤ => fun a => finiteTerminal A hN P (χ a) ht I (z a))
      (fun a => terminal A hN P (χ a) ht (z a)) atTop := by
  apply AsymptoticFiniteFoldAssembly.tendstoUniformly
    (b:=fun v n => |(scalar A v:ℝ)| *(AsymptoticFoldMajorant.majorant 1 ((P.ε*level A v)^2)⁻¹ n))
  · intro v
    exact (AsymptoticFoldMajorant.majorant_summable_bound zero_le_one (by positivity : 0≤((P.ε*level A v)^2)⁻¹)).1.mul_left _
  · intro v n a
    rw [norm_smul,amplitude_norm A (χ a) (hχ a)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa only [levelQ_cast] using AsymptoticRegularFoldedTerminal.term_norm_le (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
      (lowCell A P.ε v) (highStrip P.ε) P.epsilon_pos
      (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
      (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht n (z a)

#print axioms finiteTerminalPart_norm_le
#print axioms finiteTerminal_norm_le
#print axioms finiteTerminal_tendstoUniformly

theorem finiteLow_covariant (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (t : ℕ) (I : Finset ℤ) :
    Covariant (fun z => finiteLow A hN P χ t I z) := by
  apply covariant_finsetSum
  intro v _
  apply AsymptoticRegularTrace.covariant_smul
  apply covariant_finsetSum
  intro n _
  exact AsymptoticRegularFoldedLow.term_covariant (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell A P.ε v) (lowStrip P.ε) P.rho_pos.le
    (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v) (fun _ hz => hz.1) t n

theorem finiteLow_matrix_measurable (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (t : ℕ) (I : Finset ℤ) (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (finiteLow A hN P χ t I z) a b) := by
  apply matrix_finsetSum_measurable
  intro v _ a b
  apply matrix_smul_measurable
  intro a b
  apply matrix_finsetSum_measurable
  intro n _ a b
  exact AsymptoticRegularFoldedLow.term_matrix_measurable (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell_measurable A P.ε v) (lowStrip_measurable P.ε) P.rho_pos.le
    (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v) (fun _ hz => hz.1) t n a b

#print axioms finiteLow_covariant
#print axioms finiteLow_matrix_measurable

theorem finiteTerminal_covariant (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (I : Finset ℤ) :
    Covariant (fun z => finiteTerminal A hN P χ ht I z) := by
  apply covariant_finsetSum
  intro v _
  apply AsymptoticRegularTrace.covariant_smul
  apply covariant_finsetSum
  intro n _
  exact AsymptoticRegularFoldedTerminal.term_covariant (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell A P.ε v) (highStrip P.ε) P.epsilon_pos
    (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht n

theorem finiteTerminal_matrix_measurable (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (I : Finset ℤ) (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (finiteTerminal A hN P χ ht I z) a b) := by
  apply matrix_finsetSum_measurable
  intro v _ a b
  apply matrix_smul_measurable
  intro a b
  apply matrix_finsetSum_measurable
  intro n _ a b
  exact AsymptoticRegularFoldedTerminal.term_matrix_measurable (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell_measurable A P.ε v) (highStrip_measurable P.ε) P.epsilon_pos
    (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht n a b

#print axioms finiteTerminal_covariant
#print axioms finiteTerminal_matrix_measurable

end AsymptoticRegularCertificate
