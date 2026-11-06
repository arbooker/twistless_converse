module

public import AsymptoticRegularFoldedTerminalV1
public import AsymptoticCertificateOperatorsV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularCertificate

open MeasureTheory UpperHalfPlane Set FinitenessCertificate FinitenessGlobalHeight
open AsymptoticCertificateBranches AsymptoticCertificateOperators AsymptoticRegularTrace
open AsymptoticRegularFoldedLow (Space)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def levelQ (v : Index A) : ℚ := Nat.lcm N ((modulus A v)^2)
def inputShiftQ (v : Index A) : ℚ := (v.2.1.val.val.2-(v.1:ℕ):ℚ)/Q
def outputShiftQ (v : Index A) : ℚ := (v.2.2.val:ℚ)/modulus A v

theorem levelQ_cast (v : Index A) : (levelQ A v:ℝ)=level A v := by simp [levelQ,level]
theorem inputShiftQ_cast (v : Index A) : (inputShiftQ A v:ℝ)=inputShift A v := by
  simp [inputShiftQ,inputShift]
theorem outputShiftQ_cast (v : Index A) : (outputShiftQ A v:ℝ)=outputShift A v := by
  simp [outputShiftQ,outputShift]

theorem levelQ_pos (hN : 0<N) (v : Index A) : 0<levelQ A v := by
  have he := level_pos A hN v
  rw [← levelQ_cast A v] at he
  exact_mod_cast he

theorem outputShiftQ_nonneg (v : Index A) : 0≤(outputShiftQ A v:ℝ) := by
  rw [outputShiftQ_cast]
  exact outputShift_nonneg A v

theorem outputShiftQ_le_one (v : Index A) : (outputShiftQ A v:ℝ)≤1 := by
  rw [outputShiftQ_cast]
  exact (outputShift_lt_one A v).le

noncomputable def lowPart (hN : 0<N) (P : Parameters A) (t : ℕ) (v : Index A) (z : ℍ) :
    Space →L[ℂ] Space :=
  AsymptoticRegularFoldedLow.operator (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell A P.ε v) (lowStrip P.ε) P.rho_pos.le (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => hz.1) t z

theorem lowPart_norm_le (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 1≤t) (v : Index A) (z : ℍ) :
    ‖lowPart A hN P t v z‖≤P.ρ^(t-1)*(3*P.ρ+16/level A v) := by
  simpa only [lowPart,levelQ_cast] using AsymptoticRegularFoldedLow.operator_norm_le
    (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell A P.ε v) (lowStrip P.ε) P.rho_pos.le (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => hz.1) ht z

noncomputable def terminalPart (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (v : Index A) (z : ℍ) : Space →L[ℂ] Space :=
  AsymptoticRegularFoldedTerminal.operator (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell A P.ε v) (highStrip P.ε) P.epsilon_pos (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht z

theorem terminalPart_norm_le (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (v : Index A) (z : ℍ) : ‖terminalPart A hN P ht v z‖≤3+4*((P.ε*level A v)^2)⁻¹ := by
  simpa only [terminalPart,levelQ_cast] using AsymptoticRegularFoldedTerminal.operator_norm_le
    (levelQ_pos A hN v) (inputShiftQ A v) (outputShiftQ A v)
    (lowCell A P.ε v) (highStrip P.ε) P.epsilon_pos (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht z

noncomputable def low (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (t : ℕ) (z : ℍ) :
    Space →L[ℂ] Space := ∑ v : Index A,amplitude A χ v • lowPart A hN P t v z

noncomputable def terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) {t : ℕ} (ht : 2≤t) (z : ℍ) :
    Space →L[ℂ] Space := ∑ v : Index A,amplitude A χ v • terminalPart A hN P ht v z

theorem low_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    ‖low A hN P χ t z‖≤P.ρ^(t-1)*lowConstant A P := by
  apply (norm_sum_le _ _).trans
  rw [lowConstant,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  rw [norm_smul,amplitude_norm A χ hχ]
  have hb := mul_le_mul_of_nonneg_left (lowPart_norm_le A hN P ht v z) (abs_nonneg (scalar A v:ℝ))
  convert hb using 1
  ring

theorem terminal_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) {t : ℕ} (ht : 2≤t) (z : ℍ) :
    ‖terminal A hN P χ ht z‖≤terminalConstant A P := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v _
  rw [norm_smul,amplitude_norm A χ hχ]
  exact mul_le_mul_of_nonneg_left (terminalPart_norm_le A hN P ht v z) (abs_nonneg _)

/-- One scalar bound contracts both actual realizations, uniformly in
the orbit root, the sector multiplier and the holomorphic weight. -/
theorem common_contraction_parameters (hN : 0<N) (P : Parameters A) :
    ∃ P' : Parameters A,P'.ε=P.ε ∧ P'.ρ=P.ρ ∧ P.s≤P'.s ∧
      ∀ χ : ℕ → ℂ,(∀ q,q∣Q → ‖χ q‖=1) →
        (∀ z,‖low A hN P' χ (P'.s+3) z‖<1/2) ∧
        (∀ m,‖AsymptoticCertificateOperators.low A hN P' χ (P'.s+3) m‖<1/2) := by
  obtain ⟨P',hε,hρ,hs,hb⟩ := contraction_bound_parameters A P
  exact ⟨P',hε,hρ,hs,fun χ hχ =>
    ⟨fun z => (low_norm_le A hN P' χ hχ (by omega) z).trans_lt hb,
     fun m => (AsymptoticCertificateOperators.low_norm_le A hN P' χ hχ (by omega) m).trans_lt hb⟩⟩

theorem low_covariant (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) {t : ℕ} (ht : 1≤t) :
    Covariant (low A hN P χ t) := by
  apply covariant_finsetSum
  intro v _
  apply covariant_smul
  exact AsymptoticRegularFoldedLow.operator_covariant (levelQ_pos A hN v)
    (inputShiftQ A v) (outputShiftQ A v) (lowCell A P.ε v) (lowStrip P.ε)
    P.rho_pos.le (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v) (fun _ hz => hz.1) ht

theorem terminal_covariant (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) {t : ℕ} (ht : 2≤t) :
    Covariant (terminal A hN P χ ht) := by
  apply covariant_finsetSum
  intro v _
  apply covariant_smul
  exact AsymptoticRegularFoldedTerminal.operator_covariant (levelQ_pos A hN v)
    (inputShiftQ A v) (outputShiftQ A v) (lowCell A P.ε v) (highStrip P.ε)
    P.epsilon_pos (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht

theorem low_matrix_measurable (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 1≤t) (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (low A hN P χ t z) g h) := by
  apply matrix_finsetSum_measurable
  intro v _ g h
  apply matrix_smul_measurable
  intro g h
  exact AsymptoticRegularFoldedLow.operator_matrix_measurable (levelQ_pos A hN v)
    (inputShiftQ A v) (outputShiftQ A v) (lowCell_measurable A P.ε v) (lowStrip_measurable P.ε)
    P.rho_pos.le (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v) (fun _ hz => hz.1) ht g h

theorem terminal_matrix_measurable (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (terminal A hN P χ ht z) g h) := by
  apply matrix_finsetSum_measurable
  intro v _ g h
  apply matrix_smul_measurable
  intro g h
  exact AsymptoticRegularFoldedTerminal.operator_matrix_measurable (levelQ_pos A hN v)
    (inputShiftQ A v) (outputShiftQ A v) (lowCell_measurable A P.ε v) (highStrip_measurable P.ε)
    P.epsilon_pos (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht g h

#print axioms low_norm_le
#print axioms terminal_norm_le
#print axioms common_contraction_parameters
#print axioms low_covariant
#print axioms terminal_covariant
#print axioms low_matrix_measurable
#print axioms terminal_matrix_measurable

end AsymptoticRegularCertificate
