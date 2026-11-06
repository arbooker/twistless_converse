module

public import AsymptoticCertificateBranchesV1
public import AsymptoticFoldedTerminalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCertificateOperators

open MeasureTheory UpperHalfPlane Set Filter
open FinitenessCertificate FinitenessGlobalHeight AsymptoticCertificateBranches
open AsymptoticHyperbolicSlash
open scoped Topology

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

def lowStrip (ε : ℝ) : Set ℍ := AsymptoticMassTransport.strip∩{z | z.im<ε}
def highStrip (ε : ℝ) : Set ℍ := AsymptoticMassTransport.strip∩{z | ε≤z.im}
def lowCell (ε : ℝ) (v : Index A) : Set ℍ := cell A v∩{z | z.im<ε}

theorem lowStrip_measurable (ε : ℝ) : MeasurableSet (lowStrip ε) :=
  AsymptoticMassTransport.strip_measurable.inter
    (measurableSet_Iio.preimage continuous_im.measurable)

theorem highStrip_measurable (ε : ℝ) : MeasurableSet (highStrip ε) :=
  AsymptoticMassTransport.strip_measurable.inter
    (measurableSet_Ici.preimage continuous_im.measurable)

theorem lowCell_measurable (ε : ℝ) (v : Index A) : MeasurableSet (lowCell A ε v) :=
  (cell_measurable A v).inter (measurableSet_Iio.preimage continuous_im.measurable)

noncomputable def lowPart (hN : 0<N) (P : Parameters A) (t m : ℕ) (v : Index A) : Space →L[ℂ] Space :=
  AsymptoticFoldedLow.operator (level_pos A hN v) (inputShift A v) (outputShift A v)
    (lowCell_measurable A P.ε v) (lowStrip_measurable P.ε) P.rho_pos.le
    (outputShift_nonneg A v) (outputShift_lt_one A v).le (fun _ hz => hz.1) t m

theorem lowPart_norm_le (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 1≤t)
    (m : ℕ) (v : Index A) :
    ‖lowPart A hN P t m v‖≤P.ρ^(t-1)*(3*P.ρ+16/level A v) :=
  AsymptoticFoldedLow.operator_norm_le (level_pos A hN v) (inputShift A v) (outputShift A v)
    (lowCell_measurable A P.ε v) (lowStrip_measurable P.ε) P.rho_pos.le
    (outputShift_nonneg A v) (outputShift_lt_one A v).le (fun _ hz => hz.1) ht m

noncomputable def terminalPart (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (m : ℕ) (v : Index A) : Space →L[ℂ] Space :=
  AsymptoticFoldedTerminal.operator (level_pos A hN v) (inputShift A v) (outputShift A v)
    (lowCell_measurable A P.ε v) (highStrip_measurable P.ε) P.epsilon_pos
    (outputShift_nonneg A v) (outputShift_lt_one A v).le
    (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht m

theorem terminalPart_norm_le (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (m : ℕ) (v : Index A) :
    ‖terminalPart A hN P ht m v‖≤3+4*((P.ε*level A v)^2)⁻¹ :=
  AsymptoticFoldedTerminal.operator_norm_le (level_pos A hN v) (inputShift A v) (outputShift A v)
    (lowCell_measurable A P.ε v) (highStrip_measurable P.ε) P.epsilon_pos
    (outputShift_nonneg A v) (outputShift_lt_one A v).le
    (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht m

noncomputable def amplitude (χ : ℕ → ℂ) (v : Index A) : ℂ := (scalar A v:ℂ)*χ (modulus A v)

theorem amplitude_norm (χ : ℕ → ℂ) (hχ : ∀ q, q∣Q → ‖χ q‖=1) (v : Index A) :
    ‖amplitude A χ v‖=|(scalar A v:ℝ)| := by
  have hq : modulus A v∣Q := v.2.1.val.property.1
  rw [amplitude,norm_mul,hχ (modulus A v) hq,Complex.norm_ratCast,mul_one]

noncomputable def lowConstant (P : Parameters A) : ℝ :=
  ∑ v : Index A, |(scalar A v:ℝ)| *(3*P.ρ+16/level A v)

noncomputable def terminalConstant (P : Parameters A) : ℝ :=
  ∑ v : Index A, |(scalar A v:ℝ)| *(3+4*((P.ε*level A v)^2)⁻¹)

/-- The complete low-to-low reconstruction operator from the actual
finite rational certificate and all its integer folds. -/
noncomputable def low (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (t m : ℕ) : Space →L[ℂ] Space :=
  ∑ v : Index A, amplitude A χ v • lowPart A hN P t m v

/-- The complete low-to-terminal branch operator from the certificate. -/
noncomputable def terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) : Space →L[ℂ] Space :=
  ∑ v : Index A, amplitude A χ v • terminalPart A hN P ht m v

theorem low_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q, q∣Q → ‖χ q‖=1) {t : ℕ} (ht : 1≤t) (m : ℕ) :
    ‖low A hN P χ t m‖≤P.ρ^(t-1)*lowConstant A P := by
  apply (norm_sum_le _ _).trans
  rw [lowConstant,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  rw [norm_smul,amplitude_norm A χ hχ]
  have hb := mul_le_mul_of_nonneg_left (lowPart_norm_le A hN P ht m v) (abs_nonneg (scalar A v:ℝ))
  convert hb using 1
  ring

theorem terminal_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q, q∣Q → ‖χ q‖=1) {t : ℕ} (ht : 2≤t) (m : ℕ) :
    ‖terminal A hN P χ ht m‖≤terminalConstant A P := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v _
  rw [norm_smul,amplitude_norm A χ hχ]
  exact mul_le_mul_of_nonneg_left (terminalPart_norm_le A hN P ht m v) (abs_nonneg _)

/-- Increasing the auxiliary exponent preserves the original
direct-height certificate and all its geometric constants. -/
def raiseExponent (P : Parameters A) (s : ℕ) (hs : P.s≤s) : Parameters A :=
  { P with
    s := s
    mass_bound := by
      apply le_trans _ P.mass_bound
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one P.rho_pos.le P.rho_lt_one.le hs)
        ((by norm_num : (0:ℝ)≤1).trans (FinitenessIntegerWeight.one_le_cost A)) }

/-- A scalar majorant below one half, common to the hyperbolic and
counting realizations and independent of the weight or sector. -/
theorem contraction_bound_parameters (P : Parameters A) :
    ∃ P' : Parameters A, P'.ε=P.ε ∧ P'.ρ=P.ρ ∧ P.s≤P'.s ∧
      P'.ρ^(P'.s+3-1)*lowConstant A P'<1/2 := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one P.rho_pos.le P.rho_lt_one).mul_const
    (P.ρ^2*lowConstant A P)
  simp only [zero_mul] at ht
  have hev : ∀ᶠ n : ℕ in atTop, P.ρ^n*(P.ρ^2*lowConstant A P)<1/2 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨n,hn⟩ := eventually_atTop.mp hev
  let P' := raiseExponent A P (max n P.s) (le_max_right _ _)
  refine ⟨P',rfl,rfl,le_max_right _ _,?_⟩
  have hh := hn (max n P.s) (le_max_left _ _)
  change P.ρ^(max n P.s+3-1)*lowConstant A P<1/2
  rw [show max n P.s+3-1=max n P.s+2 by omega,pow_add]
  simpa only [mul_assoc] using hh

/-- One auxiliary exponent works uniformly for every holomorphic weight
and every unit-modulus sector multiplier. Its geometric cell rules and
height cutoff are exactly those of the supplied certificate. -/
theorem contraction_parameters (hN : 0<N) (P : Parameters A) :
    ∃ P' : Parameters A, P'.ε=P.ε ∧ P'.ρ=P.ρ ∧ P.s≤P'.s ∧
      ∀ χ : ℕ → ℂ, (∀ q, q∣Q → ‖χ q‖=1) → ∀ m : ℕ,
        ‖low A hN P' χ (P'.s+3) m‖<1/2 := by
  obtain ⟨P',hε,hρ,hs,hb⟩ := contraction_bound_parameters A P
  exact ⟨P',hε,hρ,hs,fun χ hχ m =>
    (low_norm_le A hN P' χ hχ (by omega : 1≤P'.s+3) m).trans_lt hb⟩

#print axioms low_norm_le
#print axioms terminal_norm_le
#print axioms contraction_bound_parameters
#print axioms contraction_parameters

end AsymptoticCertificateOperators
