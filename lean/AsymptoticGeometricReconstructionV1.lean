module

public import AsymptoticCertificateSupportV1
public import AsymptoticNeumannReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticGeometricReconstruction

open MeasureTheory UpperHalfPlane Set ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight AsymptoticHyperbolicSlash
open AsymptoticCertificateOperators

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Actual terminal data, extended by zero in the hyperbolic L² space. -/
noncomputable abbrev TerminalSpace (P : Parameters A) :=
  AsymptoticRegionL2.Space volume (highStrip P.ε) (highStrip_measurable P.ε)

noncomputable def lowSolution (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (m : ℕ) :
    TerminalSpace A P →L[ℂ] Space :=
  AsymptoticReconstruction.low (low A hN P χ (P.s+3) m)
    ((terminal A hN P χ (by omega : 2≤P.s+3) m).comp (TerminalSpace A P).subtypeL)

/-- The geometric extension is the unchanged terminal section plus the
Neumann solution of the actual, fully folded low-height equation. -/
noncomputable def extension (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (m : ℕ) :
    TerminalSpace A P →L[ℂ] Space :=
  (TerminalSpace A P).subtypeL+lowSolution A hN P χ m

theorem lowSolution_equation (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (m : ℕ)
    (hK : ‖low A hN P χ (P.s+3) m‖<1) (g : TerminalSpace A P) :
    lowSolution A hN P χ m g=
      low A hN P χ (P.s+3) m (lowSolution A hN P χ m g)+
        terminal A hN P χ (by omega : 2≤P.s+3) m (g:Space) :=
  AsymptoticReconstruction.low_equation _ _ hK g

theorem lowSolution_terminal_zero (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (m : ℕ)
    (hK : ‖low A hN P χ (P.s+3) m‖<1) (g : TerminalSpace A P) :
    highProjection A P (lowSolution A hN P χ m g)=0 := by
  rw [lowSolution_equation A hN P χ m hK g,map_add,
    high_low_zero A hN P χ (by omega : 1≤P.s+3),high_terminal_zero,add_zero]

/-- The terminal identity is proved for the actual measurable terminal
projection, rather than assumed as a lower-bound hypothesis. -/
theorem extension_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (m : ℕ)
    (hK : ‖low A hN P χ (P.s+3) m‖<1) (g : TerminalSpace A P) :
    highProjection A P (extension A hN P χ m g)=(g:Space) := by
  have hg : highProjection A P (g:Space)=(g:Space) :=
    (AsymptoticRegionL2.mem_space _ _ _ _).mp g.property
  rw [extension,add_apply,map_add,lowSolution_terminal_zero A hN P χ m hK g,add_zero]
  exact hg

theorem extension_norm_ge (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (m : ℕ)
    (hK : ‖low A hN P χ (P.s+3) m‖<1) (g : TerminalSpace A P) :
    ‖g‖≤‖extension A hN P χ m g‖ := by
  calc
    ‖g‖=‖highProjection A P (extension A hN P χ m g)‖ := by
      rw [extension_terminal A hN P χ m hK g]
      rfl
    _ ≤ ‖highProjection A P‖*‖extension A hN P χ m g‖ := (highProjection A P).le_opNorm _
    _ ≤ ‖extension A hN P χ m g‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (highProjection_norm_le A P) (norm_nonneg _)

theorem terminal_inclusion_norm_le (P : Parameters A) : ‖(TerminalSpace A P).subtypeL‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simp

/-- A bound independent of the holomorphic weight and of the sector,
once the common contraction exponent has been chosen. -/
theorem extension_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q, q∣Q → ‖χ q‖=1) (m : ℕ)
    (hK : ‖low A hN P χ (P.s+3) m‖<1/2) :
    ‖extension A hN P χ m‖≤1+2*terminalConstant A P := by
  have hK1 : ‖low A hN P χ (P.s+3) m‖<1 := lt_trans hK (by norm_num)
  have hB := terminal_norm_le A hN P χ hχ (by omega : 2≤P.s+3) m
  have hC : 0≤terminalConstant A P := (norm_nonneg _).trans hB
  have hb : ‖(terminal A hN P χ (by omega : 2≤P.s+3) m).comp (TerminalSpace A P).subtypeL‖≤
      terminalConstant A P := by
    apply (opNorm_comp_le _ _).trans
    simpa only [mul_one] using mul_le_mul hB (terminal_inclusion_norm_le A P)
      (norm_nonneg (TerminalSpace A P).subtypeL) hC
  have hlo := AsymptoticReconstruction.low_norm_le
    (low A hN P χ (P.s+3) m)
    ((terminal A hN P χ (by omega : 2≤P.s+3) m).comp (TerminalSpace A P).subtypeL) hK1
  have hden : 0<1-‖low A hN P χ (P.s+3) m‖ := by linarith
  have hfrac : ‖(terminal A hN P χ (by omega : 2≤P.s+3) m).comp (TerminalSpace A P).subtypeL‖/
      (1-‖low A hN P χ (P.s+3) m‖)≤2*terminalConstant A P := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact (norm_add_le _ _).trans
    (add_le_add (terminal_inclusion_norm_le A P) (hlo.trans hfrac))

/-- No new boundary condition is introduced: every L² solution of the
literal weighted reconstruction equation is the extension of its own
terminal data. Substitution of the analytic FE remains a separate step. -/
theorem extension_unique (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (m : ℕ)
    (hK : ‖low A hN P χ (P.s+3) m‖<1) (u : Space)
    (hu : u=highProjection A P u+low A hN P χ (P.s+3) m u+
      terminal A hN P χ (by omega : 2≤P.s+3) m (highProjection A P u)) :
    extension A hN P χ m
      (AsymptoticRegionL2.restrict volume (highStrip P.ε) (highStrip_measurable P.ε) u)=u := by
  let g : TerminalSpace A P :=
    AsymptoticRegionL2.restrict volume (highStrip P.ε) (highStrip_measurable P.ε) u
  have hg : (g:Space)=highProjection A P u := rfl
  have hv : u-highProjection A P u=
      low A hN P χ (P.s+3) m (u-highProjection A P u)+
        terminal A hN P χ (by omega : 2≤P.s+3) m (g:Space) := by
    rw [map_sub,low_high_zero A hN P χ (by omega : 1≤P.s+3),sub_zero,hg]
    apply sub_eq_iff_eq_add.mpr
    calc
      u=highProjection A P u+low A hN P χ (P.s+3) m u+
        terminal A hN P χ (by omega : 2≤P.s+3) m (highProjection A P u) := hu
      _ = _ := by abel
  have he : u-highProjection A P u=lowSolution A hN P χ m g :=
    AsymptoticReconstruction.low_unique _ _ hK hv
  change (g:Space)+lowSolution A hN P χ m g=u
  rw [← he,hg]
  abel

/-- Existence of one common auxiliary exponent and an actual bounded
terminal extension for all weights and sectors of the certificate. -/
theorem uniform_extension (hN : 0<N) (P : Parameters A) :
    ∃ P' : Parameters A, P'.ε=P.ε ∧ P'.ρ=P.ρ ∧ P.s≤P'.s ∧
      ∀ χ : ℕ → ℂ, (∀ q, q∣Q → ‖χ q‖=1) → ∀ m : ℕ,
        ‖extension A hN P' χ m‖≤1+2*terminalConstant A P' ∧
          ∀ g : TerminalSpace A P', highProjection A P' (extension A hN P' χ m g)=(g:Space) ∧
            ‖g‖≤‖extension A hN P' χ m g‖ := by
  obtain ⟨P',hε,hρ,hs,hK⟩ := contraction_parameters A hN P
  refine ⟨P',hε,hρ,hs,?_⟩
  intro χ hχ m
  have hk := hK χ hχ m
  have hk1 : ‖low A hN P' χ (P'.s+3) m‖<1 := lt_trans hk (by norm_num)
  exact ⟨extension_norm_le A hN P' χ hχ m hk,
    fun g => ⟨extension_terminal A hN P' χ m hk1 g,extension_norm_ge A hN P' χ m hk1 g⟩⟩

#print axioms extension_terminal
#print axioms extension_norm_ge
#print axioms extension_norm_le
#print axioms extension_unique
#print axioms uniform_extension

end AsymptoticGeometricReconstruction
