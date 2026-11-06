module

public import AsymptoticRegularSupportV1
public import AsymptoticNeumannReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularReconstruction

open UpperHalfPlane Set ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight
open AsymptoticRegularFoldedLow (Space)
open AsymptoticRegularCertificate
open AsymptoticCertificateOperators (highStrip terminalConstant)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Actual terminal data, extended by zero in the counting Hilbert space. -/
noncomputable abbrev TerminalSpace (P : Parameters A) (z : ℍ) :=
  AsymptoticOrbitRegion.Space (G:=AsymptoticRationalGroup.Group) (highStrip P.ε) z

noncomputable def lowSolution (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ) :
    TerminalSpace A P z →L[ℂ] Space :=
  AsymptoticReconstruction.low (low A hN P χ (P.s+3) z)
    ((terminal A hN P χ (by omega : 2≤P.s+3) z).comp (TerminalSpace A P z).subtypeL)

/-- The geometric extension is the unchanged terminal section plus the
Neumann solution of the actual, fully folded low-height equation. -/
noncomputable def extension (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ) :
    TerminalSpace A P z →L[ℂ] Space :=
  (TerminalSpace A P z).subtypeL+lowSolution A hN P χ z

theorem lowSolution_equation (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (g : TerminalSpace A P z) :
    lowSolution A hN P χ z g=
      low A hN P χ (P.s+3) z (lowSolution A hN P χ z g)+
        terminal A hN P χ (by omega : 2≤P.s+3) z (g:Space) :=
  AsymptoticReconstruction.low_equation _ _ hK g

theorem lowSolution_terminal_zero (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (g : TerminalSpace A P z) :
    highProjection A P z (lowSolution A hN P χ z g)=0 := by
  rw [lowSolution_equation A hN P χ z hK g,map_add,
    high_low_zero A hN P χ (by omega : 1≤P.s+3),high_terminal_zero,add_zero]

/-- The terminal identity is proved for the actual counting terminal
projection, rather than assumed as a lower-bound hypothesis. -/
theorem extension_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (g : TerminalSpace A P z) :
    highProjection A P z (extension A hN P χ z g)=(g:Space) := by
  have hg : highProjection A P z (g:Space)=(g:Space) :=
    (AsymptoticOrbitRegion.mem_space _ _ _).mp g.property
  rw [extension,add_apply,map_add,lowSolution_terminal_zero A hN P χ z hK g,add_zero]
  exact hg

theorem extension_norm_ge (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (g : TerminalSpace A P z) :
    ‖g‖≤‖extension A hN P χ z g‖ := by
  calc
    ‖g‖=‖highProjection A P z (extension A hN P χ z g)‖ := by
      rw [extension_terminal A hN P χ z hK g]
      rfl
    _ ≤ ‖highProjection A P z‖*‖extension A hN P χ z g‖ := (highProjection A P z).le_opNorm _
    _ ≤ ‖extension A hN P χ z g‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (highProjection_norm_le A P z) (norm_nonneg _)

theorem terminal_inclusion_norm_le (P : Parameters A) (z : ℍ) : ‖(TerminalSpace A P z).subtypeL‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simp

/-- A bound independent of the holomorphic weight and of the sector,
once the common contraction exponent has been chosen. -/
theorem extension_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q, q∣Q → ‖χ q‖=1) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1/2) :
    ‖extension A hN P χ z‖≤1+2*terminalConstant A P := by
  have hK1 : ‖low A hN P χ (P.s+3) z‖<1 := lt_trans hK (by norm_num)
  have hB := terminal_norm_le A hN P χ hχ (by omega : 2≤P.s+3) z
  have hC : 0≤terminalConstant A P := (norm_nonneg _).trans hB
  have hb : ‖(terminal A hN P χ (by omega : 2≤P.s+3) z).comp (TerminalSpace A P z).subtypeL‖≤
      terminalConstant A P := by
    apply (opNorm_comp_le _ _).trans
    simpa only [mul_one] using mul_le_mul hB (terminal_inclusion_norm_le A P z)
      (norm_nonneg (TerminalSpace A P z).subtypeL) hC
  have hlo := AsymptoticReconstruction.low_norm_le
    (low A hN P χ (P.s+3) z)
    ((terminal A hN P χ (by omega : 2≤P.s+3) z).comp (TerminalSpace A P z).subtypeL) hK1
  have hden : 0<1-‖low A hN P χ (P.s+3) z‖ := by linarith
  have hfrac : ‖(terminal A hN P χ (by omega : 2≤P.s+3) z).comp (TerminalSpace A P z).subtypeL‖/
      (1-‖low A hN P χ (P.s+3) z‖)≤2*terminalConstant A P := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact (norm_add_le _ _).trans
    (add_le_add (terminal_inclusion_norm_le A P z) (hlo.trans hfrac))

/-- No new boundary condition is introduced: every L² solution of the
literal weighted reconstruction equation is the extension of its own
terminal data. Substitution of the known branch laws remains a separate step. -/
theorem extension_unique (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (u : Space)
    (hu : u=highProjection A P z u+low A hN P χ (P.s+3) z u+
      terminal A hN P χ (by omega : 2≤P.s+3) z (highProjection A P z u)) :
    extension A hN P χ z
      (AsymptoticOrbitRegion.restrict (highStrip P.ε) z u)=u := by
  let g : TerminalSpace A P z :=
    AsymptoticOrbitRegion.restrict (highStrip P.ε) z u
  have hg : (g:Space)=highProjection A P z u := rfl
  have hv : u-highProjection A P z u=
      low A hN P χ (P.s+3) z (u-highProjection A P z u)+
        terminal A hN P χ (by omega : 2≤P.s+3) z (g:Space) := by
    rw [map_sub,low_high_zero A hN P χ (by omega : 1≤P.s+3),sub_zero,hg]
    apply sub_eq_iff_eq_add.mpr
    calc
      u=highProjection A P z u+low A hN P χ (P.s+3) z u+
        terminal A hN P χ (by omega : 2≤P.s+3) z (highProjection A P z u) := hu
      _ = _ := by abel
  have he : u-highProjection A P z u=lowSolution A hN P χ z g :=
    AsymptoticReconstruction.low_unique _ _ hK hv
  change (g:Space)+lowSolution A hN P χ z g=u
  rw [← he,hg]
  abel

/-- Existence of one common auxiliary exponent and an actual bounded
terminal extension for all orbit roots and sectors of the certificate. -/
theorem uniform_extension (hN : 0<N) (P : Parameters A) :
    ∃ P' : Parameters A, P'.ε=P.ε ∧ P'.ρ=P.ρ ∧ P.s≤P'.s ∧
      ∀ χ : ℕ → ℂ, (∀ q, q∣Q → ‖χ q‖=1) → ∀ z : ℍ,
        ‖extension A hN P' χ z‖≤1+2*terminalConstant A P' ∧
          ∀ g : TerminalSpace A P' z, highProjection A P' z (extension A hN P' χ z g)=(g:Space) ∧
            ‖g‖≤‖extension A hN P' χ z g‖ := by
  obtain ⟨P',hε,hρ,hs,hK⟩ := common_contraction_parameters A hN P
  refine ⟨P',hε,hρ,hs,?_⟩
  intro χ hχ z
  have hk := (hK χ hχ).1 z
  have hk1 : ‖low A hN P' χ (P'.s+3) z‖<1 := lt_trans hk (by norm_num)
  exact ⟨extension_norm_le A hN P' χ hχ z hk,
    fun g => ⟨extension_terminal A hN P' χ z hk1 g,extension_norm_ge A hN P' χ z hk1 g⟩⟩

#print axioms extension_terminal
#print axioms extension_norm_ge
#print axioms extension_norm_le
#print axioms extension_unique
#print axioms uniform_extension

end AsymptoticRegularReconstruction
