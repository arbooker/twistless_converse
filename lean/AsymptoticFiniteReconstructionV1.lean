module

public import AsymptoticFiniteNeumannV1
public import AsymptoticRegularIncludedReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticGeometricReconstruction

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight
open AsymptoticCertificateOperators AsymptoticHyperbolicSlash

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def finiteExtension (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (m n : ℕ) :
    TerminalSpace A P →L[ℂ] Space :=
  (TerminalSpace A P).subtypeL+AsymptoticReconstruction.finiteLow (low A hN P χ (P.s+3) m)
    ((terminal A hN P χ (by omega : 2≤P.s+3) m).comp (TerminalSpace A P).subtypeL) n

theorem forcing_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (m : ℕ) :
    ‖(terminal A hN P χ (by omega : 2≤P.s+3) m).comp (TerminalSpace A P).subtypeL‖≤terminalConstant A P := by
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left (terminal_inclusion_norm_le A P) (norm_nonneg _)).trans
  simpa only [mul_one] using terminal_norm_le A hN P χ hχ (by omega : 2≤P.s+3) m

/-- Every finite depth preserves the actual terminal data exactly. -/
theorem finiteExtension_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (m n : ℕ)
    (g : TerminalSpace A P) : highProjection A P (finiteExtension A hN P χ m n g)=(g:Space) := by
  have hz := AsymptoticReconstruction.finiteLow_terminal_zero (highProjection A P)
    (low A hN P χ (P.s+3) m)
    ((terminal A hN P χ (by omega : 2≤P.s+3) m).comp (TerminalSpace A P).subtypeL)
    (high_low_zero A hN P χ (by omega : 1≤P.s+3) m)
    (fun g => high_terminal_zero A hN P χ (by omega : 2≤P.s+3) m (g:Space)) n g
  have hg : highProjection A P (g:Space)=(g:Space) :=
    (AsymptoticRegionL2.mem_space _ _ _ _).mp g.property
  change highProjection A P ((g:Space)+_)=(g:Space)
  rw [map_add,hg]
  exact (congrArg (fun x : Space => (g:Space)+x) hz).trans (add_zero _)

theorem finiteExtension_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (m n : ℕ)
    (hK : ‖low A hN P χ (P.s+3) m‖≤1/2) :
    ‖finiteExtension A hN P χ m n‖≤1+2*terminalConstant A P := by
  have hn := AsymptoticReconstruction.finiteLow_norm_le _
    ((terminal A hN P χ (by omega : 2≤P.s+3) m).comp (TerminalSpace A P).subtypeL) hK (by norm_num) n
  have hb := forcing_norm_le A hN P χ hχ m
  have hs := terminal_inclusion_norm_le A P
  have ha := norm_add_le (TerminalSpace A P).subtypeL
    (AsymptoticReconstruction.finiteLow (low A hN P χ (P.s+3) m)
      ((terminal A hN P χ (by omega : 2≤P.s+3) m).comp (TerminalSpace A P).subtypeL) n)
  have hf : ‖(terminal A hN P χ (by omega : 2≤P.s+3) m).comp (TerminalSpace A P).subtypeL‖/
      (1-(1/2:ℝ))≤2*terminalConstant A P := by
    calc
      _ = 2*‖(terminal A hN P χ (by omega : 2≤P.s+3) m).comp (TerminalSpace A P).subtypeL‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num)
  exact ha.trans (add_le_add hs (hn.trans hf))

theorem finiteExtension_error (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (m n : ℕ)
    (hK : ‖low A hN P χ (P.s+3) m‖≤1/2) :
    ‖finiteExtension A hN P χ m n-extension A hN P χ m‖≤2*terminalConstant A P*(1/2:ℝ)^n := by
  have he : finiteExtension A hN P χ m n-extension A hN P χ m=
      AsymptoticReconstruction.finiteLow (low A hN P χ (P.s+3) m)
        ((terminal A hN P χ (by omega : 2≤P.s+3) m).comp (TerminalSpace A P).subtypeL) n-
      AsymptoticReconstruction.low (low A hN P χ (P.s+3) m)
        ((terminal A hN P χ (by omega : 2≤P.s+3) m).comp (TerminalSpace A P).subtypeL) := by
    unfold finiteExtension extension lowSolution
    abel
  rw [he]
  convert AsymptoticReconstruction.finiteLow_error _ _ hK (by norm_num)
    (forcing_norm_le A hN P χ hχ m) n using 1
  ring

#print axioms forcing_norm_le
#print axioms finiteExtension_terminal
#print axioms finiteExtension_norm_le
#print axioms finiteExtension_error

end AsymptoticGeometricReconstruction

namespace AsymptoticRegularReconstruction

open UpperHalfPlane ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight
open AsymptoticRegularCertificate
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCertificateOperators (terminalConstant)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def finiteFull (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (n : ℕ) (z : ℍ) : Space →L[ℂ] Space :=
  (1+AsymptoticReconstruction.finiteLow (low A hN P χ (P.s+3) z)
    (terminal A hN P χ (by omega : 2≤P.s+3) z) n).comp (highProjection A P z)

theorem finiteFull_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (n : ℕ) (z : ℍ) (f : Space) :
    highProjection A P z (finiteFull A hN P χ n z f)=highProjection A P z f := by
  have hz := AsymptoticReconstruction.finiteLow_terminal_zero (highProjection A P z)
    (low A hN P χ (P.s+3) z) (terminal A hN P χ (by omega : 2≤P.s+3) z)
    (high_low_zero A hN P χ (by omega : 1≤P.s+3) z)
    (high_terminal_zero A hN P χ (by omega : 2≤P.s+3) z) n (highProjection A P z f)
  change highProjection A P z (highProjection A P z f+_)=_
  rw [map_add]
  apply (congrArg (fun x : Space => highProjection A P z (highProjection A P z f)+x) hz).trans
  rw [add_zero]
  exact congrArg (fun T : Space →L[ℂ] Space => T f)
    (AsymptoticOrbitDiagonal.corner_idempotent _ z)

theorem finiteFull_error (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (n : ℕ) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖≤1/2) :
    ‖finiteFull A hN P χ n z-full A hN P χ z‖≤2*terminalConstant A P*(1/2:ℝ)^n := by
  have he : finiteFull A hN P χ n z-full A hN P χ z=
      (AsymptoticReconstruction.finiteLow (low A hN P χ (P.s+3) z)
        (terminal A hN P χ (by omega : 2≤P.s+3) z) n-
      AsymptoticReconstruction.low (low A hN P χ (P.s+3) z)
        (terminal A hN P χ (by omega : 2≤P.s+3) z)).comp (highProjection A P z) := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [finiteFull,full,comp_apply,sub_apply,add_apply]
    abel
  rw [he]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left (highProjection_norm_le A P z) (norm_nonneg _)).trans
  rw [mul_one]
  convert AsymptoticReconstruction.finiteLow_error _ _ hK (by norm_num)
    (terminal_norm_le A hN P χ hχ (by omega : 2≤P.s+3) z) n using 1
  ring

#print axioms finiteFull_terminal
#print axioms finiteFull_error

end AsymptoticRegularReconstruction
