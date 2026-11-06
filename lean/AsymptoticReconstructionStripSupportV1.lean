module

public import AsymptoticRegularIncludedReconstructionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularCertificate

open UpperHalfPlane ContinuousLinearMap AsymptoticCertificateBranches
open FinitenessCertificate FinitenessGlobalHeight
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCertificateOperators (lowCell lowStrip highStrip)
open AsymptoticMassTransport (strip)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem lowPart_zero_off_strip (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 1≤t)
    (v : Index A) (z : ℍ) (f : Space) (g : AsymptoticRationalGroup.Group) (hg : g • z∉strip) :
    lowPart A hN P t v z f g=0 := by
  apply AsymptoticRegularFoldedLow.operator_zero_off_source (levelQ_pos A hN v)
    (inputShiftQ A v) (outputShiftQ A v) (lowCell A P.ε v) (lowStrip P.ε)
    P.rho_pos.le (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v) (fun _ hz => hz.1) ht z f g
  exact fun hv => hg (cell_subset_strip A v hv.1)

theorem terminalPart_zero_off_strip (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (v : Index A) (z : ℍ) (f : Space) (g : AsymptoticRationalGroup.Group) (hg : g • z∉strip) :
    terminalPart A hN P ht v z f g=0 := by
  apply AsymptoticRegularFoldedTerminal.operator_zero_off_source (levelQ_pos A hN v)
    (inputShiftQ A v) (outputShiftQ A v) (lowCell A P.ε v) (highStrip P.ε)
    P.epsilon_pos (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht z f g
  exact fun hv => hg (cell_subset_strip A v hv.1)

theorem low_zero_off_strip (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) {t : ℕ} (ht : 1≤t)
    (z : ℍ) (f : Space) (g : AsymptoticRationalGroup.Group) (hg : g • z∉strip) :
    low A hN P χ t z f g=0 := by
  simp only [low,_root_.sum_apply,_root_.smul_apply,lp.coeFn_sum,Finset.sum_apply,
    lp.coeFn_smul,Pi.smul_apply,lowPart_zero_off_strip A hN P ht _ z f g hg,
    smul_zero,Finset.sum_const_zero]

theorem terminal_zero_off_strip (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) {t : ℕ} (ht : 2≤t)
    (z : ℍ) (f : Space) (g : AsymptoticRationalGroup.Group) (hg : g • z∉strip) :
    terminal A hN P χ ht z f g=0 := by
  simp only [terminal,_root_.sum_apply,_root_.smul_apply,lp.coeFn_sum,Finset.sum_apply,
    lp.coeFn_smul,Pi.smul_apply,terminalPart_zero_off_strip A hN P ht _ z f g hg,
    smul_zero,Finset.sum_const_zero]

#print axioms lowPart_zero_off_strip
#print axioms terminalPart_zero_off_strip
#print axioms low_zero_off_strip
#print axioms terminal_zero_off_strip

end AsymptoticRegularCertificate

namespace AsymptoticRegularReconstruction

open UpperHalfPlane ContinuousLinearMap AsymptoticRegularCertificate
open FinitenessCertificate FinitenessGlobalHeight
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCertificateOperators (highStrip)
open AsymptoticMassTransport (strip)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem extension_zero_off_strip (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (f : TerminalSpace A P z)
    (g : AsymptoticRationalGroup.Group) (hg : g • z∉strip) :
    extension A hN P χ z f g=0 := by
  have hf : (f:Space) g=0 := by
    have he := (AsymptoticOrbitRegion.mem_space _ _ _).mp f.property
    have hh := congrArg (fun v : Space => v g) he
    have hn : g • z∉highStrip P.ε := fun h => hg h.1
    simpa only [AsymptoticOrbitDiagonal.corner_apply,ite_eq_right hn] using hh.symm
  have hl : lowSolution A hN P χ z f g=0 := by
    have he := congrArg (fun v : Space => v g) (lowSolution_equation A hN P χ z hK f)
    simpa only [lp.coeFn_add,Pi.add_apply,
      low_zero_off_strip A hN P χ (t:=P.s+3) (by omega) z _ g hg,
      terminal_zero_off_strip A hN P χ (t:=P.s+3) (by omega) z _ g hg,add_zero] using he
  simp only [extension,add_apply,lp.coeFn_add,Pi.add_apply,Submodule.subtypeL_apply,hf,hl,add_zero]

theorem includedExtension_zero_off_strip (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (z : ℍ)
    (hK : ‖low A hN P χ (P.s+3) z‖<1) (f : TerminalSpace A P z)
    (g : AsymptoticRationalGroup.Group) (hg : g • z∉strip) :
    includedExtension A hN P χ z f g=0 := by
  rw [includedExtension,comp_apply,AsymptoticRegularInclusion.inclusion_apply,
    extension_zero_off_strip A hN P χ z hK f g hg,mul_zero]

#print axioms extension_zero_off_strip
#print axioms includedExtension_zero_off_strip

end AsymptoticRegularReconstruction
