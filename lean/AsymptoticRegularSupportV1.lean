module

public import AsymptoticRegularCertificateV1
public import AsymptoticRegularFoldedSupportV1
public import AsymptoticOrbitRegionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularCertificate

open UpperHalfPlane Set ContinuousLinearMap AsymptoticCertificateBranches
open FinitenessCertificate FinitenessGlobalHeight
open AsymptoticCertificateOperators (lowCell lowStrip highStrip)
open AsymptoticRegularFoldedLow (Space)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def highProjection (P : Parameters A) (z : ℍ) : Space →L[ℂ] Space :=
  AsymptoticOrbitDiagonal.corner (highStrip P.ε) z

theorem highProjection_norm_le (P : Parameters A) (z : ℍ) : ‖highProjection A P z‖≤1 :=
  AsymptoticOrbitRegion.corner_norm_le _ _

theorem high_lowPart_zero (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 1≤t)
    (v : Index A) (z : ℍ) (f : Space) : highProjection A P z (lowPart A hN P t v z f)=0 := by
  apply (AsymptoticOrbitRegion.corner_eq_zero_iff _ _ _).mpr
  intro g hg
  apply AsymptoticRegularFoldedLow.operator_zero_off_source (levelQ_pos A hN v)
    (inputShiftQ A v) (outputShiftQ A v) (lowCell A P.ε v) (lowStrip P.ε)
    P.rho_pos.le (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v) (fun _ hz => hz.1) ht z f g
  intro hlow
  exact (not_lt_of_ge (show P.ε≤(g • z).im from hg.2)) (show (g • z).im<P.ε from hlow.2)

theorem high_terminalPart_zero (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (v : Index A) (z : ℍ) (f : Space) : highProjection A P z (terminalPart A hN P ht v z f)=0 := by
  apply (AsymptoticOrbitRegion.corner_eq_zero_iff _ _ _).mpr
  intro g hg
  apply AsymptoticRegularFoldedTerminal.operator_zero_off_source (levelQ_pos A hN v)
    (inputShiftQ A v) (outputShiftQ A v) (lowCell A P.ε v) (highStrip P.ε)
    P.epsilon_pos (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v)
    (fun _ hz => show _≤P.ε from (show _<P.ε from hz.2).le) (fun _ hz => hz.1) ht z f g
  intro hlow
  exact (not_lt_of_ge (show P.ε≤(g • z).im from hg.2)) (show (g • z).im<P.ε from hlow.2)

theorem lowPart_high_zero (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 1≤t)
    (v : Index A) (z : ℍ) (f : Space) : lowPart A hN P t v z (highProjection A P z f)=0 := by
  apply AsymptoticRegularFoldedLow.operator_eq_zero_of_target (levelQ_pos A hN v)
    (inputShiftQ A v) (outputShiftQ A v) (lowCell A P.ε v) (lowStrip P.ε)
    P.rho_pos.le (outputShiftQ_nonneg A v) (outputShiftQ_le_one A v) (fun _ hz => hz.1) ht z
  intro g hlow
  have hnot : g • z∉highStrip P.ε := fun hh =>
    (not_lt_of_ge (show P.ε≤(g • z).im from hh.2)) (show (g • z).im<P.ε from hlow.2)
  classical
  simp only [highProjection,AsymptoticOrbitDiagonal.corner_apply,ite_eq_right hnot]

theorem high_low_zero (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 1≤t) (z : ℍ) (f : Space) : highProjection A P z (low A hN P χ t z f)=0 := by
  simp only [low,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    high_lowPart_zero A hN P ht,smul_zero,Finset.sum_const_zero]

theorem high_terminal_zero (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (z : ℍ) (f : Space) : highProjection A P z (terminal A hN P χ ht z f)=0 := by
  simp only [terminal,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    high_terminalPart_zero A hN P ht,smul_zero,Finset.sum_const_zero]

theorem low_high_zero (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 1≤t) (z : ℍ) (f : Space) : low A hN P χ t z (highProjection A P z f)=0 := by
  simp only [low,_root_.sum_apply,_root_.smul_apply,
    lowPart_high_zero A hN P ht,smul_zero,Finset.sum_const_zero]

#print axioms high_low_zero
#print axioms high_terminal_zero
#print axioms low_high_zero

end AsymptoticRegularCertificate
