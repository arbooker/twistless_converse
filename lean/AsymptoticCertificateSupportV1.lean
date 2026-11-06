module

public import AsymptoticCertificateOperatorsV1
public import AsymptoticFoldedSupportV1
public import AsymptoticRegionL2V1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCertificateOperators

open MeasureTheory UpperHalfPlane Set Filter ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight AsymptoticCertificateBranches
open AsymptoticHyperbolicSlash

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def highProjection (P : Parameters A) : Space →L[ℂ] Space :=
  AsymptoticRegionL2.projection volume (highStrip P.ε) (highStrip_measurable P.ε)

theorem highProjection_norm_le (P : Parameters A) : ‖highProjection A P‖≤1 :=
  AsymptoticRegionL2.projection_norm_le _ _ _

theorem high_lowPart_zero (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 1≤t)
    (m : ℕ) (v : Index A) (f : Space) : highProjection A P (lowPart A hN P t m v f)=0 := by
  apply (AsymptoticRegionL2.projection_eq_zero_iff _ _ _ _).mpr
  have hh : ∀ᵐ z ∂volume, z∉lowCell A P.ε v → lowPart A hN P t m v f z=0 :=
    AsymptoticFoldedLow.operator_zero_off_source (level_pos A hN v) (inputShift A v) (outputShift A v)
      (lowCell_measurable A P.ε v) (lowStrip_measurable P.ε) P.rho_pos.le
      (outputShift_nonneg A v) (outputShift_lt_one A v).le (fun _ hz => hz.1) ht m f
  filter_upwards [hh] with z hz hhigh
  apply hz
  intro hlow
  exact (not_lt_of_ge (show P.ε≤z.im from hhigh.2)) (show z.im<P.ε from hlow.2)

theorem high_terminalPart_zero (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 2≤t)
    (m : ℕ) (v : Index A) (f : Space) : highProjection A P (terminalPart A hN P ht m v f)=0 := by
  apply (AsymptoticRegionL2.projection_eq_zero_iff _ _ _ _).mpr
  have hh : ∀ᵐ z ∂volume, z∉lowCell A P.ε v → terminalPart A hN P ht m v f z=0 :=
    AsymptoticFoldedTerminal.operator_zero_off_source (level_pos A hN v) (inputShift A v) (outputShift A v)
      (lowCell_measurable A P.ε v) (highStrip_measurable P.ε) P.epsilon_pos
      (outputShift_nonneg A v) (outputShift_lt_one A v).le
      (fun z hz => show z.im≤P.ε from (show z.im<P.ε from hz.2).le) (fun _ hz => hz.1) ht m f
  filter_upwards [hh] with z hz hhigh
  apply hz
  intro hlow
  exact (not_lt_of_ge (show P.ε≤z.im from hhigh.2)) (show z.im<P.ε from hlow.2)

theorem lowPart_high_zero (hN : 0<N) (P : Parameters A) {t : ℕ} (ht : 1≤t)
    (m : ℕ) (v : Index A) (f : Space) : lowPart A hN P t m v (highProjection A P f)=0 := by
  apply AsymptoticFoldedLow.operator_eq_zero_of_target (level_pos A hN v) (inputShift A v) (outputShift A v)
    (lowCell_measurable A P.ε v) (lowStrip_measurable P.ε) P.rho_pos.le
    (outputShift_nonneg A v) (outputShift_lt_one A v).le (fun _ hz => hz.1) ht m
  filter_upwards [AsymptoticRegionL2.projection_coeFn volume (highStrip P.ε)
    (highStrip_measurable P.ε) f] with z hz hlow
  have hnot : z∉highStrip P.ε := fun hh => (not_lt_of_ge (show P.ε≤z.im from hh.2)) (show z.im<P.ε from hlow.2)
  simpa [highProjection,hnot] using hz

theorem high_low_zero (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 1≤t) (m : ℕ) (f : Space) : highProjection A P (low A hN P χ t m f)=0 := by
  simp only [low,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    high_lowPart_zero A hN P ht,smul_zero,Finset.sum_const_zero]

theorem high_terminal_zero (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 2≤t) (m : ℕ) (f : Space) : highProjection A P (terminal A hN P χ ht m f)=0 := by
  simp only [terminal,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,
    high_terminalPart_zero A hN P ht,smul_zero,Finset.sum_const_zero]

theorem low_high_zero (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    {t : ℕ} (ht : 1≤t) (m : ℕ) (f : Space) : low A hN P χ t m (highProjection A P f)=0 := by
  simp only [low,_root_.sum_apply,_root_.smul_apply,
    lowPart_high_zero A hN P ht,smul_zero,Finset.sum_const_zero]

#print axioms high_low_zero
#print axioms high_terminal_zero
#print axioms low_high_zero

end AsymptoticCertificateOperators
