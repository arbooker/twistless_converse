module

public import QuantitativeMaassOrbitCoreMeasureV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand QuantitativeSpectralObservability
open scoped Topology ENNReal MatrixGroups

namespace QuantitativeMaass

/-- Quotient energy outside the orbit-saturated compact core is bounded
by the actual finite cusp cover, with no fundamental-domain assumption
on the quotient density. -/
theorem quotient_orbitCore_compl_cusps (N : ℕ) [NeZero N] (hN : 0<N) (H : ℝ)
    (F : ℍ→ℝ≥0∞) (hF : Measurable F)
    (hinv : ∀ g : gamma N,∀ z,F (g.val•z)=F z) :
    (∫⁻ z in (orbitCore N (wideCompactCover N H))ᶜ,F z ∂quotientMeasure N)≤
      ∑' q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N,∑' b : Bool,
        ∫⁻ z in cuspTailSet N H,F (cuspAction (globalCuspChart N q b) z) := by
  let O := orbitCore N (wideCompactCover N H)
  have hO : MeasurableSet O := orbitCore_measurable N _ (wideCompactCover_compact N hN H).measurableSet
  let G := Oᶜ.indicator F
  have hG : Measurable G := hF.indicator hO.compl
  have hGi : ∀ g : gamma N,∀ z,G (g.val•z)=G z := by
    intro g z
    have hmem : g.val•z∈Oᶜ ↔ z∈Oᶜ := not_congr (orbitCore_mem_smul N _ g z)
    dsimp only [G]
    by_cases hz : z∈Oᶜ
    · rw [Set.indicator_of_mem (hmem.mpr hz),Set.indicator_of_mem hz,hinv]
    · rw [Set.indicator_of_notMem (fun h => hz (hmem.mp h)),Set.indicator_of_notMem hz]
  have hc := quotient_mass_le_core_cusps N hN H G hG hGi
  have hcore : (∫⁻ z in wideCompactCover N H,G z)=0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem (wideCompactCover_compact N hN H).measurableSet] with z hz
    exact Set.indicator_of_notMem (not_not_intro (orbitCore_contains N _ hz)) F
  rw [hcore,zero_add] at hc
  have heq : (∫⁻ z,G z ∂quotientMeasure N)=∫⁻ z in Oᶜ,F z ∂quotientMeasure N :=
    lintegral_indicator hO.compl F
  rw [heq] at hc
  apply hc.trans
  apply ENNReal.tsum_le_tsum
  intro q
  apply ENNReal.tsum_le_tsum
  intro b
  apply lintegral_mono
  intro z
  change G (cuspAction (globalCuspChart N q b) z)≤F (cuspAction (globalCuspChart N q b) z)
  by_cases hz : cuspAction (globalCuspChart N q b) z∈Oᶜ
  · exact (Set.indicator_of_mem hz F).le
  · rw [show G (cuspAction (globalCuspChart N q b) z)=0 from Set.indicator_of_notMem hz F]
    exact bot_le

#print axioms quotient_orbitCore_compl_cusps

end QuantitativeMaass
