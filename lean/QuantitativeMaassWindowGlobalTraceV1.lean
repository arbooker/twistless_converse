module

public import QuantitativeMaassQuotientExcessV1
public import QuantitativeMaassWindowCuspGrowthV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand QuantitativeSpectralObservability
open scoped Topology InnerProductSpace MatrixGroups ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

variable {ι : Type*} (N : ℕ) [NeZero N] (K : SchwartzMap ℝ ℝ)
  (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
  (R : ℝ) (hR : 0<R) (a b : ℝ) (v : ι → AutomorphicSpace N) (S : Finset ι)

/-- Literal finite packet energy in the genuine quotient measure. -/
theorem window_finite_packet_energy_integral :
    (∑ i∈S,ENNReal.ofReal (‖windowWavePacket N K hc R hR a b (v i)‖^2))=
      ∫⁻ z,ENNReal.ofReal (∑ i∈S,‖inner ℂ (windowAbelColumn N K he hc R hR a b z) (v i)‖^2) ∂quotientMeasure N := by
  classical
  have hi (i : ι) : ENNReal.ofReal (‖windowWavePacket N K hc R hR a b (v i)‖^2)=
      ∫⁻ z,ENNReal.ofReal (‖inner ℂ (windowAbelColumn N K he hc R hR a b z) (v i)‖^2) ∂quotientMeasure N := by
    change ENNReal.ofReal (‖(windowWavePacket N K hc R hR a b (v i)).val‖^2)=_
    rw [lp_norm_square_lintegral]
    apply lintegral_congr_ae
    filter_upwards [windowAbelColumn_packet_coeFn N K he hc R hR a b (v i)] with z hz
    rw [hz]
  simp_rw [hi]
  have hm (i : ι) : Measurable (fun z => ENNReal.ofReal (‖inner ℂ (windowAbelColumn N K he hc R hR a b z) (v i)‖^2)) :=
    (((windowAbelColumn_continuous N K he hc R hR a b).inner continuous_const).norm.pow 2).measurable.ennreal_ofReal
  rw [←lintegral_finsetSum S (fun i _ => hm i)]
  apply lintegral_congr
  intro z
  exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)).symm

/-- The same finite energy identity on the actual infinite cusp restriction. -/
theorem window_finite_tail_energy_integral (A : SL(2,ℤ)) (Y : ℝ) (hY : 2≤Y) :
    (∑ i∈S,ENNReal.ofReal (‖cuspTailRestriction N N A Y hY
      (windowWavePacket N K hc R hR a b (v i))‖^2))=
      ∫⁻ z in cuspTailSet N Y,ENNReal.ofReal
        (∑ i∈S,‖inner ℂ (windowAbelColumn N K he hc R hR a b (cuspAction A z)) (v i)‖^2) := by
  classical
  have hi (i : ι) : ENNReal.ofReal (‖cuspTailRestriction N N A Y hY
      (windowWavePacket N K hc R hR a b (v i))‖^2)=
      ∫⁻ z in cuspTailSet N Y,ENNReal.ofReal (‖inner ℂ (windowAbelColumn N K he hc R hR a b (cuspAction A z)) (v i)‖^2) := by
    rw [lp_norm_square_lintegral]
    apply lintegral_congr_ae
    filter_upwards [continuous_invariant_tail_restriction N N A Y hY (windowWavePacket N K hc R hR a b (v i)) _
      ((windowAbelColumn_continuous N K he hc R hR a b).inner continuous_const)
      (fun γ z => by rw [windowAbelColumn_invariant N K he hc R hR a b])
      (windowAbelColumn_packet_coeFn N K he hc R hR a b (v i))] with z hz
    rw [hz]
  simp_rw [hi]
  have hm (i : ι) : Measurable (fun z => ENNReal.ofReal
      (‖inner ℂ (windowAbelColumn N K he hc R hR a b (cuspAction A z)) (v i)‖^2)) :=
    ((((windowAbelColumn_continuous N K he hc R hR a b).comp (cuspAction_continuous A)).inner
      continuous_const).norm.pow 2).measurable.ennreal_ofReal
  rw [←lintegral_finsetSum S (fun i _ => hm i)]
  apply lintegral_congr
  intro z
  exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)).symm

include he in
/-- Sharp leading-volume bound on every finite orthonormal family. Only the
nonidentity excess is charged to the overlapping geometric core and cusp cover. -/
theorem window_finite_packet_sharp_cover (hN : 0<N) (hv : Orthonormal ℂ v)
    (Y : ℝ) (hY : 2≤Y) :
    (∑ i∈S,ENNReal.ofReal (‖windowWavePacket N K hc R hR a b (v i)‖^2))≤
      ENNReal.ofReal (windowIdentityContribution K hc R hR a b).re*quotientMeasure N univ+
        (∫⁻ z in wideCompactCover N Y,ENNReal.ofReal (‖windowGeometricRemainder N K hc R hR a b z‖))+
        ∑' q : SL(2,ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ∑' d : Bool,
          ∑ i∈S,ENNReal.ofReal (‖cuspTailRestriction N N (globalCuspChart N q d) Y hY
            (windowWavePacket N K hc R hR a b (v i))‖^2) := by
  classical
  let F := fun z => ∑ i∈S,‖inner ℂ (windowAbelColumn N K he hc R hR a b z) (v i)‖^2
  let I := (windowIdentityContribution K hc R hR a b).re
  have hI : 0≤I := windowIdentityContribution_re_nonneg K he hc R hR a b
  have hF : Continuous F := continuous_finsetSum S (fun i _ =>
    ((windowAbelColumn_continuous N K he hc R hR a b).inner continuous_const).norm.pow 2)
  have hinv : ∀ γ : gamma N,∀ z,F (γ.val•z)=F z := by
    intro γ z
    change (∑ i∈S,‖inner ℂ (windowAbelColumn N K he hc R hR a b (γ•z)) (v i)‖^2)=_
    rw [windowAbelColumn_invariant N K he hc R hR a b]
  have hh := quotient_positive_excess_cover N hN Y I hI F hF.measurable hinv
  rw [window_finite_packet_energy_integral N K he hc R hR a b v S]
  apply hh.trans
  apply add_le_add
  · apply add_le_add le_rfl
    apply lintegral_mono
    intro z
    exact ENNReal.ofReal_le_ofReal (window_finite_energy_excess_bound N K he hc R hR a b v hv S z)
  · apply ENNReal.tsum_le_tsum
    intro q
    apply ENNReal.tsum_le_tsum
    intro d
    rw [window_finite_tail_energy_integral N K he hc R hR a b v S (globalCuspChart N q d) Y hY]
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    apply max_le
    · exact sub_le_self _ hI
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

#print axioms window_finite_packet_energy_integral
#print axioms window_finite_tail_energy_integral
#print axioms window_finite_packet_sharp_cover

end QuantitativeMaass
