module

public import QuantitativeArithmeticMaassCutoffDifferenceV1
public import QuantitativeArithmeticMaassColumnRegionEnergyV1
public import QuantitativeMaassCylinderColumnDomainV1
public import QuantitativeMaassAbelContinuityV1
public import QuantitativeMaassRadialKernelSymmetryV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped ENNReal ContDiff

namespace QuantitativeMaass

/-- Local restriction of the actual completed cylinder column has its
literal smooth kernel representative, also for hyperbolic area measure. -/
theorem cylinderAbelColumn_local_representative (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F ⊆ Iic (Real.cosh R))
    (K : Set ℍ) (hK : IsCompact K) (z : ℍ) :
    (quotientRestriction 0 K hK hK.measurableSet
      (cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z)) : ℍ → ℂ)
      =ᵐ[volume.restrict K] radialPoincareKernel 0 (abelProfile F) z := by
  rw [cylinderAbelColumn_eq_physicalRadialSeed]
  exact quotientRestriction_representative_ae 0 K hK hK.measurableSet
    ⟨_, poincareSeed_representative 0 _⟩

/-- Kernel symmetry and Tonelli turn source mass in a collar into column
energy integrated over that collar. The identity is nonnegative and needs
no unjustified global trace-class assumption on the cylinder. -/
theorem cylinderAbelColumn_region_swap (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F ⊆ Iic (Real.cosh R))
    (ν : Measure ℍ) [SFinite ν] :
    (∫⁻ z, ∫⁻ x, ENNReal.ofReal (‖radialPoincareKernel 0 (abelProfile F) z x‖^2)
      ∂ν ∂quotientMeasure 0) =
    ∫⁻ x, ENNReal.ofReal (‖cylinderAbelColumn F hF R hR hs x‖^2) ∂ν := by
  rw [lintegral_lintegral_swap
    ((oneSidedAbelKernel_joint_continuous 0 F hF R hR hs).norm.pow 2).measurable.ennreal_ofReal.aemeasurable]
  apply lintegral_congr
  intro x
  rw [complexLp_norm_square_lintegral]
  apply lintegral_congr_ae
  filter_upwards [cylinderAbelColumn_coeFn F hF R hR hs x] with z hz
  rw [hz, radialPoincareKernel_symm 0 (abelProfile F) z x]

/-- Integrated sharp/smooth transfer error for actual cylinder columns.
Its only geometric cost is target overlap times source energy in the collar. -/
theorem cylinderAbelColumn_transfer_collar_energy (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F ⊆ Iic (Real.cosh R))
    (K : Set ℍ) (hK : IsCompact K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N), (∀ γ ∈ S, γ • z ∈ K) → S.card ≤ m)
    (a b : ℍ → ℂ)
    (ha : AEStronglyMeasurable a (volume.restrict K))
    (hb : AEStronglyMeasurable b (volume.restrict K)) (A B C : ℝ)
    (haB : ∀ᵐ x ∂volume.restrict K, ‖a x‖ ≤ A)
    (hbB : ∀ᵐ x ∂volume.restrict K, ‖b x‖ ≤ B)
    (Ω : Set ℍ) (hΩ : MeasurableSet Ω)
    (hchange : ∀ᵐ x ∂volume.restrict K, ‖a x-b x‖ ≤ C ∧ (x ∉ Ω → a x=b x)) :
    (∫⁻ z, ENNReal.ofReal (‖
      boundedCrossQuotientLocalization N 0 K hK a ha haB
        (cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z))-
      boundedCrossQuotientLocalization N 0 K hK b hb hbB
        (cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z))‖^2)
      ∂quotientMeasure 0) ≤
    ENNReal.ofReal ((m : ℝ)*C^2)*
      ∫⁻ x in Ω, ENNReal.ofReal (‖cylinderAbelColumn F hF R hR hs x‖^2)
        ∂volume.restrict K := by
  let ν := (volume.restrict K).restrict Ω
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal ((m : ℝ)*C^2)*
        ∫⁻ x, ENNReal.ofReal (‖radialPoincareKernel 0 (abelProfile F) z x‖^2) ∂ν
        ∂quotientMeasure 0 := by
      apply lintegral_mono
      intro z
      let f := cylinderAutomorphic (cylinderAbelColumn F hF R hR hs z)
      let u := quotientRestriction 0 K hK hK.measurableSet f
      have hi := ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp
        (Lp.memLp u)).restrict (s := Ω)
      have heq : ENNReal.ofReal (∫ x in Ω, ‖u x‖^2 ∂volume.restrict K) =
          ∫⁻ x, ENNReal.ofReal (‖radialPoincareKernel 0 (abelProfile F) z x‖^2) ∂ν := by
        rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))]
        apply lintegral_congr_ae
        filter_upwards [(cylinderAbelColumn_local_representative F hF R hR hs K hK z).filter_mono
          (ae_mono Measure.restrict_le_self)] with x hx
        rw [hx]
      have hbnd := ENNReal.ofReal_le_ofReal
        (boundedCrossQuotientLocalization_difference_collar N 0 K hK m hm a b ha hb
          A B C haB hbB Ω hΩ hchange f)
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (m : ℝ)*C^2), heq] at hbnd
      exact hbnd
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        cylinderAbelColumn_region_swap F hF R hR hs ν]

#print axioms cylinderAbelColumn_local_representative
#print axioms cylinderAbelColumn_region_swap
#print axioms cylinderAbelColumn_transfer_collar_energy

end QuantitativeMaass
