module

public import QuantitativeMaassInvariantLocalIntegralV1
public import QuantitativeArithmeticMaassGradientCoreV1
public import QuantitativeMaassPoincareNormBoundV1

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassGradient
open scoped ENNReal

namespace QuantitativeMaass
open MaassDifferential

/-- The mass plus summed gradient energy is invariant even though the
individual coordinate gradients need not be invariant. -/
theorem poincareEnergyDensity_invariant (N : ℕ) (u : SmoothUpperSeed)
    (g : gamma N) (z : ℍ) :
    poincareEnergyDensity N u (g • z) = poincareEnergyDensity N u z := by
  have hi : ∀ a : gamma N, ∀ w,
      upperFunction (congruencePoincareCartesian N u.toFun) (a • w) =
      upperFunction (congruencePoincareCartesian N u.toFun) w := by
    intro a w
    simp only [congruencePoincareCartesian_represents, poincareSum_invariant]
  have he := upperEnergy_poincare_right N
    (congruencePoincareCartesian_smooth N u.smooth u.compact) u.smooth u.compact hi
  simp only [poincareEnergyDensity, he, poincareSum_invariant]

/-- Explicit local gradient energy from the supplied orbit multiplicity.
No compact-dependent constant is chosen inside the estimate. -/
theorem seedGradient_local_lintegral_le (N : ℕ) (u : SmoothUpperSeed) (i : Bool)
    (K : Set ℍ) (hK : MeasurableSet K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m) :
    (∫⁻ z, ENNReal.ofReal (‖seedGradient N i u z‖^2) ∂volume.restrict K) ≤
      (m : ℝ≥0∞) * ENNReal.ofReal (‖poincareEnergySeed N u‖^2) := by
  have hmeas : Measurable (poincareEnergyDensity N u) := by
    exact ((poincareSeed_representative N u).1.norm.pow_const 2).add
      (Complex.continuous_re.comp (upperEnergy_continuous
        (congruencePoincareCartesian_smooth N u.smooth u.compact)
        (congruencePoincareCartesian_smooth N u.smooth u.compact))).measurable
  have hb := invariant_lintegral_restrict_le volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N) K hK (m : ℝ≥0∞)
    (orbit_indicator_tsum_le_of_overlap K m hm)
    (fun z => ENNReal.ofReal (poincareEnergyDensity N u z)) hmeas.ennreal_ofReal
    (fun g z => congrArg ENNReal.ofReal (poincareEnergyDensity_invariant N u g z))
  change (∫⁻ z, ENNReal.ofReal (poincareEnergyDensity N u z) ∂volume.restrict K) ≤
    (m : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal (poincareEnergyDensity N u z) ∂quotientMeasure N at hb
  rw [← ofReal_integral_eq_lintegral_ofReal (poincareEnergyDensity_integrable N u)
    (Filter.Eventually.of_forall (poincareEnergyDensity_nonnegative N u)),
    ← poincareEnergySeed_norm_sq_integral] at hb
  exact (lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (seedGradient_sq_le N i u z))).trans hb

/-- Local square-integrability of each gradient follows from the
invariant summed-energy estimate. -/
theorem seedGradient_local_memLp (N : ℕ) (u : SmoothUpperSeed) (i : Bool)
    (K : Set ℍ) (hK : MeasurableSet K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m) :
    MemLp (seedGradient N i u) 2 (volume.restrict K) := by
  apply (memLp_two_iff_integrable_sq_norm
    (seedGradient_continuous N i u).aestronglyMeasurable).mpr
  refine ⟨((seedGradient_continuous N i u).norm.pow 2).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun z => sq_nonneg ‖seedGradient N i u z‖))).mpr
  exact (seedGradient_local_lintegral_le N u i K hK m hm).trans_lt
    (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)

/-- A norm estimate suitable for extending local gradient maps from the
Poincare form core, retaining the explicit overlap constant. -/
theorem seedGradient_local_norm_sq_le (N : ℕ) (u : SmoothUpperSeed) (i : Bool)
    (K : Set ℍ) (hK : MeasurableSet K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m) :
    ‖(seedGradient_local_memLp N u i K hK m hm).toLp (seedGradient N i u)‖^2 ≤
      (m : ℝ) * ‖poincareEnergySeed N u‖^2 := by
  have hb := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
    (seedGradient_local_lintegral_le N u i K hK m hm)
  rwa [square_energy_toReal _ (seedGradient_local_memLp N u i K hK m hm),
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (sq_nonneg _)] at hb

#print axioms poincareEnergyDensity_invariant
#print axioms seedGradient_local_lintegral_le
#print axioms seedGradient_local_memLp
#print axioms seedGradient_local_norm_sq_le

end QuantitativeMaass
