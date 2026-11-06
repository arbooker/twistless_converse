module

public import QuantitativeHolomorphicFiniteBranchTraceV1
public import AsymptoticConcreteRationalBranchV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open MeasureTheory UpperHalfPlane AsymptoticUnweightedKernel

/-- The quantitative estimate for the literal retained rational
pullback operator.  Its action and its weight-dependent slash phase
are discharged by the existing concrete operator construction. -/
theorem retained_rational_operator_trace_bound
    (g : AsymptoticRationalGroup.Group) (a b c d : ℤ) (hdet : a * d - b * c ≠ 0)
    (Ω : Set ℍ) (hΩ : MeasurableSet Ω) (hfinite : volume Ω ≠ ⊤)
    (hstrip : Ω ⊆ AsymptoticMassTransport.strip)
    (hend : ∀ z ∈ Ω, g • z ∈ AsymptoticMassTransport.strip)
    (coeff : ℍ → ℂ) (hcmeas : Measurable coeff) (hcoeff : ∀ z, ‖coeff z‖ ≤ 1)
    {D Y H R ε : ℝ} (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H) (hε : 0 < ε)
    (hregion : ∀ z ∈ Ω, Y ≤ (g • z).im ∧ Y ≤ z.im ∧ (g • z).im ≤ H ∧
      z.im ≤ H ∧ |(g • z).re - z.re| ≤ R)
    (hden : ∀ z ∈ Ω, (c : ℂ) * (z : ℂ) + d ≠ 0)
    (hbound : ∀ z ∈ Ω, ‖(c : ℂ) * (z : ℂ) + d‖ ≤ D)
    (hformula : ∀ z ∈ Ω, ((g • z : ℍ) : ℂ) = ((a : ℂ) * (z : ℂ) + b) / ((c : ℂ) * (z : ℂ) + d))
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hne : ∀ j ∈ S, c ≠ 0 ∨ d ≠ a + j * c ∨ b + j * d ≠ 0)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H R ≤ 1 + |(n : ℝ)|) :
    |liftedTrace h hε
        (AsymptoticConcreteRationalBranch.operator g (Ω.indicator coeff)
          (hcmeas.indicator hΩ)
          (indicator_coefficient_bound Ω coeff (by norm_num : (0 : ℝ) ≤ 1) hcoeff) (h + 1)) /
        ((2 * h + 2 : ℕ) : ℝ)| ≤
      periodizedBranchError D Y H R (volume.real Ω) h S.card / (4 * Real.pi) := by
  let phased : ℍ → ℂ := fun z => coeff z * AsymptoticSlashGauge.phase g (h + 1) z
  have hpm : AEStronglyMeasurable phased (volume.restrict Ω) :=
    (hcmeas.mul (AsymptoticSlashGauge.phase_continuous g (h + 1)).measurable).aestronglyMeasurable
  have hpb : ∀ z ∈ Ω, ‖phased z‖ ≤ 1 := by
    intro z _
    simpa only [phased, norm_mul, AsymptoticSlashGauge.phase_norm, mul_one] using hcoeff z
  exact normalized_matrix_branch_trace_bound a b c d hdet (fun z => g • z)
    (AsymptoticRationalBranches.action_continuous g).measurable Ω hΩ hfinite hstrip phased hpm hpb
    hD hY hH hε hregion hden hbound hformula h hsmall S hne hfar _
    (fun n => AsymptoticConcreteRationalBranch.retained_operator_mode g Ω hΩ hend coeff hcmeas
      (by norm_num : (0 : ℝ) ≤ 1) hcoeff h n hε)

/-- The quantitative estimate for the literal retained rational
pullback operator.  Its action and its weight-dependent slash phase
are discharged by the existing concrete operator construction. -/
theorem retained_rational_operator_trace_bound_of_cap
    (g : AsymptoticRationalGroup.Group) (a b c d : ℤ) (hdet : a * d - b * c ≠ 0)
    (Ω : Set ℍ) (hΩ : MeasurableSet Ω) (hfinite : volume Ω ≠ ⊤)
    (hstrip : Ω ⊆ AsymptoticMassTransport.strip)
    (hend : ∀ z ∈ Ω, g • z ∈ AsymptoticMassTransport.strip)
    (coeff : ℍ → ℂ) {C : ℝ} (hC : 0 < C) (hcmeas : Measurable coeff) (hcoeff : ∀ z, ‖coeff z‖ ≤ C)
    {D Y H R ε : ℝ} (hD : 0 ≤ D) (hY : 0 < Y) (hH : 0 < H) (hε : 0 < ε)
    (hregion : ∀ z ∈ Ω, Y ≤ (g • z).im ∧ Y ≤ z.im ∧ (g • z).im ≤ H ∧
      z.im ≤ H ∧ |(g • z).re - z.re| ≤ R)
    (hden : ∀ z ∈ Ω, (c : ℂ) * (z : ℂ) + d ≠ 0)
    (hbound : ∀ z ∈ Ω, ‖(c : ℂ) * (z : ℂ) + d‖ ≤ D)
    (hformula : ∀ z ∈ Ω, ((g • z : ℍ) : ℂ) = ((a : ℂ) * (z : ℂ) + b) / ((c : ℂ) * (z : ℂ) + d))
    (h : ℕ) (hsmall : (h + 1 : ℝ) ^ (-(1 / 3 : ℝ)) * D ≤ 1)
    (S : Finset ℤ)
    (hne : ∀ j ∈ S, c ≠ 0 ∨ d ≠ a + j * c ∨ b + j * d ≠ 0)
    (hfar : ∀ n : ℤ, n ∉ S → 2 * compactBaseBound Y H R ≤ 1 + |(n : ℝ)|) :
    |liftedTrace h hε
        (AsymptoticConcreteRationalBranch.operator g (Ω.indicator coeff)
          (hcmeas.indicator hΩ)
          (indicator_coefficient_bound Ω coeff hC.le hcoeff) (h + 1)) /
        ((2 * h + 2 : ℕ) : ℝ)| ≤
      (C * periodizedBranchError D Y H R (volume.real Ω) h S.card) / (4 * Real.pi) := by
  let phased : ℍ → ℂ := fun z => coeff z * AsymptoticSlashGauge.phase g (h + 1) z
  have hpm : AEStronglyMeasurable phased (volume.restrict Ω) :=
    (hcmeas.mul (AsymptoticSlashGauge.phase_continuous g (h + 1)).measurable).aestronglyMeasurable
  have hpb : ∀ z ∈ Ω, ‖phased z‖ ≤ C := by
    intro z _
    simpa only [phased, norm_mul, AsymptoticSlashGauge.phase_norm, mul_one] using hcoeff z
  exact normalized_matrix_branch_trace_bound_of_cap a b c d hdet (fun z => g • z)
    (AsymptoticRationalBranches.action_continuous g).measurable Ω hΩ hfinite hstrip phased hC hpm hpb
    hD hY hH hε hregion hden hbound hformula h hsmall S hne hfar _
    (fun n => AsymptoticConcreteRationalBranch.retained_operator_mode g Ω hΩ hend coeff hcmeas
      hC.le hcoeff h n hε)

#print axioms retained_rational_operator_trace_bound_of_cap
#print axioms retained_rational_operator_trace_bound

end QuantitativeHolomorphic
