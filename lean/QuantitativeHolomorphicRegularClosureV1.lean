module

public import QuantitativeHolomorphicRegularObservationV1
public import QuantitativeHolomorphicApproximationChoiceV1
public import AsymptoticRegularInfiniteKernelV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeHolomorphic

open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open ContinuousLinearMap AsymptoticCompactObservationCount AsymptoticFiniteBranch
open AsymptoticRegularTrace MeasureTheory Filter
open scoped Topology

theorem regularSum_matrix_measurable (E : Expression)
    (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (regularSum E z) g h) := by
  induction E generalizing g h with
  | nil => exact measurable_const
  | cons b E ih =>
    exact matrix_add_measurable (regular b) (regularSum E)
      (AsymptoticOrbitBranch.operator_matrix_measurable
        (fun a => (AsymptoticRationalGroup.measurePreserving a).measurable)
        b.label b.coefficient b.bound_nonneg b.norm_le b.measurable) ih g h

theorem regularSum_covariant (E : Expression) : Covariant (regularSum E) := by
  induction E with
  | nil => intro z a g h; rfl
  | cons b E ih =>
    exact covariant_add (regular b) (regularSum E)
      (AsymptoticOrbitBranch.operator_covariant b.label b.coefficient b.bound_nonneg b.norm_le) ih

/-- Uniform finite rational approximation proves actual matrix measurability
and covariance; these are conclusions, not hypotheses on the limit family. -/
theorem regular_of_uniform_expression_approximation
    (B : UpperHalfPlane → RegularSpace →L[ℂ] RegularSpace)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ E : Expression, ∀ z, ‖regularSum E z-B z‖ < ε) :
    (∀ g h, Measurable (fun z => matrix (B z) g h)) ∧ Covariant B := by
  have hex (n : ℕ) := hB (1/((n:ℝ)+1)) (by positivity)
  choose E hE using hex
  have hn (z : UpperHalfPlane) : Tendsto (fun n => regularSum (E n) z) atTop (𝓝 (B z)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hE n z).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hv (z : UpperHalfPlane) (v : RegularSpace) :
      Tendsto (fun n => regularSum (E n) z v) atTop (𝓝 (B z v)) :=
    ((ContinuousLinearMap.apply ℂ RegularSpace v).continuous.tendsto _).comp (hn z)
  exact ⟨strong_limit_matrix_measurable _ _ (fun n => regularSum_matrix_measurable (E n)) hv,
    covariant_of_strong_limit _ _ (fun n => regularSum_covariant (E n)) hv⟩

variable {N Q : ℕ} {hQ : 0 < Q} (A : Certificate N Q hQ)
variable {ι : Type*}

def normalizedRegularAmbientCountReconstruction (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (z : UpperHalfPlane) : RegularSpace →L[ℂ] RegularSpace :=
  (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)).comp
    (AsymptoticRegularReconstruction.TerminalSpace A
      (AsymptoticReconstructedCount.parameters A P) z).subtypeL.adjoint

/-- The exact normalized reconstruction, extended by zero off its terminal
source, is a measurable covariant family. All approximation parameters are
common to the orbit roots. -/
theorem normalizedRegularCountReconstruction_regular (hN : 0 < N) (P : Parameters A)
    (e : Sector N) :
    (∀ g h, Measurable (fun z => matrix
      (normalizedRegularAmbientCountReconstruction A hN P e z) g h)) ∧
    Covariant (normalizedRegularAmbientCountReconstruction A hN P e) := by
  refine regular_of_uniform_expression_approximation
    (normalizedRegularAmbientCountReconstruction A hN P e) ?_
  intro ε hε
  obtain ⟨n,j,J,hJ,hsmall⟩ := exists_normalizedCutError_lt A P hε
  refine ⟨normalizedReconstructionExpression (scaledCutCountExpression A hN P e 0 j J) n, ?_⟩
  intro z
  have he := normalizedCutCountExpression_regular_ambient_error A hN P e z n 0
    (le_refl _) j J hJ
  exact he.trans_lt hsmall

/-- The actual positive global observation filter is measurable and covariant,
without an assumed regularity statement for its inverse-square-root normalization. -/
theorem observationRegularFilter_regular (hN : 0 < N) (P : Parameters A)
    (e : Sector N) (qs : Finset ι) (r : ι → Row N) (s : ι → Set UpperHalfPlane)
    (hs : ∀ i, IsCompact (s i)) (d : ℕ) :
    let B := fun z => observationRegularFilter A hN P e qs r s hs z
      (normalizedReconstruction (scaledRegularCountReconstruction A hN P e z)) d
    (∀ g h, Measurable (fun z => matrix (B z) g h)) ∧ Covariant B := by
  refine regular_of_uniform_expression_approximation _ ?_
  intro ε hε
  obtain ⟨n,j,J,hJ,hsmall⟩ := exists_normalizedCutError_lt A P
    (div_pos hε (by positivity : (0:ℝ)<2*d+2))
  refine ⟨countObservationFilterExpression A hN P e qs r s hs 0 j J n d, ?_⟩
  intro z
  apply (countObservationFilterExpression_regular_error A hN P e qs r s hs z 0
    (le_refl _) j J n d hJ).trans_lt
  nlinarith [(lt_div_iff₀ (by positivity : (0:ℝ)<2*d+2)).mp hsmall]

#print axioms normalizedRegularCountReconstruction_regular
#print axioms observationRegularFilter_regular

end QuantitativeHolomorphic
