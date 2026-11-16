module

public import QuantitativeMaassScalarMetricGramV1
public import QuantitativeMaassCylinderPhysicalV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane AsymptoticMassTransport
open AsymptoticClassicalPetersson AsymptoticFiniteBranch
namespace QuantitativeMaass

/-- The same pointwise metric on the physical hyperbolic ambient space. -/
def ScalarCylinderMetric.physicalChange {N : ℕ} (M : ScalarCylinderMetric N) :
    AsymptoticHyperbolicSlash.Space≃L[ℂ]AsymptoticHyperbolicSlash.Space :=
  positiveL2MultiplierEquiv volume M.weight M.measurable M.lower_pos M.bounds

theorem ScalarCylinderMetric.physicalChange_coeFn {N : ℕ} (M : ScalarCylinderMetric N)
    (f : AsymptoticHyperbolicSlash.Space) :
    (M.physicalChange f : ℍ→ℂ)=ᵐ[volume]fun z => (M.weight z:ℂ)*f z :=
  positiveL2MultiplierEquiv_coeFn _ _ _ _ _ f

theorem ScalarCylinderMetric.physicalChange_norm {N : ℕ} (M : ScalarCylinderMetric N) :
    ‖M.physicalChange.toContinuousLinearMap‖≤M.upper :=
  positiveL2MultiplierEquiv_norm _ _ _ _ _ M.branch.bound_nonneg

theorem ScalarCylinderMetric.physicalChange_inv_norm {N : ℕ} (M : ScalarCylinderMetric N) :
    ‖M.physicalChange.symm.toContinuousLinearMap‖≤M.lower⁻¹ :=
  positiveL2MultiplierEquiv_symm_norm _ _ _ _ _

theorem ScalarCylinderMetric.physicalChange_zeroExtension {N : ℕ} (M : ScalarCylinderMetric N)
    (f : Lp ℂ 2 (quotientMeasure 0)) :
    M.physicalChange (cylinderZeroExtension f)=cylinderZeroExtension (M.change f) := by
  apply Lp.ext
  filter_upwards [M.physicalChange_coeFn (cylinderZeroExtension f),cylinderZeroExtension_coeFn f,
    cylinderZeroExtension_coeFn_of_ae (M.change f) _ (M.coeFn f)] with z h1 h2 h3
  rw [h1,h2,h3]
  by_cases hz : z∈strip
  · simp only [Set.indicator_of_mem hz]
  · simp only [Set.indicator_of_notMem hz,mul_zero]

theorem ScalarCylinderMetric.physicalChange_branch {N : ℕ} (M : ScalarCylinderMetric N) :
    holomorphicSum [M.branch] 0=M.physicalChange.toContinuousLinearMap := by
  simp only [holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  change AsymptoticConcreteRationalBranch.operator 1 _ _ _ 0=_
  rw [AsymptoticConcreteRationalBranch.operator_one_label]
  rfl

/-- Original physical canonical reconstruction retains the proved quotient
norm after multiplication by the very same finite-branch metric. -/
theorem admissibleScalarMetric_physical_norm (N : ℕ) [NeZero N]
    (hN : GridAdmissibleGap.Admissible N) {δ : ℝ} (hδ : 0<δ) {ν : ℕ} (hν : 1≤ν)
    (χ : admissibleGeneratorIndex N hN.1→ℂ) (hχ : ∀ i,‖χ i‖=1)
    (x : completedGeneratorSpace N hN.1 χ) :
    ‖(admissibleScalarMetric N hN hδ hν).physicalChange
      (cylinderZeroExtension (weightedQuotientEmbedding N hδ hν x.val))‖=‖x‖ := by
  rw [ScalarCylinderMetric.physicalChange_zeroExtension,cylinderZeroExtension.norm_map]
  exact admissibleScalarMetric_generator_norm N hN hδ hν χ hχ x

#print axioms ScalarCylinderMetric.physicalChange_norm
#print axioms ScalarCylinderMetric.physicalChange_inv_norm
#print axioms ScalarCylinderMetric.physicalChange_zeroExtension
#print axioms ScalarCylinderMetric.physicalChange_branch
#print axioms admissibleScalarMetric_physical_norm
end QuantitativeMaass
