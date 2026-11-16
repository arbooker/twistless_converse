module

public import QuantitativeMaassScalarMetricRegularV1
public import QuantitativeMaassCanonicalRegularityV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open UpperHalfPlane MeasureTheory ContinuousLinearMap AsymptoticFiniteBranch AsymptoticRegularTrace
open AsymptoticRegularCompactBranch (Space)
namespace QuantitativeMaass

theorem ScalarCylinderMetric.inverse_complex_bound {N : ℕ} (M : ScalarCylinderMetric N) (z : ℍ) :
    ‖(((M.weight z)⁻¹:ℝ):ℂ)‖≤M.lower⁻¹ := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (M.lower_pos.trans_le (M.bounds z).1))]
  exact inv_anti₀ M.lower_pos (M.bounds z).1

def ScalarCylinderMetric.inverseBranch {N : ℕ} (M : ScalarCylinderMetric N) : Branch where
  label := 1
  coefficient z := ((M.weight z)⁻¹:ℝ)
  measurable := Complex.measurable_ofReal.comp M.measurable.inv
  bound := M.lower⁻¹
  bound_nonneg := (inv_pos.mpr M.lower_pos).le
  norm_le := M.inverse_complex_bound

theorem ScalarCylinderMetric.inverseBranch_physical {N : ℕ} (M : ScalarCylinderMetric N) :
    holomorphicSum [M.inverseBranch] 0=M.physicalChange.symm.toContinuousLinearMap := by
  simp only [holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  change AsymptoticConcreteRationalBranch.operator 1 _ _ _ 0=_
  rw [AsymptoticConcreteRationalBranch.operator_one_label]
  rfl

theorem ScalarCylinderMetric.inverseBranch_regular {N : ℕ} (M : ScalarCylinderMetric N) (x : ℍ) :
    regularSum [M.inverseBranch] x=(M.regularChange x).symm.toContinuousLinearMap := by
  ext1 v
  apply lp.ext
  funext a
  simp only [regularSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  change ((M.weight (a • x))⁻¹:ℝ)*v (1*a)=((M.weight (a • x))⁻¹:ℝ)*v a
  rw [one_mul]

/-- A diagonal inverse metric moves to a bounded weight on the rooted trace
without any cyclicity or integrability assumption. -/
theorem ScalarCylinderMetric.inverse_trace_weight {N : ℕ} (M : ScalarCylinderMetric N)
    (F : ℍ→Space→L[ℂ]Space) :
    signedTrace volume (fun x => (M.regularChange x).symm.toContinuousLinearMap*F x*
      (M.regularChange x).symm.toContinuousLinearMap.adjoint)=
    signedTrace volume (fun x =>
      (regularSum [M.inverseBranch] x*regularSum [M.inverseBranch] x)*F x) := by
  unfold signedTrace
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [M.inverseBranch_regular]
  let d : AsymptoticRationalGroup.Group→ℂ := fun a => ((M.weight (a • x))⁻¹:ℝ)
  have hd (a : AsymptoticRationalGroup.Group) : ‖d a‖≤M.lower⁻¹ := M.inverse_complex_bound (a • x)
  let D := AsymptoticOrbitDiagonal.operator d (inv_pos.mpr M.lower_pos).le hd
  change (matrix ((D.comp (F x)).comp D.adjoint) 1 1).re=
    (matrix ((D.comp D).comp (F x)) 1 1).re
  rw [CountingMetric.diagonal_sandwich_matrix]
  change (d 1*star (d 1)*matrix (F x) 1 1).re=(d 1*(d 1*matrix (F x) 1 1)).re
  have hdreal : star (d 1)=d 1 := by simp only [d,Complex.star_def,Complex.conj_ofReal]
  rw [hdreal,mul_assoc]

#print axioms ScalarCylinderMetric.inverse_complex_bound
#print axioms ScalarCylinderMetric.inverseBranch_physical
#print axioms ScalarCylinderMetric.inverseBranch_regular
#print axioms ScalarCylinderMetric.inverse_trace_weight
end QuantitativeMaass
