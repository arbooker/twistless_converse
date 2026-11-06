module

public import FinitenessAllLevelCauchyOperatorV1
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelBoundarySampling

open Complex Filter Metric Set MeasureTheory FinitenessAllLevelDiskSeries
  FinitenessAllLevelDiskAlgebra FinitenessAllLevelCauchyOperator

theorem extend_measurable {r : ℝ} (f : space r) : Measurable (extend f.val) := by
  classical
  exact f.val.continuous.measurable.dite measurable_const isClosed_closedBall.measurableSet

/-- Measurable uniformly bounded circle data is circle integrable; finitely
many cell boundaries need not be continuity points. -/
theorem circleIntegrable_of_bound {R C : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : Measurable f) (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C) :
    CircleIntegrable f 0 R := by
  apply (intervalIntegrable_const :
    IntervalIntegrable (fun _ : ℝ => C) volume 0 (2 * Real.pi)).mono_fun'
  · exact (hf.comp (continuous_circleMap 0 R).measurable).aestronglyMeasurable
  · exact Eventually.of_forall (fun θ => hb _ (circleMap_mem_sphere 0 hR θ))

def sampleLinear (r : ℝ) (weight source : ℂ → ℂ) : space r →ₗ[ℂ] (ℂ → ℂ) where
  toFun f z := weight z * extend f.val (source z)
  map_add' f g := by
    funext z
    change weight z * extend (f.val + g.val) (source z) = _
    rw [extend_add]
    exact mul_add _ _ _
  map_smul' a f := by
    funext z
    change weight z * extend (a • f.val) (source z) = a * (weight z * extend f.val (source z))
    rw [extend_smul]
    change weight z * (a * extend f.val (source z)) = _
    ring

/-- A single weighted source evaluation gives a bounded integrable boundary
operator. The source may be merely measurable, which permits cell choices. -/
def sample (r : ℝ) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (weight source : ℂ → ℂ) (hw : Measurable weight) (hs : Measurable source)
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖weight z‖ ≤ C) : BoundaryOperator (space r) R where
  data := sampleLinear r weight source
  bound := C
  bound_nonneg := hC
  norm_le f z hz := by
    change ‖weight z * extend f.val (source z)‖ ≤ C * ‖f‖
    rw [norm_mul]
    exact mul_le_mul (hb z hz) (FinitenessAllLevelDiskRestriction.norm_extend_le f _)
      (norm_nonneg _) hC
  integrable f := by
    apply circleIntegrable_of_bound (C := C * ‖f‖) hR (hw.mul ((extend_measurable f).comp hs))
    intro z hz
    change ‖weight z * extend f.val (source z)‖ ≤ C * ‖f‖
    rw [norm_mul]
    exact mul_le_mul (hb z hz) (FinitenessAllLevelDiskRestriction.norm_extend_le f _)
      (norm_nonneg _) hC

/-- Restrict a branch to a measurable boundary cell. The bound is unchanged,
and no assertion of continuity across the cell interface is made. -/
def cellSample (r : ℝ) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (cell : Set ℂ) (hc : MeasurableSet cell) (weight source : ℂ → ℂ)
    (hw : Measurable weight) (hs : Measurable source)
    (hb : ∀ z ∈ sphere (0 : ℂ) R, z ∈ cell → ‖weight z‖ ≤ C) :
    BoundaryOperator (space r) R := by
  classical
  apply sample r hR hC (cell.indicator weight) source (hw.indicator hc) hs
  intro z hz
  by_cases hzc : z ∈ cell
  · simpa only [indicator_of_mem hzc] using hb z hz hzc
  · simpa only [indicator_of_notMem hzc, norm_zero] using hC

def sum {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {R : ℝ}
    {ι : Type*} (s : Finset ι) (B : ι → BoundaryOperator X R) : BoundaryOperator X R where
  data := ∑ i ∈ s, (B i).data
  integrable x := by
    simp only [LinearMap.sum_apply]
    exact CircleIntegrable.sum s (fun i _ => (B i).integrable x)
  bound := ∑ i ∈ s, (B i).bound
  bound_nonneg := Finset.sum_nonneg (fun i _ => (B i).bound_nonneg)
  norm_le x z hz := by
    simp only [LinearMap.sum_apply, Finset.sum_apply]
    calc
      _ ≤ ∑ i ∈ s, ‖(B i).data x z‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, (B i).bound * ‖x‖ :=
        Finset.sum_le_sum (fun i _ => (B i).norm_le x z hz)
      _ = _ := (Finset.sum_mul _ _ _).symm

def zero (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] (R : ℝ) :
    BoundaryOperator X R where
  data := 0
  integrable _ := circleIntegrable_const 0 0 R
  bound := 0
  bound_nonneg := le_rfl
  norm_le _ _ _ := by simp

theorem cellSample_apply (r : ℝ) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (cell : Set ℂ) (hc : MeasurableSet cell) (weight source : ℂ → ℂ)
    (hw : Measurable weight) (hs : Measurable source)
    (hb : ∀ z ∈ sphere (0 : ℂ) R, z ∈ cell → ‖weight z‖ ≤ C)
    (f : space r) (z : ℂ) :
    (cellSample r hR hC cell hc weight source hw hs hb).data f z =
      cell.indicator weight z * extend f.val (source z) := rfl

theorem sum_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {R : ℝ}
    {ι : Type*} (s : Finset ι) (B : ι → BoundaryOperator X R) (x : X) (z : ℂ) :
    (sum s B).data x z = ∑ i ∈ s, (B i).data x z := by
  simp only [sum, LinearMap.sum_apply, Finset.sum_apply]

/-- A finite piecewise sampling expression followed by positive Cauchy
projection gives a compact operator on the initial disk algebra. -/
theorem sampled_projection_compact {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {ι : Type*} (s : Finset ι) (B : ι → BoundaryOperator (space r) R) :
    IsCompactOperator (project hr hrR (sum s B)) := project_isCompactOperator hr hrR _

#print axioms extend_measurable
#print axioms circleIntegrable_of_bound
#print axioms sample
#print axioms cellSample
#print axioms sum
#print axioms sampled_projection_compact

end FinitenessAllLevelBoundarySampling
