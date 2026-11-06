module

public import FinitenessAllLevelCauchyTransformV1
public import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCauchyOperator

open Complex Metric Set FinitenessAllLevelDiskSeries FinitenessAllLevelDiskAlgebra
  FinitenessAllLevelCauchyTransform

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Linear boundary data with a uniform bound and actual circle integrability.
This interface does not assume a compact operator or a reconstruction theorem.
The certificate boundary expression must still be supplied separately. -/
structure BoundaryOperator (R : ℝ) where
  data : X →ₗ[ℂ] (ℂ → ℂ)
  integrable : ∀ x, CircleIntegrable (data x) 0 R
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ x z, z ∈ sphere (0 : ℂ) R → ‖data x z‖ ≤ bound * ‖x‖

variable {X}

def projectLinear {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (B : BoundaryOperator X R) :
    X →ₗ[ℂ] space r where
  toFun x := toDisk hr hrR (B.data x) (B.integrable x)
  map_add' x y := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    change positive R (B.data (x + y)) z.val =
      positive R (B.data x) z.val + positive R (B.data y) z.val
    rw [map_add]
    exact positive_add (lt_of_le_of_lt hr hrR) (B.integrable x) (B.integrable y)
      (closedBall_subset_ball hrR z.property)
  map_smul' a x := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    change positive R (B.data (a • x)) z.val = a • positive R (B.data x) z.val
    rw [map_smul]
    exact positive_smul R (B.data x) a z.val

theorem projectLinear_bound {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (B : BoundaryOperator X R) (x : X) :
    ‖projectLinear hr hrR B x‖ ≤ (2 * R / (R - r) * B.bound) * ‖x‖ := by
  have h := toDisk_norm_le hr hrR (mul_nonneg B.bound_nonneg (norm_nonneg x))
    (B.data x) (B.integrable x) (B.norm_le x)
  calc
    ‖projectLinear hr hrR B x‖ = ‖toDisk hr hrR (B.data x) (B.integrable x)‖ := rfl
    _ ≤ 2 * R * (B.bound * ‖x‖ / (R - r)) := h
    _ = _ := by ring

/-- The positive Cauchy projection is a bounded operator into the actual
Banach disk algebra, with a bound depending explicitly on the radius gap. -/
def project {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (B : BoundaryOperator X R) :
    X →L[ℂ] space r :=
  (projectLinear hr hrR B).mkContinuous (2 * R / (R - r) * B.bound)
    (projectLinear_bound hr hrR B)

theorem project_apply {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (B : BoundaryOperator X R) (x : X) (z : Disk r) :
    (project hr hrR B x).val z = positive R (B.data x) z.val := rfl

theorem project_factor {r t R : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htR : t < R)
    (B : BoundaryOperator X R) :
    project hr (lt_of_le_of_lt hrt htR) B =
      (FinitenessAllLevelDiskRestriction.restrict hrt).comp
        (project (hr.trans hrt) htR B) := by
  ext x : 1
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  rfl

/-- Compactness follows by projecting first into an intermediate disk and
then applying the verified compact restriction operator. -/
theorem project_isCompactOperator {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (B : BoundaryOperator X R) : IsCompactOperator (project hr hrR B) := by
  have hrt : r < (r + R) / 2 := by linarith
  have htR : (r + R) / 2 < R := by linarith
  rw [project_factor hr hrt.le htR B]
  exact (FinitenessAllLevelDiskRestriction.restrict_isCompactOperator hrt).comp_clm _

theorem cauchy_congr {R : ℝ} (hR : 0 ≤ R) {f g : ℂ → ℂ}
    (he : EqOn f g (sphere (0 : ℂ) R)) (w : ℂ) : cauchy R f w = cauchy R g w := by
  unfold cauchy
  congr 1
  exact circleIntegral.integral_congr hR (fun z hz => by rw [he hz])

theorem positive_congr {R : ℝ} (hR : 0 ≤ R) {f g : ℂ → ℂ}
    (he : EqOn f g (sphere (0 : ℂ) R)) (w : ℂ) : positive R f w = positive R g w := by
  unfold positive
  rw [cauchy_congr hR he w, cauchy_congr hR he 0]

/-- Exact recovery for a holomorphic function whose boundary is reproduced
by the supplied data. This is the equation later needed for original solutions. -/
theorem project_eq_of_boundary {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (B : BoundaryOperator X R) (x : X) {F : ℂ → ℂ}
    (hF : DiffContOnCl ℂ F (ball 0 R)) (hF0 : F 0 = 0)
    (he : EqOn (B.data x) F (sphere (0 : ℂ) R)) (z : Disk r) :
    (project hr hrR B x).val z = F z.val := by
  rw [project_apply, positive_congr (hr.trans hrR.le) he,
    positive_eq (lt_of_le_of_lt hr hrR) hF (closedBall_subset_ball hrR z.property),
    hF0, sub_zero]

/-- A generic compact affine pencil from two integrable bounded boundary
operators. Instantiation by the actual certificate data remains separate. -/
def pencil {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (B₀ B₁ : BoundaryOperator X R) (lam : ℂ) : X →L[ℂ] space r :=
  project hr hrR B₀ + lam • project hr hrR B₁

theorem pencil_isCompactOperator {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (B₀ B₁ : BoundaryOperator X R) (lam : ℂ) :
    IsCompactOperator (pencil hr hrR B₀ B₁ lam) :=
  (project_isCompactOperator hr hrR B₀).add
    ((project_isCompactOperator hr hrR B₁).smul lam)

theorem pencil_differentiable {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (B₀ B₁ : BoundaryOperator X R) : Differentiable ℂ (pencil hr hrR B₀ B₁) := by
  let : IsBoundedSMul ℂ (X →L[ℂ] space r) :=
    IsBoundedSMul.of_norm_smul_le (fun c T => ContinuousLinearMap.opNorm_smul_le c T)
  unfold pencil
  exact (differentiable_const (project hr hrR B₀)).add
    ((differentiable_id : Differentiable ℂ (fun z : ℂ => z)).smul_const (project hr hrR B₁))

#print axioms projectLinear_bound
#print axioms project_isCompactOperator
#print axioms project_eq_of_boundary
#print axioms pencil_isCompactOperator
#print axioms pencil_differentiable

end FinitenessAllLevelCauchyOperator
