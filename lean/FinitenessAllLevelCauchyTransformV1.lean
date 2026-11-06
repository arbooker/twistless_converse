module

public import FinitenessAllLevelDiskRestrictionV1
public import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelCauchyTransform

open Complex Metric Set FinitenessAllLevelDiskSeries FinitenessAllLevelDiskAlgebra
open scoped Topology

/-- The Cauchy transform is defined for circle-integrable boundary data;
continuity of the boundary values is not required. -/
def cauchy (R : ℝ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(0, R), (z - w)⁻¹ • f z

/-- Remove the constant Fourier coefficient of the Cauchy transform. -/
def positive (R : ℝ) (f : ℂ → ℂ) (w : ℂ) : ℂ := cauchy R f w - cauchy R f 0

theorem kernel_integrable {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : CircleIntegrable f 0 R) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    CircleIntegrable (fun z => (z - w)⁻¹ • f z) 0 R := by
  apply hf.continuousOn_smul (g := fun z : ℂ => (z - w)⁻¹)
  apply (continuous_id.sub continuous_const).continuousOn.inv₀
  intro z hz
  apply sub_ne_zero.mpr
  intro he
  change z = w at he
  subst z
  have hh : dist w 0 = R := by simpa only [mem_sphere, abs_of_nonneg hR] using hz
  exact (ne_of_lt hw) hh

theorem cauchy_differentiableOn {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : CircleIntegrable f 0 R) : DifferentiableOn ℂ (cauchy R f) (ball 0 R) := by
  intro w hw
  have hnot : w ∉ sphere (0 : ℂ) |R| := by
    simpa only [mem_sphere, abs_of_nonneg hR] using (ne_of_lt hw)
  exact ((Complex.hasDerivAt_circleIntegral_sub_inv_smul hf hnot).const_smul
    ((2 * Real.pi * I : ℂ)⁻¹)).differentiableAt.differentiableWithinAt

theorem positive_differentiableOn {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : CircleIntegrable f 0 R) : DifferentiableOn ℂ (positive R f) (ball 0 R) :=
  (cauchy_differentiableOn hR hf).sub_const _

@[simp] theorem positive_zero (R : ℝ) (f : ℂ → ℂ) : positive R f 0 = 0 := sub_self _

theorem cauchy_add {R : ℝ} (hR : 0 ≤ R) {f g : ℂ → ℂ}
    (hf : CircleIntegrable f 0 R) (hg : CircleIntegrable g 0 R)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    cauchy R (f + g) w = cauchy R f w + cauchy R g w := by
  simp only [cauchy, Pi.add_apply, smul_add]
  rw [circleIntegral.integral_add (kernel_integrable hR hf hw) (kernel_integrable hR hg hw)]
  exact smul_add _ _ _

theorem cauchy_smul (R : ℝ) (f : ℂ → ℂ) (a w : ℂ) :
    cauchy R (a • f) w = a • cauchy R f w := by
  simp only [cauchy, Pi.smul_apply, smul_comm _ a, circleIntegral.integral_smul]

theorem positive_add {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ}
    (hf : CircleIntegrable f 0 R) (hg : CircleIntegrable g 0 R)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    positive R (f + g) w = positive R f w + positive R g w := by
  rw [positive, cauchy_add hR.le hf hg hw,
    cauchy_add hR.le hf hg (mem_ball_self hR)]
  unfold positive
  ring

theorem positive_smul (R : ℝ) (f : ℂ → ℂ) (a w : ℂ) :
    positive R (a • f) w = a • positive R f w := by
  simp only [positive, cauchy_smul, smul_sub]

/-- An explicit bound with a positive radius gap. This bound applies even
to discontinuous circle-integrable boundary values. -/
theorem cauchy_norm_le {r R C : ℝ} (hR : 0 ≤ R) (hrR : r < R) (hC : 0 ≤ C)
    {f : ℂ → ℂ} (hf : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C)
    {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) r) :
    ‖cauchy R f w‖ ≤ R * (C / (R - r)) := by
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR
  intro z hz
  have hgap : R - r ≤ ‖z - w‖ := by
    have hz' : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
    have hw' : ‖w‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hw
    have hh := norm_sub_norm_le z w
    linarith
  rw [norm_smul, norm_inv, inv_mul_eq_div]
  exact div_le_div₀ hC (hf z hz) (sub_pos.mpr hrR) hgap

theorem positive_norm_le {r R C : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hC : 0 ≤ C)
    {f : ℂ → ℂ} (hf : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C)
    {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) r) :
    ‖positive R f w‖ ≤ 2 * R * (C / (R - r)) := by
  have hR := hr.trans hrR.le
  have h0 := cauchy_norm_le hR hrR hC hf (show (0 : ℂ) ∈ closedBall 0 r by simpa using hr)
  have hw' := cauchy_norm_le hR hrR hC hf hw
  exact (norm_sub_le _ _).trans (by linarith)

/-- Cauchy's formula identifies the projection on genuine holomorphic
functions, including the exact removal of the constant coefficient. -/
theorem positive_eq {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball 0 R)) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    positive R f w = f w - f 0 := by
  exact congrArg₂ (· - ·)
    (hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw)
    (hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (mem_ball_self hR))

/-- The positive Cauchy transform as an actual element of the smaller
zero-constant-term Banach disk algebra. -/
def toDisk {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (f : ℂ → ℂ)
    (hf : CircleIntegrable f 0 R) : space r := by
  let F : C(Disk r, ℂ) := ⟨fun z => positive R f z.val,
    continuousOn_iff_continuous_domRestrict.mp
      ((positive_differentiableOn (hr.trans hrR.le) hf).continuousOn.mono
        (closedBall_subset_ball hrR))⟩
  refine ⟨F, ?_, ?_⟩
  · apply ((positive_differentiableOn (hr.trans hrR.le) hf).mono
      (ball_subset_ball hrR.le)).congr
    intro z hz
    rw [extend, dite_eq_left (ball_subset_closedBall hz)]
    rfl
  · rw [extend, dite_eq_left (show (0 : ℂ) ∈ closedBall 0 r by simpa using hr)]
    exact positive_zero R f

theorem toDisk_apply {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (f : ℂ → ℂ)
    (hf : CircleIntegrable f 0 R) (z : Disk r) :
    (toDisk hr hrR f hf).val z = positive R f z.val := rfl

theorem toDisk_norm_le {r R C : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hC : 0 ≤ C)
    (f : ℂ → ℂ) (hf : CircleIntegrable f 0 R)
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C) :
    ‖toDisk hr hrR f hf‖ ≤ 2 * R * (C / (R - r)) := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hgap : 0 < R - r := sub_pos.mpr hrR
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro z
  exact positive_norm_le hr hrR hC hb z.property

#print axioms positive_differentiableOn
#print axioms positive_norm_le
#print axioms positive_eq
#print axioms toDisk_norm_le

end FinitenessAllLevelCauchyTransform
