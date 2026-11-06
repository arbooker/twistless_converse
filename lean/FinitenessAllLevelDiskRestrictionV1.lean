module

public import FinitenessAllLevelDiskAlgebraV1
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.UniformConvergence

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelDiskRestriction

open Filter Set Metric FinitenessAllLevelDiskSeries FinitenessAllLevelDiskAlgebra
open scoped Topology BoundedContinuousFunction NNReal

def inclusion {r R : ℝ} (h : r ≤ R) : C(Disk r, Disk R) :=
  ⟨Set.inclusion (closedBall_subset_closedBall h), continuous_inclusion _⟩

/-- Restriction from the larger disk algebra into the continuous functions
on the smaller closed disk. -/
def restrictC {r R : ℝ} (h : r ≤ R) : space R →L[ℂ] C(Disk r, ℂ) :=
  (ContinuousMap.compCLM ℂ ℂ (inclusion h)).comp (space R).subtypeL

theorem restrictC_apply {r R : ℝ} (h : r ≤ R) (f : space R) (z : Disk r) :
    restrictC h f z = extend f.val z.val := by
  exact (extend_apply f.val (inclusion h z)).symm

theorem norm_extend_le {R : ℝ} (f : space R) (z : ℂ) : ‖extend f.val z‖ ≤ ‖f‖ := by
  by_cases hz : z ∈ closedBall (0 : ℂ) R
  · rw [extend, dite_eq_left hz]
    exact f.val.norm_coe_le_norm _
  · simp only [extend, dite_eq_right hz, norm_zero]
    exact norm_nonneg _

theorem norm_restrictC_le {r R : ℝ} (h : r ≤ R) (f : space R) :
    ‖restrictC h f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro z
  rw [restrictC_apply]
  exact norm_extend_le f z.val

/-- A uniform derivative bound on the smaller disk, obtained from Schwarz's
lemma on balls of radius R-r centered at each point of that disk. -/
theorem fderiv_bound {r R : ℝ} (h : r < R) (f : space R) (hf : ‖f‖ ≤ 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) r) :
    ‖fderiv ℂ (extend f.val) z‖ ≤ 2 / (R - r) := by
  have hsub : ball z (R - r) ⊆ ball (0 : ℂ) R := by
    apply ball_subset_ball'
    have hh : dist z 0 ≤ r := hz
    linarith
  apply Complex.norm_fderiv_le_div_of_mapsTo_ball (f.property.1.mono hsub)
    (fun w _ => ?_) (sub_pos.mpr h)
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_sub_le _ _).trans (by
    have hw := (norm_extend_le f w).trans hf
    have hz' := (norm_extend_le f z).trans hf
    linarith)

theorem restrictC_lipschitz {r R : ℝ} (h : r < R) (f : space R) (hf : ‖f‖ ≤ 1) :
    LipschitzWith ⟨2 / (R - r), by positivity⟩ (restrictC h.le f) := by
  have hl : LipschitzOnWith ⟨2 / (R - r), by positivity⟩
      (extend f.val) (closedBall (0 : ℂ) r) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℂ)
    · intro z hz
      exact f.property.1.differentiableAt (isOpen_ball.mem_nhds
        (closedBall_subset_ball h hz))
    · intro z hz
      exact fderiv_bound h f hf hz
    · exact convex_closedBall 0 r
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [restrictC_apply, restrictC_apply]
  exact hl.dist_le_mul z.val z.property w.val w.property

/-- Restricting to a strictly smaller disk is compact. The proof uses the
actual supremum norm, the derivative estimate, and Arzela--Ascoli. -/
theorem restrictC_isCompactOperator {r R : ℝ} (h : r < R) :
    IsCompactOperator (restrictC h.le) := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact (Disk r) ℂ
  let A : Set (Disk r →ᵇ ℂ) :=
    (fun f : space R => e (restrictC h.le f)) '' closedBall 0 1
  have hb (g : Disk r →ᵇ ℂ) (z : Disk r) (hg : g ∈ A) :
      g z ∈ closedBall (0 : ℂ) 1 := by
    obtain ⟨f, hf, rfl⟩ := hg
    have hf' : ‖f‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hf
    rw [mem_closedBall, dist_zero_right]
    change ‖restrictC h.le f z‖ ≤ 1
    exact ((restrictC h.le f).norm_coe_le_norm z).trans ((norm_restrictC_le h.le f).trans hf')
  have heq : Equicontinuous ((↑) : A → Disk r → ℂ) := by
    apply (LipschitzWith.uniformEquicontinuous _
      (⟨2 / (R - r), by positivity⟩ : ℝ≥0) ?_).equicontinuous
    intro g
    obtain ⟨f, hf, hg⟩ := g.property
    have hf' : ‖f‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hf
    have he : (fun z : Disk r => g.val z) = (restrictC h.le f : Disk r → ℂ) := by
      rw [← hg]
      rfl
    change LipschitzWith (⟨2 / (R - r), by positivity⟩ : ℝ≥0) (fun z : Disk r => g.val z)
    rw [he]
    exact restrictC_lipschitz h f hf'
  have hc : IsCompact (closure A) := BoundedContinuousFunction.arzela_ascoli
    (closedBall (0 : ℂ) 1) (isCompact_closedBall _ _) A hb heq
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (restrictC h.le).toLinearMap (by norm_num : (0 : ℝ) < 1)).mpr
  refine ⟨e.symm '' closure A, hc.image e.symm.continuous, ?_⟩
  rintro g ⟨f, hf, rfl⟩
  exact ⟨e (restrictC h.le f), subset_closure ⟨f, hf, rfl⟩, e.symm_apply_apply _⟩

theorem restrictC_mem {r R : ℝ} (h : r ≤ R) (f : space R) : restrictC h f ∈ space r := by
  have he (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r) :
      extend (restrictC h f) z = extend f.val z := by
    rw [extend, dite_eq_left hz]
    exact restrictC_apply h f ⟨z, hz⟩
  refine ⟨?_, ?_⟩
  · apply (f.property.1.mono (ball_subset_ball h)).congr
    intro z hz
    exact he z (ball_subset_closedBall hz)
  · by_cases hz : (0 : ℂ) ∈ closedBall (0 : ℂ) r
    · rw [he 0 hz]
      exact f.property.2
    · simp only [extend, dite_eq_right hz]

/-- Restriction as an operator between the two actual Banach disk algebras. -/
def restrict {r R : ℝ} (h : r ≤ R) : space R →L[ℂ] space r :=
  (restrictC h).codRestrict (space r) (restrictC_mem h)

theorem restrict_isCompactOperator {r R : ℝ} (h : r < R) :
    IsCompactOperator (restrict h.le) :=
  (restrictC_isCompactOperator h).codRestrict (restrictC_mem h.le) (space_isClosed r)

#print axioms fderiv_bound
#print axioms restrictC_lipschitz
#print axioms restrictC_isCompactOperator
#print axioms restrict_isCompactOperator

end FinitenessAllLevelDiskRestriction
