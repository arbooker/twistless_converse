module

public import FinitenessAllLevelTopologyV1
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

set_option autoImplicit false
@[expose] public noncomputable section

namespace FinitenessAllLevelDiskAlgebra

open Filter Set Metric FinitenessAllLevelDiskSeries FinitenessAllLevelProperness
  FinitenessOriginalInput FinitenessOriginalFourier
open scoped Topology

/-- Extension by zero is used only to express differentiability on the open
disk. No continuity or holomorphy across its boundary is required. -/
def extend {R : ℝ} (f : C(Disk R, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ closedBall (0 : ℂ) R then f ⟨z, hz⟩ else 0

@[simp] theorem extend_apply {R : ℝ} (f : C(Disk R, ℂ)) (z : Disk R) :
    extend f z.val = f z := by simp [extend, z.property]

@[simp] theorem extend_zero (R : ℝ) : extend (0 : C(Disk R, ℂ)) = 0 := by
  funext z
  simp [extend]

@[simp] theorem extend_add {R : ℝ} (f g : C(Disk R, ℂ)) :
    extend (f + g) = extend f + extend g := by
  funext z
  by_cases hz : z ∈ closedBall (0 : ℂ) R <;> simp [extend, hz]

@[simp] theorem extend_smul {R : ℝ} (c : ℂ) (f : C(Disk R, ℂ)) :
    extend (c • f) = c • extend f := by
  funext z
  by_cases hz : z ∈ closedBall (0 : ℂ) R <;> simp [extend, hz]

/-- The zero-constant-term disk algebra, with the inherited supremum norm. -/
def space (R : ℝ) : Submodule ℂ C(Disk R, ℂ) where
  carrier := {f | DifferentiableOn ℂ (extend f) (ball 0 R) ∧ extend f 0 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    exact ⟨by simpa only [extend_add] using hf.1.add hg.1,
      by simp only [extend_add, Pi.add_apply, hf.2, hg.2, add_zero]⟩
  smul_mem' := by
    intro c f hf
    exact ⟨by simpa only [extend_smul] using hf.1.const_smul c,
      by simp only [extend_smul, Pi.smul_apply, hf.2, smul_zero]⟩

theorem extend_tendstoUniformlyOn {R : ℝ} {a : ℕ → C(Disk R, ℂ)}
    {f : C(Disk R, ℂ)} (ht : Tendsto a atTop (𝓝 f)) :
    TendstoUniformlyOn (fun n => extend (a n)) (extend f) atTop (closedBall 0 R) := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  simpa only [Function.comp_def, extend_apply] using
    (ContinuousMap.tendsto_iff_tendstoUniformly.mp ht)

/-- Uniform limits retain holomorphy on the interior and the zero constant
term. This proves closedness in the actual continuous-function Banach space. -/
theorem space_isClosed (R : ℝ) : IsClosed (space R : Set C(Disk R, ℂ)) := by
  apply IsSeqClosed.isClosed
  intro a f ha ht
  have hu := extend_tendstoUniformlyOn ht
  refine ⟨(hu.mono ball_subset_closedBall).tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall (fun n => (ha n).1)) isOpen_ball, ?_⟩
  by_cases h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) R
  · have hz : Tendsto (fun n => extend (a n) 0) atTop (𝓝 (0 : ℂ)) := by
      simpa only [(ha _).2] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    exact tendsto_nhds_unique (hu.tendsto_at h0) hz
  · simp [extend, h0]

instance completeSpace (R : ℝ) : CompleteSpace (space R) :=
  (space_isClosed R).isComplete.completeSpace_coe

instance secondCountableTopology (R : ℝ) : SecondCountableTopology (space R) :=
  inferInstanceAs (SecondCountableTopology ↥(space R : Set C(Disk R, ℂ)))

instance separableSpace (R : ℝ) : TopologicalSpace.SeparableSpace (space R) := inferInstance

/-- The actual Fourier series of an original solution belongs to this
Banach disk algebra for every radius strictly between zero and one. -/
theorem diskMap_mem (N k : ℕ) (f : S N k)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) : diskMap k R f.val ∈ space R := by
  have ha := FinitenessOriginalDiskIndependence.polynomial N k f
  have he (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R) :
      extend (diskMap k R f.val) z =
        FinitenessPolynomialSeries.sum (fullCoefficients f.val k) z := by
    rw [extend, dite_eq_left hz]
    exact FinitenessAllLevelTopology.polynomial_diskSeries_apply ha hR.le hR1 ⟨z, hz⟩
  refine ⟨?_, ?_⟩
  · apply ((FinitenessPolynomialSeries.holomorphic ha).mono
      (ball_subset_ball hR1.le)).congr
    intro z hz
    exact he z (ball_subset_closedBall hz)
  · rw [he 0 (by simpa using hR.le)]
    exact FinitenessPolynomialSeries.zero (fullCoefficients_zero f.property.zero k)

def representative (N k : ℕ) {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (f : S N k) : space R := ⟨diskMap k R f.val, diskMap_mem N k f hR hR1⟩

theorem representative_continuous {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (hgood : ¬ p ∣ N) (hlarge : N < p ^ 2) (m : ℕ)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    Continuous (representative N (2 * m) hR hR1) :=
  (FinitenessAllLevelTopology.disk_continuous hN hp hgood hlarge m hR.le hR1).subtype_mk _

theorem representative_injective (N k : ℕ) {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    Function.Injective (representative N k hR hR1) := by
  intro f g he
  exact FinitenessAllLevelTopology.disk_injective N k hR hR1 (congrArg Subtype.val he)

#print axioms space_isClosed
#print axioms completeSpace
#print axioms diskMap_mem
#print axioms representative_continuous
#print axioms representative_injective

end FinitenessAllLevelDiskAlgebra
