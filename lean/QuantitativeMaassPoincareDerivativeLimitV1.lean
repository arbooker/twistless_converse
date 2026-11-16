module

public import QuantitativeMaassPoincareGradientSumV1
public import QuantitativeMaassOrbitDerivativeMeasureV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff MatrixGroups

namespace QuantitativeMaass
open MaassDifferential

theorem integralCuspChart_contDiffOn (s : SL(2,ℤ)) :
    ContDiffOn ℝ ∞ (integralCuspChart s) {Z : Point | 0<Z.2} := by
  unfold integralCuspChart
  split_ifs
  · exact (affineChart_smooth _ _).contDiffOn
  · exact (affineChart_smooth _ _).comp_contDiffOn
      ((F_contDiffOn (by norm_num : (0:ℝ)<1)).comp (affineChart_smooth _ _).contDiffOn
        (fun Z hZ => by
          change 0<1*Z.2
          simpa only [one_mul] using (show 0<Z.2 from hZ)))

/-- A common local finite sum represents all seeds with the prescribed support,
without any differentiability hypothesis on the seeds. -/
theorem compact_poincare_common_local_sum (N : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (Z : Point) (hZ : 0<Z.2) :
    ∃ T : Finset (gamma N),∀ f : Point → ℂ,tsupport (upperFunction f)⊆K →
      congruencePoincareCartesian N f=ᶠ[𝓝 Z]
        fun W => ∑ g∈T,f (integralCuspChart (representative g) W) := by
  classical
  obtain ⟨T,U,hU,hT⟩ := compact_orbit_locally_finite (G := gamma N) K hK (cartesianLift Z)
  refine ⟨T,?_⟩
  intro f hf
  have hout (y : ℍ) (hy : y∈U) (g : gamma N) (hg : g∉T) : upperFunction f (g•y)=0 := by
    by_contra hn
    exact hT y hy g hg (hf (subset_tsupport _ hn))
  filter_upwards [(cartesianLift_continuousAt Z hZ).preimage_mem_nhds hU,
    (isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hW hpos
  change poincareSum (G := gamma N) (upperFunction f) (cartesianLift W)=_
  rw [show poincareSum (G := gamma N) (upperFunction f) (cartesianLift W)=
    ∑ g∈T,upperFunction f (g•cartesianLift W) from tsum_eq_sum (hout _ hW)]
  exact Finset.sum_congr rfl (fun g _ => congruence_pullback_cartesian N f g W hpos)

/-- Convergence of actual seed derivatives at every orbit point gives convergence
of the actual derivative of the periodization, using one local finite sum. -/
theorem compact_poincare_fderiv_tendsto (N : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (u : ℕ → Point → ℂ) (f : Point → ℂ)
    (hus : ∀ n,tsupport (upperFunction (u n))⊆K) (hfs : tsupport (upperFunction f)⊆K)
    (Z : Point) (hZ : 0<Z.2)
    (hu : ∀ n (g : gamma N),DifferentiableAt ℝ (u n) (integralCuspChart (representative g) Z))
    (hf : ∀ g : gamma N,DifferentiableAt ℝ f (integralCuspChart (representative g) Z))
    (ht : ∀ g : gamma N,Tendsto (fun n => fderiv ℝ (u n) (integralCuspChart (representative g) Z))
      atTop (𝓝 (fderiv ℝ f (integralCuspChart (representative g) Z)))) :
    Tendsto (fun n => fderiv ℝ (congruencePoincareCartesian N (u n)) Z)
      atTop (𝓝 (fderiv ℝ (congruencePoincareCartesian N f) Z)) := by
  classical
  obtain ⟨T,hT⟩ := compact_poincare_common_local_sum N K hK Z hZ
  have hc (g : gamma N) : DifferentiableAt ℝ (integralCuspChart (representative g)) Z :=
    ((integralCuspChart_contDiffOn (representative g)).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hZ)).differentiableAt (by simp)
  have he (v : Point → ℂ) (hvs : tsupport (upperFunction v)⊆K)
      (hvd : ∀ g : gamma N,DifferentiableAt ℝ v (integralCuspChart (representative g) Z)) :
      fderiv ℝ (congruencePoincareCartesian N v) Z=
        ∑ g∈T,(fderiv ℝ v (integralCuspChart (representative g) Z)).comp
          (fderiv ℝ (integralCuspChart (representative g)) Z) := by
    rw [(hT v hvs).fderiv_eq]
    rw [fderiv_fun_sum (u := T) (A := fun g W => v (integralCuspChart (representative g) W))
      (fun g _ => (hvd g).comp Z (hc g))]
    exact Finset.sum_congr rfl (fun g _ => fderiv_comp Z (hvd g) (hc g))
  simp_rw [he (u _) (hus _) (hu _),he f hfs hf]
  apply tendsto_finsetSum
  intro g _
  have hh : Continuous (fun D : Point →L[ℝ] ℂ =>
      D.comp (fderiv ℝ (integralCuspChart (representative g)) Z)) := by
    fun_prop
  exact hh.continuousAt.tendsto.comp (ht g)

#print axioms integralCuspChart_contDiffOn
#print axioms compact_poincare_common_local_sum
#print axioms compact_poincare_fderiv_tendsto

end QuantitativeMaass
