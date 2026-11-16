module

public import QuantitativeMaassEnergyLocalizationV1
public import QuantitativeMaassPoincareFixedSupportV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- An orbit term whose image is outside the seed support has zero derivative. -/
theorem congruence_pullback_dir_zero (N : ℕ) (u : Point → ℂ) (g : gamma N)
    {Z : Point} (hZ : 0<Z.2)
    (hz : g•cartesianLift Z∉tsupport (upperFunction u)) (w : Point) :
    dir w (u ∘ integralCuspChart (representative g)) Z=0 := by
  have ht : Tendsto (fun W => g•cartesianLift W) (𝓝 Z) (𝓝 (g•cartesianLift Z)) :=
    ((AsymptoticRationalBranches.action_continuous g.val).continuousAt.comp
      (cartesianLift_continuousAt Z hZ)).tendsto
  have he := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto ht
  have he' : (u ∘ integralCuspChart (representative g))=ᶠ[𝓝 Z] 0 := by
    filter_upwards [he,(isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hW hpos
    change u (integralCuspChart (representative g) W)=0
    rw [←congruence_pullback_cartesian N u g W hpos]
    exact hW
  unfold dir D
  rw [he'.fderiv_eq]
  simp

/-- The pointwise derivative sum uses only the actual compact orbit overlap,
so one cardinality bound works for all smooth seeds in the fixed compact set. -/
theorem compact_poincare_derivative_sum (N : ℕ) (K : Set ℍ) (hK : IsCompact K) :
    ∃ M : ℕ,∀ (u : SmoothUpperSeed),tsupport (upperFunction u.toFun)⊆K →
      ∀ Z : Point,0<Z.2 → ∃ S : Finset (gamma N),S.card≤M ∧
        (∀ w : Point,dir w (congruencePoincareCartesian N u.toFun) Z=
          ∑ g∈S,dir w (u.toFun ∘ integralCuspChart (representative g)) Z) ∧
        (∀ g∉S,g•cartesianLift Z∉K) := by
  classical
  obtain ⟨M,hM⟩ := compact_orbit_overlap (G := gamma N) K hK
  refine ⟨M,?_⟩
  intro u hu Z hZ
  let hfin := compact_orbit_point_finite (G := gamma N) K hK (cartesianLift Z)
  let S := hfin.toFinset
  have hS (g : gamma N) : g∈S ↔ g•cartesianLift Z∈K := hfin.mem_toFinset
  obtain ⟨T,U,hU,hT⟩ := compact_orbit_locally_finite (G := gamma N) K hK (cartesianLift Z)
  have hST : S⊆T := by
    intro g hg
    by_contra hn
    exact hT _ (mem_of_mem_nhds hU) g hn ((hS g).mp hg)
  have hout (y : ℍ) (hy : y∈U) (g : gamma N) (hg : g∉T) :
      upperFunction u.toFun (g•y)=0 := by
    by_contra hn
    exact hT y hy g hg (hu (subset_tsupport _ hn))
  have he : congruencePoincareCartesian N u.toFun =ᶠ[𝓝 Z]
      fun W => ∑ g∈T,u.toFun (integralCuspChart (representative g) W) := by
    filter_upwards [(cartesianLift_continuousAt Z hZ).preimage_mem_nhds hU,
      (isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hW hpos
    change poincareSum (G := gamma N) (upperFunction u.toFun) (cartesianLift W)=_
    rw [show poincareSum (G := gamma N) (upperFunction u.toFun) (cartesianLift W)=
      ∑ g∈T,upperFunction u.toFun (g•cartesianLift W) from tsum_eq_sum (hout _ hW)]
    exact Finset.sum_congr rfl (fun g _ => congruence_pullback_cartesian N u.toFun g W hpos)
  refine ⟨S,hM _ S (fun g hg => (hS g).mp hg),?_,fun g hg => mt (hS g).mpr hg⟩
  intro w
  calc
    dir w (congruencePoincareCartesian N u.toFun) Z=
        dir w (fun W => ∑ g∈T,u.toFun (integralCuspChart (representative g) W)) Z := by
      unfold dir D
      rw [he.fderiv_eq]
    _ = ∑ g∈T,dir w (u.toFun ∘ integralCuspChart (representative g)) Z :=
      dir_finset_sum T _ (isOpen_lt continuous_const continuous_snd)
        (fun g _ => integralCuspChart_pullback_smooth (representative g) u.smooth) hZ w
    _ = ∑ g∈S,dir w (u.toFun ∘ integralCuspChart (representative g)) Z := by
      symm
      apply Finset.sum_subset hST
      intro g _ hg
      exact congruence_pullback_dir_zero N u.toFun g hZ
        (fun h => hg ((hS g).mpr (hu h))) w

#print axioms congruence_pullback_dir_zero
#print axioms compact_poincare_derivative_sum

end QuantitativeMaass
