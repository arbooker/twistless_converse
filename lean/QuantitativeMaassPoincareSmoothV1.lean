module

public import QuantitativeMaassPoincareLocalV1
public import QuantitativeMaassCuspDifferentialV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set Filter Matrix UpperHalfPlane
open scoped Topology ContDiff MatrixGroups

namespace QuantitativeMaass
open MaassDifferential

/-- A total chart map, used only at positive height below. -/
def cartesianLift (Z : Point) : ℍ := UpperHalfPlane.ofComplex ⟨Z.1,Z.2⟩

theorem cartesianLift_positive (Z : Point) (hZ : 0<Z.2) :
    cartesianLift Z=horocyclePoint Z.1 Z.2 hZ := by
  exact ofComplex_apply_of_im_pos (z := (⟨Z.1,Z.2⟩:ℂ)) hZ

theorem cartesianLift_continuousAt (Z : Point) (hZ : 0<Z.2) :
    ContinuousAt cartesianLift Z := by
  have hc : Continuous (fun W : Point => (⟨W.1,W.2⟩:ℂ)) := by
    have he : (fun W : Point => (⟨W.1,W.2⟩:ℂ))=
        (fun W : Point => (W.1:ℂ)+(W.2:ℂ)*Complex.I) := by
      funext W
      apply Complex.ext <;> simp
    rw [he]
    fun_prop
  rw [ContinuousAt,nhds_induced,tendsto_comap_iff]
  rw [cartesianLift_positive Z hZ]
  apply Tendsto.congr' _ hc.continuousAt
  filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hW
  exact (congrArg UpperHalfPlane.coe
    (ofComplex_apply_of_im_pos (z := (⟨W.1,W.2⟩:ℂ)) hW)).symm

theorem upperFunction_integral_action (u : Point → ℂ) (s : SL(2,ℤ))
    (Z : Point) (hZ : 0<Z.2) :
    upperFunction u (s • cartesianLift Z)=u (integralCuspChart s Z) := by
  rw [cartesianLift_positive Z hZ]
  unfold upperFunction
  rw [integralCuspChart_action s Z.1 Z.2 hZ]
  rfl

/-- Literal automorphic periodization of a Cartesian seed. -/
def poincareCartesian (H : Subgroup SL(2,ℤ)) (u : Point → ℂ) (Z : Point) : ℂ :=
  poincareSum (G := H) (upperFunction u) (cartesianLift Z)

/-- Every positive-height neighborhood sees only finitely many actual
integral chart pullbacks of a compact seed. -/
theorem poincareCartesian_eventually_finite (H : Subgroup SL(2,ℤ))
    (u : Point → ℂ) (hu : HasCompactSupport (upperFunction u))
    (Z : Point) (hZ : 0<Z.2) :
    ∃ S : Finset H, poincareCartesian H u =ᶠ[𝓝 Z]
      fun W => ∑ g∈S, u (integralCuspChart g.val W) := by
  obtain ⟨S,hS⟩ := poincareSum_eventually_finite (G := H) (upperFunction u) hu (cartesianLift Z)
  refine ⟨S,?_⟩
  filter_upwards [hS.comp_tendsto (cartesianLift_continuousAt Z hZ),
    (isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hsum hW
  change poincareSum (G := H) (upperFunction u) (cartesianLift W)=_
  dsimp only [Function.comp_apply] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro g _
  exact upperFunction_integral_action u g.val W hW

/-- Genuine smooth automorphic test functions are constructed from compact
smooth seeds; smoothness follows from a proved locally finite sum, without
assuming convergence or differentiability of a Poincaré series. -/
theorem poincareCartesian_smooth (H : Subgroup SL(2,ℤ)) {u : Point → ℂ}
    (hu : ContDiffOn ℝ ∞ u {Z | 0<Z.2}) (hc : HasCompactSupport (upperFunction u)) :
    ContDiffOn ℝ ∞ (poincareCartesian H u) {Z | 0<Z.2} := by
  have hs : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  rw [hs.contDiffOn_iff]
  intro Z hZ
  obtain ⟨S,hS⟩ := poincareCartesian_eventually_finite H u hc Z hZ
  apply ContDiffAt.congr_of_eventuallyEq _ hS
  exact ((ContDiffOn.sum (s := S) fun g _ =>
    integralCuspChart_pullback_smooth g.val hu).contDiffAt (hs.mem_nhds hZ))

theorem poincareCartesian_represents (H : Subgroup SL(2,ℤ)) (u : Point → ℂ) (z : ℍ) :
    upperFunction (poincareCartesian H u) z=poincareSum (G := H) (upperFunction u) z := by
  unfold upperFunction poincareCartesian
  rw [cartesianLift_positive _ z.im_pos]
  rfl

theorem poincareCartesian_automorphic (H : Subgroup SL(2,ℤ)) (u : Point → ℂ)
    (g : H) (z : ℍ) :
    upperFunction (poincareCartesian H u) (g • z)=upperFunction (poincareCartesian H u) z := by
  rw [poincareCartesian_represents,poincareCartesian_represents]
  exact poincareSum_invariant (upperFunction u) g z

#print axioms poincareCartesian_smooth
#print axioms poincareCartesian_automorphic

end QuantitativeMaass
