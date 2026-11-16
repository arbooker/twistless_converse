module
public import QuantitativeArithmeticMaassModularHeightV1
public import QuantitativeMaassEnergyCovarianceV1
public import QuantitativeMaassWeightedCutoffV1
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticCongruenceLabels
open scoped MatrixGroups Topology ContDiff
namespace QuantitativeArithmeticMaassModularHeight
open QuantitativeMaass MaassDifferential

def profile (ψ : ℝ → ℂ) (Z : Point) : ℂ := ψ (height (cartesianLift Z))

theorem upper_profile (ψ : ℝ → ℂ) (z : ℍ) :
    upperFunction (profile ψ) z=ψ (height z) := by
  unfold upperFunction profile
  rw [cartesianLift_positive _ z.im_pos]
  rfl

theorem profile_invariant (ψ : ℝ → ℂ) (g : SL(2,ℤ)) (z : ℍ) :
    upperFunction (profile ψ) (g•z)=upperFunction (profile ψ) z := by
  rw [upper_profile,upper_profile,height_invariant]

/-- Every point has an actual integral cusp chart in which the invariant
profile agrees locally with the ordinary height profile. -/
theorem profile_local_chart (ψ : ℝ → ℂ) (hψ : ∀ y, y≤2 → ψ y=0)
    (Z : Point) (hZ : 0<Z.2) : ∃ g : SL(2,ℤ),
    profile ψ =ᶠ[𝓝 Z] (fun W => ψ W.2) ∘ integralCuspChart g := by
  obtain ⟨g,hg⟩ := exists_high_chart (cartesianLift Z)
  refine ⟨g,?_⟩
  have hact : Continuous (fun z : ℍ => g•z) := by
    simpa only [integralLabel_action] using AsymptoticRationalBranches.action_continuous (integralLabel g)
  have hc : ContinuousAt (fun W : Point => (g•cartesianLift W).im) Z :=
    continuous_im.continuousAt.comp
      (hact.continuousAt.comp (cartesianLift_continuousAt Z hZ))
  have hn := hc.eventually (Ioi_mem_nhds hg)
  filter_upwards [hn,(isOpen_lt continuous_const continuous_snd).mem_nhds hZ] with W hh hw
  change ψ (height (cartesianLift W))=ψ (integralCuspChart g W).2
  rw [← height_invariant g (cartesianLift W),profile_eq ψ hψ _ hh]
  exact upperFunction_integral_action (fun V : Point => ψ V.2) g W hw

theorem profile_smooth (ψ : ℝ → ℂ) (hψ : ∀ y, y≤2 → ψ y=0)
    (hs : ContDiff ℝ ∞ ψ) : ContDiffOn ℝ ∞ (profile ψ) {Z | 0<Z.2} := by
  have ho : IsOpen {Z : Point | 0<Z.2} := isOpen_lt continuous_const continuous_snd
  rw [ho.contDiffOn_iff]
  intro Z hZ
  obtain ⟨g,hg⟩ := profile_local_chart ψ hψ Z hZ
  apply ContDiffAt.congr_of_eventuallyEq _ hg
  exact (integralCuspChart_pullback_smooth g
    (hs.comp_contDiffOn contDiffOn_snd)).contDiffAt (ho.mem_nhds hZ)

/-- The energy bound reduces to a one-variable height profile, without
loss in its constant under the modular change of chart. -/
theorem profile_energy_bound (ψ : ℝ → ℂ) (hψ : ∀ y, y≤2 → ψ y=0)
    (hs : ContDiff ℝ ∞ ψ) {G : ℝ}
    (hG : ∀ Z : Point, 0<Z.2 →
      (hyperbolicEnergy (fun W : Point => ψ W.2) (fun W : Point => ψ W.2) Z).re≤G^2)
    (z : ℍ) : (upperEnergy (profile ψ) (profile ψ) z).re≤G^2 := by
  obtain ⟨g,hg⟩ := profile_local_chart ψ hψ (z.re,z.im) z.im_pos
  unfold upperEnergy upperFunction
  rw [hyperbolicEnergy_congr_left hg,hyperbolicEnergy_congr_right hg]
  have he := hyperbolicEnergy_integralCuspChart g
    (hs.comp_contDiffOn contDiffOn_snd) (hs.comp_contDiffOn contDiffOn_snd)
    (Z := (z.re,z.im)) z.im_pos
  simp only [Function.comp_def] at he ⊢
  rw [he]
  exact hG _ (integralCuspChart_pos g (z.re,z.im) z.im_pos)

/-- Exact hyperbolic energy of a one-variable height profile. -/
theorem vertical_energy_eq (ψ : ℝ → ℂ) (hs : ContDiff ℝ ∞ ψ) (Z : Point) :
    (hyperbolicEnergy (fun W : Point => ψ W.2) (fun W : Point => ψ W.2) Z).re=
      Z.2^2*‖deriv ψ Z.2‖^2 := by
  have hd := ((hs.differentiable (by simp) Z.2).hasDerivAt.hasFDerivAt.comp Z
    (hasFDerivAt_snd (𝕜 := ℝ) (p := Z))).fderiv
  simp only [Function.comp_def] at hd
  have hx : X (fun W : Point => ψ W.2) Z=0 := by
    unfold X dir D
    rw [hd]
    simp [e₁]
  have hy : Y (fun W : Point => ψ W.2) Z=deriv ψ Z.2 := by
    unfold Y dir D
    rw [hd]
    simp [e₂]
  rw [hyperbolicEnergy_self_eq,hx,hy]
  simp

/-- A genuine smooth invariant cutoff on every congruence quotient, built
from scalar data. No invariant function or gradient bound is assumed. -/
def cuspCutoff (N : ℕ) (ψ : ℝ → ℂ) (hψ : ∀ y, y≤2 → ψ y=0)
    (hs : ContDiff ℝ ∞ ψ) (hr : ∀ y, star (ψ y)=ψ y)
    (B : ℝ) (hB : 0≤B) (hb : ∀ y, ‖ψ y‖≤B) (G : ℝ)
    (hG : ∀ y : ℝ, 0<y → y^2*‖deriv ψ y‖^2≤G^2) : Weighted.Cutoff N where
  value := profile ψ
  smooth := profile_smooth ψ hψ hs
  invariant := by
    intro g z
    have he : representative g • z=g•z := by
      rw [← integralLabel_action,representative_label]
      rfl
    rw [← he]
    exact profile_invariant ψ (representative g) z
  real := fun Z => hr _
  bound := B
  bound_nonneg := hB
  value_bound := fun z => by rw [upper_profile]; exact hb _
  gradientBound := G
  gradient_bound := profile_energy_bound ψ hψ hs (fun Z hZ => by
    rw [vertical_energy_eq ψ hs];exact hG Z.2 hZ)

#print axioms vertical_energy_eq
#print axioms cuspCutoff
#print axioms profile_invariant
#print axioms profile_smooth
#print axioms profile_energy_bound
end QuantitativeArithmeticMaassModularHeight
