module

public import QuantitativeMaassPacketCompositionV1
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Ordinary derivatives are uniformly bounded strictly inside the physical
half-line. No assertion about the ordinary derivative at its boundary is used. -/
theorem physical_derivative_bound (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (B : ℝ) (hs : Function.support F⊆Iic B) :
    ∃ C : ℝ,0<C ∧ ∀ q : ℝ,1<q → ‖deriv F q‖≤C := by
  have hc : ContinuousOn (derivWithin F (Ici 1)) (Icc 1 (B+1)) :=
    (hF.continuousOn_derivWithin (uniqueDiffOn_Ici (1:ℝ)) (by simp)).mono
      (fun _ hx => hx.1)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 0+1,by positivity,?_⟩
  intro q hq
  by_cases hqB : q≤B+1
  · have hb := hC q ⟨hq.le,hqB⟩
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds hq)] at hb
    exact hb.trans (by linarith [le_max_left C 0])
  · have hd : Function.support (deriv F)⊆Iic B :=
      support_deriv_subset.trans (closure_minimal hs isClosed_Iic)
    have hz : deriv F q=0 := by
      by_contra hn
      have := hd hn
      change q≤B at this
      linarith
    rw [hz,norm_zero]
    positivity

/-- The literal Abel profile is continuous up to q=1 from the physical side.
A fixed finite integration interval and a uniform derivative bound justify DCT. -/
theorem abelProfile_continuousOn_physical (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (B : ℝ) (hB : 1≤B)
    (hs : Function.support F⊆Iic B) : ContinuousOn (abelProfile F) (Ici 1) := by
  have hd : Function.support (deriv F)⊆Iic B :=
    support_deriv_subset.trans (closure_minimal hs isClosed_Iic)
  obtain ⟨C,_,hC⟩ := physical_derivative_bound F hF B hs
  intro q hq
  have hm (u : ℝ) : AEStronglyMeasurable (fun s : ℝ => deriv F (u+s^2))
      (volume.restrict (Ioc (0:ℝ) (B+1))) :=
    ((measurable_deriv F).comp (by fun_prop)).aestronglyMeasurable
  have hb : ∀ᶠ u in 𝓝[Ici 1] q,∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) (B+1)),
      ‖deriv F (u+s^2)‖≤C := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs0
    exact hC (u+s^2) (by have : 1≤u := hu; nlinarith [sq_pos_of_pos hs0.1])
  have hl : ∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) (B+1)),Tendsto
      (fun u : ℝ => deriv F (u+s^2)) (𝓝[Ici 1] q) (𝓝 (deriv F (q+s^2))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs0
    have hv : 1<q+s^2 := by have : 1≤q := hq; nlinarith [sq_pos_of_pos hs0.1]
    have hc := (hF.mono Ioi_subset_Ici_self).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by simp)
    exact ((hc _ hv).continuousAt (Ioi_mem_nhds hv)).tendsto.comp
      ((continuousAt_id.add continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds)
  have hi : Integrable (fun _ : ℝ => C) (volume.restrict (Ioc (0:ℝ) (B+1))) :=
    integrableOn_const (by simp)
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    (Eventually.of_forall hm) hb hi hl
  have hI : Tendsto (abelIntegral (deriv F)) (𝓝[Ici 1] q)
      (𝓝 (abelIntegral (deriv F) q)) := by
    rw [abelIntegral_physical_interval _ B hB hd q hq]
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (abelIntegral_physical_interval _ B hB hd u hu).symm
  exact hI.const_mul _

/-- Compact physical radial profiles give a jointly continuous literal
periodized kernel. Proper discontinuity makes one finite translate set work
throughout a neighborhood in BOTH variables. -/
theorem radialPoincareKernel_joint_continuous_physical (N : ℕ) (g : ℝ → ℂ)
    (hg : ContinuousOn g (Ici 1)) (R : ℝ) (hR : 0≤R)
    (hs : Function.support g⊆Iic (Real.cosh R)) :
    Continuous (fun p : ℍ×ℍ => radialPoincareKernel N g p.1 p.2) := by
  classical
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun γ => AsymptoticRationalBranches.action_continuous γ.val⟩
  have hc (γ : gamma N) : Continuous (fun p : ℍ×ℍ =>
      g (Real.cosh (dist (γ•p.2) p.1))) :=
    hg.comp_continuous (Real.continuous_cosh.comp
      (((continuous_const_smul γ).comp continuous_snd).dist continuous_fst))
      (fun _ => Real.one_le_cosh _)
  apply continuous_iff_continuousAt.mpr
  intro p
  let hf := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
    (Γ:=gamma N) (isCompact_closedBall p.2 (1:ℝ)) (isCompact_closedBall p.1 (R+1))
  let S := hf.toFinset
  have he : (fun a : ℍ×ℍ => radialPoincareKernel N g a.1 a.2)=ᶠ[𝓝 p]
      (fun a => ∑ γ∈S,g (Real.cosh (dist (γ•a.2) a.1))) := by
    filter_upwards [continuous_fst.continuousAt (Metric.ball_mem_nhds p.1 zero_lt_one),
      continuous_snd.continuousAt (Metric.ball_mem_nhds p.2 zero_lt_one)] with a ha1 ha2
    change dist a.1 p.1<1 at ha1
    change dist a.2 p.2<1 at ha2
    simp only [radialPoincareKernel,poincareSum,radialFunction_upper]
    apply tsum_eq_sum
    intro γ hγ
    by_contra hn
    have hb : dist (γ•a.2) a.1≤R := by
      have hh := Real.cosh_le_cosh.mp (hs hn)
      simpa only [abs_of_nonneg dist_nonneg,abs_of_nonneg hR] using hh
    apply hγ
    apply hf.mem_toFinset.mpr
    refine ⟨γ•a.2,⟨a.2,Metric.mem_closedBall.mpr ha2.le,rfl⟩,?_⟩
    exact (dist_triangle (γ•a.2) a.1 p.1).trans
      (add_le_add hb ha1.le)
  apply ContinuousAt.congr_of_eventuallyEq _ he
  exact (continuous_finsetSum S fun γ _ => hc γ).continuousAt

/-- In particular the original one-sided Abel kernel is jointly continuous,
including its geometric diagonal. This does not yet assert a trace identity. -/
theorem oneSidedAbelKernel_joint_continuous (N : ℕ) (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (R : ℝ) (hR : 0≤R)
    (hs : Function.support F⊆Iic (Real.cosh R)) :
    Continuous (fun p : ℍ×ℍ => radialPoincareKernel N (abelProfile F) p.1 p.2) :=
  radialPoincareKernel_joint_continuous_physical N _
    (abelProfile_continuousOn_physical F hF _ (Real.one_le_cosh R) hs)
    R hR (abelProfile_support F _ hs)

#print axioms physical_derivative_bound
#print axioms abelProfile_continuousOn_physical
#print axioms radialPoincareKernel_joint_continuous_physical
#print axioms oneSidedAbelKernel_joint_continuous

end QuantitativeMaass
