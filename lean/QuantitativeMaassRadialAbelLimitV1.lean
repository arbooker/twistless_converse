module

public import QuantitativeMaassRadialShiftLimitV1
public import QuantitativeMaassAbelOperatorBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- A common finite integration interval on the physical radial half-line. -/
theorem abelIntegral_physical_interval (g : ℝ → ℂ) (B : ℝ) (hB : 1≤B)
    (hs : Function.support g⊆Iic B) (q : ℝ) (hq : 1≤q) :
    abelIntegral g q=∫ s in Ioc (0:ℝ) (B+1),g (q+s^2) := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun _ h => h.1)
  intro s hs'
  have hhigh : B+1<s := by
    by_contra hn
    exact hs'.2 ⟨hs'.1,le_of_not_gt hn⟩
  by_contra hn
  have hh : q+s^2≤B := hs hn
  nlinarith [sq_nonneg (s-1)]

/-- No bound below q=1 is needed in the Abel integral. -/
theorem abelIntegral_norm_bound_physical (g : ℝ → ℂ) (B C : ℝ) (hB : 1≤B)
    (hs : Function.support g⊆Iic B) (hb : ∀ q,1≤q → ‖g q‖≤C)
    (q : ℝ) (hq : 1≤q) : ‖abelIntegral g q‖≤C*(B+1) := by
  rw [abelIntegral_physical_interval g B hB hs q hq]
  have h := norm_setIntegral_le_of_norm_le_const (μ:=volume) (s:=Ioc (0:ℝ) (B+1))
    (f:=fun s => g (q+s^2)) (by simp) (fun s _ => hb (q+s^2) (by nlinarith [sq_nonneg s]))
  simpa only [Real.volume_real_Ioc_of_le (by linarith : 0≤B+1),sub_zero] using h

theorem abelProfile_norm_bound_physical (F : ℝ → ℂ) (B C : ℝ) (hB : 1≤B)
    (hs : Function.support F⊆Iic B) (hb : ∀ q,1≤q → ‖deriv F q‖≤C)
    (q : ℝ) (hq : 1≤q) :
    ‖abelProfile F q‖≤(Real.sqrt 2/Real.pi)*(C*(B+1)) := by
  have hd : Function.support (deriv F)⊆Iic B :=
    support_deriv_subset.trans (closure_minimal hs isClosed_Iic)
  have h := abelIntegral_norm_bound_physical (deriv F) B C hB hd hb q hq
  rw [abelProfile,norm_mul,norm_neg]
  have hn : ‖(Real.sqrt 2/Real.pi:ℂ)‖=Real.sqrt 2/Real.pi := by
    rw [← Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le)]
  rw [hn]
  exact mul_le_mul_of_nonneg_left h (div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le)

/-- The actual Abel profiles converge at every physical radial coordinate,
including q=1. The target uses the ordinary derivative of the original F;
the integration variable is strictly positive, so no extension at q=1 is assumed. -/
theorem radialShiftAbelProfile_tendsto {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (B : ℝ) (hB : 1≤B) (hs : Function.support F⊆Iic B)
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) (q : ℝ) (hq : 1≤q) :
    Tendsto (fun i => abelProfile (radialShiftApprox F (a i)) q) l (𝓝 (abelProfile F q)) := by
  have hz : ∀ x,B<x → F x=0 := by
    intro x hx
    by_contra hn
    exact (not_le_of_gt hx) (hs hn)
  have hs' (i : ι) : Function.support (deriv (radialShiftApprox F (a i)))⊆Iic B :=
    support_deriv_subset.trans (closure_minimal
      (radialShiftApprox_upper_support F B hz _ (ha i)) isClosed_Iic)
  have hd : Function.support (deriv F)⊆Iic B :=
    support_deriv_subset.trans (closure_minimal hs isClosed_Iic)
  obtain ⟨C,_,hC⟩ := radialShiftApprox_uniform_derivative_bound F hF B hz 1
  have hm (i : ι) : AEStronglyMeasurable (fun s : ℝ =>
      deriv (radialShiftApprox F (a i)) (q+s^2)) (volume.restrict (Ioc (0:ℝ) (B+1))) :=
    (((contDiff_infty_iff_deriv.mp (radialShiftApprox_smooth F hF _ (ha i))).2.continuous).comp
      (by fun_prop)).aestronglyMeasurable
  have hb : ∀ᶠ i in l,∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) (B+1)),
      ‖deriv (radialShiftApprox F (a i)) (q+s^2)‖≤C := by
    filter_upwards [(tendsto_order.1 ha0).2 1 (by norm_num)] with i hi
    filter_upwards with s
    simpa only [iteratedDeriv_one] using hC (a i) (ha i) hi.le (q+s^2)
      (by nlinarith [sq_nonneg s])
  have hl : ∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) (B+1)),Tendsto
      (fun i => deriv (radialShiftApprox F (a i)) (q+s^2)) l (𝓝 (deriv F (q+s^2))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs0
    have hv : 1<q+s^2 := by nlinarith [sq_pos_of_pos hs0.1]
    have heq : iteratedDerivWithin 1 F (Ici 1) (q+s^2)=iteratedDeriv 1 F (q+s^2) := by
      apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici (1:ℝ))
      · exact ((hF _ hv.le).contDiffAt (Ici_mem_nhds hv)).of_le (by simp)
      · exact hv.le
    simpa only [heq,iteratedDeriv_one] using
      radialShiftApprox_derivatives_tendsto l F hF a ha ha0 (q+s^2) hv.le 1
  have hi : Integrable (fun _ : ℝ => C) (volume.restrict (Ioc (0:ℝ) (B+1))) :=
    integrableOn_const (by simp)
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    (Eventually.of_forall hm) hb hi hl
  have hI : Tendsto (fun i => abelIntegral (deriv (radialShiftApprox F (a i))) q) l
      (𝓝 (abelIntegral (deriv F) q)) := by
    simpa only [abelIntegral_physical_interval _ B hB (hs' _) q hq,
      abelIntegral_physical_interval _ B hB hd q hq] using h
  exact hI.const_mul _


/-- The normalized Abel profiles have one physical-domain bound before a is chosen. -/
theorem radialShiftAbelProfile_uniform_bound (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ici 1)) (B : ℝ) (hB : 1≤B)
    (hs : Function.support F⊆Iic B) :
    ∃ D : ℝ,0<D ∧ ∀ a : ℝ,0<a → a≤1 → ∀ q : ℝ,1≤q →
      ‖abelProfile (radialShiftApprox F a) q‖≤D := by
  have hz : ∀ x,B<x → F x=0 := fun x hx => by
    by_contra hn
    exact (not_le_of_gt hx) (hs hn)
  obtain ⟨C,hC,hbound⟩ := radialShiftApprox_uniform_derivative_bound F hF B hz 1
  refine ⟨(Real.sqrt 2/Real.pi)*(C*(B+1)),by positivity,?_⟩
  intro a ha ha1 q hq
  exact abelProfile_norm_bound_physical _ B C hB
    (radialShiftApprox_upper_support F B hz a ha)
    (fun x hx => by simpa only [iteratedDeriv_one] using hbound a ha ha1 x hx) q hq

theorem radialProfile_energy_interval (g : ℝ → ℂ) (B : ℝ)
    (hs : Function.support g⊆Iic B) :
    (∫ q in Ioi (1:ℝ),‖g q‖^2)=∫ q in Ioc (1:ℝ) B,‖g q‖^2 := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun _ h => h.1)
  intro q hq
  have hhigh : B<q := by
    by_contra hn
    exact hq.2 ⟨hq.1,le_of_not_gt hn⟩
  have hz : g q=0 := by
    by_contra hn
    exact (not_le_of_gt hhigh) (hs hn)
  simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]

/-- Radial squared energies converge as genuine integrals, not by an
invalid appeal to operator-norm continuity of the trace. -/
theorem radialShiftAbelProfile_energy_tendsto {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (B : ℝ) (hB : 1≤B) (hs : Function.support F⊆Iic B)
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => ∫ q in Ioi (1:ℝ),‖abelProfile (radialShiftApprox F (a i)) q‖^2) l
      (𝓝 (∫ q in Ioi (1:ℝ),‖abelProfile F q‖^2)) := by
  have hz : ∀ x,B<x → F x=0 := fun x hx => by
    by_contra hn
    exact (not_le_of_gt hx) (hs hn)
  have hs' (i : ι) : Function.support (abelProfile (radialShiftApprox F (a i)))⊆Iic B :=
    abelProfile_support _ B (radialShiftApprox_upper_support F B hz _ (ha i))
  obtain ⟨D,hD,hbound⟩ := radialShiftAbelProfile_uniform_bound F hF B hB hs
  have hm (i : ι) : AEStronglyMeasurable (fun q : ℝ =>
      ‖abelProfile (radialShiftApprox F (a i)) q‖^2) (volume.restrict (Ioc (1:ℝ) B)) :=
    ((abelProfile_smooth _ (radialShiftApprox_smooth F hF _ (ha i))
      (radialShiftApprox_compact F B hz _ (ha i))).continuous.norm.pow 2).aestronglyMeasurable
  have hb : ∀ᶠ i in l,∀ᵐ q ∂volume.restrict (Ioc (1:ℝ) B),
      ‖‖abelProfile (radialShiftApprox F (a i)) q‖^2‖≤D^2 := by
    filter_upwards [(tendsto_order.1 ha0).2 1 (by norm_num)] with i hi
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound _ (ha i) hi.le q hq.1.le) 2
  have hl : ∀ᵐ q ∂volume.restrict (Ioc (1:ℝ) B),Tendsto
      (fun i => ‖abelProfile (radialShiftApprox F (a i)) q‖^2) l (𝓝 (‖abelProfile F q‖^2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    exact (radialShiftAbelProfile_tendsto l F hF B hB hs a ha ha0 q hq.1.le).norm.pow 2
  have hi : Integrable (fun _ : ℝ => D^2) (volume.restrict (Ioc (1:ℝ) B)) :=
    integrableOn_const (by simp)
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => D^2)
    (Eventually.of_forall hm) hb hi hl
  simpa only [radialProfile_energy_interval _ B (hs' _),
    radialProfile_energy_interval _ B (abelProfile_support F B hs)] using h

/-- Fixed compact support makes the periodization sum finite before the
approximation parameter is chosen. -/
theorem poincareSum_tendsto_compact {G A ι : Type*} [Group G] [TopologicalSpace A]
    [MulAction G A] [ProperlyDiscontinuousSMul G A] (l : Filter ι)
    (K : Set A) (hK : IsCompact K) (f : ι → A → ℂ) (g : A → ℂ)
    (hf : ∀ i,Function.support (f i)⊆K) (hg : Function.support g⊆K)
    (hl : ∀ x,Tendsto (fun i => f i x) l (𝓝 (g x))) (x : A) :
    Tendsto (fun i => poincareSum (G:=G) (f i) x) l (𝓝 (poincareSum (G:=G) g x)) := by
  classical
  let hS := compact_orbit_point_finite (G:=G) K hK x
  let S := hS.toFinset
  have he (u : A → ℂ) (hu : Function.support u⊆K) :
      poincareSum (G:=G) u x=∑ γ∈S,u (γ•x) := by
    apply tsum_eq_sum
    intro γ hγ
    by_contra hn
    exact hγ (hS.mem_toFinset.mpr (hu hn))
  simp only [he _ (hf _),he g hg]
  exact tendsto_finsetSum S (fun γ _ => hl (γ•x))

/-- Pointwise convergence of the actual periodized radial kernel. -/
theorem radialShiftAbelKernel_tendsto {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (N : ℕ) (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0))
    (x y : UpperHalfPlane) :
    Tendsto (fun i => radialPoincareKernel N (abelProfile (radialShiftApprox F (a i))) x y) l
      (𝓝 (radialPoincareKernel N (abelProfile F) x y)) := by
  have hz : ∀ q,Real.cosh R<q → F q=0 := fun q hq => by
    by_contra hn
    exact (not_le_of_gt hq) (hs hn)
  apply poincareSum_tendsto_compact (G:=gamma N) l (Metric.closedBall x R)
    (isCompact_closedBall x R)
  · intro i
    exact (subset_tsupport _).trans (radialFunction_support _ x R hR
      (abelProfile_support _ _ (radialShiftApprox_upper_support F _ hz _ (ha i))))
  · exact (subset_tsupport _).trans (radialFunction_support _ x R hR
      (abelProfile_support F _ hs))
  · intro z
    simp only [radialFunction_upper]
    exact radialShiftAbelProfile_tendsto l F hF _ (Real.one_le_cosh R) hs a ha ha0 _
      (Real.one_le_cosh _)


/-- Strong radial L2 approximation, with the domination and measurability
of the limiting profile derived from the approximants. -/
theorem radialShiftAbelProfile_L2_tendsto {ι : Type*} (l : Filter ι)
    [l.IsCountablyGenerated] [NeBot l]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (B : ℝ) (hB : 1≤B) (hs : Function.support F⊆Iic B)
    (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => ∫ q in Ioi (1:ℝ),
      ‖abelProfile (radialShiftApprox F (a i)) q-abelProfile F q‖^2) l (𝓝 0) := by
  have hz : ∀ x,B<x → F x=0 := fun x hx => by
    by_contra hn
    exact (not_le_of_gt hx) (hs hn)
  obtain ⟨D,hD,hbound⟩ := radialShiftAbelProfile_uniform_bound F hF B hB hs
  have hsmall : ∀ᶠ i in l,a i<1 := (tendsto_order.1 ha0).2 1 (by norm_num)
  have hm (i : ι) : AEStronglyMeasurable
      (abelProfile (radialShiftApprox F (a i))) (volume.restrict (Ioc (1:ℝ) B)) :=
    (abelProfile_smooth _ (radialShiftApprox_smooth F hF _ (ha i))
      (radialShiftApprox_compact F B hz _ (ha i))).continuous.aestronglyMeasurable
  have hl : ∀ᵐ q ∂volume.restrict (Ioc (1:ℝ) B),Tendsto
      (fun i => abelProfile (radialShiftApprox F (a i)) q) l (𝓝 (abelProfile F q)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    exact radialShiftAbelProfile_tendsto l F hF B hB hs a ha ha0 q hq.1.le
  have hmF : AEStronglyMeasurable (abelProfile F) (volume.restrict (Ioc (1:ℝ) B)) :=
    aestronglyMeasurable_of_tendsto_ae l hm hl
  have hbF (q : ℝ) (hq : 1≤q) : ‖abelProfile F q‖≤D := by
    apply le_of_tendsto (radialShiftAbelProfile_tendsto l F hF B hB hs a ha ha0 q hq).norm
    filter_upwards [hsmall] with i hi
    exact hbound _ (ha i) hi.le q hq
  have hb : ∀ᶠ i in l,∀ᵐ q ∂volume.restrict (Ioc (1:ℝ) B),
      ‖‖abelProfile (radialShiftApprox F (a i)) q-abelProfile F q‖^2‖≤(2*D)^2 := by
    filter_upwards [hsmall] with i hi
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have h := (norm_sub_le (abelProfile (radialShiftApprox F (a i)) q) (abelProfile F q)).trans
      (add_le_add (hbound _ (ha i) hi.le q hq.1.le) (hbF q hq.1.le))
    linarith
  have hlim : ∀ᵐ q ∂volume.restrict (Ioc (1:ℝ) B),Tendsto
      (fun i => ‖abelProfile (radialShiftApprox F (a i)) q-abelProfile F q‖^2) l (𝓝 (0:ℝ)) := by
    filter_upwards [hl] with q hq
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using
      (hq.sub_const (abelProfile F q)).norm.pow 2
  have hi : Integrable (fun _ : ℝ => (2*D)^2) (volume.restrict (Ioc (1:ℝ) B)) :=
    integrableOn_const (by simp)
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => (2*D)^2)
    (Eventually.of_forall (fun i => ((hm i).sub hmF).norm.pow 2)) hb hi hlim
  have hs' (i : ι) : Function.support (fun q =>
      abelProfile (radialShiftApprox F (a i)) q-abelProfile F q)⊆Iic B := by
    intro q hq
    by_contra hn
    have hzero (g : ℝ → ℂ) (hg : Function.support g⊆Iic B) : g q=0 := by
      by_contra hneq
      exact hn (hg hneq)
    exact hq (by
      dsimp only
      rw [hzero _ (abelProfile_support _ _
      (radialShiftApprox_upper_support F B hz _ (ha i))),hzero _ (abelProfile_support F B hs),sub_self])
  simpa only [radialProfile_energy_interval _ B (hs' _),integral_zero,Pi.pow_apply,Pi.sub_apply] using h

#print axioms radialShiftAbelProfile_L2_tendsto

#print axioms radialShiftAbelProfile_uniform_bound
#print axioms radialProfile_energy_interval
#print axioms radialShiftAbelProfile_energy_tendsto
#print axioms poincareSum_tendsto_compact
#print axioms radialShiftAbelKernel_tendsto

#print axioms abelIntegral_physical_interval
#print axioms abelIntegral_norm_bound_physical
#print axioms abelProfile_norm_bound_physical
#print axioms radialShiftAbelProfile_tendsto

end QuantitativeMaass
