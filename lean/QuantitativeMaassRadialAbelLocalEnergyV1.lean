module

public import QuantitativeMaassRadialAbelLimitV1
public import QuantitativeMaassRadialCompactEnergyV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- One pointwise periodization bound for every bounded seed in a fixed compact set. -/
theorem compact_poincare_uniform_bound {G A : Type*} [Group G] [TopologicalSpace A]
    [MulAction G A] [ProperlyDiscontinuousSMul G A] (K : Set A) (hK : IsCompact K) :
    ∃ M : ℕ,∀ (f : A → ℂ),Function.support f⊆K → ∀ D : ℝ,0≤D →
      (∀ x,‖f x‖≤D) → ∀ x,‖poincareSum (G:=G) f x‖≤(M:ℝ)*D := by
  classical
  obtain ⟨M,hM⟩ := compact_orbit_overlap (G:=G) K hK
  refine ⟨M,?_⟩
  intro f hf D hD hb x
  let hS := compact_orbit_point_finite (G:=G) K hK x
  let S := hS.toFinset
  have hout (γ : G) (hγ : γ∉S) : f (γ•x)=0 := by
    by_contra hn
    exact hγ (hS.mem_toFinset.mpr (hf hn))
  have hcard : S.card≤M := hM x S (fun γ hγ => hS.mem_toFinset.mp hγ)
  change ‖∑' γ : G,f (γ•x)‖≤_
  rw [tsum_eq_sum hout]
  calc
    _ ≤ ∑ γ∈S,‖f (γ•x)‖ := norm_sum_le _ _
    _ ≤ ∑ _γ∈S,D := Finset.sum_le_sum (fun γ _ => hb (γ•x))
    _ = (S.card:ℝ)*D := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hD

/-- One kernel bound for all approximants, all centres in a compact ball,
and every point in the quotient. No quantitative growth of this constant is claimed. -/
theorem radialShiftAbelKernel_local_bound (N : ℕ)
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (o : ℍ) (L : ℝ) :
    ∃ D : ℝ,0≤D ∧ ∀ a : ℝ,0<a → a≤1 → ∀ x : ℍ,dist x o≤L → ∀ y : ℍ,
      ‖radialPoincareKernel N (abelProfile (radialShiftApprox F a)) x y‖≤D := by
  have hz : ∀ q,Real.cosh R<q → F q=0 := fun q hq => by
    by_contra hn
    exact (not_le_of_gt hq) (hs hn)
  obtain ⟨C,hC,hbound⟩ := radialShiftAbelProfile_uniform_bound F hF _ (Real.one_le_cosh R) hs
  obtain ⟨M,hM⟩ := compact_poincare_uniform_bound (G:=gamma N)
    (Metric.closedBall o (R+L)) (isCompact_closedBall o (R+L))
  refine ⟨M*C,mul_nonneg (Nat.cast_nonneg _) hC.le,?_⟩
  intro a ha ha1 x hx y
  apply hM (upperFunction (radialFunction (abelProfile (radialShiftApprox F a)) x))
  · intro z hz'
    have hd : dist z x≤R := radialFunction_support _ x R hR
      (abelProfile_support _ _ (radialShiftApprox_upper_support F _ hz a ha))
      (subset_tsupport _ hz')
    exact (dist_triangle z x o).trans (add_le_add hd hx)
  · exact hC.le
  · intro z
    rw [radialFunction_upper]
    exact hbound a ha ha1 _ (Real.one_le_cosh _)

/-- Strong local squared-kernel convergence on the actual quotient product
measure. In particular this is stronger than operator-norm convergence;
compactness in the centre variable is explicit. -/
theorem radialShiftAbelKernel_local_L2_tendsto {ι : Type*} (l : Filter ι)
    [l.IsCountablyGenerated] [NeBot l] (N : ℕ) [NeZero N]
    (F : ℝ → ℂ) (hF : ContDiffOn ℝ ∞ F (Ici 1))
    (R : ℝ) (hR : 0≤R) (hs : Function.support F⊆Iic (Real.cosh R))
    (o : ℍ) (L : ℝ) (a : ι → ℝ) (ha : ∀ i,0<a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => ∫ p : ℍ×ℍ in (Metric.closedBall o L) ×ˢ univ,
      ‖radialPoincareKernel N (abelProfile (radialShiftApprox F (a i))) p.1 p.2-
        radialPoincareKernel N (abelProfile F) p.1 p.2‖^2
      ∂(quotientMeasure N).prod (quotientMeasure N)) l (𝓝 0) := by
  let S : Set (ℍ×ℍ) := (Metric.closedBall o L) ×ˢ univ
  let μ := ((quotientMeasure N).prod (quotientMeasure N)).restrict S
  have hS : MeasurableSet S := Metric.isClosed_closedBall.measurableSet.prod MeasurableSet.univ
  have hz : ∀ q,Real.cosh R<q → F q=0 := fun q hq => by
    by_contra hn
    exact (not_le_of_gt hq) (hs hn)
  let K (i : ι) (p : ℍ×ℍ) := radialPoincareKernel N
    (abelProfile (radialShiftApprox F (a i))) p.1 p.2
  let H (p : ℍ×ℍ) := radialPoincareKernel N (abelProfile F) p.1 p.2
  have hm (i : ι) : AEStronglyMeasurable (K i) μ :=
    (radialPoincareKernel_joint_measurable N _ (abelProfile_smooth _
      (radialShiftApprox_smooth F hF _ (ha i))
      (radialShiftApprox_compact F _ hz _ (ha i))).continuous).aestronglyMeasurable
  have hl (p : ℍ×ℍ) : Tendsto (fun i => K i p) l (𝓝 (H p)) :=
    radialShiftAbelKernel_tendsto l N F hF R hR hs a ha ha0 p.1 p.2
  have hmH : AEStronglyMeasurable H μ :=
    aestronglyMeasurable_of_tendsto_ae l hm (Eventually.of_forall hl)
  obtain ⟨D,hD,hbound⟩ := radialShiftAbelKernel_local_bound N F hF R hR hs o L
  have hsmall : ∀ᶠ i in l,a i<1 := (tendsto_order.1 ha0).2 1 (by norm_num)
  have hH (p : ℍ×ℍ) (hp : p∈S) : ‖H p‖≤D := by
    apply le_of_tendsto (hl p).norm
    filter_upwards [hsmall] with i hi
    exact hbound _ (ha i) hi.le p.1 hp.1 p.2
  have hb : ∀ᶠ i in l,∀ᵐ p ∂μ,‖‖K i p-H p‖^2‖≤(2*D)^2 := by
    filter_upwards [hsmall] with i hi
    filter_upwards [ae_restrict_mem hS] with p hp
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have h := (norm_sub_le (K i p) (H p)).trans
      (add_le_add (hbound _ (ha i) hi.le p.1 hp.1 p.2) (hH p hp))
    linarith
  have hi : Integrable (fun _ : ℍ×ℍ => (2*D)^2) μ := integrable_const _
  have hlim : ∀ᵐ p ∂μ,Tendsto (fun i => ‖K i p-H p‖^2) l (𝓝 (0:ℝ)) := by
    filter_upwards with p
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using
      ((hl p).sub_const (H p)).norm.pow 2
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => (2*D)^2)
    (Eventually.of_forall (fun i => ((hm i).sub hmH).norm.pow 2)) hb hi hlim
  simpa only [Pi.pow_apply,Pi.sub_apply,integral_zero] using h

#print axioms compact_poincare_uniform_bound
#print axioms radialShiftAbelKernel_local_bound
#print axioms radialShiftAbelKernel_local_L2_tendsto

end QuantitativeMaass
