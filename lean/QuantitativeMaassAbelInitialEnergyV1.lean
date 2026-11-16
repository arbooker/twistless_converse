module

public import QuantitativeMaassAbelNormalizedOperatorV1
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass

/-- Dominated convergence upgrades the actual pointwise Abel initial limit
to quotient energy convergence for bounded continuous invariant inputs. -/
theorem abelNormalizedProfile_energy_tendsto {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (N : ℕ) [NeZero N] (R : ι → ℝ) (hR : ∀ i,0<R i) (hlim : Tendsto R l (𝓝 0))
    (f : ℍ → ℂ) (hf : Continuous f) (hinv : ∀ γ : gamma N, ∀ y,f (γ•y)=f y)
    (hL : MemLp f 2 (quotientMeasure N)) (B : ℝ) (_hB : 0≤B) (hb : ∀ x,‖f x‖≤B) :
    Tendsto (fun i => ∫ x,‖(radialKernelData N (abelNormalizedProfile (R i))
      (abelNormalizedProfile_smooth _ (hR i)) (R i) (hR i).le
      (abelNormalizedProfile_support _ (hR i))).output f x-f x‖^2 ∂quotientMeasure N)
      l (𝓝 0) := by
  let D (i : ι) := radialKernelData N (abelNormalizedProfile (R i))
    (abelNormalizedProfile_smooth _ (hR i)) (R i) (hR i).le
    (abelNormalizedProfile_support _ (hR i))
  have hm (i : ι) : Measurable (fun x => ‖(D i).output f x-f x‖^2) :=
    (((D i).output_measurable f hf.measurable).sub hf.measurable).norm.pow_const 2
  have hb' (i : ι) (x : ℍ) : ‖(D i).output f x-f x‖≤2*B := by
    have hh := abelNormalizedProfile_output_bound N (R i) (hR i) f hf.measurable hinv hL B hb x
    exact (norm_sub_le _ _).trans (by linarith [hb x])
  have ht := tendsto_integral_filter_of_dominated_convergence (l:=l) (μ:=quotientMeasure N)
    (F:=fun i x => ‖(D i).output f x-f x‖^2) (f:=fun _ => (0:ℝ))
    (fun _ => (2*B)^2) (Eventually.of_forall (fun i => (hm i).aestronglyMeasurable))
    (Eventually.of_forall (fun i => Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb' i x) 2)))
    (integrable_const _) (Eventually.of_forall (fun x => by
      have hh := abelNormalizedProfile_output_tendsto l N R hR hlim f hf.measurable hinv hL x hf.continuousAt
      simpa only [sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using
        (hh.sub (tendsto_const_nhds (x:=f x))).norm.pow 2))
  simpa only [integral_zero] using ht

/-- Energy convergence identifies the limit in the actual quotient Hilbert
norm, with all changes of L2 representatives accounted for almost everywhere. -/
theorem abelNormalizedOperator_tendsto_of_representative {ι : Type*} (l : Filter ι)
    [l.IsCountablyGenerated] (N : ℕ) [NeZero N] (R : ι → ℝ) (hR : ∀ i,0<R i)
    (hlim : Tendsto R l (𝓝 0)) (f : AutomorphicSpace N)
    (f₀ : ℍ → ℂ) (hf₀ : Continuous f₀) (hinv : ∀ γ : gamma N, ∀ y,f₀ (γ•y)=f₀ y)
    (hL : MemLp f₀ 2 (quotientMeasure N)) (he : (f.val : ℍ → ℂ)=ᵐ[quotientMeasure N] f₀)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x,‖f₀ x‖≤B) :
    Tendsto (fun i => abelNormalizedOperator N (R i) (hR i) f) l (𝓝 f) := by
  let D (i : ι) := radialKernelData N (abelNormalizedProfile (R i))
    (abelNormalizedProfile_smooth _ (hR i)) (R i) (hR i).le
    (abelNormalizedProfile_support _ (hR i))
  have hnorm (i : ι) : ‖abelNormalizedOperator N (R i) (hR i) f-f‖^2=
      ∫ x,‖(D i).output f₀ x-f₀ x‖^2 ∂quotientMeasure N := by
    change ‖(abelNormalizedOperator N (R i) (hR i) f-f).val‖^2=_
    rw [AsymptoticL2Multiplier.norm_sq_eq_integral]
    apply integral_congr_ae
    have ho : ((abelNormalizedOperator N (R i) (hR i) f).val : ℍ → ℂ)=ᵐ[quotientMeasure N]
        (D i).output f.val := (D i).operator_coeFn f.val
    filter_upwards [Lp.coeFn_sub (abelNormalizedOperator N (R i) (hR i) f).val f.val,
      ho,he] with x hx hy hz
    change ‖((abelNormalizedOperator N (R i) (hR i) f).val-f.val) x‖^2=_
    rw [hx,Pi.sub_apply,hy,hz,(D i).output_congr_ae he]
  have hsq : Tendsto (fun i => ‖abelNormalizedOperator N (R i) (hR i) f-f‖^2) l (𝓝 0) := by
    simp_rw [hnorm]
    exact abelNormalizedProfile_energy_tendsto l N R hR hlim f₀ hf₀ hinv hL B hB hb
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using ht

#print axioms abelNormalizedProfile_energy_tendsto
#print axioms abelNormalizedOperator_tendsto_of_representative

end QuantitativeMaass
