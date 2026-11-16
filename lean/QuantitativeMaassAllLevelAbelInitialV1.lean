module

public import QuantitativeMaassInfiniteMeasureApproxV1
public import QuantitativeMaassAbelStrongInitialV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass.AllLevel

/-- Compact Poincare seeds are genuinely L1 even on the infinite-volume
translation quotient. -/
theorem poincareSeed_integrable (N : ℕ) (u : SmoothUpperSeed) :
    Integrable (poincareSum (G:=gamma N) (upperFunction u.toFun)) (quotientMeasure N) :=
  (integral_poincare_unfold volume
    (fun g : gamma N => AsymptoticRationalGroup.measurePreserving g.val)
    (density N) (density_measurable N) (density_orbit_sum N)
    (upperFunction u.toFun) (upperFunction_continuous u.smooth).measurable
    ((upperFunction_continuous u.smooth).integrable_of_hasCompactSupport u.compact)).1

/-- The all-level contraction converges strongly on bounded continuous L1
representatives. No finite total measure enters the argument. -/
theorem abelNormalizedOperator_tendsto_L1 {ι : Type*} (l : Filter ι)
    [l.IsCountablyGenerated] (N : ℕ) (R : ι → ℝ) (hR : ∀ i,0<R i)
    (hlim : Tendsto R l (𝓝 0)) (f : AutomorphicSpace N)
    (f₀ : ℍ → ℂ) (hf₀ : Continuous f₀) (hinv : ∀ γ : gamma N, ∀ y,f₀ (γ•y)=f₀ y)
    (hL : MemLp f₀ 2 (quotientMeasure N)) (hI : Integrable f₀ (quotientMeasure N))
    (he : (f.val : ℍ → ℂ)=ᵐ[quotientMeasure N] f₀)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x,‖f₀ x‖≤B) :
    Tendsto (fun i => abelNormalizedOperator N (R i) (hR i) f) l (𝓝 f) := by
  let D (i : ι) := radialKernelData N (abelNormalizedProfile (R i))
    (abelNormalizedProfile_smooth _ (hR i)) (R i) (hR i).le
    (abelNormalizedProfile_support _ (hR i))
  have ht := bounded_L1_diagonal_tendsto (quotientMeasure N) l
    (fun i => (D i).output f₀) f₀
    (fun i => ((D i).output_measurable f₀ hf₀.measurable).aestronglyMeasurable)
    hI B hB (fun i => Eventually.of_forall (fun x =>
      abelNormalizedProfile_output_bound N (R i) (hR i) f₀ hf₀.measurable hinv hL B hb x))
    (Eventually.of_forall (fun x => abelNormalizedProfile_output_tendsto l N R hR hlim
      f₀ hf₀.measurable hinv hL x hf₀.continuousAt))
  have hp (i : ι) : inner ℂ (abelNormalizedOperator N (R i) (hR i) f) f=
      ∫ x,star ((D i).output f₀ x)*f₀ x ∂quotientMeasure N := by
    change inner ℂ (abelNormalizedOperator N (R i) (hR i) f).val f.val=_
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(D i).operator_coeFn f.val,he] with x hx hy
    change (D i).operator f.val x=(D i).output f.val x at hx
    change f.val x*star ((D i).operator f.val x)=_
    rw [hx,hy,(D i).output_congr_ae he,mul_comm]
  have hself : inner ℂ f f=∫ x,star (f₀ x)*f₀ x ∂quotientMeasure N := by
    change inner ℂ f.val f.val=_
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [he] with x hx
    change f.val x*star (f.val x)=star (f₀ x)*f₀ x
    rw [hx,mul_comm]
  apply contraction_inner_tendsto l _ f
    (Eventually.of_forall (fun i => abelNormalizedOperator_apply_norm N (R i) (hR i) f))
  have ht' : Tendsto (fun i => inner ℂ (abelNormalizedOperator N (R i) (hR i) f) f)
      l (𝓝 (inner ℂ f f)) := by simpa only [hp,hself] using ht
  have hr : (inner ℂ f f).re=‖f‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) f
  simpa only [Function.comp_def,hr] using
    (Complex.continuous_re.continuousAt.tendsto.comp ht')

theorem abelNormalizedOperator_tendsto_seed {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (N : ℕ) (R : ι → ℝ) (hR : ∀ i,0<R i) (hlim : Tendsto R l (𝓝 0))
    (u : SmoothUpperSeed) :
    Tendsto (fun i => abelNormalizedOperator N (R i) (hR i) (poincareSeedVector N u))
      l (𝓝 (poincareSeedVector N u)) := by
  let : ContinuousConstSMul (gamma N) ℍ :=
    ⟨fun γ => AsymptoticRationalBranches.action_continuous γ.val⟩
  obtain ⟨B,hB,hb⟩ := poincareSeed_representative_bounded N u
  exact abelNormalizedOperator_tendsto_L1 l N R hR hlim
    (poincareSeedVector N u) (poincareSum (G:=gamma N) (upperFunction u.toFun))
    (poincareSum_continuous _ u.compact (upperFunction_continuous u.smooth))
    (fun γ y => poincareSum_invariant _ γ y) (poincareSeed_representative N u).2.2
    (poincareSeed_integrable N u) (poincareSeedVector_coeFn N u) B hB hb

/-- The normalized geometric Abel operators converge strongly to identity
on the entire actual quotient L2 space. The extension uses the proved dense
seed family and the uniform contraction bound, with no regularity premise
on the final input vector. -/
theorem abelNormalizedOperator_tendsto {ι : Type*} (l : Filter ι) [l.IsCountablyGenerated]
    (N : ℕ) (R : ι → ℝ) (hR : ∀ i,0<R i) (hlim : Tendsto R l (𝓝 0))
    (f : AutomorphicSpace N) :
    Tendsto (fun i => abelNormalizedOperator N (R i) (hR i) f) l (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0<ε/3 := by positivity
  obtain ⟨u,hu⟩ := Metric.denseRange_iff.mp (poincareSeedVector_dense N) f (ε/3) he
  let v := poincareSeedVector N u
  have hv : ‖f-v‖<ε/3 := by simpa only [dist_eq_norm] using hu
  have ht := abelNormalizedOperator_tendsto_seed l N R hR hlim u
  filter_upwards [Metric.tendsto_nhds.mp ht (ε/3) he] with i hi
  let K := abelNormalizedOperator N (R i) (hR i)
  have hmid : ‖K v-v‖<ε/3 := by simpa only [dist_eq_norm] using hi
  have hd : K f-f=K (f-v)+(K v-v)+(v-f) := by
    rw [map_sub]
    abel
  rw [dist_eq_norm]
  change ‖K f-f‖<ε
  rw [hd]
  calc
    _ ≤ (‖K (f-v)‖+‖K v-v‖)+‖v-f‖ := by
      have h1 := norm_add_le (K (f-v)) (K v-v)
      have h2 := norm_add_le (K (f-v)+(K v-v)) (v-f)
      linarith
    _ ≤ (‖f-v‖+‖K v-v‖)+‖v-f‖ := by
      have h := abelNormalizedOperator_apply_norm N (R i) (hR i) (f-v)
      change ‖K (f-v)‖≤‖f-v‖ at h
      linarith
    _ < ε := by rw [norm_sub_rev v f]; linarith

#print axioms abelNormalizedOperator_tendsto
#print axioms poincareSeed_integrable
#print axioms abelNormalizedOperator_tendsto_L1
#print axioms abelNormalizedOperator_tendsto_seed

end QuantitativeMaass.AllLevel
