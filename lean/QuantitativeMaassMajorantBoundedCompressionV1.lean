module

public import QuantitativeMaassMajorantExactBandCompressionV1
public import QuantitativeMaassColumnParityGramV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance

/-- Exact-band compression also applies to uniformly bounded observations.
The fixed bound is removed by scalar normalization, without changing either
spatial cutoff or requiring the observation to commute with a spectral band. -/
theorem originalMajorant_bounded_cutoff_exact_band_compression {ι : Type*} (N : ℕ) (hN : 0<N)
    (basis : HilbertBasis ι ℂ (localCuspidalSpace N hN)) (e : ι→ℝ)
    (he : ∀ i,0≤e i)
    (hgraph : ∀ i,FriedrichsGraph N (basis i:AutomorphicSpace N)
      ((e i:ℂ) • (basis i:AutomorphicSpace N)))
    (δ C D : ℝ) (hδ : 0<δ) (hC : 0≤C) (hD : 0≤D) (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (hKe : Function.Even K)
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    (T : ℝ→AutomorphicSpace N→L[ℂ]AutomorphicSpace N)
    (M : ℝ) (hM : 0<M) (hT : ∀ᶠ t in atTop,‖T t‖≤M)
    (hPT : ∀ᶠ t in atTop,(localCuspidalSpace N hN).starProjection*T t=T t)
    (hTP : ∀ᶠ t in atTop,T t*(localCuspidalSpace N hN).starProjection=T t) (W : ℝ) :
    ∃ G : ℝ,0<G ∧ Tendsto (fun t => Real.exp (W*Strong.strongScale t)*
      originalMajorantCutoffTraceDifference N hN basis e he hgraph (movingLowerEdge δ C ε t) D
        (movingLowerEdge_pos hδ C ε t) K hc hKe ε T (exactBandParameter G t) t/
        (t*ε t)) atTop (𝓝 0) := by
  let U := fun t => ((M⁻¹:ℝ):ℂ) • T t
  have hU : ∀ᶠ t in atTop,‖U t‖≤1 := by
    filter_upwards [hT] with t ht
    apply opNorm_le_bound _ zero_le_one
    intro v
    change ‖((M⁻¹:ℝ):ℂ) • T t v‖≤1*‖v‖
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hM),one_mul]
    calc
      _ ≤ M⁻¹*(M*‖v‖) := mul_le_mul_of_nonneg_left
        ((T t).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right ht (norm_nonneg v)))
        (inv_pos.mpr hM).le
      _ = _ := by rw [←mul_assoc,inv_mul_cancel₀ hM.ne',one_mul]
  have hPU : ∀ᶠ t in atTop,(localCuspidalSpace N hN).starProjection*U t=U t := by
    filter_upwards [hPT] with t ht
    change (localCuspidalSpace N hN).starProjection.comp (((M⁻¹:ℝ):ℂ) • T t)=_
    rw [comp_smul]
    exact congrArg (fun A : AutomorphicSpace N→L[ℂ]AutomorphicSpace N => ((M⁻¹:ℝ):ℂ) • A) ht
  have hUP : ∀ᶠ t in atTop,U t*(localCuspidalSpace N hN).starProjection=U t := by
    filter_upwards [hTP] with t ht
    change (((M⁻¹:ℝ):ℂ) • T t).comp (localCuspidalSpace N hN).starProjection=_
    rw [smul_comp]
    exact congrArg (fun A : AutomorphicSpace N→L[ℂ]AutomorphicSpace N => ((M⁻¹:ℝ):ℂ) • A) ht
  obtain ⟨G,hG,hlim⟩ := originalMajorant_supported_cutoff_exact_band_compression N hN basis e he hgraph
    δ C D hδ hC hD K hc hKe hK hm ε hε hp U hU hPU hUP W
  refine ⟨G,hG,?_⟩
  have hh := hlim.const_mul M
  rw [mul_zero] at hh
  convert hh using 1
  funext t
  simp only [originalMajorantCutoffTraceDifference,U,columnLinearTrace_real_smul]
  field_simp [hM.ne']

#print axioms originalMajorant_bounded_cutoff_exact_band_compression
end QuantitativeMaass.Scheduled
