module

public import QuantitativeMaassPositiveMultiplierEquivV1
public import QuantitativeMaassNewSignSmoothingV1
public import QuantitativeMaassNewRamifiedEquationV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ENNReal
namespace QuantitativeMaass

/-- Simultaneous normalizer eigenvectors admit continuous representatives
approaching them with the same exact eigenrelations. -/
theorem normalizerFamily_continuous_approximation {ι : Type*} (N : ℕ) [NeZero N]
    (g : ι→quotientNormalizerGroup N) (χ : ι→ℂ) (x : AutomorphicSpace N)
    (hx : ∀ i,quotientNormalizerPullback N (g i) x=χ i • x) :
    ∃ f : ℕ→AutomorphicL2.representatives (gamma N) (quotientMeasure N),
      (∀ n,Continuous (f n).val) ∧
      (∀ n i,quotientNormalizerPullback N (g i) (AutomorphicL2.denseEmbedding _ _ (f n))=
        χ i • AutomorphicL2.denseEmbedding _ _ (f n)) ∧
      Tendsto (fun n => AutomorphicL2.denseEmbedding _ _ (f n)) atTop (𝓝 x) := by
  let R : ℕ→ℝ := fun n => 1/((n:ℝ)+1)
  have hR (n : ℕ) : 0<R n := by dsimp only [R];positivity
  choose f hf he using fun n => abelNormalizedOperator_continuous_representative N (R n) (hR n) x
  refine ⟨f,hf,?_,?_⟩
  · intro n i
    rw [he]
    change quotientNormalizerPullback N (g i)
      (AllLevel.radialKernelOperator N (abelNormalizedProfile (R n)) (abelNormalizedProfile_smooth (R n) (hR n))
        (R n) (hR n).le (abelNormalizedProfile_support (R n) (hR n)) x)=χ i • _
    rw [quotientNormalizerPullback_radial,hx,map_smul]
    rfl
  · simp_rw [he]
    exact AllLevel.abelNormalizedOperator_tendsto atTop N R hR
      tendsto_one_div_add_atTop_nhds_zero_nat x

variable {ι : Type*} [Fintype ι] [Nonempty ι] (N : ℕ) (g : ι→quotientNormalizerGroup N)
  {δ Y : ℝ} (hδ : 0<δ) (hY : 0<Y) {ν : ℕ} (hν : 1≤ν)
  (hcover : ∀ z : ℍ,∃ i,∃ a : gamma N,Y≤(a.val • ((g i).val • z)).im)

include hδ hY hν hcover

theorem normalizerCoverMetric_representative_norm
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hg : ∀ i z,‖f.val ((g i).val • z)‖=‖f.val z‖) :
    ‖normalizerCoverMetricEquiv N g hδ hY hν hcover
      (weightedQuotientEmbedding N hδ hν (AutomorphicL2.denseEmbedding _ _ f))‖=
        ‖AutomorphicL2.denseEmbedding _ _ f‖ := by
  let v := normalizerCoverMetricEquiv N g hδ hY hν hcover
    (weightedQuotientEmbedding N hδ hν (AutomorphicL2.denseEmbedding _ _ f))
  have hv : (v : ℍ→ℂ)=ᵐ[quotientMeasure 0]fun z =>
      ((normalizerCoverMetric N g δ ν z*AsymptoticCompactBranch.cap δ ν z:ℝ):ℂ)*f.val z := by
    have he := normalizerCoverMetricEquiv_coeFn N g hδ hY hν hcover
      (weightedQuotientEmbedding N hδ hν (AutomorphicL2.denseEmbedding _ _ f))
    rw [weightedQuotientEmbedding_representative] at he
    filter_upwards [he,(weightedRepresentative_memLp N hδ hν f).coeFn_toLp] with z hm hf
    change (normalizerCoverMetricEquiv N g hδ hY hν hcover
      (weightedQuotientRepresentative N hδ hν f)) z=_ at hm
    have hval : v=normalizerCoverMetricEquiv N g hδ hY hν hcover
        (weightedQuotientRepresentative N hδ hν f) := by
      dsimp only [v]
      rw [weightedQuotientEmbedding_representative]
    rw [hval,hm]
    change (normalizerCoverMetric N g δ ν z:ℂ)*
      (weightedRepresentative_memLp N hδ hν f).toLp _ z=_
    rw [hf]
    push_cast
    ring
  have he : ENNReal.ofReal (‖v‖^2)=ENNReal.ofReal (‖AutomorphicL2.denseEmbedding _ _ f‖^2) := by
    rw [complexLp_norm_square_lintegral]
    calc
      _ = ∫⁻ z,ENNReal.ofReal (‖((normalizerCoverMetric N g δ ν z*
          AsymptoticCompactBranch.cap δ ν z:ℝ):ℂ)*f.val z‖^2) ∂quotientMeasure 0 := by
        apply lintegral_congr_ae
        filter_upwards [hv] with z hz
        rw [hz]
      _ = ∫⁻ z,ENNReal.ofReal (‖f.val z‖^2) ∂quotientMeasure N :=
        normalizerCoverMetric_representative_energy N g hδ hν
          (fun z => (heightWeightFloor_pos hδ hY ν).trans_le
            (normalizerCoverWeight_lower N g hδ hY hν hcover z)) f.val f.property.1 f.property.2.1 hg
      _ = _ := by
        change _=ENNReal.ofReal (‖f.property.2.2.toLp f.val‖^2)
        rw [complexLp_norm_square_lintegral]
        apply lintegral_congr_ae
        filter_upwards [f.property.2.2.coeFn_toLp] with z hz
        rw [hz]
  have hh := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at hh
  exact (sq_eq_sq₀ (norm_nonneg v) (norm_nonneg (AutomorphicL2.denseEmbedding _ _ f))).mp hh

/-- Exact scalar normalization on completed normalizer sectors. No density
of simultaneous eigen-representatives is assumed; it was proved by smoothing. -/
theorem normalizerCoverMetric_completed_norm [NeZero N] (x : AutomorphicSpace N)
    (hx : ∀ i,g i∈normalizerEigenStabilizer N x) :
    ‖normalizerCoverMetricEquiv N g hδ hY hν hcover (weightedQuotientEmbedding N hδ hν x)‖=‖x‖ := by
  choose χ hχ he using hx
  obtain ⟨f,hf,hfe,hlim⟩ := normalizerFamily_continuous_approximation N g χ x he
  have hn (n : ℕ) :
      ‖normalizerCoverMetricEquiv N g hδ hY hν hcover
        (weightedQuotientEmbedding N hδ hν (AutomorphicL2.denseEmbedding _ _ (f n)))‖=
      ‖AutomorphicL2.denseEmbedding _ _ (f n)‖ := by
    apply normalizerCoverMetric_representative_norm N g hδ hY hν hcover (f n)
    intro i z
    rw [normalizer_eigen_continuous N (g i) (f n) (hf n) (χ i) (hfe n i) z,norm_mul,hχ,one_mul]
  have hleft := ((normalizerCoverMetricEquiv N g hδ hY hν hcover).continuous.comp
    (weightedQuotientEmbedding N hδ hν).continuous).norm.tendsto x |>.comp hlim
  have hright := continuous_norm.tendsto x |>.comp hlim
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall (fun n => (hn n).symm)))

#print axioms normalizerFamily_continuous_approximation
#print axioms normalizerCoverMetric_representative_norm
#print axioms normalizerCoverMetric_completed_norm
end QuantitativeMaass
