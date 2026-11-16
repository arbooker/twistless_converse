module

public import QuantitativeArithmeticMaassMovingFluxBoundsV1
public import QuantitativeArithmeticMaassCylinderNewtonColumnsV1

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open QuantitativeNinaMaass AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled
local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance

local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

/-- Integrability of the actual moving-transfer columns, before any
spectral projection. -/
theorem movingCutoff_column_memLp (N : ℕ) {δ : ℝ} (hδ : 0<δ) (C D : ℝ)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (t : ℝ) :
    MemLp (fun z => cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)
      (cylinderAutomorphic (column K hc he ε t z))) 2 (quotientMeasure 0) := by
  let a := movingLowerEdge δ C ε t
  have ha := movingLowerEdge_pos hδ C ε t
  exact boundedCrossQuotientLocalization_column_memLp N (evenCoshLift (time K hc ε t))
    (evenCoshLift_smoothOn (time K hc ε t) ((time K hc ε t).smooth ⊤)
      (time_even K hc he ε t) (time_compact K hc ε t))
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    (evenCoshLift_support_of_time_support (time K hc ε t) _
      (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le (time_support K hc ε t))
    (cutoffRectangle a t) (upperRectangle_compact 0 1 a _ ha) a (Real.exp (Strong.strongScale t/2))
    ha (fun _ hz => hz.2) (upperFunction (cutoffSeed a D t ha).toFun)
    (upperFunction_continuous (cutoffSeed a D t ha).smooth).aestronglyMeasurable
    (Eventually.of_forall (fun z => cutoffSeed_bound a D t ha z))

/-- The actual column-operator cost is independent of the number of
spectral states. In particular, transporting a finite-band approximation
does not introduce a further factor of t. -/
theorem movingBand_column_operator_norm (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ t in atTop,∀ (N : ℕ) (hN : 0<N) (S : CuspEnergySpectrum N hN) (B D : ℝ),
      let A := cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)
      let c := fun z => WideInput.bandTransfer S t B A (column K hc he ε t z)
      let hcol := WideInput.bandTransfer_column_memLp S t B A (column K hc he ε t)
        (movingCutoff_column_memLp N hδ C D K hc he ε t)
      ‖finiteEnergyColumnOperator (quotientMeasure 0) c hcol‖^2≤Real.exp (35*Strong.strongScale t) := by
  filter_upwards [packet_scheduled_norm K hc ε hε hp,movingMultiplicity_bound hδ C hC ε hε hp]
    with t hpacket hm
  intro N hN S B D A c hcol
  have hA : ‖A‖^2≤Real.exp (34*Strong.strongScale t) := by
    apply (movingCutoffTransfer_norm_sq N hδ C D ε t).trans
    calc
      _≤(Real.exp (17*Strong.strongScale t))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hm 2
      _=_ := by rw [pow_two,←Real.exp_add]; congr 1; ring
  let P := cylinderTimePacket (time K hc ε t) ((time K hc ε t).smooth ⊤) (time_compact K hc ε t)
  have hP (v : Lp ℂ 2 (quotientMeasure 0)) : P v=ᵐ[quotientMeasure 0]
      (fun z => inner ℂ (column K hc he ε t z) v) :=
    cylinderTimePacket_column_coeFn (time K hc ε t) ((time K hc ε t).smooth ⊤)
      (time_even K hc he ε t) (time_compact K hc ε t) (time_real K hc he ε t)
      (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
      (time_support K hc ε t)
      (evenCoshLift_support_of_time_support _ _
        (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le (time_support K hc ε t)) v
  rw [transferredColumnOperator_eq (quotientMeasure 0) P (column K hc he ε t) hP
    (WideInput.bandTransfer S t B A) hcol]
  have hn : ‖P.comp (WideInput.bandTransfer S t B A).adjoint‖≤‖P‖*‖A‖ := by
    apply (opNorm_comp_le _ _).trans
    rw [adjoint.norm_map]
    exact mul_le_mul_of_nonneg_left (WideInput.bandTransfer_norm S t B A) (norm_nonneg P)
  calc
    _≤(‖P‖*‖A‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _≤Real.exp (Strong.strongScale t)*Real.exp (34*Strong.strongScale t) := by
      rw [mul_pow]
      exact mul_le_mul hpacket hA (sq_nonneg _) (Real.exp_pos _).le
    _=_ := by rw [←Real.exp_add]; congr 1; ring

/-- Any finite-source squared error now transfers to the globally
integrated moving-band columns with only an explicit strong-scale cost. -/
theorem movingBand_finiteSource_energy (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C)
    {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN)
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    ∀ᶠ t in atTop,∀ B D : ℝ,∀ {ι : Type*} [Fintype ι]
      (b : OrthonormalBasis ι ℂ (S.band (t-B) (t+B))) (E : S.band (t-B) (t+B)→L[ℂ]F),
      let A := cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)
      (∫ z,‖E (WideInput.bandTransfer S t B A (column K hc he ε t z))‖^2 ∂quotientMeasure 0)≤
        Real.exp (35*Strong.strongScale t)*finiteSourceEnergy b E := by
  filter_upwards [movingBand_column_operator_norm K hc he ε hε hp hδ C hC] with t ht
  intro B D ι _ b E A
  have hcol := WideInput.bandTransfer_column_memLp S t B A (column K hc he ε t)
    (movingCutoff_column_memLp N hδ C D K hc he ε t)
  exact (finiteSourceEnergy_column_bound (quotientMeasure 0) _ hcol b E).trans
    (mul_le_mul_of_nonneg_right (ht N hN S B D) (finiteSourceEnergy_nonneg b E))

#print axioms movingCutoff_column_memLp
#print axioms movingBand_column_operator_norm
#print axioms movingBand_finiteSource_energy
end QuantitativeMaass.Scheduled
