module

public import QuantitativeMaassMajorantPacketNormV1
public import QuantitativeArithmeticMaassMovingBandColumnOperatorV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory ContinuousLinearMap UpperHalfPlane
open AsymptoticClassicalPetersson QuantitativeNinaMaass
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass.Scheduled

/-- The normalization and enlargement change the profile, but not its
fixed propagation support multiplier. -/
theorem originalMajorant_support (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (ε : ℝ→ℝ) (t : ℝ) :
    Function.support (QuantitativeNinaMaass.originalWindowMajorant K hc ε t)⊆
      Icc (-(supportRadius K hc*radius ε t)) (supportRadius K hc*radius ε t) := by
  intro s hs
  apply (Classical.choose_spec (symmetricWindowTimeTest_uniform_support K hc)).2
    (radius ε t) (radius_pos ε t)
    (t-smoothingWidth (slowScale t) (ε t)) (t+ε t+smoothingWidth (slowScale t) (ε t))
  intro hz
  apply hs
  change ((windowEnergyDenominator K ε t)⁻¹:ℂ)*symmetricWindowTimeTest K
    (radius ε t) (t-smoothingWidth (slowScale t) (ε t))
    (t+ε t+smoothingWidth (slowScale t) (ε t)) s=0
  rw [hz,mul_zero]

/-- Literal cylinder columns of Nina's normalized enlarged majorant. -/
def originalMajorantColumn (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (ε : ℝ→ℝ) (t : ℝ) : ℍ→Lp ℂ 2 (quotientMeasure 0) :=
  cylinderTimeColumn (QuantitativeNinaMaass.originalWindowMajorant K hc ε t)
    (originalWindowMajorant_compact K hc ε t) (originalWindowMajorant_even K he hc ε t)
    (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
    (originalMajorant_support K hc ε t)

/-- Localizing the actual majorant columns gives square-integrability
before taking any cuspidal or finite-band projection. -/
theorem originalMajorant_cutoff_memLp (N : ℕ) {δ : ℝ} (hδ : 0<δ) (C D : ℝ)
    (K : SchwartzMap ℝ ℝ) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (he : Function.Even K) (ε : ℝ→ℝ) (t : ℝ) :
    MemLp (fun z => cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)
      (cylinderAutomorphic (originalMajorantColumn K hc he ε t z))) 2 (quotientMeasure 0) := by
  let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε t
  let R := supportRadius K hc*radius ε t
  have hR : 0≤R := (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
  let a := movingLowerEdge δ C ε t
  have ha := movingLowerEdge_pos hδ C ε t
  exact boundedCrossQuotientLocalization_column_memLp N (evenCoshLift f)
    (evenCoshLift_smoothOn f (f.smooth ⊤) (originalWindowMajorant_even K he hc ε t)
      (originalWindowMajorant_compact K hc ε t)) R hR
    (evenCoshLift_support_of_time_support f R hR (originalMajorant_support K hc ε t))
    (cutoffRectangle a t) (upperRectangle_compact 0 1 a _ ha) a (Real.exp (Strong.strongScale t/2))
    ha (fun _ hz => hz.2) (upperFunction (cutoffSeed a D t ha).toFun)
    (upperFunction_continuous (cutoffSeed a D t ha).smooth).aestronglyMeasurable
    (Eventually.of_forall (fun z => cutoffSeed_bound a D t ha z))

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    FiniteDimensional ℂ (S.band a b) := S.band_finiteDimensional a b

/-- The actual enlarged normalized packet has the same finite-band
column-operator envelope. No equality with the one-sided columns is used. -/
theorem originalMajorant_band_column_operator_norm (K : SchwartzMap ℝ ℝ)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (he : Function.Even K)
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t ∧ ε t≤1)
    (hp : Tendsto (fun t => ε t*slowScale t) atTop atTop)
    {δ : ℝ} (hδ : 0<δ) (C : ℝ) (hC : 0≤C) :
    ∀ᶠ t in atTop,∀ (N : ℕ) (hN : 0<N) (S : CuspEnergySpectrum N hN) (B D : ℝ),
      let A := cutoffTransfer N (movingLowerEdge δ C ε t) D t (movingLowerEdge_pos hδ C ε t)
      let c := fun z => WideInput.bandTransfer S t B A (originalMajorantColumn K hc he ε t z)
      let hcol := WideInput.bandTransfer_column_memLp S t B A (originalMajorantColumn K hc he ε t)
        (originalMajorant_cutoff_memLp N hδ C D K hc he ε t)
      ‖finiteEnergyColumnOperator (quotientMeasure 0) c hcol‖^2≤Real.exp (35*Strong.strongScale t) := by
  filter_upwards [originalMajorant_cylinder_scheduled_norm K hc ε hε hp,
    movingMultiplicity_bound hδ C hC ε hε hp] with t hpacket hm
  intro N hN S B D A c hcol
  have hA : ‖A‖^2≤Real.exp (34*Strong.strongScale t) := by
    apply (movingCutoffTransfer_norm_sq N hδ C D ε t).trans
    calc
      _ ≤ (Real.exp (17*Strong.strongScale t))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hm 2
      _ = _ := by rw [pow_two,←Real.exp_add]; congr 1; ring
  let f := QuantitativeNinaMaass.originalWindowMajorant K hc ε t
  let P := cylinderTimePacket f (f.smooth ⊤) (originalWindowMajorant_compact K hc ε t)
  have hP (v : Lp ℂ 2 (quotientMeasure 0)) : P v=ᵐ[quotientMeasure 0]
      (fun z => inner ℂ (originalMajorantColumn K hc he ε t z) v) :=
    cylinderTimePacket_column_coeFn f (f.smooth ⊤) (originalWindowMajorant_even K he hc ε t)
      (originalWindowMajorant_compact K hc ε t) (originalWindowMajorant_real K he hc ε t)
      (supportRadius K hc*radius ε t) (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le
      (originalMajorant_support K hc ε t)
      (evenCoshLift_support_of_time_support f _
        (mul_pos (supportRadius_pos K hc) (radius_pos ε t)).le (originalMajorant_support K hc ε t)) v
  rw [transferredColumnOperator_eq (quotientMeasure 0) P (originalMajorantColumn K hc he ε t) hP
    (WideInput.bandTransfer S t B A) hcol]
  have hn : ‖P.comp (WideInput.bandTransfer S t B A).adjoint‖≤‖P‖*‖A‖ := by
    apply (opNorm_comp_le _ _).trans
    rw [adjoint.norm_map]
    exact mul_le_mul_of_nonneg_left (WideInput.bandTransfer_norm S t B A) (norm_nonneg P)
  calc
    _ ≤ (‖P‖*‖A‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ Real.exp (Strong.strongScale t)*Real.exp (34*Strong.strongScale t) := by
      rw [mul_pow]
      exact mul_le_mul hpacket hA (sq_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

#print axioms originalMajorant_support
#print axioms originalMajorant_cutoff_memLp
#print axioms originalMajorant_band_column_operator_norm
end QuantitativeMaass.Scheduled
