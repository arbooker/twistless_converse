module

public import QuantitativeMaassDeepLVWideDensityV1
public import QuantitativeMaassFiniteSourceBasisV1
public import QuantitativeArithmeticMaassJointBandV1

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Filter MeasureTheory Module QuantitativeNinaMaass
open AsymptoticClassicalPetersson QuantitativeSpectralObservability
open scoped Topology InnerProductSpace ENNReal FourierTransform SchwartzMap
namespace QuantitativeMaass

local instance (N : ℕ) (hN : 0<N) : NormedAddCommGroup (localCuspidalSpace N hN) := inferInstance
local instance (N : ℕ) (hN : 0<N) : InnerProductSpace ℂ (localCuspidalSpace N hN) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    NormedAddCommGroup (S.band a b) := inferInstance
local instance {N : ℕ} {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b : ℝ) :
    InnerProductSpace ℂ (S.band a b) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    NormedAddCommGroup (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    InnerProductSpace ℂ (S.parityBand a b σ) := inferInstance
local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    FiniteDimensional ℂ (S.parityBand a b σ) := by
  let := S.band_finiteDimensional a b
  infer_instance

local instance {N : ℕ} [NeZero N] {hN : 0<N} (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    CompleteSpace (S.parityBand a b σ) := FiniteDimensional.complete ℂ _

/-- The literal isometric inclusion of a cusp parity band in quotient L2. -/
def parityBandQuotientInclusion {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (a b σ : ℝ) :
    S.parityBand a b σ→L[ℂ]AutomorphicSpace N :=
  (localCuspidalSpace N hN).subtypeL.comp
    ((S.band a b).subtypeL.comp (S.parityBand a b σ).subtypeL)

namespace Strong

/-- The common-degree LV deficit is small in finite source energy on the
actual whole parity band, independently of the chosen orthonormal basis. -/
theorem weighted_wide_LV_parity_energy {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (σ U W : ℝ) (hU : 0≤U)
    (basis : (t : ℝ)→OrthonormalBasis
      (Fin (finrank ℂ (S.parityBand (t-Real.exp (U*strongScale t)) (t+Real.exp (U*strongScale t)) σ))) ℂ
      (S.parityBand (t-Real.exp (U*strongScale t)) (t+Real.exp (U*strongScale t)) σ))
    (ε : ℝ→ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)*finiteSourceEnergy (basis t)
      ((actualLVDeficit N p hN hpN a b hab (deepLVDegree t)).comp
        (parityBandQuotientInclusion S (t-Real.exp (U*strongScale t)) (t+Real.exp (U*strongScale t)) σ))/(t*ε t))
      atTop (𝓝 0) := by
  obtain ⟨G,hG,hbound⟩ := weighted_wide_LV_deficit_family_density N p hN hpN hNp hpres a b hab
    K he hc hK hm U W hU ε hε hproduct
  apply squeeze_zero' _ _ hG
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t heps ht
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (finiteSourceEnergy_nonneg _ _)) (mul_pos ht heps).le
  · filter_upwards [hbound,hε,eventually_gt_atTop (0:ℝ)] with t hbound heps ht
    apply div_le_div_of_nonneg_right _ (mul_pos ht heps).le
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    obtain ⟨e,r,τ,hr,hgraph,heigen⟩ := QuantitativeArithmeticMaassJointBand.full_band_joint_basis
      S p hpN a b hab (t-Real.exp (U*strongScale t)) (t+Real.exp (U*strongScale t)) σ
    have ho : Orthonormal ℂ (fun i => ((e i).val.val : AutomorphicSpace N)) := by
      apply orthonormal_iff_ite.mpr
      intro i j
      change inner ℂ (e i) (e j)=_
      exact orthonormal_iff_ite.mp e.orthonormal i j
    have hh := hbound (fun i => ((e i).val.val : AutomorphicSpace N)) ho
      (fun i => (e i).val.val.property) r τ (fun i => (hr i).2) hgraph heigen
    rw [finiteSourceEnergy_basis_independent (basis t) e]
    change (∑ i,‖actualLVDeficit N p hN hpN a b hab (deepLVDegree t) ((e i).val.val : AutomorphicSpace N)‖^2)≤G t
    have heq (i) : ‖actualLVDeficit N p hN hpN a b hab (deepLVDegree t) ((e i).val.val : AutomorphicSpace N)‖^2=
        (lvDeficitMultiplier p (deepLVDegree t) (r i) (τ i))^2 := by
      rw [actualLVDeficit_eigen N p hN hpN a b hab _ (r i) (τ i) (hgraph i) (heigen i)]
      simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,ho.norm_eq_one i,mul_one,sq_abs]
    simpa only [heq] using hh

#print axioms weighted_wide_LV_parity_energy
end Strong
end QuantitativeMaass
