module

public import QuantitativeMaassStrongWideHeckeFamilyV1
public import QuantitativeMaassExceptionalBasisV1
public import QuantitativeArithmeticMaassJointBandV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory Module QuantitativeNinaMaass
open AsymptoticClassicalPetersson QuantitativeSpectralObservability
open QuantitativeArithmeticExceptionalMoments QuantitativeArithmeticMaassExceptionalBands
open scoped Topology InnerProductSpace ENNReal FourierTransform SchwartzMap

namespace QuantitativeMaass.Strong

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

/-- Actual exceptional rank on an exponentially growing cusp parity band is negligible
even after every fixed exponential fourth-root-scale cost. The threshold is strictly above
the normalized regular-tree edge; no physical gap is assumed. -/
theorem weighted_wide_normalized_hecke_band_exceptional_density {N : ℕ} [NeZero N] {hN : 0<N}
    (S : CuspEnergySpectrum N hN) (p : ℕ) [Fact p.Prime] (hpN : ¬p∣N)
    (hNp : (N:ZMod p)≠0) (A B : ℤ) (hAB : (p:ℤ)*A+(N:ℤ)*B=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1) (σ η : ℝ)
    (hη : 2*Real.sqrt (p:ℝ)/((p:ℝ)+1)<η)
    (D : ℝ) (hD : 0≤D) (W : ℝ) (ε : ℝ → ℝ) (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)*(finrank ℂ (exceptionalSpace
      (normalizedBandHecke_symmetric S p hpN A B hAB (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ) η):ℝ)/(t*ε t))
      atTop (𝓝 0) := by
  classical
  let c := Real.sqrt (p:ℝ)/((p:ℝ)+1)
  have hpp : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hcpos : 0<c := by dsimp only [c];positivity
  have hq : 2<η/c := by
    apply (lt_div_iff₀ hcpos).mpr
    simpa only [c,mul_div_assoc] using hη
  obtain ⟨g,hg,hcount⟩ := weighted_wide_hecke_exceptional_family_density N p hN hpN hNp A B hAB
    K he hc hK hm (η/c) hq D W hD ε hε hproduct
  apply squeeze_zero' _ _ hg
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    positivity
  · filter_upwards [hcount,hε,eventually_gt_atTop (0:ℝ)] with t hcount he ht
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    obtain ⟨e,r,τ,hr,hgraph,heigen⟩ := QuantitativeArithmeticMaassJointBand.full_band_joint_basis
      S p hpN A B hAB (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ
    have hbe (i) : normalizedBandHecke S p (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ (e i)=
        ((c*τ i:ℝ):ℂ) • e i := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rw [normalizedBandHecke_actual S p hpN A B hAB,heigen]
      simp only [c,Complex.ofReal_mul,smul_smul,Submodule.coe_smul]
    let J := {i : Fin (finrank ℂ (S.parityBand (t-Real.exp (D*strongScale t)) (t+Real.exp (D*strongScale t)) σ)) // η≤|c*τ i|}
    let f (i : J) : AutomorphicSpace N := (e i.val).val.val
    have ho : Orthonormal ℂ (fun i => ((e i).val.val : AutomorphicSpace N)) := by
      apply orthonormal_iff_ite.mpr
      intro i j
      change inner ℂ (e i) (e j)=_
      exact orthonormal_iff_ite.mp e.orthonormal i j
    have hf : Orthonormal ℂ f := ho.comp _ Subtype.val_injective
    have hτ (i : J) : η/c≤|τ i.val| := by
      apply (div_le_iff₀ hcpos).mpr
      have hi := i.property
      rw [abs_mul,abs_of_pos hcpos] at hi
      simpa only [mul_comm] using hi
    have hsize := hcount f hf (fun i => (e i.val).val.val.property)
      (fun i => r i.val) (fun i => τ i.val) (fun i => (hr i.val).2)
      (fun i => hgraph i.val) (fun i => heigen i.val) hτ
    rw [exceptionalSpace_finrank_basis _ _ e (fun i => c*τ i) hbe η]
    simpa only [J,Nat.card_eq_fintype_card] using hsize

#print axioms weighted_wide_normalized_hecke_band_exceptional_density

end QuantitativeMaass.Strong
