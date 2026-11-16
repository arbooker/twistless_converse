module

public import QuantitativeMaassLocalEnergyDensityV1
public import QuantitativeMaassPoincareEnergyOverlapV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- Compact cross-quotient localization is bounded in the actual form-core
norm. Both geometric multiplicities remain explicit. The cutoff bounds are
needed only on its compact support; no quotient invariance is assumed. -/
theorem cross_poincare_localization_norm_sq_le (N M : ℕ)
    (v b : SmoothUpperSeed) (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mM)
    (B C : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2) :
    ‖poincareEnergySeed N
      (b.localized (congruencePoincareCartesian M v.toFun)
        (congruencePoincareCartesian_smooth M v.smooth v.compact))‖^2 ≤
      (mN : ℝ) * (mM : ℝ) * (2*B^2+2*C^2) * ‖poincareEnergySeed M v‖^2 := by
  let G := congruencePoincareCartesian M v.toFun
  have hG := congruencePoincareCartesian_smooth M v.smooth v.compact
  let q := b.localized G hG
  have hqK : tsupport (upperFunction q.toFun) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    apply hbK
    apply subset_tsupport
    intro hb
    apply hz
    change G (z.re,z.im) * b.toFun (z.re,z.im) = 0
    change b.toFun (z.re,z.im) = 0 at hb
    rw [hb, mul_zero]
  let mass := fun z : ℍ => ‖upperFunction q.toFun z‖^2
  let energy := fun z : ℍ => (upperEnergy q.toFun q.toFun z).re
  have hiMass : Integrable mass :=
    ((upperFunction_continuous q.smooth).memLp_of_hasCompactSupport q.compact).integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0)
  have hiEnergy : Integrable energy :=
    (upperEnergy_integrable q.smooth q.smooth q.compact).re
  have hzero (z : ℍ) (hz : z ∉ K) : mass z + energy z = 0 := by
    have hqz : upperFunction q.toFun z = 0 := by
      by_contra hn
      exact hz (hqK (subset_tsupport _ hn))
    have hez : upperEnergy q.toFun q.toFun z = 0 := by
      by_contra hn
      exact hz (hqK (upperEnergy_support_right _ _ hn))
    simp only [mass, energy, hqz, hez, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Complex.zero_re, zero_add]
  have hrestrict : (∫ z : ℍ, mass z) + (∫ z : ℍ, energy z) =
      ∫ z in K, mass z + energy z := by
    rw [← integral_add hiMass hiEnergy]
    calc
      _ = ∫ z : ℍ, K.indicator (fun w => mass w + energy w) z := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro z
        by_cases hz : z ∈ K
        · rw [Set.indicator_of_mem hz]
        · rw [Set.indicator_of_notMem hz]
          exact hzero z hz
      _ = _ := integral_indicator hK.measurableSet
  have hpoint (z : ℍ) (hz : z ∈ K) :
      mass z + energy z ≤ (2*B^2+2*C^2)*poincareEnergyDensity M v z := by
    have hbs : ‖b.toFun (z.re,z.im)‖^2 ≤ B^2 :=
      (sq_le_sq₀ (norm_nonneg _) hB).mpr (hbound z hz)
    have he := hyperbolicEnergy_product_bound hG b.smooth (Z := (z.re,z.im)) z.im_pos
    have hq : q.toFun = fun W => b.toFun W * G W := by
      funext W
      exact mul_comm _ _
    have hE := hyperbolicEnergy_self_nonneg G (z.re,z.im)
    have hmass := sq_nonneg ‖G (z.re,z.im)‖
    have hgradz := hgrad z hz
    change (hyperbolicEnergy b.toFun b.toFun (z.re,z.im)).re ≤ C^2 at hgradz
    have hmulE := mul_le_mul_of_nonneg_right hbs hE
    have hmulMass := mul_le_mul_of_nonneg_right hbs hmass
    have hmulGrad := mul_le_mul_of_nonneg_left hgradz hmass
    have hrep : G (z.re,z.im) =
        poincareSum (G := gamma M) (upperFunction v.toFun) z :=
      congruencePoincareCartesian_represents M v.toFun z
    change ‖upperFunction q.toFun z‖^2 +
      (upperEnergy q.toFun q.toFun z).re ≤ _
    rw [hq]
    change ‖b.toFun (z.re,z.im)*G (z.re,z.im)‖^2 +
      (hyperbolicEnergy (fun W => b.toFun W*G W)
        (fun W => b.toFun W*G W) (z.re,z.im)).re ≤ _
    rw [norm_mul, mul_pow]
    unfold poincareEnergyDensity
    rw [← hrep]
    change _ ≤ (2*B^2+2*C^2) *
      (‖G (z.re,z.im)‖^2 + (hyperbolicEnergy G G (z.re,z.im)).re)
    nlinarith [mul_nonneg (sq_nonneg B) hmass, mul_nonneg (sq_nonneg C) hE]
  have hiDensity : IntegrableOn (poincareEnergyDensity M v) K :=
    (poincareEnergyDensity_continuous M v).continuousOn.integrableOn_compact hK
  have hlocal : (∫ z in K, mass z + energy z) ≤
      (2*B^2+2*C^2) * ((mM : ℝ)*‖poincareEnergySeed M v‖^2) := by
    calc
      _ ≤ ∫ z in K, (2*B^2+2*C^2)*poincareEnergyDensity M v z := by
        apply integral_mono_ae ((hiMass.add hiEnergy).restrict)
          (hiDensity.const_mul _)
        filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
        exact hpoint z hz
      _ = (2*B^2+2*C^2) * ∫ z in K, poincareEnergyDensity M v z :=
        integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (poincareEnergyDensity_local_integral_le M v K hK mM hmM) (by positivity)
  have hp := poincareEnergySeed_norm_sq_le_of_overlap N K hK mN hmN q hqK
  change ‖poincareEnergySeed N q‖^2 ≤ _
  change ‖poincareEnergySeed N q‖^2 ≤
    (mN : ℝ)*((∫ z : ℍ, mass z)+(∫ z : ℍ, energy z)) at hp
  rw [hrestrict] at hp
  apply (hp.trans (mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg mN))).trans_eq
  ring

#print axioms cross_poincare_localization_norm_sq_le

end QuantitativeMaass
