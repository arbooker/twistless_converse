module

public import QuantitativeMaassCrossEnergyCompatibilityV1
public import QuantitativeMaassCrossPoincareFluxV1
public import QuantitativeMaassLocalGradientExtensionV1
public import QuantitativeMaassGradientLocalizationV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane ContinuousLinearMap
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassGradient
open scoped Topology ContDiff InnerProductSpace

namespace QuantitativeMaass
open MaassDifferential

/-- A pointwise summed-energy bound controls either hyperbolic derivative.
There is no invariance assertion about an individual derivative. -/
theorem cutoffGradient_norm_le_of_energy (b : Point → ℂ) (C : ℝ)
    (i : Bool) (z : ℍ) (hgrad : (upperEnergy b b z).re ≤ C^2) :
    ‖cutoffGradient i b z‖ ≤ |C| := by
  apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg C)).mp
  rw [sq_abs]
  apply le_trans _ hgrad
  have he := hyperbolicEnergy_self_eq b (z.re,z.im)
  unfold cutoffGradient upperEnergy upperFunction
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, he]
  cases i <;> simp only [axis, Bool.false_eq_true, ite_false, ite_true]
  · change z.im^2*‖Y b (z.re,z.im)‖^2 ≤ _
    nlinarith [mul_nonneg (sq_nonneg z.im) (sq_nonneg ‖X b (z.re,z.im)‖)]
  · change z.im^2*‖X b (z.re,z.im)‖^2 ≤ _
    nlinarith [mul_nonneg (sq_nonneg z.im) (sq_nonneg ‖Y b (z.re,z.im)‖)]

/-- Multiplication by a cutoff derivative on the actual local L2 space. -/
def crossLocalCutoffGradient (K : Set ℍ) (hK : MeasurableSet K)
    (b : SmoothUpperSeed) (C : ℝ)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (i : Bool) : Lp ℂ 2 (volume.restrict K) →L[ℂ] Lp ℂ 2 (volume.restrict K) :=
  AsymptoticL2Multiplier.operator (C := |C|) (cutoffGradient i b.toFun)
    (cutoffGradient_continuous i b.toFun b.smooth).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem hK] with z hz
      exact cutoffGradient_norm_le_of_energy b.toFun C i z (hgrad z hz))

theorem crossLocalCutoffGradient_coeFn (K : Set ℍ) (hK : MeasurableSet K)
    (b : SmoothUpperSeed) (C : ℝ)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (i : Bool) (v : Lp ℂ 2 (volume.restrict K)) :
    crossLocalCutoffGradient K hK b C hgrad i v =ᵐ[volume.restrict K]
      fun z => cutoffGradient i b.toFun z * v z :=
  AsymptoticL2Multiplier.operator_coeFn (C := |C|) _ _ _ v

/-- The four local L2 pairings in the cross-quotient cutoff flux. Both
gradient maps and both local function restrictions are bounded maps on
their actual completed spaces. -/
def crossLocalEnergyFlux (N M : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mM)
    (b : SmoothUpperSeed) (C : ℝ)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (u : QuotientEnergySpace N) (v : QuotientEnergySpace M) : ℂ :=
  let u₀ := quotientRestriction N K hK hK.measurableSet (energyInclusion N u)
  let v₀ := quotientRestriction M K hK hK.measurableSet (energyInclusion M v)
  let Du := localQuotientGradient N K hK.measurableSet mN hmN
  let Dv := localQuotientGradient M K hK.measurableSet mM hmM
  let Db := crossLocalCutoffGradient K hK.measurableSet b C hgrad
  (inner ℂ (Du true u) (Db true v₀) - inner ℂ (Db true u₀) (Dv true v)) +
    (inner ℂ (Du false u) (Db false v₀) - inner ℂ (Db false u₀) (Dv false v))

/-- On the dense Poincare seed domain the completed local pairings are
exactly the literal compact flux integral. -/
theorem crossLocalEnergyFlux_seed_integral (N M : ℕ) (K : Set ℍ) (hK : IsCompact K)
    (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mM)
    (b : SmoothUpperSeed) (C : ℝ)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (u v : SmoothUpperSeed) :
    let F := congruencePoincareCartesian N u.toFun
    let G := congruencePoincareCartesian M v.toFun
    crossLocalEnergyFlux N M K hK mN mM hmN hmM b C hgrad
      (poincareEnergySeed N u) (poincareEnergySeed M v) =
    ∫ z in K, (z.im : ℂ)^2 *
      ((star (X F (z.re,z.im)) * X b.toFun (z.re,z.im) * G (z.re,z.im) -
        star (X b.toFun (z.re,z.im) * F (z.re,z.im)) * X G (z.re,z.im)) +
       (star (Y F (z.re,z.im)) * Y b.toFun (z.re,z.im) * G (z.re,z.im) -
        star (Y b.toFun (z.re,z.im) * F (z.re,z.im)) * Y G (z.re,z.im))) := by
  intro F G
  let a := localSeedGradientLp N K hK.measurableSet mN hmN
  let c := localSeedGradientLp M K hK.measurableSet mM hmM
  let U := quotientRestriction N K hK hK.measurableSet (poincareSeedVector N u)
  let V := quotientRestriction M K hK hK.measurableSet (poincareSeedVector M v)
  let D := crossLocalCutoffGradient K hK.measurableSet b C hgrad
  simp only [crossLocalEnergyFlux, localQuotientGradient_seed,
    energyInclusion_coe, poincareEnergySeed_value]
  change (inner ℂ (a true u) (D true V) - inner ℂ (D true U) (c true v)) +
    (inner ℂ (a false u) (D false V) - inner ℂ (D false U) (c false v)) = _
  rw [L2.inner_def, L2.inner_def, L2.inner_def, L2.inner_def]
  rw [← integral_sub (L2.integrable_inner (𝕜 := ℂ) (a true u) (D true V))
      (L2.integrable_inner (𝕜 := ℂ) (D true U) (c true v)),
    ← integral_sub (L2.integrable_inner (𝕜 := ℂ) (a false u) (D false V))
      (L2.integrable_inner (𝕜 := ℂ) (D false U) (c false v))]
  have hadd := integral_add
      ((L2.integrable_inner (𝕜 := ℂ) (a true u) (D true V)).sub
        (L2.integrable_inner (𝕜 := ℂ) (D true U) (c true v)))
      ((L2.integrable_inner (𝕜 := ℂ) (a false u) (D false V)).sub
        (L2.integrable_inner (𝕜 := ℂ) (D false U) (c false v)))
  simp only [Pi.sub_apply] at hadd
  rw [← hadd]
  apply integral_congr_ae
  have hU := quotientRestriction_representative_ae N K hK hK.measurableSet
    ⟨_, poincareSeed_representative N u⟩
  have hV := quotientRestriction_representative_ae M K hK hK.measurableSet
    ⟨_, poincareSeed_representative M v⟩
  change U =ᵐ[volume.restrict K] poincareSum (G := gamma N) (upperFunction u.toFun) at hU
  change V =ᵐ[volume.restrict K] poincareSum (G := gamma M) (upperFunction v.toFun) at hV
  have ha (i : Bool) : a i u =ᵐ[volume.restrict K] seedGradient N i u :=
    (seedGradient_local_memLp N u i K hK.measurableSet mN hmN).coeFn_toLp
  have hc (i : Bool) : c i v =ᵐ[volume.restrict K] seedGradient M i v :=
    (seedGradient_local_memLp M v i K hK.measurableSet mM hmM).coeFn_toLp
  filter_upwards [ha true, ha false, hc true, hc false, hU, hV,
    crossLocalCutoffGradient_coeFn K hK.measurableSet b C hgrad true U,
    crossLocalCutoffGradient_coeFn K hK.measurableSet b C hgrad false U,
    crossLocalCutoffGradient_coeFn K hK.measurableSet b C hgrad true V,
    crossLocalCutoffGradient_coeFn K hK.measurableSet b C hgrad false V]
    with z hat haf hct hcf hu hv hdut hduf hdvt hdvf
  change (inner ℂ ((a true u) z) ((D true V) z) -
      inner ℂ ((D true U) z) ((c true v) z)) +
    (inner ℂ ((a false u) z) ((D false V) z) -
      inner ℂ ((D false U) z) ((c false v) z)) = _
  rw [hat, haf, hct, hcf, hdut, hduf, hdvt, hdvf, hu, hv]
  have hFz : poincareSum (G := gamma N) (upperFunction u.toFun) z = F (z.re,z.im) :=
    (congruencePoincareCartesian_represents N u.toFun z).symm
  have hGz : poincareSum (G := gamma M) (upperFunction v.toFun) z = G (z.re,z.im) :=
    (congruencePoincareCartesian_represents M v.toFun z).symm
  rw [hFz, hGz]
  dsimp only [F, G]
  have hsreal : star (z.im : ℂ) = (z.im : ℂ) := Complex.conj_ofReal z.im
  simp only [RCLike.inner_apply, starRingEnd_apply, seedGradient, cutoffGradient,
    axis, Bool.false_eq_true, ite_false, ite_true, upperFunction, X, Y,
    star_mul, hsreal]
  ring

/-- The exact cutoff flux on the two completed energy spaces. This is
the continuous extension of the compact Green identity, not a spectral
localization assumption. All four local L2 pairings are defined above. -/
theorem crossEnergyLocalization_flux (N M : ℕ)
    (b : SmoothUpperSeed) (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mM)
    (B C : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (hr : ∀ Z, star (b.toFun Z) = b.toFun Z)
    (u : QuotientEnergySpace N) (v : QuotientEnergySpace M) :
    quotientClosedEnergy N u (crossEnergyLocalization N M b v) -
      quotientClosedEnergy M (crossEnergyLocalization M N b u) v =
        crossLocalEnergyFlux N M K hK mN mM hmN hmM b C hgrad u v := by
  have hseed (s t : SmoothUpperSeed) :
      quotientClosedEnergy N (poincareEnergySeed N s)
          (crossEnergyLocalization N M b (poincareEnergySeed M t)) -
        quotientClosedEnergy M
          (crossEnergyLocalization M N b (poincareEnergySeed N s))
          (poincareEnergySeed M t) =
      crossLocalEnergyFlux N M K hK mN mM hmN hmM b C hgrad
        (poincareEnergySeed N s) (poincareEnergySeed M t) := by
    rw [crossEnergyLocalization_on_seed N M b K hK hbK mN mM hmN hmM
        B C hB hbound hgrad,
      crossEnergyLocalization_on_seed M N b K hK hbK mM mN hmM hmN
        B C hB hbound hgrad,
      quotientClosedEnergy_coe, quotientClosedEnergy_coe]
    simp only [poincareEnergySeed_value, poincareEnergySeed_laplacian]
    rw [← poincareSeedVector_laplacian_symmetric N s]
    rw [cross_poincare_localization_flux N M s t b hr,
      crossLocalEnergyFlux_seed_integral N M K hK mN mM hmN hmM b C hgrad s t]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hzb : z ∉ tsupport (upperFunction b.toFun) := fun h => hz (hbK h)
    have hx := upper_dir_zero_of_notMem_tsupport hzb e₁
    have hy := upper_dir_zero_of_notMem_tsupport hzb e₂
    simp only [X, Y, hx, hy, mul_zero, zero_mul, star_zero, sub_self, zero_add]
  have hleft (s : SmoothUpperSeed) :
      (fun w : QuotientEnergySpace M =>
        quotientClosedEnergy N (poincareEnergySeed N s) (crossEnergyLocalization N M b w) -
          quotientClosedEnergy M (crossEnergyLocalization M N b (poincareEnergySeed N s)) w) =
      (fun w => crossLocalEnergyFlux N M K hK mN mM hmN hmM b C hgrad
        (poincareEnergySeed N s) w) := by
    apply (poincareEnergySeed_completion_dense M).equalizer
    · unfold quotientClosedEnergy
      fun_prop
    · unfold crossLocalEnergyFlux
      fun_prop
    · funext t
      exact hseed s t
  have hall :
      (fun w : QuotientEnergySpace N =>
        quotientClosedEnergy N w (crossEnergyLocalization N M b v) -
          quotientClosedEnergy M (crossEnergyLocalization M N b w) v) =
      (fun w => crossLocalEnergyFlux N M K hK mN mM hmN hmM b C hgrad w v) := by
    apply (poincareEnergySeed_completion_dense N).equalizer
    · unfold quotientClosedEnergy
      fun_prop
    · unfold crossLocalEnergyFlux
      fun_prop
    · funext s
      exact congrFun (hleft s) v
  exact congrFun hall u

#print axioms cutoffGradient_norm_le_of_energy
#print axioms crossLocalEnergyFlux_seed_integral
#print axioms crossEnergyLocalization_flux

end QuantitativeMaass
