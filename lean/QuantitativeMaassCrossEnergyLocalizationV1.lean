module

public import QuantitativeMaassCrossPoincareBoundV1
public import QuantitativeArithmeticMaassGradientExtensionV1

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential QuantitativeArithmeticMaassGradient

/-- First periodize at the input level, then multiply by the compact seed.
The resulting seed may subsequently be periodized at a different level. -/
def crossPoincareSeedMap (M : ℕ) (b : SmoothUpperSeed) :
    smoothSeedModule →ₗ[ℂ] smoothSeedModule where
  toFun u := seedModule
    (b.localized (congruencePoincareCartesian M (moduleSeed u).toFun)
      (congruencePoincareCartesian_smooth M (moduleSeed u).smooth (moduleSeed u).compact))
  map_add' u v := by
    apply Subtype.ext
    funext Z
    change congruencePoincareCartesian M ((moduleSeed u).add (moduleSeed v)).toFun Z *
      b.toFun Z =
      congruencePoincareCartesian M (moduleSeed u).toFun Z * b.toFun Z +
      congruencePoincareCartesian M (moduleSeed v).toFun Z * b.toFun Z
    rw [poincareCartesian_add]
    exact add_mul _ _ _
  map_smul' c u := by
    apply Subtype.ext
    funext Z
    change congruencePoincareCartesian M ((moduleSeed u).smul c).toFun Z * b.toFun Z =
      c * (congruencePoincareCartesian M (moduleSeed u).toFun Z * b.toFun Z)
    rw [poincareCartesian_smul]
    ring

/-- The seed estimate retains both prescribed orbit multiplicities when
expressed as the norm bound required for extension to the energy completion. -/
theorem smoothEnergyMap_cross_localization_bound (N M : ℕ)
    (b : SmoothUpperSeed) (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mM)
    (B C : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (u : smoothSeedModule) :
    ‖smoothEnergyMap N (crossPoincareSeedMap M b u)‖ ≤
      Real.sqrt ((mN : ℝ)*(mM : ℝ)*(2*B^2+2*C^2)) * ‖smoothEnergyMap M u‖ := by
  change ‖(poincareEnergySeed N
      (b.localized (congruencePoincareCartesian M (moduleSeed u).toFun)
        (congruencePoincareCartesian_smooth M (moduleSeed u).smooth (moduleSeed u).compact)) :
      QuotientEnergySpace N)‖ ≤
    Real.sqrt ((mN : ℝ)*(mM : ℝ)*(2*B^2+2*C^2)) *
      ‖(poincareEnergySeed M (moduleSeed u) : QuotientEnergySpace M)‖
  simp only [Completion.norm_coe]
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt
    (by positivity : 0 ≤ (mN : ℝ)*(mM : ℝ)*(2*B^2+2*C^2))]
  exact cross_poincare_localization_norm_sq_le N M (moduleSeed u) b K hK hbK
    mN mM hmN hmM B C hB hbound hgrad

/-- Compact cross-quotient localization on the actual completed energy
spaces, obtained by the proved bound on the dense Poincare seed map. -/
def crossEnergyLocalization (N M : ℕ) (b : SmoothUpperSeed) :
    QuotientEnergySpace M →L[ℂ] QuotientEnergySpace N :=
  ((smoothEnergyMap N).comp (crossPoincareSeedMap M b)).extendOfNorm (smoothEnergyMap M)

theorem crossEnergyLocalization_on_seed (N M : ℕ)
    (b : SmoothUpperSeed) (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mM)
    (B C : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2)
    (u : SmoothUpperSeed) :
    crossEnergyLocalization N M b (poincareEnergySeed M u : QuotientEnergySpace M) =
      (poincareEnergySeed N
        (b.localized (congruencePoincareCartesian M u.toFun)
          (congruencePoincareCartesian_smooth M u.smooth u.compact)) : QuotientEnergySpace N) := by
  exact LinearMap.extendOfNorm_eq
    (f := (smoothEnergyMap N).comp (crossPoincareSeedMap M b)) (e := smoothEnergyMap M)
    (smoothEnergyMap_dense M)
    ⟨Real.sqrt ((mN : ℝ)*(mM : ℝ)*(2*B^2+2*C^2)),
      smoothEnergyMap_cross_localization_bound N M b K hK hbK mN mM hmN hmM
        B C hB hbound hgrad⟩ (seedModule u)

theorem crossEnergyLocalization_norm (N M : ℕ)
    (b : SmoothUpperSeed) (K : Set ℍ) (hK : IsCompact K)
    (hbK : tsupport (upperFunction b.toFun) ⊆ K) (mN mM : ℕ)
    (hmN : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mN)
    (hmM : ∀ z : ℍ, ∀ S : Finset (gamma M),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ mM)
    (B C : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, ‖upperFunction b.toFun z‖ ≤ B)
    (hgrad : ∀ z ∈ K, (upperEnergy b.toFun b.toFun z).re ≤ C^2) :
    ‖crossEnergyLocalization N M b‖ ≤
      Real.sqrt ((mN : ℝ)*(mM : ℝ)*(2*B^2+2*C^2)) :=
  LinearMap.opNorm_extendOfNorm_le
    (f := (smoothEnergyMap N).comp (crossPoincareSeedMap M b)) (e := smoothEnergyMap M)
    (smoothEnergyMap_dense M) (Real.sqrt_nonneg _)
    (smoothEnergyMap_cross_localization_bound N M b K hK hbK mN mM hmN hmM
      B C hB hbound hgrad)

#print axioms smoothEnergyMap_cross_localization_bound
#print axioms crossEnergyLocalization_on_seed
#print axioms crossEnergyLocalization_norm

end QuantitativeMaass
