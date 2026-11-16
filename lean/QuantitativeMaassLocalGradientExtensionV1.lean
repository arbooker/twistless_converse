module

public import QuantitativeMaassLocalGradientRestrictionV1
public import QuantitativeArithmeticMaassGradientExtensionV1

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MeasureTheory Set UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassGradient

namespace QuantitativeMaass

variable (N : ℕ) (K : Set ℍ) (hK : MeasurableSet K) (m : ℕ)
    (hm : ∀ z : ℍ, ∀ S : Finset (gamma N),
      (∀ g ∈ S, g • z ∈ K) → S.card ≤ m) (i : Bool)

def localSeedGradientLp (u : SmoothUpperSeed) : Lp ℂ 2 (volume.restrict K) :=
  (seedGradient_local_memLp N u i K hK m hm).toLp (seedGradient N i u)

theorem localSeedGradientLp_add (u v : SmoothUpperSeed) :
    localSeedGradientLp N K hK m hm i (u.add v) =
      localSeedGradientLp N K hK m hm i u + localSeedGradientLp N K hK m hm i v := by
  unfold localSeedGradientLp
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (congrFun (seedGradient_add N i u v))

theorem localSeedGradientLp_smul (c : ℂ) (u : SmoothUpperSeed) :
    localSeedGradientLp N K hK m hm i (u.smul c) =
      c • localSeedGradientLp N K hK m hm i u := by
  unfold localSeedGradientLp
  rw [← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall (congrFun (seedGradient_smul N i c u))

def smoothLocalGradientMap : smoothSeedModule →ₗ[ℂ] Lp ℂ 2 (volume.restrict K) where
  toFun u := localSeedGradientLp N K hK m hm i (moduleSeed u)
  map_add' u v := localSeedGradientLp_add N K hK m hm i (moduleSeed u) (moduleSeed v)
  map_smul' c u := localSeedGradientLp_smul N K hK m hm i c (moduleSeed u)

theorem smoothLocalGradientMap_bound (u : smoothSeedModule) :
    ‖smoothLocalGradientMap N K hK m hm i u‖ ≤
      Real.sqrt (m : ℝ) * ‖smoothEnergyMap N u‖ := by
  change ‖localSeedGradientLp N K hK m hm i (moduleSeed u)‖ ≤
    Real.sqrt (m : ℝ) * ‖(poincareEnergySeed N (moduleSeed u) : QuotientEnergySpace N)‖
  rw [Completion.norm_coe]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  exact seedGradient_local_norm_sq_le N (moduleSeed u) i K hK m hm

/-- Actual local hyperbolic gradient on the entire completed quotient
energy space. Its local L2 bound uses summed-energy invariance, not
invariance of an individual gradient component. -/
def localQuotientGradient : QuotientEnergySpace N →L[ℂ] Lp ℂ 2 (volume.restrict K) :=
  (smoothLocalGradientMap N K hK m hm i).extendOfNorm (smoothEnergyMap N)

theorem localQuotientGradient_seed (u : SmoothUpperSeed) :
    localQuotientGradient N K hK m hm i (poincareEnergySeed N u : QuotientEnergySpace N) =
      localSeedGradientLp N K hK m hm i u :=
  LinearMap.extendOfNorm_eq (f := smoothLocalGradientMap N K hK m hm i)
    (e := smoothEnergyMap N) (smoothEnergyMap_dense N)
    ⟨Real.sqrt (m : ℝ), smoothLocalGradientMap_bound N K hK m hm i⟩ (seedModule u)

theorem localQuotientGradient_norm_le :
    ‖localQuotientGradient N K hK m hm i‖ ≤ Real.sqrt (m : ℝ) :=
  LinearMap.opNorm_extendOfNorm_le (f := smoothLocalGradientMap N K hK m hm i)
    (e := smoothEnergyMap N) (smoothEnergyMap_dense N) (Real.sqrt_nonneg _)
    (smoothLocalGradientMap_bound N K hK m hm i)

#print axioms localQuotientGradient_seed
#print axioms localQuotientGradient_norm_le

end QuantitativeMaass
