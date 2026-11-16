module

public import QuantitativeMaassLocalizationIntegralV1

set_option autoImplicit false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane UniformSpace
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- The concrete linear space of smooth compact upper-half-plane seeds.
No seminorm or quotient norm is imposed on this auxiliary space. -/
def smoothSeedModule : Submodule ℂ (Point→ℂ) where
  carrier := {u | ContDiffOn ℝ ∞ u {Z | 0<Z.2} ∧ HasCompactSupport (upperFunction u)}
  zero_mem' := ⟨contDiffOn_const,by change IsCompact (tsupport (0 : ℍ→ℂ)); simp⟩
  add_mem' hu hv := ⟨hu.1.add hv.1,hu.2.add hv.2⟩
  smul_mem' c u hu := by
    refine ⟨contDiffOn_const.smul hu.1,?_⟩
    exact (SmoothUpperSeed.smul ⟨u,hu.1,hu.2⟩ c).compact

def moduleSeed (u : smoothSeedModule) : SmoothUpperSeed := ⟨u.val,u.property.1,u.property.2⟩
def seedModule (u : SmoothUpperSeed) : smoothSeedModule := ⟨u.toFun,u.smooth,u.compact⟩

/-- The actual dense map into the completed quotient energy form. -/
def smoothEnergyMap (N : ℕ) : smoothSeedModule →ₗ[ℂ] QuotientEnergySpace N where
  toFun u := (poincareEnergySeed N (moduleSeed u) : QuotientEnergySpace N)
  map_add' u v := by
    rw [← Completion.coe_add]
    apply congrArg (fun x : QuotientEnergyDomain N => (x : QuotientEnergySpace N))
    apply Subtype.ext
    exact poincareSeedVector_add N (moduleSeed u) (moduleSeed v)
  map_smul' c u := by
    rw [← Completion.coe_smul]
    apply congrArg (fun x : QuotientEnergyDomain N => (x : QuotientEnergySpace N))
    apply Subtype.ext
    exact poincareSeedVector_smul N c (moduleSeed u)

theorem smoothEnergyMap_seed (N : ℕ) (u : SmoothUpperSeed) :
    smoothEnergyMap N (seedModule u)=(poincareEnergySeed N u : QuotientEnergySpace N) := rfl

theorem smoothEnergyMap_dense (N : ℕ) : DenseRange (smoothEnergyMap N) := by
  apply (poincareEnergySeed_completion_dense N).mono
  rintro x ⟨u,rfl⟩
  exact ⟨seedModule u,rfl⟩

def smoothSeedMultiplier (b : Point→ℂ) (hb : ContDiffOn ℝ ∞ b {Z | 0<Z.2}) :
    smoothSeedModule →ₗ[ℂ] smoothSeedModule where
  toFun u := seedModule ((moduleSeed u).localized b hb)
  map_add' u v := by
    apply Subtype.ext
    funext Z
    exact mul_add (b Z) (u.val Z) (v.val Z)
  map_smul' c u := by
    apply Subtype.ext
    funext Z
    change b Z*(c*u.val Z)=c*(b Z*u.val Z)
    ring

#print axioms smoothEnergyMap_dense

end QuantitativeMaass
