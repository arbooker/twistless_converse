module

public import AsymptoticCongruenceOldTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceStrip

open AsymptoticCongruenceLabels

theorem gamma_le_of_dvd {d N : ℕ} (hd : d∣N) : gamma N≤gamma d := by
  apply Subgroup.map_mono
  intro A hA
  rw [CongruenceSubgroup.Gamma0_mem] at hA ⊢
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mpr
  have hd' : (d:ℤ)∣(N:ℤ) := by exact_mod_cast hd
  exact hd'.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hA)

/-- Finite relative index survives passage to projective integral labels.
This does not require the integral-label map to be injective. -/
theorem gamma_finite_relIndex (N d : ℕ) [NeZero N] : (gamma N).IsFiniteRelIndex (gamma d) := by
  have hf : (CongruenceSubgroup.Gamma0 N).IsFiniteRelIndex (CongruenceSubgroup.Gamma0 d) :=
    (Subgroup.isFiniteRelIndex_iff_finiteIndex).mpr inferInstance
  exact hf.map integralLabel

noncomputable instance gamma_quotient_finite (N d : ℕ) [NeZero N] :
    Finite (gamma d ⧸ (gamma N).subgroupOf (gamma d)) := by
  let := gamma_finite_relIndex N d
  infer_instance

#print axioms gamma_le_of_dvd
#print axioms gamma_finite_relIndex

end AsymptoticCongruenceStrip

namespace AsymptoticCongruenceOldSpace

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticCongruenceQuotient
open AsymptoticRegularTrace
open scoped lp

variable {N d : ℕ} [NeZero N] (hd : d∣N) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)

/-- The literal lower-level old direction, with the overgroup and its
finite relative index proved from the level divisibility. -/
noncomputable def lowerSpace (z : ℍ) : Submodule ℂ ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  space N (gamma d) (gamma_le_of_dvd hd) hε ht z

noncomputable instance lowerSpace_complete (z : ℍ) : CompleteSpace (lowerSpace hd hε ht z) :=
  inferInstanceAs (CompleteSpace (space N (gamma d) (gamma_le_of_dvd hd) hε ht z))

theorem lowerSpace_mem (z : ℍ) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) :
    v∈lowerSpace hd hε ht z ↔ v∈quotientSpace N hε ht z ∧
      ∀ a : gamma d,∀ g,coordinate N ε t z (a.val*g) v=coordinate N ε t z g v :=
  space_mem N (gamma d) (gamma_le_of_dvd hd) hε ht z v

theorem lowerSpace_trace :
    (trace volume (fun z => (lowerSpace hd hε ht z).starProjection)).toReal=
      (trace volume (AsymptoticCongruenceQuotient.projection N hε ht)).toReal/
        (((gamma N).subgroupOf (gamma d)).index:ℝ) :=
  projection_trace_toReal N (gamma d) (gamma_le_of_dvd hd) hε ht

#print axioms lowerSpace_mem
#print axioms lowerSpace_trace

end AsymptoticCongruenceOldSpace
