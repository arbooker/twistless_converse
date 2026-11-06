module

public import AsymptoticModularAreaV1
public import AsymptoticModularFundamentalV1
public import AsymptoticOrbitDensityIndexV1
public import AsymptoticCongruenceTraceFiniteV1
public import AsymptoticLowerLevelOldSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public section

namespace AsymptoticCongruenceQuotient

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticRegularTrace AsymptoticModularDomain
open scoped ENNReal Modular

set_option backward.isDefEq.respectTransparency false in
/-- The actual quotient projection has trace equal to the exact
congruence covolume. The modular area and finite-index scaling are proved. -/
theorem projection_trace_covolume (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) :
    trace volume (projection N hε ht)=
      ((gamma N).relIndex (gamma 1):ℝ≥0∞)*ENNReal.ofReal (Real.pi/3) := by
  let : NeZero N := ⟨hN.ne'⟩
  let H := (gamma N).subgroupOf (gamma 1)
  have hle : gamma N ≤ gamma 1 := gamma_le_of_dvd (one_dvd N)
  let f : ℍ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖amplitude N ε t z‖^2)
  have hf : Measurable f := ((amplitude_measurable N ε t).norm.pow_const 2).ennreal_ofReal
  have hn (x : ℍ) : (∑' h : H,f (h.val • x))=1 := by
    have he := (Subgroup.subgroupOfEquivOfLe hle).toEquiv.tsum_eq
      (fun g : gamma N => f (g.val • x))
    exact he.trans (amplitude_ofReal_tsum N hε ht x)
  have hi := AsymptoticOrbitDensity.integral_eq_index_mul_volume (G:=gamma 1) volume
    (fun g => AsymptoticRationalGroup.measurePreserving g.val) H f hf hn
    ModularGroup.fd gamma_one_fundamental
  rw [closed_domain_area] at hi
  have he : trace volume (projection N hε ht)=∫⁻ z : ℍ,f z := by
    apply lintegral_congr
    intro z
    rw [projection_diagonal,one_smul]
    congr 1
    simpa only [OneMemClass.coe_one,one_smul] using (amplitude_norm_sq N hε ht 1 z).symm
  exact he.trans hi

/-- Real-valued form of the exact quotient trace used in the count bound. -/
theorem projection_trace_covolume_toReal (N : ℕ) (hN : 0<N) {ε : ℝ} (hε : 0<ε)
    {t : ℕ} (ht : 1≤t) :
    (trace volume (projection N hε ht)).toReal=
      ((gamma N).relIndex (gamma 1):ℝ)*(Real.pi/3) := by
  rw [projection_trace_covolume N hN hε ht,ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)]

#print axioms projection_trace_covolume
#print axioms projection_trace_covolume_toReal

end AsymptoticCongruenceQuotient
