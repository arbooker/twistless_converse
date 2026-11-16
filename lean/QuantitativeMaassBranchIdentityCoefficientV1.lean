module

public import QuantitativeMaassConcreteBranchPacketV1
public import QuantitativeMaassCorrespondenceCosetV1
public import QuantitativeHolomorphicMatrixCompactGeometryV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane AsymptoticFiniteBranch
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip AsymptoticMassTransport
open QuantitativeHolomorphic AsymptoticRegularTrace
namespace QuantitativeMaass

attribute [local instance] Classical.propDecidable

/-- Every actual finite-expression integer representative has positive
determinant and represents the same positive real Möbius map. -/
theorem integerAction_positive_real {g : AsymptoticRationalGroup.Group}
    {M : IntegerMatrix2} (hM : IntegerAction g M) :
    ∃ hpos : 0<M.det,∀ z : ℍ,g•z=positiveIntegralGL M hpos•z := by
  have hpos : 0<M.det := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM.det_one_le)
  refine ⟨hpos,?_⟩
  intro z
  apply UpperHalfPlane.ext
  rw [hM.2,positiveIntegralGL_fractional]

/-- An identity-coset branch whose input and output are in the chosen
half-open strip has the identity projective label. This removes spurious
integer-translation main terms. -/
theorem identityCoset_retained_label_one (b : Branch) (M : IntegerMatrix2)
    (hM : IntegerAction b.label M) (hpos : 0<M.det)
    (z : ℍ) (hz : z∈strip) (hbz : b.label•z∈strip)
    (hid : integralIdentityCoset 0 M) : b.label=1 := by
  have hact (x : ℍ) : b.label•x=positiveIntegralGL M hpos•x := by
    apply UpperHalfPlane.ext
    rw [hM.2,positiveIntegralGL_fractional]
  obtain ⟨γ,hγ⟩ := hid
  have hfix (x : ℍ) : γ•(b.label•x)=x := by
    rw [hact]
    exact congruence_product_fixed_of_scalar 0 M hpos γ hγ x
  have hg : γ=1 := gamma_zero_strip_unique (b.label•z) hbz γ (by change γ•(b.label•z)∈strip;rw [hfix];exact hz)
  apply rational_label_eq_one_of_fixed
  intro x
  simpa only [hg,one_smul] using hfix x

/-- The actual periodized identity contribution equals the regular
identity coefficient once the input-strip indicator is retained. -/
theorem cylinder_branch_identity_coefficient (b : Branch) (M : IntegerMatrix2)
    (hM : IntegerAction b.label M) (hpos : 0<M.det)
    (z : ℍ) (hz : z∈strip) (v : ℂ) :
    cylinderInputBranchCoefficient b z*(if integralIdentityCoset 0 M then v else 0)=
      matrix (regular b z) 1 1*v := by
  classical
  have hm : matrix (regular b z) 1 1=if b.label=1 then b.coefficient z else 0 := by
    simp only [regular,AsymptoticOrbitBranch.operator_matrix,mul_one,one_smul]
  rw [hm]
  by_cases hg : b.label=1
  · have hid : integralIdentityCoset 0 M := by
      refine ⟨1,(integralProduct_scalar_iff_fixed 0 M hpos 1).mpr ?_⟩
      intro x
      have hx : positiveIntegralGL M hpos•x=b.label•x := by
        apply UpperHalfPlane.ext
        rw [positiveIntegralGL_fractional,hM.2]
      rw [one_smul,hx,hg,one_smul]
    have hbz : z∈(fun x : ℍ => b.label•x) ⁻¹' strip := by
      change b.label•z∈strip
      simpa only [hg,one_smul] using hz
    rw [ite_eq_left hg,ite_eq_left hid,cylinderInputBranchCoefficient,indicator_of_mem hbz]
  · rw [ite_eq_right hg,zero_mul]
    by_cases hid : integralIdentityCoset 0 M
    · have hbz : z∉(fun x : ℍ => b.label•x) ⁻¹' strip :=
        fun hh => hg (identityCoset_retained_label_one b M hM hpos z hz hh hid)
      rw [ite_eq_left hid,cylinderInputBranchCoefficient,indicator_of_notMem hbz,zero_mul]
    · rw [ite_eq_right hid,mul_zero]

#print axioms integerAction_positive_real
#print axioms identityCoset_retained_label_one
#print axioms cylinder_branch_identity_coefficient
end QuantitativeMaass
