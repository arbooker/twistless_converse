module

public import QuantitativeMaassCorrespondenceIdentityV1
public import QuantitativeMaassHeckeTreeCosetsV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson AsymptoticCongruenceLabels
open scoped Topology ENNReal MatrixGroups

namespace QuantitativeMaass

/-- A positive integral matrix fixing every point is scalar. Two points
on the imaginary axis suffice to recover its three scalar equations. -/
theorem positiveIntegralGL_scalar_of_fixed (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
    (hf : ∀ z : ℍ,positiveIntegralGL M hM • z=z) :
    M 1 0=0 ∧ M 1 1=M 0 0 ∧ M 0 1=0 := by
  have he (z : ℍ) : (M 0 0:ℂ)*(z:ℂ)+M 0 1=
      (z:ℂ)*((M 1 0:ℂ)*(z:ℂ)+M 1 1) := by
    have hh := congrArg (fun w : ℍ => (w:ℂ)) (hf z)
    rw [positiveIntegralGL_fractional] at hh
    exact (div_eq_iff (QuantitativeArithmetic.integer_matrix_denominator_ne_zero M hM.ne' z)).mp hh
  have h1 := congrArg Complex.re (he I)
  have h2 := congrArg Complex.im (he I)
  let z2 : ℍ := ⟨2*Complex.I,by norm_num⟩
  have h3 := congrArg Complex.re (he z2)
  norm_num [z2,Complex.mul_re,Complex.mul_im] at h1 h2 h3
  have hc : (M 1 0:ℝ)=0 := by linarith
  have hb : (M 0 1:ℝ)=0 := by linarith
  exact ⟨by exact_mod_cast hc,by exact_mod_cast h2.symm,by exact_mod_cast hb⟩

/-- The actual scalar product test is equivalent to fixing the entire
upper half-plane; it is independent of the chosen SL representative. -/
theorem integralProduct_scalar_iff_fixed (N : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : 0<M.det) (γ : gamma N) :
    ¬integralProductNonscalar N M γ ↔ ∀ z : ℍ,γ•(positiveIntegralGL M hM • z)=z := by
  refine ⟨fun h z => congruence_product_fixed_of_scalar N M hM γ h z,?_⟩
  intro hf
  have hp : 0<((representative γ).val*M).det := by rw [congruence_product_det];exact hM
  have hh := positiveIntegralGL_scalar_of_fixed ((representative γ).val*M) hp
    (fun z => (congruence_positiveIntegralGL_action N γ M hM hp z).trans (hf z))
  unfold integralProductNonscalar
  simp only [hh.1,hh.2.1,hh.2.2,ne_eq,not_true_eq_false,or_self,not_false_eq_true]

/-- The identity-coset predicate for upper-triangular integral matrices is
exactly the integer-translation test used in the checked Hecke tree counts. -/
theorem integralIdentityCoset_upper_iff (N : ℕ) (M : HeckeUpper)
    (hM : 0<M.matrix.det) : integralIdentityCoset N M.matrix ↔ M.translation := by
  constructor
  · rintro ⟨γ,hγ⟩
    let A := representative γ
    have he : (A.val*M.matrix) 1 0=0 ∧
        (A.val*M.matrix) 1 1=(A.val*M.matrix) 0 0 ∧ (A.val*M.matrix) 0 1=0 := by
      change ¬(_≠0 ∨ _≠_ ∨ _≠0) at hγ
      push Not at hγ
      exact hγ
    have ha : M.a≠0 := by
      intro ha
      simp [HeckeUpper.det_matrix,HeckeUpper.det,ha] at hM
    have hc : A.val 1 0=0 := by
      have hh := he.1
      simp only [Matrix.mul_apply,Fin.sum_univ_two] at hh
      change A.val 1 0*M.a+A.val 1 1*0=0 at hh
      rw [mul_zero,add_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_right ha
    have hd : A.val 0 0*A.val 1 1=1 := by
      have hh := A.property
      simpa only [Matrix.det_fin_two,hc,zero_mul,mul_zero,sub_zero] using hh
    have hdiag : A.val 0 0=A.val 1 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;> rw [h0,h1]
    have hunit : A.val 0 0≠0 := by intro hz;rw [hz,zero_mul] at hd;omega
    have haa : M.a=M.d := by
      have hh := he.2.1
      simp only [Matrix.mul_apply,Fin.sum_univ_two] at hh
      change A.val 1 0*M.b+A.val 1 1*M.d=A.val 0 0*M.a+A.val 0 1*0 at hh
      rw [hc,zero_mul,zero_add,mul_zero,add_zero,← hdiag] at hh
      exact (mul_left_cancel₀ hunit hh).symm
    refine ⟨haa,-(A.val 0 1*A.val 0 0),?_⟩
    have hh := he.2.2
    simp only [Matrix.mul_apply,Fin.sum_univ_two] at hh
    change A.val 0 0*M.b+A.val 0 1*M.d=0 at hh
    have hsq : A.val 0 0*A.val 0 0=1 := by simpa only [← hdiag] using hd
    calc
      M.b = A.val 0 0*(A.val 0 0*M.b) := by rw [← mul_assoc,hsq,one_mul]
      _ = M.d * -(A.val 0 1*A.val 0 0) := by linear_combination A.val 0 0*hh
  · rintro ⟨ha,n,hb⟩
    let A := upperSL (-n)
    have hA : A∈CongruenceSubgroup.Gamma0 N := by
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [A,upperSL,AsymptoticFreshCRT.upper]
    let γ : gamma N := ⟨integralLabel A,⟨A,hA,rfl⟩⟩
    refine ⟨γ,(integralProduct_scalar_iff_fixed N M.matrix hM γ).mpr ?_⟩
    intro z
    change integralLabel A • (positiveIntegralGL M.matrix hM • z)=z
    rw [integralLabel_action]
    apply UpperHalfPlane.ext
    rw [coe_specialLinearGroup_apply,positiveIntegralGL_fractional]
    have hd : (M.d:ℂ)≠0 := by
      have hd0 : M.d≠0 := by
        intro hd0
        simp [HeckeUpper.det_matrix,HeckeUpper.det,hd0] at hM
      exact_mod_cast hd0
    rw [show A.val 0 0=1 from rfl,show A.val 0 1= -n from rfl,
      show A.val 1 0=0 from rfl,show A.val 1 1=1 from rfl,
      show M.matrix 0 0=M.a from rfl,show M.matrix 0 1=M.b from rfl,
      show M.matrix 1 0=0 from rfl,show M.matrix 1 1=M.d from rfl]
    push_cast
    have hncast : ((algebraMap ℤ ℝ) n:ℂ)=(n:ℂ) := by
      change ((n:ℝ):ℂ)=(n:ℂ)
      exact Complex.ofReal_intCast n
    rw [hncast]
    simp only [zero_mul,zero_add,one_mul,div_one,ha,hb,Int.cast_mul]
    field_simp
    ring


#print axioms positiveIntegralGL_scalar_of_fixed
#print axioms integralProduct_scalar_iff_fixed
#print axioms integralIdentityCoset_upper_iff

end QuantitativeMaass
