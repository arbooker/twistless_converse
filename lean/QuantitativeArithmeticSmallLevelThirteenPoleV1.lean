module

public import QuantitativeArithmeticSmallLevelThirteenDiagonalV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirteen
open Matrix UpperHalfPlane ModularGroup SmallLevelNormalized Set
open scoped MatrixGroups ModularForm Manifold Topology

def branchQuadratic (M : GL (Fin 2) ℝ) (z : ℂ) : ℂ := num M z*denom M z

/-- Transporting the monomial classification across a determinant-one
matrix gives an exact polynomial-times-slash identity. -/
theorem classified_slash (m : ℕ) (H : ℍ→ℂ) (C : ℂ)
    (hC : ∀ z : ℍ, (z:ℂ)^m*H z=C)
    (M : GL (Fin 2) ℝ) (hM : (GeneralLinearGroup.det M:ℝ)=1) (z : ℍ) :
    branchQuadratic M z^m*(H ∣[((2*m:ℕ):ℤ)] M) z=C := by
  have hh := hC (M • z)
  rw [coe_smul_of_det_pos (by rw [hM]; norm_num)] at hh
  rw [det_one_slash _ hM]
  dsimp [branchQuadratic]
  rw [zpow_neg]
  change (num M z*denom M z)^m*(H (M • z)*(denom M z^((2*m:ℕ):ℤ))⁻¹)=C
  rw [zpow_natCast]
  have hd := denom_ne_zero M z
  calc
    (num M z*denom M z)^m*(H (M • z)*(denom M z^(2*m))⁻¹) =
        (num M z/denom M z)^m*H (M • z) := by
      rw [mul_pow,div_pow,pow_mul]
      field_simp
      ring
    _ = C := hh

private theorem zero_in_upper_closure : (0:ℂ)∈closure {z : ℂ | 0<z.im} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨((ε/2:ℝ):ℂ)*Complex.I,?_,?_⟩
  · simp only [mem_ofPred_eq,Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,
      Complex.ofReal_im,Complex.I_re,mul_zero,add_zero]
    positivity
  · rw [dist_zero_left,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (by positivity : 0<ε/2)]
    linarith

/-- A monomial pole cannot satisfy a three-term relation when neither
of the other two terms has a pole at zero. This is the finite-order
relation used after common-axis classification. -/
theorem classified_cyclic_zero (m : ℕ) (hm : 0<m) (H : ℍ→ℂ) (C : ℂ)
    (hC : ∀ z : ℍ, (z:ℂ)^m*H z=C)
    (B D : GL (Fin 2) ℝ)
    (hB : (GeneralLinearGroup.det B:ℝ)=1)
    (hD : (GeneralLinearGroup.det D:ℝ)=1)
    (hB0 : branchQuadratic B 0≠0) (hD0 : branchQuadratic D 0≠0)
    (hcyc : H+(H ∣[((2*m:ℕ):ℤ)] B)+(H ∣[((2*m:ℕ):ℤ)] D)=0) : H=0 := by
  let L : ℂ→ℂ := fun z => C*(branchQuadratic B z)^m*(branchQuadratic D z)^m+
    C*z^m*(branchQuadratic D z)^m+C*z^m*(branchQuadratic B z)^m
  have hL (z : ℍ) : L z=0 := by
    have hh := congrFun hcyc z
    simp only [Pi.add_apply,Pi.zero_apply] at hh
    have h0 := hC z
    have h1 := classified_slash m H C hC B hB z
    have h2 := classified_slash m H C hC D hD z
    dsimp [L]
    linear_combination
      (z:ℂ)^m*(branchQuadratic B z)^m*(branchQuadratic D z)^m*hh -
      (branchQuadratic B z)^m*(branchQuadratic D z)^m*h0 -
      (z:ℂ)^m*(branchQuadratic D z)^m*h1 -
      (z:ℂ)^m*(branchQuadratic B z)^m*h2
  have hc : Continuous L := by unfold L branchQuadratic num denom; fun_prop
  have hzero : L 0=0 := by
    exact (closure_minimal (fun z hz => hL ⟨z,hz⟩) (isClosed_eq hc continuous_const))
      zero_in_upper_closure
  have hC0 : C=0 := by
    simpa only [L,zero_pow (Nat.ne_of_gt hm),mul_zero,zero_mul,add_zero,
      mul_eq_zero,pow_eq_zero_iff (Nat.ne_of_gt hm),hB0,hD0,or_false] using hzero
  funext z
  have hh := hC z
  rw [hC0] at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero m z.ne_zero)

#print axioms classified_slash
#print axioms classified_cyclic_zero
end QuantitativeArithmeticSmallLevelThirteen
