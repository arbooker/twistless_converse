module

public import SmallLevelNormalizedEvenFrickeV1

/-! Consolidated chapter: QuantitativeArithmeticQuadraticMatrices. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticQuadraticMatricesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticQuadraticMatrices
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

theorem sqrt_two_ne : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'

/-- Determinant-two integer or rational matrices, normalized to determinant one. -/
def quadraticMatrix (a b c d : ℝ) (h : a*d-b*c=2) : GL (Fin 2) ℝ :=
  matrix (a/Real.sqrt 2) (b/Real.sqrt 2) (c/Real.sqrt 2) (d/Real.sqrt 2) (by
    have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    field_simp [sqrt_two_ne]
    nlinarith)

theorem quadraticMatrix_det (a b c d : ℝ) (h : a*d-b*c=2) :
    (GeneralLinearGroup.det (quadraticMatrix a b c d h):ℝ)=1 := matrix_det _ _ _ _ _

def signed (negative : Bool) (g : GL (Fin 2) ℝ) : GL (Fin 2) ℝ :=
  if negative then (-1)*g else g

theorem signed_slash (m : ℕ) (F : ℍ → ℂ) (negative : Bool) (g : GL (Fin 2) ℝ) :
    F ∣[((2*m:ℕ):ℤ)] signed negative g=F ∣[((2*m:ℕ):ℤ)] g := by
  cases negative
  · rfl
  · change F ∣[((2*m:ℕ):ℤ)] ((-1)*g)=_
    rw [SlashAction.slash_mul,central_even]
#print axioms quadraticMatrix_det
#print axioms signed_slash
end QuantitativeArithmeticQuadraticMatrices
end
end

/-! ## QuantitativeArithmeticIntegralQuadraticMatricesV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticQuadraticMatrices
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

def liftMatrix (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det=1 ∨ M.det=2) : GL (Fin 2) ℝ :=
  if h1 : M.det=1 then
    matrix (M 0 0) (M 0 1) (M 1 0) (M 1 1) (by
      exact_mod_cast (det_fin_two M).symm.trans h1)
  else
    quadraticMatrix (M 0 0) (M 0 1) (M 1 0) (M 1 1) (by
      exact_mod_cast (det_fin_two M).symm.trans (h.resolve_left h1))

theorem liftMatrix_det (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det=1 ∨ M.det=2) :
    (GeneralLinearGroup.det (liftMatrix M h):ℝ)=1 := by
  unfold liftMatrix
  split
  · exact matrix_det _ _ _ _ _
  · exact quadraticMatrix_det _ _ _ _ _
#print axioms liftMatrix_det
end QuantitativeArithmeticQuadraticMatrices
end
end

/-! ## QuantitativeArithmeticIntegralQuadraticProductsV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeArithmeticQuadraticMatrices
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

abbrev realMatrix (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  M.map (Int.castRingHom ℝ)

theorem lift_val_one (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det=1 ∨ M.det=2)
    (h1 : M.det=1) : (liftMatrix M h).val=realMatrix M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftMatrix,h1,matrix,realMatrix,GeneralLinearGroup.mkOfDetNeZero]

theorem lift_val_two (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det=1 ∨ M.det=2)
    (h2 : M.det=2) : (liftMatrix M h).val=(1/Real.sqrt 2) • realMatrix M := by
  have h1 : M.det≠1 := by omega
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftMatrix,h1,quadraticMatrix,matrix,realMatrix,GeneralLinearGroup.mkOfDetNeZero,
      div_eq_mul_inv,mul_comm]

theorem realMatrix_mul (M N : Matrix (Fin 2) (Fin 2) ℤ) :
    realMatrix (M*N)=realMatrix M*realMatrix N := by
  exact Matrix.map_mul

/-- Multiplication of the normalized matrices needs only integral arithmetic
provided the determinant stays in {1,2}. -/
theorem lift_mul (M N P : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : M.det=1 ∨ M.det=2) (hN : N.det=1 ∨ N.det=2)
    (hP : P.det=1 ∨ P.det=2) (hprod : M*N=P) :
    liftMatrix M hM*liftMatrix N hN=liftMatrix P hP := by
  have hd : M.det*N.det=P.det := by rw [← Matrix.det_mul,hprod]
  have hr : realMatrix M*realMatrix N=realMatrix P := by rw [← realMatrix_mul,hprod]
  rcases hM with hm|hm <;> rcases hN with hn|hn
  · have hp : P.det=1 := by rw [hm,hn] at hd; omega
    apply Units.ext
    change (liftMatrix M _).val*(liftMatrix N _).val=(liftMatrix P _).val
    rw [lift_val_one _ _ hm,lift_val_one _ _ hn,lift_val_one _ _ hp]
    exact hr
  · have hp : P.det=2 := by rw [hm,hn] at hd; omega
    apply Units.ext
    change (liftMatrix M _).val*(liftMatrix N _).val=(liftMatrix P _).val
    rw [lift_val_one _ _ hm,lift_val_two _ _ hn,lift_val_two _ _ hp,Matrix.mul_smul,hr]
  · have hp : P.det=2 := by rw [hm,hn] at hd; omega
    apply Units.ext
    change (liftMatrix M _).val*(liftMatrix N _).val=(liftMatrix P _).val
    rw [lift_val_two _ _ hm,lift_val_one _ _ hn,lift_val_two _ _ hp,Matrix.smul_mul,hr]
  · rcases hP with hp|hp <;> rw [hm,hn,hp] at hd <;> norm_num at hd

theorem lift_neg (M : Matrix (Fin 2) (Fin 2) ℤ)
    (h : M.det=1 ∨ M.det=2) (hn : (-M).det=1 ∨ (-M).det=2) :
    liftMatrix (-M) hn=(-1)*liftMatrix M h := by
  have hd : (-M).det=M.det := by simp [Matrix.det_neg]
  apply Units.ext
  change (liftMatrix (-M) hn).val=(-1 : Matrix (Fin 2) (Fin 2) ℝ)*(liftMatrix M h).val
  rw [neg_one_mul]
  rcases h with h1|h2
  · rw [lift_val_one _ _ (hd.trans h1),lift_val_one _ _ h1]
    ext i j
    simp [realMatrix]
  · rw [lift_val_two _ _ (hd.trans h2),lift_val_two _ _ h2]
    ext i j
    simp [realMatrix]

theorem lift_signed_mul (M N P : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : M.det=1 ∨ M.det=2) (hN : N.det=1 ∨ N.det=2)
    (hP : P.det=1 ∨ P.det=2) (negative : Bool)
    (hprod : M*N=if negative then -P else P) :
    liftMatrix M hM*liftMatrix N hN=signed negative (liftMatrix P hP) := by
  cases negative
  · exact lift_mul M N P hM hN hP hprod
  · have hn : (-P).det=1 ∨ (-P).det=2 := by simpa [Matrix.det_neg] using hP
    change _=(-1)*liftMatrix P hP
    rw [← lift_neg P hP hn]
    exact lift_mul M N (-P) hM hN hn hprod

#print axioms lift_mul
#print axioms lift_signed_mul
end QuantitativeArithmeticQuadraticMatrices
end
end

/-! ## QuantitativeArithmeticQuadraticUpperActionV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeArithmeticQuadraticMatrices
open Matrix UpperHalfPlane SmallLevelNormalized
open scoped MatrixGroups ModularForm

def upperFinite (b : ℤ) : GL (Fin 2) ℝ := quadraticMatrix 1 b 0 2 (by ring)
def upperInfinity (b : ℤ) : GL (Fin 2) ℝ := quadraticMatrix 2 b 0 1 (by ring)

theorem upperFinite_det (b : ℤ) : (GeneralLinearGroup.det (upperFinite b):ℝ)=1 := quadraticMatrix_det _ _ _ _ _
theorem upperInfinity_det (b : ℤ) : (GeneralLinearGroup.det (upperInfinity b):ℝ)=1 := quadraticMatrix_det _ _ _ _ _

theorem upperFinite_point (b : ℤ) (z : ℍ) :
    ((upperFinite b • z : ℍ):ℂ)=((z:ℂ)+b)/2 := by
  rw [coe_smul_of_det_pos (by rw [upperFinite_det]; norm_num)]
  norm_num [num,denom,upperFinite,quadraticMatrix,matrix,GeneralLinearGroup.mkOfDetNeZero]
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn : (Real.sqrt 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr sqrt_two_ne
  field_simp [hn]
  rw [hs]
  ring

theorem upperInfinity_point (b : ℤ) (z : ℍ) :
    ((upperInfinity b • z : ℍ):ℂ)=2*(z:ℂ)+b := by
  rw [coe_smul_of_det_pos (by rw [upperInfinity_det]; norm_num)]
  norm_num [num,denom,upperInfinity,quadraticMatrix,matrix,GeneralLinearGroup.mkOfDetNeZero]
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn : (Real.sqrt 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr sqrt_two_ne
  field_simp [hn]
  rw [hs]
  ring

theorem upperFinite_slash (b : ℤ) (m : ℕ) (F : ℍ → ℂ) (z : ℍ) :
    (F ∣[((2*m:ℕ):ℤ)] upperFinite b) z=((2:ℂ)^m)⁻¹*F (upperFinite b • z) := by
  rw [det_one_slash _ (upperFinite_det b)]
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hd : denom (upperFinite b) z=(Real.sqrt 2:ℂ) := by
    norm_num [denom,upperFinite,quadraticMatrix,matrix,GeneralLinearGroup.mkOfDetNeZero]
  rw [hd,zpow_neg,zpow_natCast,pow_mul,hs]
  ring

theorem upperInfinity_slash (b : ℤ) (m : ℕ) (F : ℍ → ℂ) (z : ℍ) :
    (F ∣[((2*m:ℕ):ℤ)] upperInfinity b) z=(2:ℂ)^m*F (upperInfinity b • z) := by
  rw [det_one_slash _ (upperInfinity_det b)]
  have hs : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hd : denom (upperInfinity b) z=(Real.sqrt 2:ℂ)⁻¹ := by
    norm_num [denom,upperInfinity,quadraticMatrix,matrix,GeneralLinearGroup.mkOfDetNeZero]
  rw [hd,zpow_neg,zpow_natCast,inv_pow,inv_inv,pow_mul,hs]
  ring
#print axioms upperFinite_slash
#print axioms upperInfinity_slash
end QuantitativeArithmeticQuadraticMatrices
end
end
