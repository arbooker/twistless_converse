module
public import QuantitativeArithmeticSparseEliminationV1
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
@[expose] public noncomputable section
namespace QuantitativeArithmeticCompact35DenominatorRepair
theorem normalized_pivots (X Y a b : ℂ)
    (hD1 : 2*X^2+2*X*a+2 ≠ 0)
    (hD2 : X^4+X*a+(-1)*Y*b+(-1) ≠ 0)
    (hD3 : Y^2+Y*b+5 ≠ 0)
    (hD10 : X^6+X^5*a+X^4*a^2+2*X^3*a+X^2*a^2+X*a+1 ≠ 0) :
    (1+X*a+X^2 ≠ 0) ∧ (-1-Y*b+X*a+X^4 ≠ 0) ∧
    (5+Y*b+Y^2 ≠ 0) ∧
    (1+X*a+X^2*a^2+X^3*a*2+X^4*a^2+X^5*a+X^6 ≠ 0) := by
  have hQ : 1+X*a+X^2 ≠ 0 := by
    intro h
    apply hD1
    calc
      2*X^2+2*X*a+2 = 2*(1+X*a+X^2) := by ring
      _ = 0 := by rw [h]; ring
  have hR : -1-Y*b+X*a+X^4 ≠ 0 := by
    convert hD2 using 1 <;> ring
  have hS : 5+Y*b+Y^2 ≠ 0 := by
    convert hD3 using 1 <;> ring
  have hT : 1+X*a+X^2*a^2+X^3*a*2+X^4*a^2+X^5*a+X^6 ≠ 0 := by
    convert hD10 using 1 <;> ring
  exact ⟨hQ,hR,hS,hT⟩

section Parameters
variable (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (hD0 : (X^2*Y^2 + X*Y^2*a + Y^2)≠0)
    (hD1 : ((2)*X^2 + (2)*X*a + (2))≠0)
    (hD2 : (X^4 + X*a + (-1)*Y*b + (-1))≠0)
    (hD3 : (Y^2 + Y*b + (5))≠0)
    (hD4 : (X^2 + X*a)≠0)
    (hD5 : (X + a)≠0)
    (hD6 : (X^4 + X^3*a)≠0)
    (hD7 : (X^3 + X^2*a)≠0)
    (hD8 : (X^6 + X^5*a)≠0)
    (hD9 : (X^5 + X^4*a)≠0)
    (hD10 : (X^6 + X^5*a + X^4*a^2 + (2)*X^3*a + X^2*a^2 + X*a + (1))≠0)
include hX hY hZ hW hD0 hD1 hD2 hD3 hD4 hD5 hD6 hD7 hD8 hD9 hD10



theorem row82 (v : ℕ → ℂ) : (((1)))*(v 127) + (0) = (X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*((((1)))*(v 184) + (((((-1)*a)/(X)))*(v 180) + (((((1))/(X^2)))*(v 188) + ((((1)))*(v 154) + (0))))) + (((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-((-1 * X ^ 2 * Y ^ 2 + -1 * Y ^ 2) / (X ^ 2 * Z * W))))*((((1)))*(v 128) + ((((1)))*(v 127) + (0))) + (((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-(1)))*((((Y^2)/(Z*W)))*(v 128) + ((((1)))*(v 154) + (0))) + (((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-(-1 * a / X)))*((((1)))*(v 180) + ((((Y^2)/(Z*W)))*(v 127) + (0))) + (((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-(1)))*((((1)))*(v 184) + ((((Y^2)/(X^2*Z*W)))*(v 128) + (0))) + (((X ^ 2 * Z * W / (X ^ 2 * Y ^ 2 + X * Y ^ 2 * a + Y ^ 2))*(-(1 / X ^ 2)))*((((1)))*(v 188) + (0)) + (0)))))) := by
  obtain ⟨hQ,hR,hS,hT⟩ := normalized_pivots X Y a b hD1 hD2 hD3 hD10

  field_simp [hX,hY,hZ,hW,hD0,hD1,hD2,hD3,hD4,hD5,hD6,hD7,hD8,hD9,hD10] <;> ring_nf
  all_goals field_simp [hQ,hR,hS,hT] <;> ring
#print axioms row82
theorem row105 (v : ℕ → ℂ) : (((1)))*(v 104) + (0) = (X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2))*(((((1))/(X^2)))*(v 104) + ((((1)))*(v 172) + (((((-1)*a)/(X)))*(v 101) + ((((1)))*(v 176) + (0))))) + (((X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2))*(-(-1 * Y ^ 2 * W / (X ^ 2 * Z))))*((((X^2*Z + (2)*X*Z*a + Z)/(Y^2*W)))*(v 104) + ((((X*Z*a)/(Y^2*W)))*(v 101) + ((((1)))*(v 105) + (0)))) + (((X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2))*(-(-1 * W / Z)))*((((1)))*(v 143) + ((((Z)/(W)))*(v 104) + (0))) + (((X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2))*(-(1)))*((((1)))*(v 172) + ((((Y^2*W)/(X^2*Z)))*(v 105) + (0))) + (((X ^ 2 / (2 * X ^ 2 + 2 * X * a + 2))*(-(1)))*((((W)/(Z)))*(v 143) + ((((1)))*(v 176) + (0))) + (0))))) := by
  obtain ⟨hQ,hR,hS,hT⟩ := normalized_pivots X Y a b hD1 hD2 hD3 hD10

  field_simp [hX,hY,hZ,hW,hD0,hD1,hD2,hD3,hD4,hD5,hD6,hD7,hD8,hD9,hD10] <;> ring_nf
  all_goals field_simp [hQ,hR,hS,hT] <;> ring
#print axioms row105
theorem row108 (v : ℕ → ℂ) : (((1)))*(v 101) + (0) = (-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*((((1)))*(v 177) + (((((1))/(Y^2)))*(v 104) + (((((-1)*b)/(Y)))*(v 109) + ((((1)))*(v 148) + ((((1)))*(v 176) + (0)))))) + (((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(-1 * X ^ 2 * W / (Y ^ 2 * Z))))*(((((-1)*X^3*Z + X*Z + (-1)*Z*a)/(X*W)))*(v 101) + ((((1)))*(v 102) + (0))) + (((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(-1 * W / (Y ^ 2 * Z))))*(((((-1)*X^2*Z + Z)/(W)))*(v 101) + ((((1)))*(v 103) + (0))) + (((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-((Y ^ 2 + 2 * Y * b + 1) / Y ^ 2)))*((((1)))*(v 104) + (0)) + (((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(-1 * b / Y)))*((((2)))*(v 104) + ((((1)))*(v 109) + ((((1)))*(v 101) + (0)))) + (((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(-1 * W / Z)))*((((1)))*(v 143) + ((((Z)/(W)))*(v 104) + (0))) + (((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(1)))*((((1)))*(v 148) + ((((W)/(Y^2*Z)))*(v 103) + (0))) + (((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(1)))*((((W)/(Z)))*(v 143) + ((((1)))*(v 176) + (0))) + (((-1 * Y ^ 2 / (X ^ 4 + X * a + -1 * Y * b + -1))*(-(1)))*((((1)))*(v 177) + ((((X^2*W)/(Y^2*Z)))*(v 102) + (0))) + (0))))))))) := by
  obtain ⟨hQ,hR,hS,hT⟩ := normalized_pivots X Y a b hD1 hD2 hD3 hD10

  field_simp [hX,hY,hZ,hW,hD0,hD1,hD2,hD3,hD4,hD5,hD6,hD7,hD8,hD9,hD10] <;> ring_nf
  all_goals field_simp [hQ,hR,hS,hT] <;> ring
#print axioms row108
theorem row143 (v : ℕ → ℂ) : (((1)))*(v 66) + (0) = (-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*((((1)))*(v 130) + (((((1))/(Y^2)))*(v 112) + (((((-1)*b)/(Y)))*(v 158) + ((((1)))*(v 145) + ((((1)))*(v 133) + (0)))))) + (((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(-1 / (X ^ 2 * Y ^ 2))))*((((-2)))*(v 66) + ((((1)))*(v 67) + (0))) + (((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1 / (X ^ 2 * Y ^ 2))))*((((2)))*(v 66) + ((((1)))*(v 69) + (0))) + (((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1 / (X ^ 2 * Y ^ 2))))*((((1)))*(v 72) + ((((1)))*(v 67) + (0))) + (((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(-1 / (X ^ 2 * Y ^ 2))))*((((1)))*(v 69) + ((((1)))*(v 73) + (0))) + (((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1 / Y ^ 2)))*((((1)))*(v 112) + (((((1))/(X^2)))*(v 73) + (0))) + (((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-((Y ^ 2 + 1) / (X ^ 2 * Y ^ 2))))*((((1)))*(v 66) + ((((1)))*(v 120) + (0))) + (((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1)))*((((1)))*(v 130) + (((((-1))/(X^2)))*(v 120) + (0))) + (((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1)))*(((((-1))/(X^2*Y^2)))*(v 72) + ((((1)))*(v 133) + (0))) + (((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(1)))*((((1)))*(v 145) + (((((-1))/(X^2*Y^2)))*(v 120) + (0))) + (((-1 * X ^ 2 * Y ^ 2 / (Y ^ 2 + Y * b + 5))*(-(-1 * b / Y)))*(((((-1))/(X^2)))*(v 66) + ((((1)))*(v 158) + (0))) + (0))))))))))) := by
  obtain ⟨hQ,hR,hS,hT⟩ := normalized_pivots X Y a b hD1 hD2 hD3 hD10

  field_simp [hX,hY,hZ,hW,hD0,hD1,hD2,hD3,hD4,hD5,hD6,hD7,hD8,hD9,hD10] <;> ring_nf
  all_goals field_simp [hQ,hR,hS,hT] <;> ring
#print axioms row143
theorem row207 (v : ℕ → ℂ) : (((1)))*(v 2) + (0) = ((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*((((1)))*(v 33) + (((((-1)*a)/(X)))*(v 39) + (((((1))/(X^2)))*(v 14) + ((((1)))*(v 43) + (0))))) + ((((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(-1 / X ^ 2)))*((((X^3*a + X^2*a^2 + X*a + (1))/(X^4 + X^3*a)))*(v 2) + ((((1)))*(v 3) + (0))) + ((((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(a / X)))*((((1)))*(v 4) + (((((-1)*X*a + (-1))/(X^2 + X*a)))*(v 2) + (0))) + ((((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(-1)))*((((1)))*(v 13) + ((((1)))*(v 2) + (0))) + ((((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(1 / X ^ 2)))*((((1)))*(v 14) + ((((1)))*(v 3) + (0))) + ((((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(1)))*((((1)))*(v 33) + ((((1)))*(v 13) + (0))) + ((((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(-1 * a / X)))*((((1)))*(v 39) + ((((1)))*(v 4) + (0))) + ((((X ^ 6 + X ^ 5 * a) / (X ^ 6 + X ^ 5 * a + X ^ 4 * a ^ 2 + 2 * X ^ 3 * a + X ^ 2 * a ^ 2 + X * a + 1))*(-(1)))*((((1)))*(v 43) + (0)) + (0)))))))) := by
  obtain ⟨hQ,hR,hS,hT⟩ := normalized_pivots X Y a b hD1 hD2 hD3 hD10

  field_simp [hX,hY,hZ,hW,hD0,hD1,hD2,hD3,hD4,hD5,hD6,hD7,hD8,hD9,hD10] <;> ring_nf
  all_goals field_simp [hQ,hR,hS,hT] <;> ring
#print axioms row207
end Parameters
end QuantitativeArithmeticCompact35DenominatorRepair
