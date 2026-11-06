module
public import QuantitativeArithmeticSevenLaurentRowsTheoryV4
public import QuantitativeArithmeticSmallLevelThirtyThreeMinorNonzeroV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirtyThreeMinorRows
open QuantitativeArithmeticSevenLaurentRows

def row0 : Poly := [((1/1:ℚ),18,(-3,0,0,0,1,0,0)),((1/1:ℚ),18,(-3,1,0,0,1,0,0)),((1/1:ℚ),18,(-2,0,0,0,0,0,0)),((1/1:ℚ),18,(-2,1,0,0,0,0,0)),((1/1:ℚ),18,(-2,1,0,0,2,0,0)),((1/1:ℚ),18,(-2,2,0,0,2,0,0)),((-1/1:ℚ),18,(-1,0,0,0,1,0,0)),((1/1:ℚ),18,(-1,1,0,0,1,0,0)),((1/1:ℚ),18,(-1,2,0,0,1,0,0)),((-1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,2,0,0)),((1/1:ℚ),18,(1,0,0,0,1,0,0)),((1/1:ℚ),42,(-3,0,0,0,1,0,0)),((1/1:ℚ),42,(-3,1,0,0,1,0,0)),((1/1:ℚ),42,(-2,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,1,0,0,0,0,0)),((1/1:ℚ),42,(-1,0,0,0,1,0,0)),((-1/1:ℚ),42,(-1,1,0,0,1,0,0)),((-1/1:ℚ),42,(-1,2,0,0,1,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((-1/1:ℚ),42,(0,1,0,0,0,0,0)),((-1/1:ℚ),42,(0,2,0,0,0,0,0)),((-1/1:ℚ),42,(1,0,0,0,1,0,0)),((-1/1:ℚ),42,(2,0,0,0,0,0,0))]

def c0_18 (x y a : ℂ) : ℂ := (1/1:ℂ)*x^(-3:ℤ)*y^(0:ℤ)*a^1 + (1/1:ℂ)*x^(-3:ℤ)*y^(1:ℤ)*a^1 + (1/1:ℂ)*x^(-2:ℤ)*y^(0:ℤ)*a^0 + (1/1:ℂ)*x^(-2:ℤ)*y^(1:ℤ)*a^0 + (1/1:ℂ)*x^(-2:ℤ)*y^(1:ℤ)*a^2 + (1/1:ℂ)*x^(-2:ℤ)*y^(2:ℤ)*a^2 + (-1/1:ℂ)*x^(-1:ℤ)*y^(0:ℤ)*a^1 + (1/1:ℂ)*x^(-1:ℤ)*y^(1:ℤ)*a^1 + (1/1:ℂ)*x^(-1:ℤ)*y^(2:ℤ)*a^1 + (-1/1:ℂ)*x^(0:ℤ)*y^(0:ℤ)*a^0 + (1/1:ℂ)*x^(0:ℤ)*y^(0:ℤ)*a^2 + (1/1:ℂ)*x^(1:ℤ)*y^(0:ℤ)*a^1

def c0_42 (x y a : ℂ) : ℂ := (1/1:ℂ)*x^(-3:ℤ)*y^(0:ℤ)*a^1 + (1/1:ℂ)*x^(-3:ℤ)*y^(1:ℤ)*a^1 + (1/1:ℂ)*x^(-2:ℤ)*y^(0:ℤ)*a^0 + (1/1:ℂ)*x^(-2:ℤ)*y^(1:ℤ)*a^0 + (1/1:ℂ)*x^(-1:ℤ)*y^(0:ℤ)*a^1 + (-1/1:ℂ)*x^(-1:ℤ)*y^(1:ℤ)*a^1 + (-1/1:ℂ)*x^(-1:ℤ)*y^(2:ℤ)*a^1 + (1/1:ℂ)*x^(0:ℤ)*y^(0:ℤ)*a^0 + (-1/1:ℂ)*x^(0:ℤ)*y^(1:ℤ)*a^0 + (-1/1:ℂ)*x^(0:ℤ)*y^(2:ℤ)*a^0 + (-1/1:ℂ)*x^(1:ℤ)*y^(0:ℤ)*a^1 + (-1/1:ℂ)*x^(2:ℤ)*y^(0:ℤ)*a^0

theorem row0_eval (x y z a : ℂ) (v : ℕ→ℂ) :
    eval x y z 1 a 1 1 v row0=c0_18 x y a*v 18+c0_42 x y a*v 42 := by
  norm_num [row0,c0_18,c0_42,eval,monomial] <;> ring

def row9 : Poly := [((-1/1:ℚ),18,(-4,0,0,0,0,0,0)),((-1/1:ℚ),18,(-3,0,0,0,1,0,0)),((-1/1:ℚ),18,(-3,1,0,0,1,0,0)),((-1/1:ℚ),18,(-2,0,0,0,0,0,0)),((-1/1:ℚ),18,(-2,1,0,0,2,0,0)),((-1/1:ℚ),18,(-1,1,0,0,1,0,0)),((-1/1:ℚ),42,(-4,0,0,0,0,0,0)),((-1/1:ℚ),42,(-3,0,0,0,1,0,0)),((-1/1:ℚ),42,(-2,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,1,0,0,0,0,0)),((1/1:ℚ),42,(-1,1,0,0,1,0,0)),((1/1:ℚ),42,(0,1,0,0,0,0,0))]

def c9_18 (x y a : ℂ) : ℂ := (-1/1:ℂ)*x^(-4:ℤ)*y^(0:ℤ)*a^0 + (-1/1:ℂ)*x^(-3:ℤ)*y^(0:ℤ)*a^1 + (-1/1:ℂ)*x^(-3:ℤ)*y^(1:ℤ)*a^1 + (-1/1:ℂ)*x^(-2:ℤ)*y^(0:ℤ)*a^0 + (-1/1:ℂ)*x^(-2:ℤ)*y^(1:ℤ)*a^2 + (-1/1:ℂ)*x^(-1:ℤ)*y^(1:ℤ)*a^1

def c9_42 (x y a : ℂ) : ℂ := (-1/1:ℂ)*x^(-4:ℤ)*y^(0:ℤ)*a^0 + (-1/1:ℂ)*x^(-3:ℤ)*y^(0:ℤ)*a^1 + (-1/1:ℂ)*x^(-2:ℤ)*y^(0:ℤ)*a^0 + (1/1:ℂ)*x^(-2:ℤ)*y^(1:ℤ)*a^0 + (1/1:ℂ)*x^(-1:ℤ)*y^(1:ℤ)*a^1 + (1/1:ℂ)*x^(0:ℤ)*y^(1:ℤ)*a^0

theorem row9_eval (x y z a : ℂ) (v : ℕ→ℂ) :
    eval x y z 1 a 1 1 v row9=c9_18 x y a*v 18+c9_42 x y a*v 42 := by
  norm_num [row9,c9_18,c9_42,eval,monomial] <;> ring

theorem minor_eq (x y a : ℂ) (hx : x≠0) :
    c9_18 x y a*c0_42 x y a-c9_42 x y a*c0_18 x y a=
      QuantitativeArithmeticSmallLevelThirtyThreeMinor.determinant x y a := by
  norm_num [c9_18,c0_42,c9_42,c0_18,QuantitativeArithmeticSmallLevelThirtyThreeMinor.determinant]
  field_simp [hx]
  ring

theorem two_rows_zero (x y z a : ℂ) (v : ℕ→ℂ) (hx : x≠0)
    (hd : QuantitativeArithmeticSmallLevelThirtyThreeMinor.determinant x y a≠0)
    (h0 : eval x y z 1 a 1 1 v row0=0)
    (h9 : eval x y z 1 a 1 1 v row9=0) : v 18=0 ∧ v 42=0 := by
  rw [row0_eval] at h0
  rw [row9_eval] at h9
  have h18 : QuantitativeArithmeticSmallLevelThirtyThreeMinor.determinant x y a*v 18=0 := by
    rw [← minor_eq x y a hx]
    linear_combination c0_42 x y a*h9-c9_42 x y a*h0
  have h42 : QuantitativeArithmeticSmallLevelThirtyThreeMinor.determinant x y a*v 42=0 := by
    rw [← minor_eq x y a hx]
    linear_combination c9_18 x y a*h0-c0_18 x y a*h9
  exact ⟨(mul_eq_zero.mp h18).resolve_left hd,(mul_eq_zero.mp h42).resolve_left hd⟩

#print axioms minor_eq
#print axioms two_rows_zero
end QuantitativeArithmeticSmallLevelThirtyThreeMinorRows
