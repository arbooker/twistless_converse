module
public meta import QuantitativeArithmeticCompactCommandsV1
public import QuantitativeArithmeticSmallLevelThirtyThreePlusEliminationTheoryV4

-- Editor-info-based tactic linting is unavailable inside compact certificates.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-! Complete mathematical proof chains; intermediate development files merged. -/
@[expose] public noncomputable section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
open QuantitativeArithmeticSevenLaurentRows
private theorem row_left_minor0 : allRow 3=[((-1/1:ℚ),18,(-4,0,0,0,0,0,0)),((-1/1:ℚ),18,(-3,0,0,0,1,0,0)),((-1/1:ℚ),18,(-3,1,0,0,1,0,0)),((-1/1:ℚ),18,(-2,0,0,0,0,0,0)),((-1/1:ℚ),18,(-2,1,0,0,2,0,0)),((-1/1:ℚ),18,(-1,1,0,0,1,0,0)),((-1/1:ℚ),42,(-4,0,0,0,0,0,0)),((-1/1:ℚ),42,(-3,0,0,0,1,0,0)),((-1/1:ℚ),42,(-2,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,1,0,0,0,0,0)),((1/1:ℚ),42,(-1,1,0,0,1,0,0)),((1/1:ℚ),42,(0,1,0,0,0,0,0))] := rfl
private theorem row_right_minor0 : allRow 22=[((-66/1:ℚ),18,(-4,-1,0,0,0,0,0)),((-44/1:ℚ),18,(-4,0,0,0,0,0,0)),((-66/1:ℚ),18,(-3,0,0,0,1,0,0)),((-44/1:ℚ),18,(-3,1,0,0,1,0,0)),((132/1:ℚ),18,(-2,-1,0,0,0,0,0)),((198/1:ℚ),18,(-1,-1,0,0,1,0,0)),((-66/1:ℚ),42,(-4,-1,0,0,0,0,0)),((-44/1:ℚ),42,(-4,0,0,0,0,0,0)),((132/1:ℚ),42,(-2,-1,0,0,0,0,0)),((66/1:ℚ),42,(-2,0,0,0,0,0,0)),((44/1:ℚ),42,(-2,1,0,0,0,0,0)),((-198/1:ℚ),42,(0,-1,0,0,0,0,0))] := rfl

compact_certificate theorem minor0_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) :
    coefficientAt x y z a (allRow 3) 18*coefficientAt x y z a (allRow 22) 42-
      coefficientAt x y z a (allRow 3) 42*coefficientAt x y z a (allRow 22) 18=
      (-132/1:ℂ)*x^(-6:ℤ)*y^(-1:ℤ)*z^(0:ℤ)*
        eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor0 := by
  rw [row_left_minor0,row_right_minor0]
  norm_num [coefficientAt,eval,monomial,minor0]
  field_simp [hx,hy,hz]
  ring

compact_certificate theorem minor0_zero (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hn : v 18≠0 ∨ v 42≠0)
    (hrows : ∀ i : Fin 23,eval x y z 1 a 1 1 v (allRow i)=0) :
    eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor0=0 := by
  have hh := two_coordinate_minor_zero x y z a (allRow 3) (allRow 22) v 18 42
    (by decide) (allRow_support 3) (allRow_support 22) hn (hrows 3) (hrows 22)
  rw [minor0_identity x y z a hx hy hz] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (zpow_ne_zero _ hx)
      · exact zpow_ne_zero _ hy
    · exact zpow_ne_zero _ hz)

#print axioms minor0_zero

private theorem row_left_minor3 : allRow 0=[((1/1:ℚ),18,(-3,0,0,0,1,0,0)),((1/1:ℚ),18,(-3,1,0,0,1,0,0)),((1/1:ℚ),18,(-2,0,0,0,0,0,0)),((1/1:ℚ),18,(-2,1,0,0,0,0,0)),((1/1:ℚ),18,(-2,1,0,0,2,0,0)),((1/1:ℚ),18,(-2,2,0,0,2,0,0)),((-1/1:ℚ),18,(-1,0,0,0,1,0,0)),((1/1:ℚ),18,(-1,1,0,0,1,0,0)),((1/1:ℚ),18,(-1,2,0,0,1,0,0)),((-1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,2,0,0)),((1/1:ℚ),18,(1,0,0,0,1,0,0)),((1/1:ℚ),42,(-3,0,0,0,1,0,0)),((1/1:ℚ),42,(-3,1,0,0,1,0,0)),((1/1:ℚ),42,(-2,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,1,0,0,0,0,0)),((1/1:ℚ),42,(-1,0,0,0,1,0,0)),((-1/1:ℚ),42,(-1,1,0,0,1,0,0)),((-1/1:ℚ),42,(-1,2,0,0,1,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((-1/1:ℚ),42,(0,1,0,0,0,0,0)),((-1/1:ℚ),42,(0,2,0,0,0,0,0)),((-1/1:ℚ),42,(1,0,0,0,1,0,0)),((-1/1:ℚ),42,(2,0,0,0,0,0,0))] := rfl
private theorem row_right_minor3 : allRow 22=[((-66/1:ℚ),18,(-4,-1,0,0,0,0,0)),((-44/1:ℚ),18,(-4,0,0,0,0,0,0)),((-66/1:ℚ),18,(-3,0,0,0,1,0,0)),((-44/1:ℚ),18,(-3,1,0,0,1,0,0)),((132/1:ℚ),18,(-2,-1,0,0,0,0,0)),((198/1:ℚ),18,(-1,-1,0,0,1,0,0)),((-66/1:ℚ),42,(-4,-1,0,0,0,0,0)),((-44/1:ℚ),42,(-4,0,0,0,0,0,0)),((132/1:ℚ),42,(-2,-1,0,0,0,0,0)),((66/1:ℚ),42,(-2,0,0,0,0,0,0)),((44/1:ℚ),42,(-2,1,0,0,0,0,0)),((-198/1:ℚ),42,(0,-1,0,0,0,0,0))] := rfl

compact_certificate theorem minor3_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) :
    coefficientAt x y z a (allRow 0) 18*coefficientAt x y z a (allRow 22) 42-
      coefficientAt x y z a (allRow 0) 42*coefficientAt x y z a (allRow 22) 18=
      (330/1:ℂ)*x^(-6:ℤ)*y^(-1:ℤ)*z^(0:ℤ)*
        eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor3 := by
  rw [row_left_minor3,row_right_minor3]
  norm_num [coefficientAt,eval,monomial,minor3]
  field_simp [hx,hy,hz]
  ring

compact_certificate theorem minor3_zero (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hn : v 18≠0 ∨ v 42≠0)
    (hrows : ∀ i : Fin 23,eval x y z 1 a 1 1 v (allRow i)=0) :
    eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor3=0 := by
  have hh := two_coordinate_minor_zero x y z a (allRow 0) (allRow 22) v 18 42
    (by decide) (allRow_support 0) (allRow_support 22) hn (hrows 0) (hrows 22)
  rw [minor3_identity x y z a hx hy hz] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (zpow_ne_zero _ hx)
      · exact zpow_ne_zero _ hy
    · exact zpow_ne_zero _ hz)

#print axioms minor3_zero

private theorem row_left_minor6 : allRow 3=[((-1/1:ℚ),18,(-4,0,0,0,0,0,0)),((-1/1:ℚ),18,(-3,0,0,0,1,0,0)),((-1/1:ℚ),18,(-3,1,0,0,1,0,0)),((-1/1:ℚ),18,(-2,0,0,0,0,0,0)),((-1/1:ℚ),18,(-2,1,0,0,2,0,0)),((-1/1:ℚ),18,(-1,1,0,0,1,0,0)),((-1/1:ℚ),42,(-4,0,0,0,0,0,0)),((-1/1:ℚ),42,(-3,0,0,0,1,0,0)),((-1/1:ℚ),42,(-2,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,1,0,0,0,0,0)),((1/1:ℚ),42,(-1,1,0,0,1,0,0)),((1/1:ℚ),42,(0,1,0,0,0,0,0))] := rfl
private theorem row_right_minor6 : allRow 11=[((1/1:ℚ),18,(-4,-1,0,0,0,0,0)),((-1/1:ℚ),18,(-4,-1,1,0,0,0,0)),((-3/1:ℚ),18,(-4,0,0,0,0,0,0)),((-2/1:ℚ),18,(-4,1,0,0,0,0,0)),((2/1:ℚ),18,(-3,-1,0,0,1,0,0)),((1/1:ℚ),18,(-3,0,0,0,1,0,0)),((-1/1:ℚ),18,(-3,0,1,0,1,0,0)),((-3/1:ℚ),18,(-3,1,0,0,1,0,0)),((-2/1:ℚ),18,(-3,2,0,0,1,0,0)),((1/1:ℚ),18,(-2,-1,1,0,0,0,0)),((3/1:ℚ),18,(-2,0,0,0,0,0,0)),((2/1:ℚ),18,(-2,0,0,0,2,0,0)),((1/1:ℚ),18,(-2,1,0,0,0,0,0)),((-3/1:ℚ),18,(-1,-1,0,0,1,0,0)),((-2/1:ℚ),18,(-1,0,0,0,1,0,0)),((1/1:ℚ),18,(-1,0,1,0,1,0,0)),((2/1:ℚ),18,(-1,1,0,0,1,0,0)),((1/1:ℚ),18,(-1,2,0,0,1,0,0)),((1/1:ℚ),18,(0,-1,0,0,0,0,0)),((-1/1:ℚ),18,(0,0,0,0,2,0,0)),((2/1:ℚ),18,(1,-1,0,0,1,0,0)),((1/1:ℚ),18,(1,0,0,0,1,0,0)),((-1/1:ℚ),18,(2,-1,0,0,0,0,0)),((1/1:ℚ),42,(-4,-1,0,0,0,0,0)),((-1/1:ℚ),42,(-4,-1,1,0,0,0,0)),((-3/1:ℚ),42,(-4,0,0,0,0,0,0)),((-2/1:ℚ),42,(-4,1,0,0,0,0,0)),((2/1:ℚ),42,(-3,-1,0,0,1,0,0)),((-1/1:ℚ),42,(-2,-1,0,0,0,0,0)),((1/1:ℚ),42,(-2,-1,1,0,0,0,0)),((1/1:ℚ),42,(-2,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,0,1,0,0,0,0)),((4/1:ℚ),42,(-2,1,0,0,0,0,0)),((2/1:ℚ),42,(-2,2,0,0,0,0,0)),((-1/1:ℚ),42,(-1,-1,0,0,1,0,0)),((-2/1:ℚ),42,(-1,0,0,0,1,0,0)),((3/1:ℚ),42,(0,-1,0,0,0,0,0)),((2/1:ℚ),42,(0,0,0,0,0,0,0)),((-1/1:ℚ),42,(0,0,1,0,0,0,0)),((-2/1:ℚ),42,(0,1,0,0,0,0,0)),((-1/1:ℚ),42,(0,2,0,0,0,0,0)),((1/1:ℚ),42,(1,0,0,0,1,0,0)),((-2/1:ℚ),42,(2,-1,0,0,0,0,0)),((-1/1:ℚ),42,(2,0,0,0,0,0,0))] := rfl

compact_certificate theorem minor6_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) :
    coefficientAt x y z a (allRow 3) 18*coefficientAt x y z a (allRow 11) 42-
      coefficientAt x y z a (allRow 3) 42*coefficientAt x y z a (allRow 11) 18=
      (1/1:ℂ)*x^(-6:ℤ)*y^(-1:ℤ)*z^(0:ℤ)*
        eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor6 := by
  rw [row_left_minor6,row_right_minor6]
  norm_num [coefficientAt,eval,monomial,minor6]
  field_simp [hx,hy,hz]
  ring

compact_certificate theorem minor6_zero (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hn : v 18≠0 ∨ v 42≠0)
    (hrows : ∀ i : Fin 23,eval x y z 1 a 1 1 v (allRow i)=0) :
    eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor6=0 := by
  have hh := two_coordinate_minor_zero x y z a (allRow 3) (allRow 11) v 18 42
    (by decide) (allRow_support 3) (allRow_support 11) hn (hrows 3) (hrows 11)
  rw [minor6_identity x y z a hx hy hz] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (zpow_ne_zero _ hx)
      · exact zpow_ne_zero _ hy
    · exact zpow_ne_zero _ hz)

#print axioms minor6_zero

private theorem row_left_minor12 : allRow 15=[((-2/1:ℚ),18,(-4,-1,0,0,0,0,0)),((1/1:ℚ),18,(-4,-1,1,0,0,0,0)),((1/1:ℚ),18,(-4,0,0,0,0,0,0)),((1/1:ℚ),18,(-4,1,0,0,0,0,0)),((-2/1:ℚ),18,(-3,-1,0,0,1,0,0)),((-2/1:ℚ),18,(-3,0,0,0,1,0,0)),((1/1:ℚ),18,(-3,0,1,0,1,0,0)),((1/1:ℚ),18,(-3,1,0,0,1,0,0)),((1/1:ℚ),18,(-3,2,0,0,1,0,0)),((-1/1:ℚ),18,(-2,-1,0,0,0,0,0)),((-2/1:ℚ),18,(-2,0,0,0,2,0,0)),((-1/1:ℚ),18,(-1,0,0,0,1,0,0)),((-1/1:ℚ),18,(0,-1,0,0,0,0,0)),((-1/1:ℚ),18,(0,0,0,0,2,0,0)),((-1/1:ℚ),18,(1,-1,0,0,1,0,0)),((-1/1:ℚ),18,(2,-1,0,0,0,0,0)),((-2/1:ℚ),42,(-4,-1,0,0,0,0,0)),((1/1:ℚ),42,(-4,-1,1,0,0,0,0)),((1/1:ℚ),42,(-4,0,0,0,0,0,0)),((1/1:ℚ),42,(-4,1,0,0,0,0,0)),((-2/1:ℚ),42,(-3,-1,0,0,1,0,0)),((-2/1:ℚ),42,(-2,-1,0,0,0,0,0)),((1/1:ℚ),42,(-2,0,0,0,0,0,0)),((-1/1:ℚ),42,(-2,0,1,0,0,0,0)),((-1/1:ℚ),42,(-2,1,0,0,0,0,0)),((-1/1:ℚ),42,(-2,2,0,0,0,0,0)),((-1/1:ℚ),42,(-1,-1,0,0,1,0,0)),((2/1:ℚ),42,(-1,0,0,0,1,0,0)),((-2/1:ℚ),42,(0,-1,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(1,0,0,0,1,0,0)),((1/1:ℚ),42,(2,-1,0,0,0,0,0))] := rfl
private theorem row_right_minor12 : allRow 22=[((-66/1:ℚ),18,(-4,-1,0,0,0,0,0)),((-44/1:ℚ),18,(-4,0,0,0,0,0,0)),((-66/1:ℚ),18,(-3,0,0,0,1,0,0)),((-44/1:ℚ),18,(-3,1,0,0,1,0,0)),((132/1:ℚ),18,(-2,-1,0,0,0,0,0)),((198/1:ℚ),18,(-1,-1,0,0,1,0,0)),((-66/1:ℚ),42,(-4,-1,0,0,0,0,0)),((-44/1:ℚ),42,(-4,0,0,0,0,0,0)),((132/1:ℚ),42,(-2,-1,0,0,0,0,0)),((66/1:ℚ),42,(-2,0,0,0,0,0,0)),((44/1:ℚ),42,(-2,1,0,0,0,0,0)),((-198/1:ℚ),42,(0,-1,0,0,0,0,0))] := rfl

compact_certificate theorem minor12_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) :
    coefficientAt x y z a (allRow 15) 18*coefficientAt x y z a (allRow 22) 42-
      coefficientAt x y z a (allRow 15) 42*coefficientAt x y z a (allRow 22) 18=
      (198/1:ℂ)*x^(-6:ℤ)*y^(-2:ℤ)*z^(0:ℤ)*
        eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor12 := by
  rw [row_left_minor12,row_right_minor12]
  norm_num [coefficientAt,eval,monomial,minor12]
  field_simp [hx,hy,hz]
  ring

compact_certificate theorem minor12_zero (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hn : v 18≠0 ∨ v 42≠0)
    (hrows : ∀ i : Fin 23,eval x y z 1 a 1 1 v (allRow i)=0) :
    eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor12=0 := by
  have hh := two_coordinate_minor_zero x y z a (allRow 15) (allRow 22) v 18 42
    (by decide) (allRow_support 15) (allRow_support 22) hn (hrows 15) (hrows 22)
  rw [minor12_identity x y z a hx hy hz] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (zpow_ne_zero _ hx)
      · exact zpow_ne_zero _ hy
    · exact zpow_ne_zero _ hz)

#print axioms minor12_zero

private theorem row_left_minor13 : allRow 0=[((1/1:ℚ),18,(-3,0,0,0,1,0,0)),((1/1:ℚ),18,(-3,1,0,0,1,0,0)),((1/1:ℚ),18,(-2,0,0,0,0,0,0)),((1/1:ℚ),18,(-2,1,0,0,0,0,0)),((1/1:ℚ),18,(-2,1,0,0,2,0,0)),((1/1:ℚ),18,(-2,2,0,0,2,0,0)),((-1/1:ℚ),18,(-1,0,0,0,1,0,0)),((1/1:ℚ),18,(-1,1,0,0,1,0,0)),((1/1:ℚ),18,(-1,2,0,0,1,0,0)),((-1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,2,0,0)),((1/1:ℚ),18,(1,0,0,0,1,0,0)),((1/1:ℚ),42,(-3,0,0,0,1,0,0)),((1/1:ℚ),42,(-3,1,0,0,1,0,0)),((1/1:ℚ),42,(-2,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,1,0,0,0,0,0)),((1/1:ℚ),42,(-1,0,0,0,1,0,0)),((-1/1:ℚ),42,(-1,1,0,0,1,0,0)),((-1/1:ℚ),42,(-1,2,0,0,1,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((-1/1:ℚ),42,(0,1,0,0,0,0,0)),((-1/1:ℚ),42,(0,2,0,0,0,0,0)),((-1/1:ℚ),42,(1,0,0,0,1,0,0)),((-1/1:ℚ),42,(2,0,0,0,0,0,0))] := rfl
private theorem row_right_minor13 : allRow 16=[((-2/1:ℚ),18,(-2,-1,0,0,0,0,0)),((1/1:ℚ),18,(-2,-1,1,0,0,0,0)),((2/1:ℚ),18,(-2,0,0,0,0,0,0)),((1/1:ℚ),18,(-2,1,0,0,0,0,0)),((-2/1:ℚ),18,(-1,-1,0,0,1,0,0)),((-2/1:ℚ),18,(-1,0,0,0,1,0,0)),((1/1:ℚ),18,(-1,0,1,0,1,0,0)),((2/1:ℚ),18,(-1,1,0,0,1,0,0)),((1/1:ℚ),18,(-1,2,0,0,1,0,0)),((-1/1:ℚ),18,(0,-1,0,0,0,0,0)),((-1/1:ℚ),18,(0,0,0,0,0,0,0)),((-2/1:ℚ),18,(0,0,0,0,2,0,0)),((1/1:ℚ),18,(1,-1,0,0,1,0,0)),((-1/1:ℚ),18,(1,1,0,0,1,0,0)),((-1/1:ℚ),18,(2,-1,0,0,0,0,0)),((-1/1:ℚ),18,(3,-1,0,0,1,0,0)),((-2/1:ℚ),42,(-2,-1,0,0,0,0,0)),((1/1:ℚ),42,(-2,-1,1,0,0,0,0)),((2/1:ℚ),42,(-2,0,0,0,0,0,0)),((1/1:ℚ),42,(-2,1,0,0,0,0,0)),((-2/1:ℚ),42,(-1,-1,0,0,1,0,0)),((-1/1:ℚ),42,(0,-1,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((-1/1:ℚ),42,(0,0,1,0,0,0,0)),((-2/1:ℚ),42,(0,1,0,0,0,0,0)),((-1/1:ℚ),42,(0,2,0,0,0,0,0)),((2/1:ℚ),42,(1,0,0,0,1,0,0)),((-2/1:ℚ),42,(2,-1,0,0,0,0,0)),((1/1:ℚ),42,(2,1,0,0,0,0,0)),((1/1:ℚ),42,(4,-1,0,0,0,0,0))] := rfl

compact_certificate theorem minor13_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) :
    coefficientAt x y z a (allRow 0) 18*coefficientAt x y z a (allRow 16) 42-
      coefficientAt x y z a (allRow 0) 42*coefficientAt x y z a (allRow 16) 18=
      (-2/1:ℂ)*x^(-4:ℤ)*y^(-1:ℤ)*z^(0:ℤ)*
        eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor13 := by
  rw [row_left_minor13,row_right_minor13]
  norm_num [coefficientAt,eval,monomial,minor13]
  field_simp [hx,hy,hz]
  ring

compact_certificate theorem minor13_zero (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hn : v 18≠0 ∨ v 42≠0)
    (hrows : ∀ i : Fin 23,eval x y z 1 a 1 1 v (allRow i)=0) :
    eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor13=0 := by
  have hh := two_coordinate_minor_zero x y z a (allRow 0) (allRow 16) v 18 42
    (by decide) (allRow_support 0) (allRow_support 16) hn (hrows 0) (hrows 16)
  rw [minor13_identity x y z a hx hy hz] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (zpow_ne_zero _ hx)
      · exact zpow_ne_zero _ hy
    · exact zpow_ne_zero _ hz)

#print axioms minor13_zero

private theorem row_left_minor25 : allRow 4=[((-2/1:ℚ),18,(-4,-1,0,0,0,0,0)),((1/1:ℚ),18,(-4,-1,1,0,0,0,0)),((1/1:ℚ),18,(-4,0,0,0,0,0,0)),((1/1:ℚ),18,(-4,1,0,0,0,0,0)),((-2/1:ℚ),18,(-3,-1,0,0,1,0,0)),((-2/1:ℚ),18,(-3,0,0,0,1,0,0)),((1/1:ℚ),18,(-3,0,1,0,1,0,0)),((1/1:ℚ),18,(-3,1,0,0,1,0,0)),((1/1:ℚ),18,(-3,2,0,0,1,0,0)),((1/1:ℚ),18,(-2,-1,0,0,0,0,0)),((-1/1:ℚ),18,(-2,-1,1,0,0,0,0)),((-2/1:ℚ),18,(-2,0,0,0,0,0,0)),((-2/1:ℚ),18,(-2,0,0,0,2,0,0)),((-1/1:ℚ),18,(-2,1,0,0,0,0,0)),((2/1:ℚ),18,(-1,-1,0,0,1,0,0)),((1/1:ℚ),18,(-1,0,0,0,1,0,0)),((-1/1:ℚ),18,(-1,0,1,0,1,0,0)),((-2/1:ℚ),18,(-1,1,0,0,1,0,0)),((-1/1:ℚ),18,(-1,2,0,0,1,0,0)),((1/1:ℚ),18,(0,0,0,0,0,0,0)),((1/1:ℚ),18,(0,0,0,0,2,0,0)),((-2/1:ℚ),18,(1,-1,0,0,1,0,0)),((1/1:ℚ),18,(1,1,0,0,1,0,0)),((1/1:ℚ),18,(3,-1,0,0,1,0,0)),((-2/1:ℚ),42,(-4,-1,0,0,0,0,0)),((1/1:ℚ),42,(-4,-1,1,0,0,0,0)),((1/1:ℚ),42,(-4,0,0,0,0,0,0)),((1/1:ℚ),42,(-4,1,0,0,0,0,0)),((-2/1:ℚ),42,(-3,-1,0,0,1,0,0)),((-1/1:ℚ),42,(-2,-1,1,0,0,0,0)),((-1/1:ℚ),42,(-2,0,0,0,0,0,0)),((-1/1:ℚ),42,(-2,0,1,0,0,0,0)),((-2/1:ℚ),42,(-2,1,0,0,0,0,0)),((-1/1:ℚ),42,(-2,2,0,0,0,0,0)),((1/1:ℚ),42,(-1,-1,0,0,1,0,0)),((2/1:ℚ),42,(-1,0,0,0,1,0,0)),((-1/1:ℚ),42,(0,-1,0,0,0,0,0)),((1/1:ℚ),42,(0,0,1,0,0,0,0)),((2/1:ℚ),42,(0,1,0,0,0,0,0)),((1/1:ℚ),42,(0,2,0,0,0,0,0)),((-1/1:ℚ),42,(1,0,0,0,1,0,0)),((3/1:ℚ),42,(2,-1,0,0,0,0,0)),((-1/1:ℚ),42,(2,1,0,0,0,0,0)),((-1/1:ℚ),42,(4,-1,0,0,0,0,0))] := rfl
private theorem row_right_minor25 : allRow 15=[((-2/1:ℚ),18,(-4,-1,0,0,0,0,0)),((1/1:ℚ),18,(-4,-1,1,0,0,0,0)),((1/1:ℚ),18,(-4,0,0,0,0,0,0)),((1/1:ℚ),18,(-4,1,0,0,0,0,0)),((-2/1:ℚ),18,(-3,-1,0,0,1,0,0)),((-2/1:ℚ),18,(-3,0,0,0,1,0,0)),((1/1:ℚ),18,(-3,0,1,0,1,0,0)),((1/1:ℚ),18,(-3,1,0,0,1,0,0)),((1/1:ℚ),18,(-3,2,0,0,1,0,0)),((-1/1:ℚ),18,(-2,-1,0,0,0,0,0)),((-2/1:ℚ),18,(-2,0,0,0,2,0,0)),((-1/1:ℚ),18,(-1,0,0,0,1,0,0)),((-1/1:ℚ),18,(0,-1,0,0,0,0,0)),((-1/1:ℚ),18,(0,0,0,0,2,0,0)),((-1/1:ℚ),18,(1,-1,0,0,1,0,0)),((-1/1:ℚ),18,(2,-1,0,0,0,0,0)),((-2/1:ℚ),42,(-4,-1,0,0,0,0,0)),((1/1:ℚ),42,(-4,-1,1,0,0,0,0)),((1/1:ℚ),42,(-4,0,0,0,0,0,0)),((1/1:ℚ),42,(-4,1,0,0,0,0,0)),((-2/1:ℚ),42,(-3,-1,0,0,1,0,0)),((-2/1:ℚ),42,(-2,-1,0,0,0,0,0)),((1/1:ℚ),42,(-2,0,0,0,0,0,0)),((-1/1:ℚ),42,(-2,0,1,0,0,0,0)),((-1/1:ℚ),42,(-2,1,0,0,0,0,0)),((-1/1:ℚ),42,(-2,2,0,0,0,0,0)),((-1/1:ℚ),42,(-1,-1,0,0,1,0,0)),((2/1:ℚ),42,(-1,0,0,0,1,0,0)),((-2/1:ℚ),42,(0,-1,0,0,0,0,0)),((1/1:ℚ),42,(0,0,0,0,0,0,0)),((1/1:ℚ),42,(1,0,0,0,1,0,0)),((1/1:ℚ),42,(2,-1,0,0,0,0,0))] := rfl

compact_certificate theorem minor25_identity (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0) :
    coefficientAt x y z a (allRow 4) 18*coefficientAt x y z a (allRow 15) 42-
      coefficientAt x y z a (allRow 4) 42*coefficientAt x y z a (allRow 15) 18=
      (-1/1:ℂ)*x^(-4:ℤ)*y^(-2:ℤ)*z^(0:ℤ)*
        eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor25 := by
  rw [row_left_minor25,row_right_minor25]
  norm_num [coefficientAt,eval,monomial,minor25]
  field_simp [hx,hy,hz]
  ring

compact_certificate theorem minor25_zero (x y z a : ℂ) (v : ℕ→ℂ)
    (hx : x≠0) (hy : y≠0) (hz : z≠0) (hn : v 18≠0 ∨ v 42≠0)
    (hrows : ∀ i : Fin 23,eval x y z 1 a 1 1 v (allRow i)=0) :
    eval (x^2) y z 1 (a*x) 1 1 (fun _ => 1) minor25=0 := by
  have hh := two_coordinate_minor_zero x y z a (allRow 4) (allRow 15) v 18 42
    (by decide) (allRow_support 4) (allRow_support 15) hn (hrows 4) (hrows 15)
  rw [minor25_identity x y z a hx hy hz] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (zpow_ne_zero _ hx)
      · exact zpow_ne_zero _ hy
    · exact zpow_ne_zero _ hz)

#print axioms minor25_zero
end QuantitativeArithmeticSmallLevelThirtyThreePlusElimination
end
