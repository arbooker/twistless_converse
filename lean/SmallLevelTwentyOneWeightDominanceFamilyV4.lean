module
public import SmallLevelExponentialDominanceV1
public import SmallLevelTwentyOneWeightCaseFamilyV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightDominance0
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOneWeightCase0

def bases : Fin 11 → ℝ := ![1,3,4,7,9,12,21,27,28,49,108]
def coefficients : Fin 11 → ℝ := ![7,-2,-4,5,-1,-3,-1,-1,-1,1,-1]

theorem polynomial_eval (m : ℕ) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)=
      (((252:ℝ)^m+∑ i, coefficients i*bases i^m : ℝ):ℂ) := by
  have h0 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(1:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 0 m using 1 <;> norm_num
  have h1 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(7:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 1 m using 1 <;> norm_num
  have h2 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2=(49:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 2 m using 1 <;> norm_num
  have h3 : ((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^0=(3:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 1 0 m using 1 <;> norm_num
  have h4 : ((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1=(21:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 1 1 m using 1 <;> norm_num
  have h5 : ((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0=(9:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 2 0 m using 1 <;> norm_num
  have h6 : ((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(27:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 3 0 m using 1 <;> norm_num
  have h7 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(4:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 0 m using 1 <;> norm_num
  have h8 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(28:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 1 m using 1 <;> norm_num
  have h9 : ((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0=(12:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 1 0 m using 1 <;> norm_num
  have h10 : ((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1=(252:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 2 1 m using 1 <;> norm_num
  have h11 : ((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(108:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 3 0 m using 1 <;> norm_num
  calc
    _ = (7:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(5:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2)+(-2:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0)+(-4:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(-3:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1)+(-1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0) := by unfold weightPolynomial; ring
    _ = _ := by
      rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
      simp only [bases,coefficients,Fin.sum_univ_succ,Complex.ofReal_add,
        Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_neg,
        Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
      norm_num
      <;> ring

theorem polynomial_ne_zero (m : ℕ) (hm : 2≤m) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)≠0 := by
  have hd := SmallLevelExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 252
    (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 2 m hm
    (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  intro h
  rw [polynomial_eval] at h
  exact hd (Complex.ofReal_eq_zero.mp h)

theorem weight_constraints (m : ℕ) (hm : 0<m) (a : ℂ) (w : Fin 42 → ℂ)
    (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (-1) (-1) (-1)
      ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m) a w r=0) :
    False := by
  obtain ⟨hL,hP⟩ := leading_constraints _ _ _ a (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) w h28 hker
  have hm1 : m=1 := by
    by_contra h
    exact polynomial_ne_zero m (by omega) hP
  subst m
  norm_num [weightPolynomial] at hP

#print axioms polynomial_ne_zero
#print axioms weight_constraints
end SmallLevelTwentyOneWeightDominance0
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightDominance1
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOneWeightCase1

def bases : Fin 11 → ℝ := ![1,4,7,9,12,21,27,28,36,49,108]
def coefficients : Fin 11 → ℝ := ![1,-2,1,-1,-3,-1,-1,-1,-2,1,-1]

theorem polynomial_eval (m : ℕ) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)=
      (((252:ℝ)^m+∑ i, coefficients i*bases i^m : ℝ):ℂ) := by
  have h0 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(1:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 0 m using 1 <;> norm_num
  have h1 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(7:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 1 m using 1 <;> norm_num
  have h2 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2=(49:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 2 m using 1 <;> norm_num
  have h3 : ((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1=(21:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 1 1 m using 1 <;> norm_num
  have h4 : ((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0=(9:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 2 0 m using 1 <;> norm_num
  have h5 : ((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(27:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 3 0 m using 1 <;> norm_num
  have h6 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(4:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 0 m using 1 <;> norm_num
  have h7 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(28:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 1 m using 1 <;> norm_num
  have h8 : ((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0=(12:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 1 0 m using 1 <;> norm_num
  have h9 : ((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^0=(36:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 2 0 m using 1 <;> norm_num
  have h10 : ((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1=(252:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 2 1 m using 1 <;> norm_num
  have h11 : ((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(108:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 3 0 m using 1 <;> norm_num
  calc
    _ = (1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0)+(-2:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(-3:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0)+(-2:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1)+(-1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0) := by unfold weightPolynomial; ring
    _ = _ := by
      rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
      simp only [bases,coefficients,Fin.sum_univ_succ,Complex.ofReal_add,
        Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_neg,
        Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
      norm_num
      <;> ring

theorem polynomial_ne_zero (m : ℕ) (hm : 2≤m) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)≠0 := by
  have hd := SmallLevelExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 252
    (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 2 m hm
    (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  intro h
  rw [polynomial_eval] at h
  exact hd (Complex.ofReal_eq_zero.mp h)

theorem weight_constraints (m : ℕ) (hm : 0<m) (a : ℂ) (w : Fin 42 → ℂ)
    (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (-1) (-1) (1)
      ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m) a w r=0) :
    m=1 ∧ a= -(3/2:ℂ) := by
  obtain ⟨hL,hP⟩ := leading_constraints _ _ _ a (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) w h28 hker
  have hm1 : m=1 := by
    by_contra h
    exact polynomial_ne_zero m (by omega) hP
  subst m
  refine ⟨rfl,?_⟩
  norm_num [residual403] at hL
  linear_combination (7/8:ℂ)*hL

#print axioms polynomial_ne_zero
#print axioms weight_constraints
end SmallLevelTwentyOneWeightDominance1
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightDominance2
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOneWeightCase2

def bases : Fin 11 → ℝ := ![1,4,7,9,12,21,27,28,36,49,108]
def coefficients : Fin 11 → ℝ := ![-1,2,1,1,-3,1,-1,-1,2,-1,-1]

theorem polynomial_eval (m : ℕ) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)=
      (((252:ℝ)^m+∑ i, coefficients i*bases i^m : ℝ):ℂ) := by
  have h0 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(1:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 0 m using 1 <;> norm_num
  have h1 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(7:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 1 m using 1 <;> norm_num
  have h2 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2=(49:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 2 m using 1 <;> norm_num
  have h3 : ((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1=(21:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 1 1 m using 1 <;> norm_num
  have h4 : ((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0=(9:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 2 0 m using 1 <;> norm_num
  have h5 : ((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(27:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 3 0 m using 1 <;> norm_num
  have h6 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(4:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 0 m using 1 <;> norm_num
  have h7 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(28:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 1 m using 1 <;> norm_num
  have h8 : ((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0=(12:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 1 0 m using 1 <;> norm_num
  have h9 : ((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^0=(36:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 2 0 m using 1 <;> norm_num
  have h10 : ((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1=(252:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 2 1 m using 1 <;> norm_num
  have h11 : ((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(108:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 3 0 m using 1 <;> norm_num
  calc
    _ = (-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0)+(2:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(-3:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0)+(2:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1)+(-1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0) := by unfold weightPolynomial; ring
    _ = _ := by
      rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
      simp only [bases,coefficients,Fin.sum_univ_succ,Complex.ofReal_add,
        Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_neg,
        Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
      norm_num
      <;> ring

theorem polynomial_ne_zero (m : ℕ) (hm : 2≤m) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)≠0 := by
  have hd := SmallLevelExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 252
    (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 2 m hm
    (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  intro h
  rw [polynomial_eval] at h
  exact hd (Complex.ofReal_eq_zero.mp h)

theorem weight_constraints (m : ℕ) (hm : 0<m) (a : ℂ) (w : Fin 42 → ℂ)
    (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (-1) (1) (-1)
      ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m) a w r=0) :
    False := by
  obtain ⟨hL,hP⟩ := leading_constraints _ _ _ a (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) w h28 hker
  have hm1 : m=1 := by
    by_contra h
    exact polynomial_ne_zero m (by omega) hP
  subst m
  norm_num [weightPolynomial] at hP

#print axioms polynomial_ne_zero
#print axioms weight_constraints
end SmallLevelTwentyOneWeightDominance2
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightDominance3
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOneWeightCase3

def bases : Fin 11 → ℝ := ![1,3,4,7,9,12,21,27,28,49,108]
def coefficients : Fin 11 → ℝ := ![-7,-2,4,5,1,-3,1,-1,-1,-1,-1]

theorem polynomial_eval (m : ℕ) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)=
      (((252:ℝ)^m+∑ i, coefficients i*bases i^m : ℝ):ℂ) := by
  have h0 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(1:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 0 m using 1 <;> norm_num
  have h1 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(7:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 1 m using 1 <;> norm_num
  have h2 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2=(49:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 2 m using 1 <;> norm_num
  have h3 : ((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^0=(3:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 1 0 m using 1 <;> norm_num
  have h4 : ((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1=(21:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 1 1 m using 1 <;> norm_num
  have h5 : ((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0=(9:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 2 0 m using 1 <;> norm_num
  have h6 : ((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(27:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 3 0 m using 1 <;> norm_num
  have h7 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(4:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 0 m using 1 <;> norm_num
  have h8 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(28:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 1 m using 1 <;> norm_num
  have h9 : ((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0=(12:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 1 0 m using 1 <;> norm_num
  have h10 : ((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1=(252:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 2 1 m using 1 <;> norm_num
  have h11 : ((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(108:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 3 0 m using 1 <;> norm_num
  calc
    _ = (-7:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(5:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2)+(-2:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0)+(4:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(-3:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1)+(-1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0) := by unfold weightPolynomial; ring
    _ = _ := by
      rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
      simp only [bases,coefficients,Fin.sum_univ_succ,Complex.ofReal_add,
        Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_neg,
        Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
      norm_num
      <;> ring

theorem polynomial_ne_zero (m : ℕ) (hm : 2≤m) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)≠0 := by
  have hd := SmallLevelExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 252
    (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 2 m hm
    (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  intro h
  rw [polynomial_eval] at h
  exact hd (Complex.ofReal_eq_zero.mp h)

theorem weight_constraints (m : ℕ) (hm : 0<m) (a : ℂ) (w : Fin 42 → ℂ)
    (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (-1) (1) (1)
      ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m) a w r=0) :
    False := by
  obtain ⟨hL,hP⟩ := leading_constraints _ _ _ a (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) w h28 hker
  have hm1 : m=1 := by
    by_contra h
    exact polynomial_ne_zero m (by omega) hP
  subst m
  norm_num [weightPolynomial] at hP

#print axioms polynomial_ne_zero
#print axioms weight_constraints
end SmallLevelTwentyOneWeightDominance3
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightDominance4
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOneWeightCase4

def bases : Fin 11 → ℝ := ![1,4,7,9,12,21,27,28,36,49,108]
def coefficients : Fin 11 → ℝ := ![-1,2,1,1,3,-1,1,-1,2,-1,1]

theorem polynomial_eval (m : ℕ) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)=
      (((252:ℝ)^m+∑ i, coefficients i*bases i^m : ℝ):ℂ) := by
  have h0 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(1:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 0 m using 1 <;> norm_num
  have h1 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(7:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 1 m using 1 <;> norm_num
  have h2 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2=(49:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 2 m using 1 <;> norm_num
  have h3 : ((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1=(21:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 1 1 m using 1 <;> norm_num
  have h4 : ((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0=(9:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 2 0 m using 1 <;> norm_num
  have h5 : ((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(27:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 3 0 m using 1 <;> norm_num
  have h6 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(4:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 0 m using 1 <;> norm_num
  have h7 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(28:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 1 m using 1 <;> norm_num
  have h8 : ((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0=(12:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 1 0 m using 1 <;> norm_num
  have h9 : ((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^0=(36:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 2 0 m using 1 <;> norm_num
  have h10 : ((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1=(252:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 2 1 m using 1 <;> norm_num
  have h11 : ((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(108:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 3 0 m using 1 <;> norm_num
  calc
    _ = (-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0)+(2:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(3:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0)+(2:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1)+(1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0) := by unfold weightPolynomial; ring
    _ = _ := by
      rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
      simp only [bases,coefficients,Fin.sum_univ_succ,Complex.ofReal_add,
        Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_neg,
        Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
      norm_num
      <;> ring

theorem polynomial_ne_zero (m : ℕ) (hm : 2≤m) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)≠0 := by
  have hd := SmallLevelExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 252
    (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 2 m hm
    (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  intro h
  rw [polynomial_eval] at h
  exact hd (Complex.ofReal_eq_zero.mp h)

theorem weight_constraints (m : ℕ) (hm : 0<m) (a : ℂ) (w : Fin 42 → ℂ)
    (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (1) (-1) (-1)
      ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m) a w r=0) :
    False := by
  obtain ⟨hL,hP⟩ := leading_constraints _ _ _ a (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) w h28 hker
  have hm1 : m=1 := by
    by_contra h
    exact polynomial_ne_zero m (by omega) hP
  subst m
  norm_num [weightPolynomial] at hP

#print axioms polynomial_ne_zero
#print axioms weight_constraints
end SmallLevelTwentyOneWeightDominance4
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightDominance5
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOneWeightCase5

def bases : Fin 11 → ℝ := ![1,3,4,7,9,12,21,27,28,49,108]
def coefficients : Fin 11 → ℝ := ![-7,2,4,5,1,3,-1,1,-1,-1,1]

theorem polynomial_eval (m : ℕ) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)=
      (((252:ℝ)^m+∑ i, coefficients i*bases i^m : ℝ):ℂ) := by
  have h0 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(1:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 0 m using 1 <;> norm_num
  have h1 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(7:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 1 m using 1 <;> norm_num
  have h2 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2=(49:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 2 m using 1 <;> norm_num
  have h3 : ((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^0=(3:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 1 0 m using 1 <;> norm_num
  have h4 : ((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1=(21:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 1 1 m using 1 <;> norm_num
  have h5 : ((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0=(9:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 2 0 m using 1 <;> norm_num
  have h6 : ((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(27:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 3 0 m using 1 <;> norm_num
  have h7 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(4:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 0 m using 1 <;> norm_num
  have h8 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(28:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 1 m using 1 <;> norm_num
  have h9 : ((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0=(12:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 1 0 m using 1 <;> norm_num
  have h10 : ((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1=(252:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 2 1 m using 1 <;> norm_num
  have h11 : ((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(108:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 3 0 m using 1 <;> norm_num
  calc
    _ = (-7:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(5:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2)+(2:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0)+(4:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(3:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1)+(1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0) := by unfold weightPolynomial; ring
    _ = _ := by
      rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
      simp only [bases,coefficients,Fin.sum_univ_succ,Complex.ofReal_add,
        Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_neg,
        Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
      norm_num
      <;> ring

theorem polynomial_ne_zero (m : ℕ) (hm : 2≤m) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)≠0 := by
  have hd := SmallLevelExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 252
    (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 2 m hm
    (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  intro h
  rw [polynomial_eval] at h
  exact hd (Complex.ofReal_eq_zero.mp h)

theorem weight_constraints (m : ℕ) (hm : 0<m) (a : ℂ) (w : Fin 42 → ℂ)
    (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (1) (-1) (1)
      ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m) a w r=0) :
    False := by
  obtain ⟨hL,hP⟩ := leading_constraints _ _ _ a (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) w h28 hker
  have hm1 : m=1 := by
    by_contra h
    exact polynomial_ne_zero m (by omega) hP
  subst m
  norm_num [weightPolynomial] at hP

#print axioms polynomial_ne_zero
#print axioms weight_constraints
end SmallLevelTwentyOneWeightDominance5
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightDominance6
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOneWeightCase6

def bases : Fin 11 → ℝ := ![1,3,4,7,9,12,21,27,28,49,108]
def coefficients : Fin 11 → ℝ := ![7,2,-4,5,-1,3,1,1,-1,1,1]

theorem polynomial_eval (m : ℕ) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)=
      (((252:ℝ)^m+∑ i, coefficients i*bases i^m : ℝ):ℂ) := by
  have h0 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(1:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 0 m using 1 <;> norm_num
  have h1 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(7:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 1 m using 1 <;> norm_num
  have h2 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2=(49:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 2 m using 1 <;> norm_num
  have h3 : ((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^0=(3:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 1 0 m using 1 <;> norm_num
  have h4 : ((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1=(21:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 1 1 m using 1 <;> norm_num
  have h5 : ((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0=(9:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 2 0 m using 1 <;> norm_num
  have h6 : ((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(27:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 3 0 m using 1 <;> norm_num
  have h7 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(4:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 0 m using 1 <;> norm_num
  have h8 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(28:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 1 m using 1 <;> norm_num
  have h9 : ((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0=(12:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 1 0 m using 1 <;> norm_num
  have h10 : ((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1=(252:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 2 1 m using 1 <;> norm_num
  have h11 : ((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(108:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 3 0 m using 1 <;> norm_num
  calc
    _ = (7:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(5:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2)+(2:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0)+(-4:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(3:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1)+(1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0) := by unfold weightPolynomial; ring
    _ = _ := by
      rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
      simp only [bases,coefficients,Fin.sum_univ_succ,Complex.ofReal_add,
        Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_neg,
        Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
      norm_num
      <;> ring

theorem polynomial_ne_zero (m : ℕ) (hm : 2≤m) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)≠0 := by
  have hd := SmallLevelExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 252
    (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 2 m hm
    (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  intro h
  rw [polynomial_eval] at h
  exact hd (Complex.ofReal_eq_zero.mp h)

theorem weight_constraints (m : ℕ) (hm : 0<m) (a : ℂ) (w : Fin 42 → ℂ)
    (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (1) (1) (-1)
      ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m) a w r=0) :
    False := by
  obtain ⟨hL,hP⟩ := leading_constraints _ _ _ a (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) w h28 hker
  have hm1 : m=1 := by
    by_contra h
    exact polynomial_ne_zero m (by omega) hP
  subst m
  norm_num [weightPolynomial] at hP

#print axioms polynomial_ne_zero
#print axioms weight_constraints
end SmallLevelTwentyOneWeightDominance6
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SmallLevelTwentyOneWeightDominance7
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOneWeightCase7

def bases : Fin 11 → ℝ := ![1,4,7,9,12,21,27,28,36,49,108]
def coefficients : Fin 11 → ℝ := ![1,-2,1,-1,3,1,1,-1,-2,1,1]

theorem polynomial_eval (m : ℕ) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)=
      (((252:ℝ)^m+∑ i, coefficients i*bases i^m : ℝ):ℂ) := by
  have h0 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(1:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 0 m using 1 <;> norm_num
  have h1 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(7:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 1 m using 1 <;> norm_num
  have h2 : ((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2=(49:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 0 2 m using 1 <;> norm_num
  have h3 : ((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1=(21:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 1 1 m using 1 <;> norm_num
  have h4 : ((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0=(9:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 2 0 m using 1 <;> norm_num
  have h5 : ((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(27:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 0 3 0 m using 1 <;> norm_num
  have h6 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0=(4:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 0 m using 1 <;> norm_num
  have h7 : ((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1=(28:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 0 1 m using 1 <;> norm_num
  have h8 : ((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0=(12:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 1 0 m using 1 <;> norm_num
  have h9 : ((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^0=(36:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 2 0 m using 1 <;> norm_num
  have h10 : ((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1=(252:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 2 1 m using 1 <;> norm_num
  have h11 : ((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0=(108:ℂ)^m := by
    convert SmallLevelExponentialDominance.three_powers (2:ℂ) 3 7 2 3 0 m using 1 <;> norm_num
  calc
    _ = (1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^0*((7:ℂ)^m)^2)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^1*((7:ℂ)^m)^1)+(-1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^2*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^0*((3:ℂ)^m)^3*((7:ℂ)^m)^0)+(-2:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^0)+(-1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^0*((7:ℂ)^m)^1)+(3:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^1*((7:ℂ)^m)^0)+(-2:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^0)+(1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^2*((7:ℂ)^m)^1)+(1:ℂ)*(((2:ℂ)^m)^2*((3:ℂ)^m)^3*((7:ℂ)^m)^0) := by unfold weightPolynomial; ring
    _ = _ := by
      rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
      simp only [bases,coefficients,Fin.sum_univ_succ,Complex.ofReal_add,
        Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_neg,
        Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
      norm_num
      <;> ring

theorem polynomial_ne_zero (m : ℕ) (hm : 2≤m) :
    weightPolynomial ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m)≠0 := by
  have hd := SmallLevelExponentialDominance.signed_sum_nonzero Finset.univ coefficients bases 252
    (by norm_num) (by intro i _; fin_cases i <;> norm_num [bases]) 2 m hm
    (by norm_num [coefficients,bases,Fin.sum_univ_succ])
  intro h
  rw [polynomial_eval] at h
  exact hd (Complex.ofReal_eq_zero.mp h)

theorem weight_constraints (m : ℕ) (hm : 0<m) (a : ℂ) (w : Fin 42 → ℂ)
    (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (1) (1) (1)
      ((2:ℂ)^m) ((3:ℂ)^m) ((7:ℂ)^m) a w r=0) :
    False := by
  obtain ⟨hL,hP⟩ := leading_constraints _ _ _ a (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) (pow_ne_zero m (by norm_num)) w h28 hker
  have hm1 : m=1 := by
    by_contra h
    exact polynomial_ne_zero m (by omega) hP
  subst m
  norm_num [weightPolynomial] at hP

#print axioms polynomial_ne_zero
#print axioms weight_constraints
end SmallLevelTwentyOneWeightDominance7
end
