module
public import SmallLevelTwentyOneFirstJetConditionsV1
public import SmallLevelTwentyOneFirstJetLinkFamilyV4
@[expose] public noncomputable section
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The common generated tactic sequences close at different stages for different rows.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace SmallLevelTwentyOneFirstJetBundle0
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne
open SmallLevelTwentyOneFirstJetCase0 SmallLevelTwentyOneFirstJetLink0

def rows429 : Fin 10 → AugmentedRow := ![augmentedIndex 6,augmentedIndex 7,augmentedIndex 8,augmentedIndex 9,augmentedIndex 11,augmentedIndex 43,augmentedIndex 47,augmentedIndex 427,augmentedIndex 428,augmentedIndex 429]
def coeff429 (x y z a : ℂ) : Fin 10 → ℂ := ![((-1)),(((-1*x^2*y)/(z))),((-1)),(((-2*y)/(z))),(((-1*y)/(z))),((-1)),((-1)),(((2*y)/(z))),(((1*x^2*y)/(z))),((1))]

theorem syzygy429_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff429 x y z a i*augmentedLaurentRow (-1) (-1) (-1) x y z a w (rows429 i))=0 := by
  simpa [coeff429,rows429,Fin.sum_univ_succ,row006_link,row007_link,row008_link,row009_link,row011_link,row043_link,row047_link,row427_link,row428_link,row429_link,add_assoc] using
    syzygy429 x y z a hx hy hz w

#print axioms syzygy429_model

def rows435 : Fin 11 → AugmentedRow := ![augmentedIndex 3,augmentedIndex 5,augmentedIndex 6,augmentedIndex 9,augmentedIndex 38,augmentedIndex 46,augmentedIndex 319,augmentedIndex 397,augmentedIndex 398,augmentedIndex 427,augmentedIndex 435]
def coeff435 (x y z a : ℂ) : Fin 11 → ℂ := ![((-1)),(((1*a)/(x))),(((1)/(x^2))),(((1*y)/(x^2*z))),(((-1*x*a)/(y*z))),((-1)),(((2)/(x^2*z))+((-1*a)/(x*y*z))+((1)/(y*z))),(((-1)/(x^2))),(((-1)/(x^2))),(((1)/(x^2*z))+((-1*y)/(x^2*z))),((1))]

theorem syzygy435_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff435 x y z a i*augmentedLaurentRow (-1) (-1) (-1) x y z a w (rows435 i))=0 := by
  simpa [coeff435,rows435,Fin.sum_univ_succ,row003_link,row005_link,row006_link,row009_link,row038_link,row046_link,row319_link,row397_link,row398_link,row427_link,row435_link,add_assoc] using
    syzygy435 x y z a hx hy hz w

#print axioms syzygy435_model

theorem conditions (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (-1) (-1) (-1) x y z a w r=0)
    (h429 : ∑ i, coeff429 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (-1) (-1) (-1) x y z w (rows429 i)=0)
    (h435 : ∑ i, coeff435 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (-1) (-1) (-1) x y z w (rows435 i)=0) :
    a*x+x^2-1=0 ∧ y+3*(-1)=0 ∧ z=6*(-1)*(-1)+(-1) := by
  have hrw000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hrw003 : row003 x y z a w=0 := by
    rw [← row003_link]; exact hker (augmentedIndex 3)
  have hrw004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hrw005 : row005 x y z a w=0 := by
    rw [← row005_link]; exact hker (augmentedIndex 5)
  have hrw006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hrw007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hrw008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hrw009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hrw010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hrw011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hrw038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hrw040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hrw043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hrw046 : row046 x y z a w=0 := by
    rw [← row046_link]; exact hker (augmentedIndex 46)
  have hrw047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hrw319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hrw387 : row387 x y z a w=0 := by
    rw [← row387_link]; exact hker (augmentedIndex 387)
  have hrw389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hrw397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hrw398 : row398 x y z a w=0 := by
    rw [← row398_link]; exact hker (augmentedIndex 398)
  have hrw403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hrw419 : row419 x y z a w=0 := by
    rw [← row419_link]; exact hker (augmentedIndex 419)
  have hrw423 : row423 x y z a w=0 := by
    rw [← row423_link]; exact hker (augmentedIndex 423)
  have hrw427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hrw428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hrw429 : row429 x y z a w=0 := by
    rw [← row429_link]; exact hker (augmentedIndex 429)
  have hrw435 : row435 x y z a w=0 := by
    rw [← row435_link]; exact hker (augmentedIndex 435)
  have hrw436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hz429_427 : augmentedLaurentShiftRow (-1) (-1) (-1) x y z w (augmentedIndex 427)=0 := rfl
  have hz429_428 : augmentedLaurentShiftRow (-1) (-1) (-1) x y z w (augmentedIndex 428)=0 := rfl
  have hz429_429 : augmentedLaurentShiftRow (-1) (-1) (-1) x y z w (augmentedIndex 429)=0 := rfl
  have hs429 : (((-1))*shift006 x y z a w+(((-7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((-14*y)/(3*z)))*shift009 x y z a w+(((-7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)=0 := by
    convert h429 using 1
    simp [coeff429,rows429,Fin.sum_univ_succ,(shift006_link x y z a w),(shift007_link x y z a w),(shift008_link x y z a w),(shift009_link x y z a w),(shift011_link x y z a w),(shift043_link x y z a w),(shift047_link x y z a w),hz429_427,hz429_428,hz429_429]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp429 := projection429 x y z a hx hy hz w
  simp only [hs429,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw387,hrw389,hrw397,hrw398,hrw403,hrw419,hrw423,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp429
  have hz435_319 : augmentedLaurentShiftRow (-1) (-1) (-1) x y z w (augmentedIndex 319)=0 := rfl
  have hz435_427 : augmentedLaurentShiftRow (-1) (-1) (-1) x y z w (augmentedIndex 427)=0 := rfl
  have hz435_435 : augmentedLaurentShiftRow (-1) (-1) (-1) x y z w (augmentedIndex 435)=0 := rfl
  have hs435 : (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((28*y)/(3*x^2*z)))*shift009 x y z a w+(((-21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)=0 := by
    convert h435 using 1
    simp [coeff435,rows435,Fin.sum_univ_succ,(shift003_link x y z a w),(shift005_link x y z a w),(shift006_link x y z a w),(shift009_link x y z a w),(shift038_link x y z a w),(shift046_link x y z a w),(shift397_link x y z a w),(shift398_link x y z a w),hz435_319,hz435_427,hz435_435]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp435 := projection435 x y z a hx hy hz w
  simp only [hs435,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw387,hrw389,hrw397,hrw398,hrw403,hrw419,hrw423,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp435
  have hr := residual403 x y z a hx hy hz w
  simp only [hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw387,hrw389,hrw397,hrw398,hrw403,hrw419,hrw423,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add] at hr
  apply SmallLevelTwentyOneFirstJet.conditions_of_three_residuals (-1) (-1) (-1) x y z a
    (by norm_num) hx hy hz
  · linear_combination -hp429
  · linear_combination -hp435
  · linear_combination (norm := ring_nf) -hr
    simp [hz]

#print axioms conditions
end SmallLevelTwentyOneFirstJetBundle0
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The common generated tactic sequences close at different stages for different rows.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace SmallLevelTwentyOneFirstJetBundle1
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne
open SmallLevelTwentyOneFirstJetCase1 SmallLevelTwentyOneFirstJetLink1

def rows429 : Fin 10 → AugmentedRow := ![augmentedIndex 6,augmentedIndex 7,augmentedIndex 8,augmentedIndex 9,augmentedIndex 11,augmentedIndex 43,augmentedIndex 47,augmentedIndex 427,augmentedIndex 428,augmentedIndex 429]
def coeff429 (x y z a : ℂ) : Fin 10 → ℂ := ![((-1)),(((-1*x^2*y)/(z))),((-1)),(((-2*y)/(z))),(((-1*y)/(z))),((-1)),((-1)),(((2*y)/(z))),(((1*x^2*y)/(z))),((1))]

theorem syzygy429_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff429 x y z a i*augmentedLaurentRow (-1) (-1) (1) x y z a w (rows429 i))=0 := by
  simpa [coeff429,rows429,Fin.sum_univ_succ,row006_link,row007_link,row008_link,row009_link,row011_link,row043_link,row047_link,row427_link,row428_link,row429_link,add_assoc] using
    syzygy429 x y z a hx hy hz w

#print axioms syzygy429_model

def rows435 : Fin 11 → AugmentedRow := ![augmentedIndex 3,augmentedIndex 5,augmentedIndex 6,augmentedIndex 9,augmentedIndex 38,augmentedIndex 46,augmentedIndex 319,augmentedIndex 397,augmentedIndex 398,augmentedIndex 427,augmentedIndex 435]
def coeff435 (x y z a : ℂ) : Fin 11 → ℂ := ![((-1)),(((1*a)/(x))),(((1)/(x^2))),(((1*y)/(x^2*z))),(((-1*x*a)/(y*z))),((-1)),(((2)/(x^2*z))+((-1*a)/(x*y*z))+((1)/(y*z))),(((-1)/(x^2))),(((-1)/(x^2))),(((1)/(x^2*z))+((-1*y)/(x^2*z))),((1))]

theorem syzygy435_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff435 x y z a i*augmentedLaurentRow (-1) (-1) (1) x y z a w (rows435 i))=0 := by
  simpa [coeff435,rows435,Fin.sum_univ_succ,row003_link,row005_link,row006_link,row009_link,row038_link,row046_link,row319_link,row397_link,row398_link,row427_link,row435_link,add_assoc] using
    syzygy435 x y z a hx hy hz w

#print axioms syzygy435_model

theorem conditions (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (-1) (-1) (1) x y z a w r=0)
    (h429 : ∑ i, coeff429 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (-1) (-1) (1) x y z w (rows429 i)=0)
    (h435 : ∑ i, coeff435 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (-1) (-1) (1) x y z w (rows435 i)=0) :
    a*x+x^2-1=0 ∧ y+3*(-1)=0 ∧ z=6*(-1)*(-1)+(1) := by
  have hrw000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hrw003 : row003 x y z a w=0 := by
    rw [← row003_link]; exact hker (augmentedIndex 3)
  have hrw004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hrw005 : row005 x y z a w=0 := by
    rw [← row005_link]; exact hker (augmentedIndex 5)
  have hrw006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hrw007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hrw008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hrw009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hrw010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hrw011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hrw038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hrw040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hrw043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hrw046 : row046 x y z a w=0 := by
    rw [← row046_link]; exact hker (augmentedIndex 46)
  have hrw047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hrw319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hrw388 : row388 x y z a w=0 := by
    rw [← row388_link]; exact hker (augmentedIndex 388)
  have hrw389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hrw397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hrw398 : row398 x y z a w=0 := by
    rw [← row398_link]; exact hker (augmentedIndex 398)
  have hrw403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hrw427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hrw428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hrw429 : row429 x y z a w=0 := by
    rw [← row429_link]; exact hker (augmentedIndex 429)
  have hrw435 : row435 x y z a w=0 := by
    rw [← row435_link]; exact hker (augmentedIndex 435)
  have hrw436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hz429_427 : augmentedLaurentShiftRow (-1) (-1) (1) x y z w (augmentedIndex 427)=0 := rfl
  have hz429_428 : augmentedLaurentShiftRow (-1) (-1) (1) x y z w (augmentedIndex 428)=0 := rfl
  have hz429_429 : augmentedLaurentShiftRow (-1) (-1) (1) x y z w (augmentedIndex 429)=0 := rfl
  have hs429 : (((-1))*shift006 x y z a w+(((-7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((-14*y)/(3*z)))*shift009 x y z a w+(((-7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)=0 := by
    convert h429 using 1
    simp [coeff429,rows429,Fin.sum_univ_succ,(shift006_link x y z a w),(shift007_link x y z a w),(shift008_link x y z a w),(shift009_link x y z a w),(shift011_link x y z a w),(shift043_link x y z a w),(shift047_link x y z a w),hz429_427,hz429_428,hz429_429]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp429 := projection429 x y z a hx hy hz w
  simp only [hs429,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw388,hrw389,hrw397,hrw398,hrw403,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp429
  have hz435_319 : augmentedLaurentShiftRow (-1) (-1) (1) x y z w (augmentedIndex 319)=0 := rfl
  have hz435_427 : augmentedLaurentShiftRow (-1) (-1) (1) x y z w (augmentedIndex 427)=0 := rfl
  have hz435_435 : augmentedLaurentShiftRow (-1) (-1) (1) x y z w (augmentedIndex 435)=0 := rfl
  have hs435 : (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((28*y)/(3*x^2*z)))*shift009 x y z a w+(((-21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)=0 := by
    convert h435 using 1
    simp [coeff435,rows435,Fin.sum_univ_succ,(shift003_link x y z a w),(shift005_link x y z a w),(shift006_link x y z a w),(shift009_link x y z a w),(shift038_link x y z a w),(shift046_link x y z a w),(shift397_link x y z a w),(shift398_link x y z a w),hz435_319,hz435_427,hz435_435]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp435 := projection435 x y z a hx hy hz w
  simp only [hs435,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw388,hrw389,hrw397,hrw398,hrw403,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp435
  have hr := residual403 x y z a hx hy hz w
  simp only [hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw388,hrw389,hrw397,hrw398,hrw403,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add] at hr
  apply SmallLevelTwentyOneFirstJet.conditions_of_three_residuals (-1) (-1) (1) x y z a
    (by norm_num) hx hy hz
  · linear_combination -hp429
  · linear_combination -hp435
  · linear_combination (norm := ring_nf) -hr
    simp [hz]

#print axioms conditions
end SmallLevelTwentyOneFirstJetBundle1
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The common generated tactic sequences close at different stages for different rows.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace SmallLevelTwentyOneFirstJetBundle2
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne
open SmallLevelTwentyOneFirstJetCase2 SmallLevelTwentyOneFirstJetLink2

def rows429 : Fin 10 → AugmentedRow := ![augmentedIndex 6,augmentedIndex 7,augmentedIndex 8,augmentedIndex 9,augmentedIndex 11,augmentedIndex 43,augmentedIndex 47,augmentedIndex 427,augmentedIndex 428,augmentedIndex 429]
def coeff429 (x y z a : ℂ) : Fin 10 → ℂ := ![((-1)),(((-1*x^2*y)/(z))),((-1)),(((-2*y)/(z))),(((-1*y)/(z))),((-1)),((-1)),(((2*y)/(z))),(((1*x^2*y)/(z))),((1))]

theorem syzygy429_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff429 x y z a i*augmentedLaurentRow (-1) (1) (-1) x y z a w (rows429 i))=0 := by
  simpa [coeff429,rows429,Fin.sum_univ_succ,row006_link,row007_link,row008_link,row009_link,row011_link,row043_link,row047_link,row427_link,row428_link,row429_link,add_assoc] using
    syzygy429 x y z a hx hy hz w

#print axioms syzygy429_model

def rows435 : Fin 11 → AugmentedRow := ![augmentedIndex 3,augmentedIndex 5,augmentedIndex 6,augmentedIndex 9,augmentedIndex 38,augmentedIndex 46,augmentedIndex 319,augmentedIndex 397,augmentedIndex 398,augmentedIndex 427,augmentedIndex 435]
def coeff435 (x y z a : ℂ) : Fin 11 → ℂ := ![((-1)),(((1*a)/(x))),(((1)/(x^2))),(((1*y)/(x^2*z))),(((-1*x*a)/(y*z))),((-1)),(((-2)/(x^2*z))+((-1*a)/(x*y*z))+((1)/(y*z))),(((-1)/(x^2))),(((-1)/(x^2))),(((-1)/(x^2*z))+((-1*y)/(x^2*z))),((1))]

theorem syzygy435_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff435 x y z a i*augmentedLaurentRow (-1) (1) (-1) x y z a w (rows435 i))=0 := by
  simpa [coeff435,rows435,Fin.sum_univ_succ,row003_link,row005_link,row006_link,row009_link,row038_link,row046_link,row319_link,row397_link,row398_link,row427_link,row435_link,add_assoc] using
    syzygy435 x y z a hx hy hz w

#print axioms syzygy435_model

theorem conditions (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (-1) (1) (-1) x y z a w r=0)
    (h429 : ∑ i, coeff429 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (-1) (1) (-1) x y z w (rows429 i)=0)
    (h435 : ∑ i, coeff435 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (-1) (1) (-1) x y z w (rows435 i)=0) :
    a*x+x^2-1=0 ∧ y+3*(1)=0 ∧ z=6*(-1)*(1)+(-1) := by
  have hrw000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hrw003 : row003 x y z a w=0 := by
    rw [← row003_link]; exact hker (augmentedIndex 3)
  have hrw004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hrw005 : row005 x y z a w=0 := by
    rw [← row005_link]; exact hker (augmentedIndex 5)
  have hrw006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hrw007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hrw008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hrw009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hrw010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hrw011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hrw038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hrw040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hrw043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hrw046 : row046 x y z a w=0 := by
    rw [← row046_link]; exact hker (augmentedIndex 46)
  have hrw047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hrw319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hrw388 : row388 x y z a w=0 := by
    rw [← row388_link]; exact hker (augmentedIndex 388)
  have hrw389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hrw397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hrw398 : row398 x y z a w=0 := by
    rw [← row398_link]; exact hker (augmentedIndex 398)
  have hrw403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hrw427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hrw428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hrw429 : row429 x y z a w=0 := by
    rw [← row429_link]; exact hker (augmentedIndex 429)
  have hrw435 : row435 x y z a w=0 := by
    rw [← row435_link]; exact hker (augmentedIndex 435)
  have hrw436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hz429_427 : augmentedLaurentShiftRow (-1) (1) (-1) x y z w (augmentedIndex 427)=0 := rfl
  have hz429_428 : augmentedLaurentShiftRow (-1) (1) (-1) x y z w (augmentedIndex 428)=0 := rfl
  have hz429_429 : augmentedLaurentShiftRow (-1) (1) (-1) x y z w (augmentedIndex 429)=0 := rfl
  have hs429 : (((-1))*shift006 x y z a w+(((-7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((-14*y)/(3*z)))*shift009 x y z a w+(((-7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)=0 := by
    convert h429 using 1
    simp [coeff429,rows429,Fin.sum_univ_succ,(shift006_link x y z a w),(shift007_link x y z a w),(shift008_link x y z a w),(shift009_link x y z a w),(shift011_link x y z a w),(shift043_link x y z a w),(shift047_link x y z a w),hz429_427,hz429_428,hz429_429]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp429 := projection429 x y z a hx hy hz w
  simp only [hs429,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw388,hrw389,hrw397,hrw398,hrw403,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp429
  have hz435_319 : augmentedLaurentShiftRow (-1) (1) (-1) x y z w (augmentedIndex 319)=0 := rfl
  have hz435_427 : augmentedLaurentShiftRow (-1) (1) (-1) x y z w (augmentedIndex 427)=0 := rfl
  have hz435_435 : augmentedLaurentShiftRow (-1) (1) (-1) x y z w (augmentedIndex 435)=0 := rfl
  have hs435 : (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((28*y)/(3*x^2*z)))*shift009 x y z a w+(((-21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)=0 := by
    convert h435 using 1
    simp [coeff435,rows435,Fin.sum_univ_succ,(shift003_link x y z a w),(shift005_link x y z a w),(shift006_link x y z a w),(shift009_link x y z a w),(shift038_link x y z a w),(shift046_link x y z a w),(shift397_link x y z a w),(shift398_link x y z a w),hz435_319,hz435_427,hz435_435]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp435 := projection435 x y z a hx hy hz w
  simp only [hs435,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw388,hrw389,hrw397,hrw398,hrw403,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp435
  have hr := residual403 x y z a hx hy hz w
  simp only [hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw388,hrw389,hrw397,hrw398,hrw403,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add] at hr
  apply SmallLevelTwentyOneFirstJet.conditions_of_three_residuals (-1) (1) (-1) x y z a
    (by norm_num) hx hy hz
  · linear_combination -hp429
  · linear_combination -hp435
  · linear_combination (norm := ring_nf) -hr
    simp [hz]

#print axioms conditions
end SmallLevelTwentyOneFirstJetBundle2
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The common generated tactic sequences close at different stages for different rows.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace SmallLevelTwentyOneFirstJetBundle3
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne
open SmallLevelTwentyOneFirstJetCase3 SmallLevelTwentyOneFirstJetLink3

def rows429 : Fin 10 → AugmentedRow := ![augmentedIndex 6,augmentedIndex 7,augmentedIndex 8,augmentedIndex 9,augmentedIndex 11,augmentedIndex 43,augmentedIndex 47,augmentedIndex 427,augmentedIndex 428,augmentedIndex 429]
def coeff429 (x y z a : ℂ) : Fin 10 → ℂ := ![((-1)),(((-1*x^2*y)/(z))),((-1)),(((-2*y)/(z))),(((-1*y)/(z))),((-1)),((-1)),(((2*y)/(z))),(((1*x^2*y)/(z))),((1))]

theorem syzygy429_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff429 x y z a i*augmentedLaurentRow (-1) (1) (1) x y z a w (rows429 i))=0 := by
  simpa [coeff429,rows429,Fin.sum_univ_succ,row006_link,row007_link,row008_link,row009_link,row011_link,row043_link,row047_link,row427_link,row428_link,row429_link,add_assoc] using
    syzygy429 x y z a hx hy hz w

#print axioms syzygy429_model

def rows435 : Fin 11 → AugmentedRow := ![augmentedIndex 3,augmentedIndex 5,augmentedIndex 6,augmentedIndex 9,augmentedIndex 38,augmentedIndex 46,augmentedIndex 319,augmentedIndex 397,augmentedIndex 398,augmentedIndex 427,augmentedIndex 435]
def coeff435 (x y z a : ℂ) : Fin 11 → ℂ := ![((-1)),(((1*a)/(x))),(((1)/(x^2))),(((1*y)/(x^2*z))),(((-1*x*a)/(y*z))),((-1)),(((-2)/(x^2*z))+((-1*a)/(x*y*z))+((1)/(y*z))),(((-1)/(x^2))),(((-1)/(x^2))),(((-1)/(x^2*z))+((-1*y)/(x^2*z))),((1))]

theorem syzygy435_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff435 x y z a i*augmentedLaurentRow (-1) (1) (1) x y z a w (rows435 i))=0 := by
  simpa [coeff435,rows435,Fin.sum_univ_succ,row003_link,row005_link,row006_link,row009_link,row038_link,row046_link,row319_link,row397_link,row398_link,row427_link,row435_link,add_assoc] using
    syzygy435 x y z a hx hy hz w

#print axioms syzygy435_model

theorem conditions (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (-1) (1) (1) x y z a w r=0)
    (h429 : ∑ i, coeff429 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (-1) (1) (1) x y z w (rows429 i)=0)
    (h435 : ∑ i, coeff435 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (-1) (1) (1) x y z w (rows435 i)=0) :
    a*x+x^2-1=0 ∧ y+3*(1)=0 ∧ z=6*(-1)*(1)+(1) := by
  have hrw000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hrw003 : row003 x y z a w=0 := by
    rw [← row003_link]; exact hker (augmentedIndex 3)
  have hrw004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hrw005 : row005 x y z a w=0 := by
    rw [← row005_link]; exact hker (augmentedIndex 5)
  have hrw006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hrw007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hrw008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hrw009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hrw010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hrw011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hrw038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hrw040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hrw043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hrw046 : row046 x y z a w=0 := by
    rw [← row046_link]; exact hker (augmentedIndex 46)
  have hrw047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hrw319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hrw387 : row387 x y z a w=0 := by
    rw [← row387_link]; exact hker (augmentedIndex 387)
  have hrw389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hrw397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hrw398 : row398 x y z a w=0 := by
    rw [← row398_link]; exact hker (augmentedIndex 398)
  have hrw403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hrw419 : row419 x y z a w=0 := by
    rw [← row419_link]; exact hker (augmentedIndex 419)
  have hrw423 : row423 x y z a w=0 := by
    rw [← row423_link]; exact hker (augmentedIndex 423)
  have hrw427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hrw428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hrw429 : row429 x y z a w=0 := by
    rw [← row429_link]; exact hker (augmentedIndex 429)
  have hrw435 : row435 x y z a w=0 := by
    rw [← row435_link]; exact hker (augmentedIndex 435)
  have hrw436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hz429_427 : augmentedLaurentShiftRow (-1) (1) (1) x y z w (augmentedIndex 427)=0 := rfl
  have hz429_428 : augmentedLaurentShiftRow (-1) (1) (1) x y z w (augmentedIndex 428)=0 := rfl
  have hz429_429 : augmentedLaurentShiftRow (-1) (1) (1) x y z w (augmentedIndex 429)=0 := rfl
  have hs429 : (((-1))*shift006 x y z a w+(((-7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((-14*y)/(3*z)))*shift009 x y z a w+(((-7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)=0 := by
    convert h429 using 1
    simp [coeff429,rows429,Fin.sum_univ_succ,(shift006_link x y z a w),(shift007_link x y z a w),(shift008_link x y z a w),(shift009_link x y z a w),(shift011_link x y z a w),(shift043_link x y z a w),(shift047_link x y z a w),hz429_427,hz429_428,hz429_429]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp429 := projection429 x y z a hx hy hz w
  simp only [hs429,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw387,hrw389,hrw397,hrw398,hrw403,hrw419,hrw423,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp429
  have hz435_319 : augmentedLaurentShiftRow (-1) (1) (1) x y z w (augmentedIndex 319)=0 := rfl
  have hz435_427 : augmentedLaurentShiftRow (-1) (1) (1) x y z w (augmentedIndex 427)=0 := rfl
  have hz435_435 : augmentedLaurentShiftRow (-1) (1) (1) x y z w (augmentedIndex 435)=0 := rfl
  have hs435 : (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((28*y)/(3*x^2*z)))*shift009 x y z a w+(((-21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)=0 := by
    convert h435 using 1
    simp [coeff435,rows435,Fin.sum_univ_succ,(shift003_link x y z a w),(shift005_link x y z a w),(shift006_link x y z a w),(shift009_link x y z a w),(shift038_link x y z a w),(shift046_link x y z a w),(shift397_link x y z a w),(shift398_link x y z a w),hz435_319,hz435_427,hz435_435]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp435 := projection435 x y z a hx hy hz w
  simp only [hs435,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw387,hrw389,hrw397,hrw398,hrw403,hrw419,hrw423,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp435
  have hr := residual403 x y z a hx hy hz w
  simp only [hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw387,hrw389,hrw397,hrw398,hrw403,hrw419,hrw423,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add] at hr
  apply SmallLevelTwentyOneFirstJet.conditions_of_three_residuals (-1) (1) (1) x y z a
    (by norm_num) hx hy hz
  · linear_combination -hp429
  · linear_combination -hp435
  · linear_combination (norm := ring_nf) -hr
    simp [hz]

#print axioms conditions
end SmallLevelTwentyOneFirstJetBundle3
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The common generated tactic sequences close at different stages for different rows.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace SmallLevelTwentyOneFirstJetBundle4
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne
open SmallLevelTwentyOneFirstJetCase4 SmallLevelTwentyOneFirstJetLink4

def rows429 : Fin 10 → AugmentedRow := ![augmentedIndex 6,augmentedIndex 7,augmentedIndex 8,augmentedIndex 9,augmentedIndex 11,augmentedIndex 43,augmentedIndex 47,augmentedIndex 427,augmentedIndex 428,augmentedIndex 429]
def coeff429 (x y z a : ℂ) : Fin 10 → ℂ := ![((-1)),(((1*x^2*y)/(z))),((-1)),(((2*y)/(z))),(((1*y)/(z))),((-1)),((-1)),(((-2*y)/(z))),(((-1*x^2*y)/(z))),((1))]

theorem syzygy429_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff429 x y z a i*augmentedLaurentRow (1) (-1) (-1) x y z a w (rows429 i))=0 := by
  simpa [coeff429,rows429,Fin.sum_univ_succ,row006_link,row007_link,row008_link,row009_link,row011_link,row043_link,row047_link,row427_link,row428_link,row429_link,add_assoc] using
    syzygy429 x y z a hx hy hz w

#print axioms syzygy429_model

def rows435 : Fin 11 → AugmentedRow := ![augmentedIndex 3,augmentedIndex 5,augmentedIndex 6,augmentedIndex 9,augmentedIndex 38,augmentedIndex 46,augmentedIndex 319,augmentedIndex 397,augmentedIndex 398,augmentedIndex 427,augmentedIndex 435]
def coeff435 (x y z a : ℂ) : Fin 11 → ℂ := ![((-1)),(((1*a)/(x))),(((1)/(x^2))),(((-1*y)/(x^2*z))),(((1*x*a)/(y*z))),((-1)),(((-2)/(x^2*z))+((1*a)/(x*y*z))+((-1)/(y*z))),(((-1)/(x^2))),(((-1)/(x^2))),(((-1)/(x^2*z))+((1*y)/(x^2*z))),((1))]

theorem syzygy435_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff435 x y z a i*augmentedLaurentRow (1) (-1) (-1) x y z a w (rows435 i))=0 := by
  simpa [coeff435,rows435,Fin.sum_univ_succ,row003_link,row005_link,row006_link,row009_link,row038_link,row046_link,row319_link,row397_link,row398_link,row427_link,row435_link,add_assoc] using
    syzygy435 x y z a hx hy hz w

#print axioms syzygy435_model

theorem conditions (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (1) (-1) (-1) x y z a w r=0)
    (h429 : ∑ i, coeff429 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (1) (-1) (-1) x y z w (rows429 i)=0)
    (h435 : ∑ i, coeff435 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (1) (-1) (-1) x y z w (rows435 i)=0) :
    a*x+x^2-1=0 ∧ y+3*(-1)=0 ∧ z=6*(1)*(-1)+(-1) := by
  have hrw000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hrw003 : row003 x y z a w=0 := by
    rw [← row003_link]; exact hker (augmentedIndex 3)
  have hrw004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hrw005 : row005 x y z a w=0 := by
    rw [← row005_link]; exact hker (augmentedIndex 5)
  have hrw006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hrw007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hrw008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hrw009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hrw010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hrw011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hrw038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hrw040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hrw043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hrw046 : row046 x y z a w=0 := by
    rw [← row046_link]; exact hker (augmentedIndex 46)
  have hrw047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hrw319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hrw388 : row388 x y z a w=0 := by
    rw [← row388_link]; exact hker (augmentedIndex 388)
  have hrw389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hrw397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hrw398 : row398 x y z a w=0 := by
    rw [← row398_link]; exact hker (augmentedIndex 398)
  have hrw403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hrw427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hrw428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hrw429 : row429 x y z a w=0 := by
    rw [← row429_link]; exact hker (augmentedIndex 429)
  have hrw435 : row435 x y z a w=0 := by
    rw [← row435_link]; exact hker (augmentedIndex 435)
  have hrw436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hz429_427 : augmentedLaurentShiftRow (1) (-1) (-1) x y z w (augmentedIndex 427)=0 := rfl
  have hz429_428 : augmentedLaurentShiftRow (1) (-1) (-1) x y z w (augmentedIndex 428)=0 := rfl
  have hz429_429 : augmentedLaurentShiftRow (1) (-1) (-1) x y z w (augmentedIndex 429)=0 := rfl
  have hs429 : (((-1))*shift006 x y z a w+(((7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((14*y)/(3*z)))*shift009 x y z a w+(((7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)=0 := by
    convert h429 using 1
    simp [coeff429,rows429,Fin.sum_univ_succ,(shift006_link x y z a w),(shift007_link x y z a w),(shift008_link x y z a w),(shift009_link x y z a w),(shift011_link x y z a w),(shift043_link x y z a w),(shift047_link x y z a w),hz429_427,hz429_428,hz429_429]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp429 := projection429 x y z a hx hy hz w
  simp only [hs429,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw388,hrw389,hrw397,hrw398,hrw403,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp429
  have hz435_319 : augmentedLaurentShiftRow (1) (-1) (-1) x y z w (augmentedIndex 319)=0 := rfl
  have hz435_427 : augmentedLaurentShiftRow (1) (-1) (-1) x y z w (augmentedIndex 427)=0 := rfl
  have hz435_435 : augmentedLaurentShiftRow (1) (-1) (-1) x y z w (augmentedIndex 435)=0 := rfl
  have hs435 : (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((-28*y)/(3*x^2*z)))*shift009 x y z a w+(((21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)=0 := by
    convert h435 using 1
    simp [coeff435,rows435,Fin.sum_univ_succ,(shift003_link x y z a w),(shift005_link x y z a w),(shift006_link x y z a w),(shift009_link x y z a w),(shift038_link x y z a w),(shift046_link x y z a w),(shift397_link x y z a w),(shift398_link x y z a w),hz435_319,hz435_427,hz435_435]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp435 := projection435 x y z a hx hy hz w
  simp only [hs435,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw388,hrw389,hrw397,hrw398,hrw403,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp435
  have hr := residual403 x y z a hx hy hz w
  simp only [hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw388,hrw389,hrw397,hrw398,hrw403,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add] at hr
  apply SmallLevelTwentyOneFirstJet.conditions_of_three_residuals (1) (-1) (-1) x y z a
    (by norm_num) hx hy hz
  · linear_combination -hp429
  · linear_combination -hp435
  · linear_combination (norm := ring_nf) -hr
    simp [hz]

#print axioms conditions
end SmallLevelTwentyOneFirstJetBundle4
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The common generated tactic sequences close at different stages for different rows.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace SmallLevelTwentyOneFirstJetBundle5
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne
open SmallLevelTwentyOneFirstJetCase5 SmallLevelTwentyOneFirstJetLink5

def rows429 : Fin 10 → AugmentedRow := ![augmentedIndex 6,augmentedIndex 7,augmentedIndex 8,augmentedIndex 9,augmentedIndex 11,augmentedIndex 43,augmentedIndex 47,augmentedIndex 427,augmentedIndex 428,augmentedIndex 429]
def coeff429 (x y z a : ℂ) : Fin 10 → ℂ := ![((-1)),(((1*x^2*y)/(z))),((-1)),(((2*y)/(z))),(((1*y)/(z))),((-1)),((-1)),(((-2*y)/(z))),(((-1*x^2*y)/(z))),((1))]

theorem syzygy429_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff429 x y z a i*augmentedLaurentRow (1) (-1) (1) x y z a w (rows429 i))=0 := by
  simpa [coeff429,rows429,Fin.sum_univ_succ,row006_link,row007_link,row008_link,row009_link,row011_link,row043_link,row047_link,row427_link,row428_link,row429_link,add_assoc] using
    syzygy429 x y z a hx hy hz w

#print axioms syzygy429_model

def rows435 : Fin 11 → AugmentedRow := ![augmentedIndex 3,augmentedIndex 5,augmentedIndex 6,augmentedIndex 9,augmentedIndex 38,augmentedIndex 46,augmentedIndex 319,augmentedIndex 397,augmentedIndex 398,augmentedIndex 427,augmentedIndex 435]
def coeff435 (x y z a : ℂ) : Fin 11 → ℂ := ![((-1)),(((1*a)/(x))),(((1)/(x^2))),(((-1*y)/(x^2*z))),(((1*x*a)/(y*z))),((-1)),(((-2)/(x^2*z))+((1*a)/(x*y*z))+((-1)/(y*z))),(((-1)/(x^2))),(((-1)/(x^2))),(((-1)/(x^2*z))+((1*y)/(x^2*z))),((1))]

theorem syzygy435_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff435 x y z a i*augmentedLaurentRow (1) (-1) (1) x y z a w (rows435 i))=0 := by
  simpa [coeff435,rows435,Fin.sum_univ_succ,row003_link,row005_link,row006_link,row009_link,row038_link,row046_link,row319_link,row397_link,row398_link,row427_link,row435_link,add_assoc] using
    syzygy435 x y z a hx hy hz w

#print axioms syzygy435_model

theorem conditions (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (1) (-1) (1) x y z a w r=0)
    (h429 : ∑ i, coeff429 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (1) (-1) (1) x y z w (rows429 i)=0)
    (h435 : ∑ i, coeff435 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (1) (-1) (1) x y z w (rows435 i)=0) :
    a*x+x^2-1=0 ∧ y+3*(-1)=0 ∧ z=6*(1)*(-1)+(1) := by
  have hrw000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hrw003 : row003 x y z a w=0 := by
    rw [← row003_link]; exact hker (augmentedIndex 3)
  have hrw004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hrw005 : row005 x y z a w=0 := by
    rw [← row005_link]; exact hker (augmentedIndex 5)
  have hrw006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hrw007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hrw008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hrw009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hrw010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hrw011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hrw038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hrw040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hrw043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hrw046 : row046 x y z a w=0 := by
    rw [← row046_link]; exact hker (augmentedIndex 46)
  have hrw047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hrw319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hrw387 : row387 x y z a w=0 := by
    rw [← row387_link]; exact hker (augmentedIndex 387)
  have hrw389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hrw397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hrw398 : row398 x y z a w=0 := by
    rw [← row398_link]; exact hker (augmentedIndex 398)
  have hrw403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hrw419 : row419 x y z a w=0 := by
    rw [← row419_link]; exact hker (augmentedIndex 419)
  have hrw423 : row423 x y z a w=0 := by
    rw [← row423_link]; exact hker (augmentedIndex 423)
  have hrw427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hrw428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hrw429 : row429 x y z a w=0 := by
    rw [← row429_link]; exact hker (augmentedIndex 429)
  have hrw435 : row435 x y z a w=0 := by
    rw [← row435_link]; exact hker (augmentedIndex 435)
  have hrw436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hz429_427 : augmentedLaurentShiftRow (1) (-1) (1) x y z w (augmentedIndex 427)=0 := rfl
  have hz429_428 : augmentedLaurentShiftRow (1) (-1) (1) x y z w (augmentedIndex 428)=0 := rfl
  have hz429_429 : augmentedLaurentShiftRow (1) (-1) (1) x y z w (augmentedIndex 429)=0 := rfl
  have hs429 : (((-1))*shift006 x y z a w+(((7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((14*y)/(3*z)))*shift009 x y z a w+(((7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)=0 := by
    convert h429 using 1
    simp [coeff429,rows429,Fin.sum_univ_succ,(shift006_link x y z a w),(shift007_link x y z a w),(shift008_link x y z a w),(shift009_link x y z a w),(shift011_link x y z a w),(shift043_link x y z a w),(shift047_link x y z a w),hz429_427,hz429_428,hz429_429]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp429 := projection429 x y z a hx hy hz w
  simp only [hs429,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw387,hrw389,hrw397,hrw398,hrw403,hrw419,hrw423,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp429
  have hz435_319 : augmentedLaurentShiftRow (1) (-1) (1) x y z w (augmentedIndex 319)=0 := rfl
  have hz435_427 : augmentedLaurentShiftRow (1) (-1) (1) x y z w (augmentedIndex 427)=0 := rfl
  have hz435_435 : augmentedLaurentShiftRow (1) (-1) (1) x y z w (augmentedIndex 435)=0 := rfl
  have hs435 : (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((-28*y)/(3*x^2*z)))*shift009 x y z a w+(((21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)=0 := by
    convert h435 using 1
    simp [coeff435,rows435,Fin.sum_univ_succ,(shift003_link x y z a w),(shift005_link x y z a w),(shift006_link x y z a w),(shift009_link x y z a w),(shift038_link x y z a w),(shift046_link x y z a w),(shift397_link x y z a w),(shift398_link x y z a w),hz435_319,hz435_427,hz435_435]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp435 := projection435 x y z a hx hy hz w
  simp only [hs435,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw387,hrw389,hrw397,hrw398,hrw403,hrw419,hrw423,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp435
  have hr := residual403 x y z a hx hy hz w
  simp only [hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw387,hrw389,hrw397,hrw398,hrw403,hrw419,hrw423,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add] at hr
  apply SmallLevelTwentyOneFirstJet.conditions_of_three_residuals (1) (-1) (1) x y z a
    (by norm_num) hx hy hz
  · linear_combination -hp429
  · linear_combination -hp435
  · linear_combination (norm := ring_nf) -hr
    simp [hz]

#print axioms conditions
end SmallLevelTwentyOneFirstJetBundle5
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The common generated tactic sequences close at different stages for different rows.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace SmallLevelTwentyOneFirstJetBundle6
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne
open SmallLevelTwentyOneFirstJetCase6 SmallLevelTwentyOneFirstJetLink6

def rows429 : Fin 10 → AugmentedRow := ![augmentedIndex 6,augmentedIndex 7,augmentedIndex 8,augmentedIndex 9,augmentedIndex 11,augmentedIndex 43,augmentedIndex 47,augmentedIndex 427,augmentedIndex 428,augmentedIndex 429]
def coeff429 (x y z a : ℂ) : Fin 10 → ℂ := ![((-1)),(((1*x^2*y)/(z))),((-1)),(((2*y)/(z))),(((1*y)/(z))),((-1)),((-1)),(((-2*y)/(z))),(((-1*x^2*y)/(z))),((1))]

theorem syzygy429_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff429 x y z a i*augmentedLaurentRow (1) (1) (-1) x y z a w (rows429 i))=0 := by
  simpa [coeff429,rows429,Fin.sum_univ_succ,row006_link,row007_link,row008_link,row009_link,row011_link,row043_link,row047_link,row427_link,row428_link,row429_link,add_assoc] using
    syzygy429 x y z a hx hy hz w

#print axioms syzygy429_model

def rows435 : Fin 11 → AugmentedRow := ![augmentedIndex 3,augmentedIndex 5,augmentedIndex 6,augmentedIndex 9,augmentedIndex 38,augmentedIndex 46,augmentedIndex 319,augmentedIndex 397,augmentedIndex 398,augmentedIndex 427,augmentedIndex 435]
def coeff435 (x y z a : ℂ) : Fin 11 → ℂ := ![((-1)),(((1*a)/(x))),(((1)/(x^2))),(((-1*y)/(x^2*z))),(((1*x*a)/(y*z))),((-1)),(((2)/(x^2*z))+((1*a)/(x*y*z))+((-1)/(y*z))),(((-1)/(x^2))),(((-1)/(x^2))),(((1)/(x^2*z))+((1*y)/(x^2*z))),((1))]

theorem syzygy435_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff435 x y z a i*augmentedLaurentRow (1) (1) (-1) x y z a w (rows435 i))=0 := by
  simpa [coeff435,rows435,Fin.sum_univ_succ,row003_link,row005_link,row006_link,row009_link,row038_link,row046_link,row319_link,row397_link,row398_link,row427_link,row435_link,add_assoc] using
    syzygy435 x y z a hx hy hz w

#print axioms syzygy435_model

theorem conditions (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (1) (1) (-1) x y z a w r=0)
    (h429 : ∑ i, coeff429 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (1) (1) (-1) x y z w (rows429 i)=0)
    (h435 : ∑ i, coeff435 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (1) (1) (-1) x y z w (rows435 i)=0) :
    a*x+x^2-1=0 ∧ y+3*(1)=0 ∧ z=6*(1)*(1)+(-1) := by
  have hrw000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hrw003 : row003 x y z a w=0 := by
    rw [← row003_link]; exact hker (augmentedIndex 3)
  have hrw004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hrw005 : row005 x y z a w=0 := by
    rw [← row005_link]; exact hker (augmentedIndex 5)
  have hrw006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hrw007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hrw008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hrw009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hrw010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hrw011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hrw038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hrw040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hrw043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hrw046 : row046 x y z a w=0 := by
    rw [← row046_link]; exact hker (augmentedIndex 46)
  have hrw047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hrw319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hrw387 : row387 x y z a w=0 := by
    rw [← row387_link]; exact hker (augmentedIndex 387)
  have hrw389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hrw397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hrw398 : row398 x y z a w=0 := by
    rw [← row398_link]; exact hker (augmentedIndex 398)
  have hrw403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hrw419 : row419 x y z a w=0 := by
    rw [← row419_link]; exact hker (augmentedIndex 419)
  have hrw423 : row423 x y z a w=0 := by
    rw [← row423_link]; exact hker (augmentedIndex 423)
  have hrw427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hrw428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hrw429 : row429 x y z a w=0 := by
    rw [← row429_link]; exact hker (augmentedIndex 429)
  have hrw435 : row435 x y z a w=0 := by
    rw [← row435_link]; exact hker (augmentedIndex 435)
  have hrw436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hz429_427 : augmentedLaurentShiftRow (1) (1) (-1) x y z w (augmentedIndex 427)=0 := rfl
  have hz429_428 : augmentedLaurentShiftRow (1) (1) (-1) x y z w (augmentedIndex 428)=0 := rfl
  have hz429_429 : augmentedLaurentShiftRow (1) (1) (-1) x y z w (augmentedIndex 429)=0 := rfl
  have hs429 : (((-1))*shift006 x y z a w+(((7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((14*y)/(3*z)))*shift009 x y z a w+(((7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)=0 := by
    convert h429 using 1
    simp [coeff429,rows429,Fin.sum_univ_succ,(shift006_link x y z a w),(shift007_link x y z a w),(shift008_link x y z a w),(shift009_link x y z a w),(shift011_link x y z a w),(shift043_link x y z a w),(shift047_link x y z a w),hz429_427,hz429_428,hz429_429]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp429 := projection429 x y z a hx hy hz w
  simp only [hs429,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw387,hrw389,hrw397,hrw398,hrw403,hrw419,hrw423,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp429
  have hz435_319 : augmentedLaurentShiftRow (1) (1) (-1) x y z w (augmentedIndex 319)=0 := rfl
  have hz435_427 : augmentedLaurentShiftRow (1) (1) (-1) x y z w (augmentedIndex 427)=0 := rfl
  have hz435_435 : augmentedLaurentShiftRow (1) (1) (-1) x y z w (augmentedIndex 435)=0 := rfl
  have hs435 : (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((-28*y)/(3*x^2*z)))*shift009 x y z a w+(((21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)=0 := by
    convert h435 using 1
    simp [coeff435,rows435,Fin.sum_univ_succ,(shift003_link x y z a w),(shift005_link x y z a w),(shift006_link x y z a w),(shift009_link x y z a w),(shift038_link x y z a w),(shift046_link x y z a w),(shift397_link x y z a w),(shift398_link x y z a w),hz435_319,hz435_427,hz435_435]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp435 := projection435 x y z a hx hy hz w
  simp only [hs435,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw387,hrw389,hrw397,hrw398,hrw403,hrw419,hrw423,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp435
  have hr := residual403 x y z a hx hy hz w
  simp only [hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw387,hrw389,hrw397,hrw398,hrw403,hrw419,hrw423,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add] at hr
  apply SmallLevelTwentyOneFirstJet.conditions_of_three_residuals (1) (1) (-1) x y z a
    (by norm_num) hx hy hz
  · linear_combination -hp429
  · linear_combination -hp435
  · linear_combination (norm := ring_nf) -hr
    simp [hz]

#print axioms conditions
end SmallLevelTwentyOneFirstJetBundle6
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
-- The common generated tactic sequences close at different stages for different rows.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace SmallLevelTwentyOneFirstJetBundle7
open Complex SmallLevelTwentyOneKnownWords SmallLevelTwentyOne
open SmallLevelTwentyOneFirstJetCase7 SmallLevelTwentyOneFirstJetLink7

def rows429 : Fin 10 → AugmentedRow := ![augmentedIndex 6,augmentedIndex 7,augmentedIndex 8,augmentedIndex 9,augmentedIndex 11,augmentedIndex 43,augmentedIndex 47,augmentedIndex 427,augmentedIndex 428,augmentedIndex 429]
def coeff429 (x y z a : ℂ) : Fin 10 → ℂ := ![((-1)),(((1*x^2*y)/(z))),((-1)),(((2*y)/(z))),(((1*y)/(z))),((-1)),((-1)),(((-2*y)/(z))),(((-1*x^2*y)/(z))),((1))]

theorem syzygy429_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff429 x y z a i*augmentedLaurentRow (1) (1) (1) x y z a w (rows429 i))=0 := by
  simpa [coeff429,rows429,Fin.sum_univ_succ,row006_link,row007_link,row008_link,row009_link,row011_link,row043_link,row047_link,row427_link,row428_link,row429_link,add_assoc] using
    syzygy429 x y z a hx hy hz w

#print axioms syzygy429_model

def rows435 : Fin 11 → AugmentedRow := ![augmentedIndex 3,augmentedIndex 5,augmentedIndex 6,augmentedIndex 9,augmentedIndex 38,augmentedIndex 46,augmentedIndex 319,augmentedIndex 397,augmentedIndex 398,augmentedIndex 427,augmentedIndex 435]
def coeff435 (x y z a : ℂ) : Fin 11 → ℂ := ![((-1)),(((1*a)/(x))),(((1)/(x^2))),(((-1*y)/(x^2*z))),(((1*x*a)/(y*z))),((-1)),(((2)/(x^2*z))+((1*a)/(x*y*z))+((-1)/(y*z))),(((-1)/(x^2))),(((-1)/(x^2))),(((1)/(x^2*z))+((1*y)/(x^2*z))),((1))]

theorem syzygy435_model (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) :
    (∑ i, coeff435 x y z a i*augmentedLaurentRow (1) (1) (1) x y z a w (rows435 i))=0 := by
  simpa [coeff435,rows435,Fin.sum_univ_succ,row003_link,row005_link,row006_link,row009_link,row038_link,row046_link,row319_link,row397_link,row398_link,row427_link,row435_link,add_assoc] using
    syzygy435 x y z a hx hy hz w

#print axioms syzygy435_model

theorem conditions (x y z a : ℂ) (hx : x≠0) (hy : y≠0) (hz : z≠0)
    (w : Fin 42 → ℂ) (h28 : w 28=1)
    (hker : ∀ r, augmentedLaurentRow (1) (1) (1) x y z a w r=0)
    (h429 : ∑ i, coeff429 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (1) (1) (1) x y z w (rows429 i)=0)
    (h435 : ∑ i, coeff435 (x/2) (y/3) (z/7) a i*
      augmentedLaurentShiftRow (1) (1) (1) x y z w (rows435 i)=0) :
    a*x+x^2-1=0 ∧ y+3*(1)=0 ∧ z=6*(1)*(1)+(1) := by
  have hrw000 : row000 x y z a w=0 := by
    rw [← row000_link]; exact hker (augmentedIndex 0)
  have hrw003 : row003 x y z a w=0 := by
    rw [← row003_link]; exact hker (augmentedIndex 3)
  have hrw004 : row004 x y z a w=0 := by
    rw [← row004_link]; exact hker (augmentedIndex 4)
  have hrw005 : row005 x y z a w=0 := by
    rw [← row005_link]; exact hker (augmentedIndex 5)
  have hrw006 : row006 x y z a w=0 := by
    rw [← row006_link]; exact hker (augmentedIndex 6)
  have hrw007 : row007 x y z a w=0 := by
    rw [← row007_link]; exact hker (augmentedIndex 7)
  have hrw008 : row008 x y z a w=0 := by
    rw [← row008_link]; exact hker (augmentedIndex 8)
  have hrw009 : row009 x y z a w=0 := by
    rw [← row009_link]; exact hker (augmentedIndex 9)
  have hrw010 : row010 x y z a w=0 := by
    rw [← row010_link]; exact hker (augmentedIndex 10)
  have hrw011 : row011 x y z a w=0 := by
    rw [← row011_link]; exact hker (augmentedIndex 11)
  have hrw038 : row038 x y z a w=0 := by
    rw [← row038_link]; exact hker (augmentedIndex 38)
  have hrw040 : row040 x y z a w=0 := by
    rw [← row040_link]; exact hker (augmentedIndex 40)
  have hrw043 : row043 x y z a w=0 := by
    rw [← row043_link]; exact hker (augmentedIndex 43)
  have hrw046 : row046 x y z a w=0 := by
    rw [← row046_link]; exact hker (augmentedIndex 46)
  have hrw047 : row047 x y z a w=0 := by
    rw [← row047_link]; exact hker (augmentedIndex 47)
  have hrw319 : row319 x y z a w=0 := by
    rw [← row319_link]; exact hker (augmentedIndex 319)
  have hrw388 : row388 x y z a w=0 := by
    rw [← row388_link]; exact hker (augmentedIndex 388)
  have hrw389 : row389 x y z a w=0 := by
    rw [← row389_link]; exact hker (augmentedIndex 389)
  have hrw397 : row397 x y z a w=0 := by
    rw [← row397_link]; exact hker (augmentedIndex 397)
  have hrw398 : row398 x y z a w=0 := by
    rw [← row398_link]; exact hker (augmentedIndex 398)
  have hrw403 : row403 x y z a w=0 := by
    rw [← row403_link]; exact hker (augmentedIndex 403)
  have hrw427 : row427 x y z a w=0 := by
    rw [← row427_link]; exact hker (augmentedIndex 427)
  have hrw428 : row428 x y z a w=0 := by
    rw [← row428_link]; exact hker (augmentedIndex 428)
  have hrw429 : row429 x y z a w=0 := by
    rw [← row429_link]; exact hker (augmentedIndex 429)
  have hrw435 : row435 x y z a w=0 := by
    rw [← row435_link]; exact hker (augmentedIndex 435)
  have hrw436 : row436 x y z a w=0 := by
    rw [← row436_link]; exact hker (augmentedIndex 436)
  have hz429_427 : augmentedLaurentShiftRow (1) (1) (1) x y z w (augmentedIndex 427)=0 := rfl
  have hz429_428 : augmentedLaurentShiftRow (1) (1) (1) x y z w (augmentedIndex 428)=0 := rfl
  have hz429_429 : augmentedLaurentShiftRow (1) (1) (1) x y z w (augmentedIndex 429)=0 := rfl
  have hs429 : (((-1))*shift006 x y z a w+(((7*x^2*y)/(12*z)))*shift007 x y z a w+((-1))*shift008 x y z a w+(((14*y)/(3*z)))*shift009 x y z a w+(((7*y)/(3*z)))*shift011 x y z a w+((-1))*shift043 x y z a w+((-1))*shift047 x y z a w)=0 := by
    convert h429 using 1
    simp [coeff429,rows429,Fin.sum_univ_succ,(shift006_link x y z a w),(shift007_link x y z a w),(shift008_link x y z a w),(shift009_link x y z a w),(shift011_link x y z a w),(shift043_link x y z a w),(shift047_link x y z a w),hz429_427,hz429_428,hz429_429]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp429 := projection429 x y z a hx hy hz w
  simp only [hs429,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw388,hrw389,hrw397,hrw398,hrw403,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp429
  have hz435_319 : augmentedLaurentShiftRow (1) (1) (1) x y z w (augmentedIndex 319)=0 := rfl
  have hz435_427 : augmentedLaurentShiftRow (1) (1) (1) x y z w (augmentedIndex 427)=0 := rfl
  have hz435_435 : augmentedLaurentShiftRow (1) (1) (1) x y z w (augmentedIndex 435)=0 := rfl
  have hs435 : (((-1))*shift003 x y z a w+(((2*a)/(x)))*shift005 x y z a w+(((4)/(x^2)))*shift006 x y z a w+(((-28*y)/(3*x^2*z)))*shift009 x y z a w+(((21*x*a)/(2*y*z)))*shift038 x y z a w+((-1))*shift046 x y z a w+(((-4)/(x^2)))*shift397 x y z a w+(((-4)/(x^2)))*shift398 x y z a w)=0 := by
    convert h435 using 1
    simp [coeff435,rows435,Fin.sum_univ_succ,(shift003_link x y z a w),(shift005_link x y z a w),(shift006_link x y z a w),(shift009_link x y z a w),(shift038_link x y z a w),(shift046_link x y z a w),(shift397_link x y z a w),(shift398_link x y z a w),hz435_319,hz435_427,hz435_435]
    <;> field_simp [hx,hy,hz] <;> ring
  have hp435 := projection435 x y z a hx hy hz w
  simp only [hs435,hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw388,hrw389,hrw397,hrw398,hrw403,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add,zero_sub] at hp435
  have hr := residual403 x y z a hx hy hz w
  simp only [hrw000,hrw003,hrw004,hrw005,hrw006,hrw007,hrw008,hrw009,hrw010,hrw011,hrw038,hrw040,hrw043,hrw046,hrw047,hrw319,hrw388,hrw389,hrw397,hrw398,hrw403,hrw427,hrw428,hrw429,hrw435,hrw436,h28,mul_zero,mul_one,add_zero,zero_add] at hr
  apply SmallLevelTwentyOneFirstJet.conditions_of_three_residuals (1) (1) (1) x y z a
    (by norm_num) hx hy hz
  · linear_combination -hp429
  · linear_combination -hp435
  · linear_combination (norm := ring_nf) -hr
    simp [hz]

#print axioms conditions
end SmallLevelTwentyOneFirstJetBundle7
end
