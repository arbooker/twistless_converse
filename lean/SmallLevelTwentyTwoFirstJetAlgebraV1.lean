module

public import SmallLevelSimplePoleTaylorTheoryV4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyTwoFirstJet
open Complex

/-- These are the two scalar first-jet obstructions after the65
monomial pivots. Linking them to the actual continued rows is separate. -/
def first (u x y : ℂ) : ℂ := 6*u*y^2+3*x+2*x*y^2+3*u*x^2+3*x^3
def second (u x y : ℂ) : ℂ := -12*u*y^2-72*x-4*x*y^2+27*u*x^2+27*x^3

theorem alternatives (u x y : ℂ) (hu : u=1 ∨ u= -1) (hx : x≠0)
    (h1 : first u x y=0) (h2 : second u x y=0) :
    (x= -2*u ∧ y^2=9) ∨ (x=u ∧ y^2= -9/8) := by
  have hu2 : u^2=1 := by rcases hu with rfl|rfl <;> norm_num
  have hp : x*((x+2*u)*(x-u))=0 := by
    dsimp [first] at h1
    dsimp [second] at h2
    linear_combination (2*h1+h2)/33-2*x*hu2
  have hprod := (mul_eq_zero.mp hp).resolve_left hx
  rcases mul_eq_zero.mp hprod with h|h
  · have hx' : x= -2*u := by linear_combination h
    refine Or.inl ⟨hx',?_⟩
    rw [hx'] at h1
    rcases hu with rfl|rfl
    · dsimp [first] at h1
      linear_combination h1/2
    · dsimp [first] at h1
      linear_combination -h1/2
  · have hx' : x=u := sub_eq_zero.mp h
    refine Or.inr ⟨hx',?_⟩
    rw [hx'] at h1
    rcases hu with rfl|rfl
    · dsimp [first] at h1
      linear_combination h1/8
    · dsimp [first] at h1
      linear_combination -h1/8

#print axioms alternatives
end SmallLevelTwentyTwoFirstJet
