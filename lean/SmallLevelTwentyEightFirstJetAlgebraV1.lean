module
public import SmallLevelSimplePoleTaylorTheoryV4
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyEightFirstJet
open Complex

/- These scalar equations are the normalized residual and two first-jet
consequences. Their linkage to the actual quotient rows is a separate proof. -/
def first (η σ Y Z a : ℂ) : ℂ :=
  -3*η*Z+3*a*Y+Y^2-3*(1-η*σ)

def second (η σ Y Z : ℂ) : ℂ :=
  3*η*Z+3*(2-η*σ)+2*Y^2

def residual (η σ Y Z a : ℂ) : ℂ :=
  (1-η*σ)-η*Z-Z^2+(η*σ)*(a*Y)+η*(a*Y)*Z+
    (6-3*η*σ)*Y^2+η*Y^2*Z-2*(a*Y)*Y^2-2*Y^4

theorem constraints (η σ Y Z a : ℂ) (hη : η=1 ∨ η= -1)
    (hσ : σ=1 ∨ σ= -1) (hY : Y≠0)
    (h1 : first η σ Y Z a=0) (h2 : second η σ Y Z=0)
    (hr : residual η σ Y Z a=0) :
    Y^2=15-6*η*σ ∧
    (15-6*η*σ)*a+(16-6*η*σ)*Y=0 ∧
    Z= -η*(12-5*η*σ) := by
  have hη2 : η^2=1 := by rcases hη with rfl|rfl <;> norm_num
  have hτ2 : (η*σ)^2=1 := by
    rcases hη with rfl|rfl <;> rcases hσ with rfl|rfl <;> norm_num
  dsimp [first] at h1
  dsimp [second] at h2
  dsimp [residual] at hr
  have hb : a*Y= -1-Y^2 := by linear_combination (h1+h2)/3
  have hu : η*Z= -(2-η*σ)-2*Y^2/3 := by linear_combination h2/3
  have hr' : (1-η*σ)-η*Z-(η*Z)^2+(η*σ)*(a*Y)+(a*Y)*(η*Z)+
      (6-3*η*σ)*Y^2+Y^2*(η*Z)-2*(a*Y)*Y^2-2*(Y^2)^2=0 := by
    linear_combination hr-Z^2*hη2
  rw [hb,hu] at hr'
  have hp : Y^2*(Y^2-(15-6*η*σ))=0 := by
    linear_combination -(9/4:ℂ)*hr'-(9/4:ℂ)*hτ2
  have ht : Y^2=15-6*η*σ :=
    sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ hY))
  refine ⟨ht,?_,?_⟩
  · rw [show (16-6*η*σ:ℂ)=(15-6*η*σ)+1 by ring,← ht]
    linear_combination Y*hb
  · calc
      Z=η*(η*Z) := by rw [← mul_assoc,← pow_two,hη2,one_mul]
      _ = -η*(12-5*η*σ) := by rw [hu,ht]; ring

#print axioms constraints
end SmallLevelTwentyEightFirstJet
