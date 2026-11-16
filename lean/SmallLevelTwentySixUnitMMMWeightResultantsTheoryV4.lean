module

public import SmallLevelTwentySixUnitMMMTheoryV4
public import SmallLevelTwentySixResultantPolynomialDataV1

/-! Consolidated chapter: SmallLevelTwentySixUnitMMM.WeightResultants. Original declarations and local scopes are retained. -/

/-! ## SmallLevelTwentySixUnitMMMWeightResultantsV1 -/
section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMM.WeightResultants
open Complex
theorem r_identity (x y z w a b t : ℂ) :
    x^2*r x y z w a b t=l0 x y z w a b t*p1 x y z w a b t-l1 x y z w a b t*p0 x y z w a b t := by
  unfold r l0 l1 p0 p1
  ring

theorem q_identity (x y z w a b t : ℂ) :
    q x y z w a b t=x^2*p3 x y z w a b t+p3b x y z w a b t*(p4 x y z w a b t-p0 x y z w a b t) := by
  unfold q p3 p3b p4 p0
  ring

theorem v_identity (x y z w a b t : ℂ) :
    x^4*v x y z w a b t=(l0 x y z w a b t)^2*q x y z w a b t-
      (l0 x y z w a b t*q2 x y z w a b t*t+l0 x y z w a b t*q1 x y z w a b t-q2 x y z w a b t*c0 x y z w a b t)*p0 x y z w a b t := by
  unfold v l0 q q2 q1 c0 p0
  ring

theorem necessary (x y z w a b t : ℂ) (hx : x≠0)
    (h0 : p0 x y z w a b t=0) (h1 : p1 x y z w a b t=0)
    (h3 : p3 x y z w a b t=0) (h4 : p4 x y z w a b t=0) :
    r x y z w a b t=0 ∧ v x y z w a b t=0 := by
  have hr : x^2*r x y z w a b t=0 := by rw [r_identity,h0,h1]; ring
  have hq : q x y z w a b t=0 := by rw [q_identity,h0,h3,h4]; ring
  have hv : x^4*v x y z w a b t=0 := by rw [v_identity,h0,hq]; ring
  exact ⟨(mul_eq_zero.mp hr).resolve_left (pow_ne_zero _ hx),
    (mul_eq_zero.mp hv).resolve_left (pow_ne_zero _ hx)⟩

theorem source_kernel_resultants (X Y Z W a b : ℂ)
    (hX : X≠0) (hY : Y≠0) (hZ : Z≠0) (hW : W≠0)
    (u : Fin 780→ℂ) (hu : ∀ i,sourceRows X Y Z W a b u i=0) (h300 : u 300≠0) :
    r X (Y^2) Z (W^2) (a*Y) (b*W) (u 540/u 300)=0 ∧
    v X (Y^2) Z (W^2) (a*Y) (b*W) (u 540/u 300)=0 := by
  apply necessary _ _ _ _ _ _ _ hX
  · have hh:=weight_row0 X Y Z W a b hX hY hZ hW u hu
    apply (mul_eq_zero.mp (show p0 X (Y^2) Z (W^2) (a*Y) (b*W) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
    unfold p0
    linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
  · have hh:=weight_row1 X Y Z W a b hX hY hZ hW u hu
    apply (mul_eq_zero.mp (show p1 X (Y^2) Z (W^2) (a*Y) (b*W) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
    unfold p1
    linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
  · have hh:=weight_row3 X Y Z W a b hX hY hZ hW u hu
    apply (mul_eq_zero.mp (show p3 X (Y^2) Z (W^2) (a*Y) (b*W) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
    unfold p3
    linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
  · have hh:=weight_row4 X Y Z W a b hX hY hZ hW u hu
    apply (mul_eq_zero.mp (show p4 X (Y^2) Z (W^2) (a*Y) (b*W) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
    unfold p4
    linear_combination (norm := (field_simp [h300]; all_goals ring)) hh

#print axioms necessary
#print axioms source_kernel_resultants
end SmallLevelTwentySixUnitMMM.WeightResultants
end
end

/-! ## SmallLevelTwentySixUnitMMMWeightTwoV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
@[expose] public noncomputable section
namespace SmallLevelTwentySixUnitMMM.WeightResultants
open Complex
theorem no_weight_two_plus (A B t : ℂ)
    (h0 : p0 2 9 13 25 A B t=0)
    (h1 : p1 2 9 13 25 A B t=0)
    (h2 : p2 2 9 13 25 A B t=0)
    (h3 : p3 2 9 13 25 A B t=0)
    (_h4 : p4 2 9 13 25 A B t=0)
    : False := by
  unfold p0 at h0
  unfold p1 at h1
  unfold p2 at h2
  unfold p3 at h3
  unfold p4 at _h4
  have hh : (1:ℂ)=0 := by
    linear_combination ((-1963769/4173961:ℂ))*h0 +
      ((-97963907/367308568:ℂ)*t)*h0 +
      ((1757453/367308568:ℂ)*B)*h0 +
      ((-43583/8347922:ℂ)*B*t)*h0 +
      ((-43583/33391688:ℂ)*B^2)*h0 +
      ((-12304465/183654284:ℂ)*A)*h0 +
      ((11346865/367308568:ℂ)*A*t)*h0 +
      ((-20935305/16695844:ℂ))*h1 +
      ((-11346865/16695844:ℂ)*t)*h1 +
      ((828077/16695844:ℂ)*B)*h1 +
      ((35319915/183654284:ℂ))*h2 +
      ((-2392921/183654284:ℂ)*t)*h2 +
      ((87166/4173961:ℂ)*B)*h2 +
      ((915243/33391688:ℂ)*B*t)*h2 +
      ((828077/16695844:ℂ)*A)*h2 +
      ((-2120990/4173961:ℂ))*h3 +
      ((-15471965/33391688:ℂ)*t)*h3 +
      ((43583/3035608:ℂ)*B)*h3 +
      ((-828077/33391688:ℂ)*A)*h3
  norm_num at hh

theorem source_kernel_weight_two_plus (a b : ℂ) (u : Fin 780→ℂ)
    (hu : ∀ i,sourceRows 2 3 13 5 a b u i=0) : ∀ j : Fin 320,u (support j)=0 := by
  by_cases h300 : u 300=0
  · exact source_zero_chart 2 3 13 5 a b (Or.inl (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) u hu h300
  · exfalso
    apply no_weight_two_plus (a*3) (b*5) (u 540/u 300)
    · have hh:=weight_row0 2 3 13 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p0 2 9 13 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p0
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row1 2 3 13 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p1 2 9 13 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p1
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row2 2 3 13 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p2 2 9 13 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p2
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row3 2 3 13 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p3 2 9 13 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p3
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row4 2 3 13 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p4 2 9 13 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p4
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh

#print axioms source_kernel_weight_two_plus

theorem no_weight_two_minus (A B t : ℂ)
    (h0 : p0 2 9 (-13) 25 A B t=0)
    (h1 : p1 2 9 (-13) 25 A B t=0)
    (h2 : p2 2 9 (-13) 25 A B t=0)
    (h3 : p3 2 9 (-13) 25 A B t=0)
    (_h4 : p4 2 9 (-13) 25 A B t=0)
    : False := by
  unfold p0 at h0
  unfold p1 at h1
  unfold p2 at h2
  unfold p3 at h3
  unfold p4 at _h4
  have hh : (1:ℂ)=0 := by
    linear_combination ((3192049/580954824:ℂ))*h0 +
      ((-256675/64550536:ℂ)*t)*h0 +
      ((-30075/64550536:ℂ)*B)*h0 +
      ((335/72619353:ℂ)*B*t)*h0 +
      ((335/290477412:ℂ)*B^2)*h0 +
      ((-67367/145238706:ℂ)*A)*h0 +
      ((155135/193651608:ℂ)*A*t)*h0 +
      ((796312/72619353:ℂ))*h1 +
      ((-1706485/96825804:ℂ)*t)*h1 +
      ((-335/24206451:ℂ)*B)*h1 +
      ((-453805/96825804:ℂ))*h2 +
      ((5273465/580954824:ℂ)*t)*h2 +
      ((1675/145238706:ℂ)*B)*h2 +
      ((-2345/96825804:ℂ)*B*t)*h2 +
      ((-335/24206451:ℂ)*A)*h2 +
      ((2793175/580954824:ℂ))*h3 +
      ((118925/290477412:ℂ)*t)*h3 +
      ((-3685/290477412:ℂ)*B)*h3 +
      ((335/48412902:ℂ)*A)*h3
  norm_num at hh

theorem source_kernel_weight_two_minus (a b : ℂ) (u : Fin 780→ℂ)
    (hu : ∀ i,sourceRows 2 3 (-13) 5 a b u i=0) : ∀ j : Fin 320,u (support j)=0 := by
  by_cases h300 : u 300=0
  · exact source_zero_chart 2 3 (-13) 5 a b (Or.inl (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) u hu h300
  · exfalso
    apply no_weight_two_minus (a*3) (b*5) (u 540/u 300)
    · have hh:=weight_row0 2 3 (-13) 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p0 2 9 (-13) 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p0
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row1 2 3 (-13) 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p1 2 9 (-13) 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p1
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row2 2 3 (-13) 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p2 2 9 (-13) 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p2
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row3 2 3 (-13) 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p3 2 9 (-13) 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p3
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh
    · have hh:=weight_row4 2 3 (-13) 5 a b (by norm_num) (by norm_num) (by norm_num) (by norm_num) u hu
      apply (mul_eq_zero.mp (show p4 2 9 (-13) 25 (a*3) (b*5) (u 540/u 300)*u 300=0 from ?_)).resolve_right h300
      unfold p4
      linear_combination (norm := (field_simp [h300]; all_goals ring)) hh

#print axioms source_kernel_weight_two_minus

end SmallLevelTwentySixUnitMMM.WeightResultants
end
end
