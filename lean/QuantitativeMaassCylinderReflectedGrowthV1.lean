module

public import QuantitativeMaassCylinderReflectedWindowV1
public import QuantitativeMaassReflectionGrowthV1
public import QuantitativeMaassCorrespondenceHeightV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson QuantitativeArithmeticMaassOverlap
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

attribute [local instance] Classical.propDecidable

theorem reflected_correspondence_geometry_uniform_exp (o : ℍ) :
    ∃ C : ℝ,0<C ∧ ∀ L D δ b : ℝ,0≤L → 0≤D → 0≤δ → 0≤b →
      (energyMultiplicity o 0 (D+δ):ℝ)*
        (Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L (D+δ+b)))≤
      C*Real.exp (10*(D+L+δ+b)) := by
  obtain ⟨A,hA,ha⟩ := energyMultiplicity_exp o
  obtain ⟨B,hB,hbound⟩ := reflectedSublevelConstant_exp o
  refine ⟨A*Real.pi*(Real.pi+B),by positivity,?_⟩
  intro L D δ b hL hD hδ hb
  have hDp : 0≤D+δ+b := by positivity
  have he4 : Real.exp (4*(D+δ))≤Real.exp (4*(D+δ+b+L)) := Real.exp_le_exp.mpr (by linarith)
  have heL : Real.exp (4*L)≤Real.exp (6*(D+δ+b+L)) := Real.exp_le_exp.mpr (by linarith)
  have hv := (centre_ball_volume_exp o L).trans (mul_le_mul_of_nonneg_left heL Real.pi_pos.le)
  have hQ := reflectedSublevelConstant_nonneg o L (D+δ+b)
  calc
    _ ≤ (A*Real.exp (4*(D+δ+b+L)))*(Real.pi*((Real.pi+B)*Real.exp (6*(D+δ+b+L)))) := by
      apply mul_le_mul ((ha (D+δ) (by positivity)).trans (mul_le_mul_of_nonneg_left he4 hA.le)) _
        (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      nlinarith [hbound L (D+δ+b) hL hDp]
    _ = (A*Real.pi*(Real.pi+B))*(Real.exp (4*(D+δ+b+L))*Real.exp (6*(D+δ+b+L))) := by ring
    _ = _ := by
      rw [←Real.exp_add]
      congr 1
      congr 1
      ring

/-- The actual reflected cylinder branch error has constants independent of its
integral matrix. Matrix growth is displayed explicitly in the exponent;
no fixed-matrix limit is substituted for the growing-filter estimate. -/
theorem cylinder_window_reflected_branch_uniform_exp (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) (o : ℍ) :
    ∃ U C : ℝ,0<U ∧ 0<C ∧ ∀
      (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (L R ε t : ℝ) (hR : 1≤R),0≤L → 0≤ε → ε≤1 → 1≤t →
      ∀ (a : ℍ→ℂ) (A : ℝ),0≤A →
      (∀ᵐ x ∂volume.restrict (Metric.closedBall o L),‖a x‖≤A) →
      |(∫ x in Metric.closedBall o L,(a x*radialPoincareKernel 0
          (windowSquareProfile K hc R (lt_of_lt_of_le zero_lt_one hR) ε t)
          x (positiveIntegralGL M hM • (J•x))).re)|≤
        A*C*Real.sqrt t*ε^2*Real.exp (U*R+30*L+
          10*dist (positiveIntegralGL M hM • (J•o)) o+20*Real.log (2*integralMatrixHeight M)) := by
  obtain ⟨U,C,hU,hC,hbound⟩ := cylinder_window_reflected_branch_bound K he hc
  obtain ⟨G,hG,hgeom⟩ := reflected_correspondence_geometry_uniform_exp o
  refine ⟨20*U+2,C*G,by positivity,mul_pos hC hG,?_⟩
  intro M hM L R ε t hR hL hε hε1 ht a A hA haB
  have hRp : 0≤R := by linarith
  have hB : 0≤2*Real.log (2*integralMatrixHeight M) := by
    have hh := (integralMatrixHeight_bounds M).1
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hg := hgeom L (2*(U*R)+2*L) (dist (positiveIntegralGL M hM • (J•o)) o)
    (2*Real.log (2*integralMatrixHeight M)) hL (by positivity) dist_nonneg hB
  apply (hbound M hM o L R ε t hR hε hε1 ht a A hA haB).trans
  calc
    _ = (A*C*Real.sqrt t*R^2*ε^2)*
        ((energyMultiplicity o 0 (2*(U*R)+2*L+dist (positiveIntegralGL M hM • (J•o)) o):ℝ)*
          (Real.pi*(volume.real (Metric.closedBall o L)+reflectedSublevelConstant o L
            (2*(U*R)+2*L+dist (positiveIntegralGL M hM • (J•o)) o+2*Real.log (2*integralMatrixHeight M))))) := by ring
    _ ≤ (A*C*Real.sqrt t*R^2*ε^2)*(G*Real.exp
        (10*((2*(U*R)+2*L)+L+dist (positiveIntegralGL M hM • (J•o)) o+
          2*Real.log (2*integralMatrixHeight M)))) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = (A*(C*G)*Real.sqrt t*ε^2)*(R^2*Real.exp ((20*U)*R))*
        Real.exp (30*L+10*dist (positiveIntegralGL M hM • (J•o)) o+
          20*Real.log (2*integralMatrixHeight M)) := by
      rw [show Real.exp (10*((2*(U*R)+2*L)+L+dist (positiveIntegralGL M hM • (J•o)) o+
          2*Real.log (2*integralMatrixHeight M)))=
        Real.exp ((20*U)*R)*Real.exp (30*L+10*dist (positiveIntegralGL M hM • (J•o)) o+
          20*Real.log (2*integralMatrixHeight M)) by rw [←Real.exp_add]; congr 1; ring]
      ring
    _ ≤ (A*(C*G)*Real.sqrt t*ε^2)*Real.exp ((20*U+2)*R)*
        Real.exp (30*L+10*dist (positiveIntegralGL M hM • (J•o)) o+
          20*Real.log (2*integralMatrixHeight M)) := by
      gcongr
      exact radius_square_exp_le (20*U) R hRp
    _ = _ := by
      rw [show Real.exp ((20*U+2)*R+30*L+10*dist (positiveIntegralGL M hM • (J•o)) o+
          20*Real.log (2*integralMatrixHeight M))=
        Real.exp ((20*U+2)*R)*Real.exp (30*L+10*dist (positiveIntegralGL M hM • (J•o)) o+
          20*Real.log (2*integralMatrixHeight M)) by rw [←Real.exp_add]; congr 1; ring]
      ring


/-- Reflection changes only the fixed basepoint constant in the uniform
polynomial height cost. -/
theorem reflected_correspondence_height_cost (o : ℍ) :
    ∃ C : ℝ,0<C ∧ ∀ (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0<M.det)
      (B : ℝ),1≤B → (∀ i j,|(M i j:ℝ)|≤B) →
      Real.exp (10*(dist (positiveIntegralGL M hM•(J•o)) o+2*Real.log (2*B)))≤C*B^40 := by
  obtain ⟨C,hC,hbound⟩ := correspondence_height_cost o
  refine ⟨Real.exp (10*dist (J•o) o)*C,by positivity,?_⟩
  intro M hM B hB hm
  have hg : 0<(positiveIntegralGL M hM).det.val := by
    rw [positiveIntegralGL_det]
    exact_mod_cast hM
  have hd := dist_triangle (positiveIntegralGL M hM•(J•o)) (positiveIntegralGL M hM•o) o
  rw [positiveGL_action_dist _ hg] at hd
  calc
    _ ≤ Real.exp (10*dist (J•o) o)*
        Real.exp (10*(dist (positiveIntegralGL M hM•o) o+2*Real.log (2*B))) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [hd]
    _ ≤ Real.exp (10*dist (J•o) o)*(C*B^40) :=
      mul_le_mul_of_nonneg_left (hbound M hM B hB hm) (Real.exp_pos _).le
    _ = _ := by ring

#print axioms reflected_correspondence_geometry_uniform_exp
#print axioms reflected_correspondence_height_cost
#print axioms cylinder_window_reflected_branch_uniform_exp
end QuantitativeMaass
