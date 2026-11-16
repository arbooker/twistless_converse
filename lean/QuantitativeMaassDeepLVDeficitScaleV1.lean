module

public import QuantitativeMaassDeepLVScheduleV1
public import QuantitativeMaassLVGeometricLowerV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace QuantitativeMaass.Strong

/-- The actual spherical deficit at twice the deep degree absorbs every
fixed exponential loss on the squared triple-logarithmic scale. -/
theorem deepLV_deficit_decay (p : ℕ) (ε : ℝ→ℝ) (W : ℝ)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)*
      lvSphericalDeficit p (2*deepLVDegree t)/ε t) atTop (𝓝 0) := by
  have hh := (deepLV_inverse_sqrt_decay ε W hε hproduct).const_mul
    (unramifiedDensityBound (p:ℝ)*lvBound p*Real.sqrt Real.pi/Real.sqrt 2)
  simp only [mul_zero] at hh
  convert hh using 1
  funext t
  simp only [lvSphericalDeficit,Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  ring

/-- An exponential cutoff in the deep degree also absorbs all the
squared-triplelog losses. -/
theorem deepLV_cutoff_tail_decay (ε : ℝ→ℝ) (W V : ℝ) (hV : 0≤V)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)/
      (Real.exp (V+(deepLVDegree t:ℝ))*ε t)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (deepLV_inverse_sqrt_decay ε W hε hproduct)
  · filter_upwards [hε] with t he
    positivity
  · filter_upwards [hε] with t he
    have hnp : 0<(deepLVDegree t:ℝ) := by exact_mod_cast deepLVDegree_pos t
    apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
    apply mul_le_mul_of_nonneg_right _ he.le
    have hn : 1≤(deepLVDegree t:ℝ) := by exact_mod_cast deepLVDegree_pos t
    calc
      Real.sqrt (deepLVDegree t:ℝ) ≤ (deepLVDegree t:ℝ) := by
        have hh := Real.sq_sqrt (Nat.cast_nonneg (deepLVDegree t) : (0:ℝ)≤deepLVDegree t)
        have hs := Real.sqrt_nonneg (deepLVDegree t:ℝ)
        nlinarith only [hh,hs,hn]
      _ ≤ Real.exp (V+(deepLVDegree t:ℝ)) := by
        have hh := Real.add_one_le_exp (V+(deepLVDegree t:ℝ))
        linarith

/-- The growing cutoff and growing LV polynomial are compatible with the
square-root geometric trace saving. -/
theorem deepLV_cutoff_geometric_decay (ε : ℝ→ℝ) (C A E V B W : ℝ)
    (hC : 0≤C) (hE : 0<E) (hV : 0≤V)
    (hε : ∀ᶠ t in atTop,0<ε t)
    (hproduct : Tendsto (fun t => ε t*slowScale t) atTop atTop) :
    Tendsto (fun t => Real.exp (W*strongScale t)*C*Real.sqrt t*
      Real.exp (A+30*Real.log (E*(Real.exp (V+(deepLVDegree t:ℝ))+3)^2)+B*(deepLVDegree t:ℝ))/(t*ε t))
      atTop (𝓝 0) := by
  let D := A+30*Real.log E+60*Real.log 4+60*V
  have hm := (deepLV_geometric_decay ε (60+B) W hε hproduct).const_mul (C*Real.exp D)
  simp only [mul_zero] at hm
  apply squeeze_zero' _ _ hm
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    positivity
  · filter_upwards [hε,eventually_gt_atTop (0:ℝ)] with t he ht
    let n := (deepLVDegree t:ℝ)
    have hH : 1≤Real.exp (V+n) := Real.one_le_exp_iff.mpr (by positivity)
    have hlog : Real.log (Real.exp (V+n)+3)≤Real.log 4+V+n := by
      have hh := Real.log_le_log (by positivity : 0<Real.exp (V+n)+3)
        (show Real.exp (V+n)+3≤4*Real.exp (V+n) by linarith only [hH])
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hh
      simpa only [add_assoc] using hh
    have hgeom : Real.exp (A+30*Real.log (E*(Real.exp (V+n)+3)^2)+B*n)≤
        Real.exp D*Real.exp ((60+B)*n) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [Real.log_mul hE.ne' (by positivity),Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      dsimp only [D]
      linarith only [hlog]
    calc
      _ ≤ Real.exp (W*strongScale t)*C*Real.sqrt t*(Real.exp D*Real.exp ((60+B)*n))/(t*ε t) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = _ := by
        dsimp only [n]
        simp only [Real.exp_add]
        ring

#print axioms deepLV_deficit_decay
#print axioms deepLV_cutoff_tail_decay
#print axioms deepLV_cutoff_geometric_decay
end QuantitativeMaass.Strong
