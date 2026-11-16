module

public import QuantitativeMaassCountableBasisV1
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace QuantitativeMaass

/-- The scalar complement of the degree-d positive LV filter has a
Gaussian majorant on its normalized spectral interval. -/
theorem lv_scalar_deficit_gaussian (u : ℝ) (_hu0 : 0≤u) (hu1 : u≤1) (d : ℕ) :
    0≤(1-u)^d ∧ (1-u)^d≤Real.exp (-(d:ℝ)*u) := by
  refine ⟨pow_nonneg (by linarith) d,?_⟩
  have h : 1-u≤Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
  have hp := pow_le_pow_left₀ (by linarith : 0≤1-u) h d
  simpa only [←Real.exp_nat_mul,mul_neg,neg_mul] using hp

/-- A bounded continuous density on [-2,2] gives a uniform inverse-square-root
LV deficit, including when the center is an endpoint. -/
theorem bounded_density_lv_deficit (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc (-2:ℝ) 2)) (C : ℝ) (hC : 0≤C)
    (hwb : ∀ x∈Icc (-2:ℝ) 2,0≤w x ∧ w x≤C)
    (a B : ℝ) (ha : a∈Icc (-2:ℝ) 2) (hB : 4≤B) (d : ℕ) (hd : 0<d) :
    0≤(∫ x in Icc (-2:ℝ) 2,w x*(1-(x-a)^2/B^2)^d) ∧
    (∫ x in Icc (-2:ℝ) 2,w x*(1-(x-a)^2/B^2)^d)≤
      C*B*Real.sqrt Real.pi/Real.sqrt (d:ℝ) := by
  have hBp : 0<B := by linarith
  have hdp : (0:ℝ)<d := by exact_mod_cast hd
  have hq (x : ℝ) (hx : x∈Icc (-2:ℝ) 2) :
      0≤(x-a)^2/B^2 ∧ (x-a)^2/B^2≤1 := by
    refine ⟨div_nonneg (sq_nonneg _) (sq_nonneg _),?_⟩
    apply (div_le_one (sq_pos_of_pos hBp)).mpr
    nlinarith [hx.1,hx.2,ha.1,ha.2,sq_nonneg (B-4)]
  have hnonneg (x : ℝ) (hx : x∈Icc (-2:ℝ) 2) :
      0≤w x*(1-(x-a)^2/B^2)^d :=
    mul_nonneg (hwb x hx).1 (lv_scalar_deficit_gaussian _ (hq x hx).1 (hq x hx).2 d).1
  have hf : IntegrableOn (fun x => w x*(1-(x-a)^2/B^2)^d) (Icc (-2:ℝ) 2) :=
    (hw.mul (show ContinuousOn (fun x : ℝ => (1-(x-a)^2/B^2)^d) (Icc (-2:ℝ) 2) by fun_prop)).integrableOn_Icc
  have hg : Integrable (fun x : ℝ => C*Real.exp (-((d:ℝ)/B^2)*(x-a)^2)) :=
    ((integrable_exp_neg_mul_sq (by positivity : 0<(d:ℝ)/B^2)).comp_sub_right a).const_mul C
  refine ⟨setIntegral_nonneg measurableSet_Icc hnonneg,?_⟩
  calc
    _ ≤ ∫ x in Icc (-2:ℝ) 2,C*Real.exp (-((d:ℝ)/B^2)*(x-a)^2) := by
      apply setIntegral_mono_on hf hg.integrableOn measurableSet_Icc
      intro x hx
      have hp := (lv_scalar_deficit_gaussian _ (hq x hx).1 (hq x hx).2 d).2
      have he : -(d:ℝ)*((x-a)^2/B^2)=-((d:ℝ)/B^2)*(x-a)^2 := by ring
      rw [he] at hp
      exact mul_le_mul (hwb x hx).2 hp
        (lv_scalar_deficit_gaussian _ (hq x hx).1 (hq x hx).2 d).1 hC
    _ ≤ ∫ x : ℝ,C*Real.exp (-((d:ℝ)/B^2)*(x-a)^2) :=
      setIntegral_le_integral hg (Filter.Eventually.of_forall (fun _ => mul_nonneg hC (Real.exp_nonneg _)))
    _ = C*Real.sqrt (Real.pi/((d:ℝ)/B^2)) := by
      rw [integral_const_mul,integral_sub_right_eq_self (fun x : ℝ => Real.exp (-((d:ℝ)/B^2)*x^2)) a,
        integral_gaussian]
    _ = _ := by
      rw [show Real.pi/((d:ℝ)/B^2)=B^2*(Real.pi/(d:ℝ)) by field_simp,
        Real.sqrt_mul (sq_nonneg B),Real.sqrt_sq_eq_abs,abs_of_pos hBp,Real.sqrt_div Real.pi_pos.le]
      ring

/-- The spherical radius of normalized adjacency on the (p+1)-regular tree. -/
def unramifiedRadius (p : ℝ) : ℝ := (p+1)/Real.sqrt p

/-- The explicit unramified Plancherel density. Identification with the
actual tree spectral measure is a separate theorem, not assumed here. -/
def unramifiedDensity (p x : ℝ) : ℝ :=
  ((p+1)/(2*Real.pi))*Real.sqrt (4-x^2)/(unramifiedRadius p^2-x^2)

def unramifiedDensityBound (p : ℝ) : ℝ :=
  (p+1)/(Real.pi*(unramifiedRadius p^2-4))

theorem unramifiedRadius_gt_two (p : ℝ) (hp : 1<p) : 2<unramifiedRadius p := by
  have hp0 : 0<p := by linarith
  have hr := Real.sq_sqrt hp0.le
  have hs : 1<Real.sqrt p := by nlinarith [Real.sqrt_nonneg p]
  unfold unramifiedRadius
  apply (lt_div_iff₀ (Real.sqrt_pos.mpr hp0)).mpr
  nlinarith [sq_pos_of_pos (sub_pos.mpr hs)]

theorem unramifiedDensity_bounds (p : ℝ) (hp : 1<p) :
    0<unramifiedDensityBound p ∧
    ∀ x∈Icc (-2:ℝ) 2,0≤unramifiedDensity p x ∧
      unramifiedDensity p x≤unramifiedDensityBound p := by
  have hp0 : 0<p := by linarith
  have hA := unramifiedRadius_gt_two p hp
  have hfloor : 0<unramifiedRadius p^2-4 := by nlinarith
  have hC : 0<unramifiedDensityBound p := by
    unfold unramifiedDensityBound
    positivity
  refine ⟨hC,?_⟩
  intro x hx
  have hx2 : x^2≤4 := by nlinarith [hx.1,hx.2]
  have hden : 0<unramifiedRadius p^2-x^2 := by linarith
  have hs : Real.sqrt (4-x^2)≤2 := by
    have h := Real.sq_sqrt (by linarith : 0≤4-x^2)
    nlinarith [Real.sqrt_nonneg (4-x^2),sq_nonneg x]
  have hn : 0≤(p+1)/(2*Real.pi) := by positivity
  constructor
  · unfold unramifiedDensity
    positivity
  · calc
      _ ≤ ((p+1)/(2*Real.pi))*2/(unramifiedRadius p^2-x^2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hn) hden.le
      _ ≤ ((p+1)/(2*Real.pi))*2/(unramifiedRadius p^2-4) :=
        div_le_div_of_nonneg_left (by positivity) hfloor (by linarith)
      _ = _ := by
        unfold unramifiedDensityBound
        field_simp [Real.pi_ne_zero,hfloor.ne']

theorem unramifiedDensity_continuousOn (p : ℝ) (hp : 1<p) :
    ContinuousOn (unramifiedDensity p) (Icc (-2:ℝ) 2) := by
  have hA := unramifiedRadius_gt_two p hp
  unfold unramifiedDensity
  apply ContinuousOn.div (by fun_prop)
    (show ContinuousOn (fun x : ℝ => unramifiedRadius p^2-x^2) (Icc (-2:ℝ) 2) by fun_prop)
  intro x hx
  have hx2 : x^2≤4 := by nlinarith [hx.1,hx.2]
  nlinarith

/-- Explicit quantitative finite-place LV deficit, uniform over the entire
spherical interval and all positive filter degrees. No density or rate premise. -/
theorem unramified_lv_deficit (p : ℝ) (hp : 1<p) (a B : ℝ)
    (ha : a∈Icc (-2:ℝ) 2) (hB : 4≤B) (d : ℕ) (hd : 0<d) :
    0≤(∫ x in Icc (-2:ℝ) 2,unramifiedDensity p x*(1-(x-a)^2/B^2)^d) ∧
    (∫ x in Icc (-2:ℝ) 2,unramifiedDensity p x*(1-(x-a)^2/B^2)^d)≤
      unramifiedDensityBound p*B*Real.sqrt Real.pi/Real.sqrt (d:ℝ) :=
  bounded_density_lv_deficit _ (unramifiedDensity_continuousOn p hp) _
    (unramifiedDensity_bounds p hp).1.le (unramifiedDensity_bounds p hp).2 a B ha hB d hd

/-- The normalization of the literal LV operator covers the spherical
interval uniformly, with the exceptional wave norm already included. -/
theorem lvBound_gt_four (p : ℕ) [Fact p.Prime] : 4<lvBound p := by
  have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hA := unramifiedRadius_gt_two (p:ℝ) hp
  have he : lvBound p=unramifiedRadius (p:ℝ)+2*Real.cosh (|Real.log p|/2) := by
    simp only [lvBound,unramifiedRadius,Nat.cast_add,Nat.cast_one]
  rw [he]
  linarith [Real.one_le_cosh (|Real.log p|/2)]

/-- Uniform finite-place deficit with the EXACT radius and center of the
actual LV operator, rather than an independently chosen model normalization. -/
theorem actual_lv_normalization_deficit (p : ℕ) [Fact p.Prime] (r : ℝ)
    (d : ℕ) (hd : 0<d) :
    0≤(∫ x in Icc (-2:ℝ) 2,unramifiedDensity (p:ℝ) x*
      (1-(x-2*Real.cos (r*Real.log p))^2/(lvBound p)^2)^d) ∧
    (∫ x in Icc (-2:ℝ) 2,unramifiedDensity (p:ℝ) x*
      (1-(x-2*Real.cos (r*Real.log p))^2/(lvBound p)^2)^d)≤
      unramifiedDensityBound (p:ℝ)*lvBound p*Real.sqrt Real.pi/Real.sqrt (d:ℝ) := by
  have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  apply unramified_lv_deficit (p:ℝ) hp _ _ _ (lvBound_gt_four p).le d hd
  constructor <;> linarith [Real.neg_one_le_cos (r*Real.log p),Real.cos_le_one (r*Real.log p)]

#print axioms lv_scalar_deficit_gaussian
#print axioms bounded_density_lv_deficit
#print axioms unramifiedRadius_gt_two
#print axioms unramifiedDensity_bounds
#print axioms unramifiedDensity_continuousOn
#print axioms unramified_lv_deficit

#print axioms lvBound_gt_four
#print axioms actual_lv_normalization_deficit

end QuantitativeMaass
