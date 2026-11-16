module
public import QuantitativeMaassHeckeTreeCosetsV1
public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Tactic
public import QuantitativeMaassTreeOperatorV1
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import QuantitativeMaassLVUniformDeficitV1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
@[expose] public noncomputable section

/-! Exact regular-tree Plancherel moments: Poisson formula, radial recurrence,
arcsine substitution and the explicit unramified density. -/

open Complex Metric Set Real
namespace QuantitativeArithmeticTreePlancherel

/-- A Poisson-weighted continuous function is integrable on the unit circle. -/
theorem poisson_circleIntegrable (w : ℂ) (hw : ‖w‖ < 1)
    (f : ℂ → ℂ) (hf : Continuous f) :
    CircleIntegrable (fun z => poissonKernel 0 w z • f z) 0 1 := by
  have hn : w ∉ sphere (0 : ℂ) |(1 : ℝ)| := by
    simpa only [abs_one, mem_sphere, dist_zero_right] using ne_of_lt hw
  have hc : ContinuousOn (poissonKernel 0 w) (sphere 0 |(1 : ℝ)|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hn)
  exact (hc.smul hf.continuousOn).circleIntegrable'

/-- The polynomial version of the Poisson formula, with no moment assumption. -/
theorem poisson_power_difference (w : ℂ) (hw : ‖w‖ < 1) (n : ℕ) :
    circleAverage (fun z => poissonKernel 0 w z • (z^n-z^(n+2))) 0 1 =
      w^n-w^(n+2) := by
  have hf : Differentiable ℂ (fun z : ℂ => z^n-z^(n+2)) := by fun_prop
  exact hf.diffContOnCl.circleAverage_poissonKernel_smul
    (by simpa only [mem_ball, dist_zero_right] using hw)

/-- The symmetric Poisson expression for a Chebyshev moment of the
unramified root distribution. Its identification with the density integral
and the actual tree operator are proved separately. -/
def poissonMoment (r : ℝ) (n : ℕ) : ℂ :=
  circleAverage (fun z => (2*(1-(r : ℂ)^2))⁻¹ •
    ((poissonKernel 0 (r : ℂ) z + poissonKernel 0 (-r : ℂ) z) •
      (z^n-z^(n+2)))) 0 1

theorem poissonMoment_eq (r : ℝ) (hr : |r| < 1) (n : ℕ) :
    poissonMoment r n = ((r : ℂ)^n+(-r : ℂ)^n)/2 := by
  have hp : ‖(r : ℂ)‖ < 1 := by simpa using hr
  have hm : ‖(-r : ℂ)‖ < 1 := by simpa using hp
  have hden : (1-(r : ℂ)^2) ≠ 0 := by
    have hsq : r^2 < 1 := by nlinarith [abs_lt.mp hr]
    exact_mod_cast (sub_pos.mpr hsq).ne'
  unfold poissonMoment
  rw [circleAverage_fun_smul]
  simp_rw [add_smul]
  rw [circleAverage_fun_add
    (poisson_circleIntegrable _ hp _ (by fun_prop))
    (poisson_circleIntegrable _ hm _ (by fun_prop)),
    poisson_power_difference _ hp, poisson_power_difference _ hm]
  simp only [smul_eq_mul, pow_add, pow_two]
  field_simp

theorem poissonMoment_even (r : ℝ) (hr : |r| < 1) (m : ℕ) :
    poissonMoment r (2*m) = (r : ℂ)^(2*m) := by
  rw [poissonMoment_eq r hr]
  simp [pow_mul]

theorem poissonMoment_odd (r : ℝ) (hr : |r| < 1) (m : ℕ) :
    poissonMoment r (2*m+1) = 0 := by
  rw [poissonMoment_eq r hr]
  simp [pow_add, pow_mul]

/-- The elementary boundary identity turning the Poisson moments into
Chebyshev moments; it holds at the endpoints as well. -/
theorem chebyshev_boundary (θ : ℝ) (n : ℤ) :
    2*(Real.sin θ)^2*(Polynomial.Chebyshev.U ℝ n).eval (Real.cos θ) =
      Real.cos (n*θ)-Real.cos ((n+2)*θ) := by
  have hU := Polynomial.Chebyshev.U_real_cos θ n
  have hminus := Real.cos_sub (((n : ℝ)+1)*θ) θ
  have hplus := Real.cos_add (((n : ℝ)+1)*θ) θ
  rw [show ((n : ℝ)+1)*θ-θ=(n : ℝ)*θ by ring] at hminus
  rw [show ((n : ℝ)+1)*θ+θ=((n : ℝ)+2)*θ by ring] at hplus
  rw [hminus,hplus]
  linear_combination 2*Real.sin θ*hU

/-- The Poisson kernel on the unit circle, expressed in its real coordinate. -/
theorem poissonKernel_unit_real (r : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    poissonKernel 0 (r : ℂ) z = (1-r^2)/(1+r^2-2*r*z.re) := by
  have hzsq : z.re^2+z.im^2=1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simpa only [Complex.normSq_apply,pow_two,mul_one] using h
  have hd : ‖z-(r : ℂ)‖^2=1+r^2-2*r*z.re := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.ofReal_re,Complex.ofReal_im,sub_zero]
    nlinarith
  simp only [poissonKernel_def,sub_zero,Complex.norm_real,Real.norm_eq_abs,sq_abs,hz,hd]
  norm_num

/-- Rational form of the positive symmetric boundary weight. This is the
unramified Plancherel weight after the substitution x=2 cos(theta). -/
theorem symmetric_poisson_weight (r : ℝ) (hr0 : 0≤r) (hr1 : r<1)
    (z : ℂ) (hz : ‖z‖=1) :
    (poissonKernel 0 (r : ℂ) z + poissonKernel 0 (-r : ℂ) z)*
      (1-z.re^2)/(1-r^2) =
      2*(1+r^2)*(1-z.re^2)/((1+r^2)^2-4*r^2*z.re^2) := by
  have hx := Complex.abs_re_le_norm z
  rw [hz,abs_le] at hx
  have hbase : 0<(1-r)^2 := sq_pos_of_pos (by linarith)
  have ha : 0<1+r^2-2*r*z.re := by nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hx.2)]
  have hb : 0<1+r^2+2*r*z.re := by nlinarith [mul_nonneg hr0 (by linarith [hx.1] : 0≤z.re+1)]
  have hc : 1-r^2 ≠ 0 := by nlinarith
  have hd : (1+r^2)^2-4*r^2*z.re^2 ≠ 0 := by
    have he : (1+r^2)^2-4*r^2*z.re^2=(1+r^2-2*r*z.re)*(1+r^2+2*r*z.re) := by ring
    rw [he]
    exact mul_ne_zero ha.ne' hb.ne'
  rw [poissonKernel_unit_real r z hz,show (-r : ℂ)=((-r : ℝ) : ℂ) by simp,
    poissonKernel_unit_real (-r) z hz]
  rw [show 1+(-r)^2-2*(-r)*z.re=1+r^2+2*r*z.re by ring]
  simp only [neg_sq]
  rw [div_add_div _ _ ha.ne' hb.ne']
  apply (div_eq_div_iff hc hd).2
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
  apply (div_eq_iff (mul_ne_zero ha.ne' hb.ne')).2
  ring

#print axioms poisson_power_difference
#print axioms poissonMoment_eq
#print axioms poissonMoment_even
#print axioms poissonMoment_odd
#print axioms chebyshev_boundary
#print axioms poissonKernel_unit_real
#print axioms symmetric_poisson_weight
end QuantitativeArithmeticTreePlancherel


open QuantitativeMaass
open scoped lp
namespace QuantitativeArithmeticTreePlancherel

/-- The exact finite radial kernel of the monic Chebyshev polynomial. -/
def radialIndicator (n k : ℕ) : ℂ :=
  if k ≤ n ∧ k % 2 = n % 2 then 1 else 0

theorem radialIndicator_root_recurrence (p n : ℕ) :
    ((p+1 : ℕ) : ℂ)*radialIndicator (n+1) 1 -
      (p : ℂ)*radialIndicator n 0 = radialIndicator (n+2) 0 := by
  unfold radialIndicator
  simp only [Nat.cast_add,Nat.cast_one]
  split_ifs <;> first | omega | ring

theorem radialIndicator_branch_recurrence (p n k : ℕ) :
    radialIndicator (n+1) k + (p : ℂ)*radialIndicator (n+1) (k+2) -
      (p : ℂ)*radialIndicator n (k+1) = radialIndicator (n+2) (k+1) := by
  unfold radialIndicator
  split_ifs <;> first | omega | ring

/-- Monic Chebyshev polynomials applied to the actual regular-tree adjacency.
For p>0 this is p^(n/2) U_n(A/(2 sqrt(p))). -/
def treeMonicChebyshev (p : ℕ) : ℕ →
    (ℓ²(TreeWord (Fin (p+1)), ℂ) →L[ℂ] ℓ²(TreeWord (Fin (p+1)), ℂ))
  | 0 => 1
  | 1 => treeAdjacency
  | n+2 => treeAdjacency * treeMonicChebyshev p (n+1) -
      (p : ℂ) • treeMonicChebyshev p n

/-- The exact rooted Chebyshev kernel, proved from adjacency on the tree. -/
theorem treeMonicChebyshev_apply_root (p n : ℕ) (v : TreeWord (Fin (p+1))) :
    treeMonicChebyshev p n treeRootVector v = radialIndicator n v.val.length := by
  induction n using Nat.twoStepInduction generalizing v with
  | zero =>
    change treeRootVector v = _
    rcases v with ⟨w,hw⟩
    cases w with
    | nil => simp [treeRootVector,TreeWord.root,radialIndicator]
    | cons a w =>
      have hn : (⟨a::w,hw⟩ : TreeWord (Fin (p+1))) ≠ TreeWord.root := by
        intro h
        have := congrArg Subtype.val h
        simp [TreeWord.root] at this
      simp [treeRootVector,Pi.single_eq_of_ne hn,radialIndicator]
  | one =>
    have h := treeAdjacency_power_root (α := Fin (p+1)) 1 v
    rw [pow_one] at h
    change treeAdjacency treeRootVector v = _
    rw [h]
    cases hk : v.val.length with
    | zero => simp [treeWalkCount,radialIndicator]
    | succ k =>
      cases k with
      | zero => simp [treeWalkCount,radialIndicator]
      | succ k => simp [treeWalkCount,radialIndicator]
  | more n ih₀ ih₁ =>
    change (treeAdjacency (treeMonicChebyshev p (n+1) treeRootVector)) v -
      (p : ℂ)*(treeMonicChebyshev p n treeRootVector v) = _
    rw [treeAdjacency_apply,ih₀]
    simp_rw [ih₁]
    rcases v with ⟨w,hw⟩
    cases w with
    | nil =>
      rw [show (⟨[],hw⟩ : TreeWord (Fin (p+1))) = TreeWord.root from rfl,
        tree_radial_sum_root]
      simpa only [Fintype.card_fin,TreeWord.root,List.length_nil] using
        radialIndicator_root_recurrence p n
    | cons a w =>
      rw [tree_radial_sum_cons]
      simpa only [Fintype.card_fin,Nat.add_sub_cancel,List.length_cons] using
        radialIndicator_branch_recurrence p n w.length

theorem treeMonicChebyshev_root_even (p m : ℕ) :
    treeMonicChebyshev p (2*m) treeRootVector TreeWord.root = 1 := by
  rw [treeMonicChebyshev_apply_root]
  simp [radialIndicator,TreeWord.root]

theorem treeMonicChebyshev_root_odd (p m : ℕ) :
    treeMonicChebyshev p (2*m+1) treeRootVector TreeWord.root = 0 := by
  rw [treeMonicChebyshev_apply_root]
  simp [radialIndicator,TreeWord.root]

/-- The actual rooted tree calculation agrees with the independently
computed Poisson moments after the Chebyshev normalization. -/
theorem tree_poisson_moments (p n : ℕ) (r : ℝ) (hr : |r|<1) :
    (r : ℂ)^n * (treeMonicChebyshev p n treeRootVector TreeWord.root) =
      poissonMoment r n := by
  by_cases hn : n%2=0
  · have he : n=2*(n/2) := by omega
    rw [he,treeMonicChebyshev_root_even,poissonMoment_even r hr,mul_one]
  · have he : n=2*(n/2)+1 := by omega
    rw [he,treeMonicChebyshev_root_odd,poissonMoment_odd r hr,mul_zero]

/-- The operator sequence is precisely the standard monic Chebyshev
polynomial S_n evaluated at normalized adjacency when p*r^2=1. -/
theorem aeval_S_tree (p n : ℕ) (r : ℂ) (hr : r^2*(p : ℂ)=1) :
    Polynomial.aeval (r • treeAdjacency (α := Fin (p+1)))
      (Polynomial.Chebyshev.S ℂ (n : ℤ)) = r^n • treeMonicChebyshev p n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Polynomial.Chebyshev.S_zero,treeMonicChebyshev]
  | one => simp [Polynomial.Chebyshev.S_one,treeMonicChebyshev]
  | more n ih₀ ih₁ =>
    rw [show ((n+2 : ℕ) : ℤ)=(n : ℤ)+2 by omega,
      Polynomial.Chebyshev.S_add_two]
    simp only [map_sub,map_mul,Polynomial.aeval_X]
    rw [← show ((n+1 : ℕ) : ℤ)=(n : ℤ)+1 by omega,ih₁,ih₀]
    have hmul : (r • treeAdjacency (α := Fin (p+1))) *
        (r^(n+1) • treeMonicChebyshev p (n+1)) =
        (r*r^(n+1)) • (treeAdjacency * treeMonicChebyshev p (n+1)) := by
      change (r • treeAdjacency).comp (r^(n+1) • treeMonicChebyshev p (n+1)) = _
      rw [ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,smul_smul]
      rfl
    rw [hmul,treeMonicChebyshev]
    simp only [smul_sub,smul_smul]
    have hc : r^(n+2)*(p : ℂ)=r^n := by
      rw [pow_add,mul_assoc,hr,mul_one]
    rw [hc]
    congr 2
    ring

/-- Standard normalized adjacency has exactly the computed Poisson
Chebyshev moments. The only level parameter condition here is p>1. -/
theorem normalized_tree_poisson_moments (p n : ℕ) (hp : 1<p) :
    (Polynomial.aeval
      (((Real.sqrt (p : ℝ))⁻¹ : ℝ) • treeAdjacency (α := Fin (p+1)))
      (Polynomial.Chebyshev.S ℂ (n : ℤ))) treeRootVector TreeWord.root =
      poissonMoment (Real.sqrt (p : ℝ))⁻¹ n := by
  have hpR : (1 : ℝ)<p := by exact_mod_cast hp
  have hs0 : 0<Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have he : Real.sqrt (p : ℝ)^2=(p : ℝ) := Real.sq_sqrt (by positivity)
  have hs : 1<Real.sqrt (p : ℝ) := by nlinarith
  have hr : (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ)^2*(p : ℂ)=1 := by
    norm_cast
    rw [inv_pow,he,inv_mul_cancel₀ (by positivity : (p : ℝ)≠0)]
  have hb : |(Real.sqrt (p : ℝ))⁻¹|<1 := by
    rw [abs_of_pos (inv_pos.mpr hs0)]
    exact inv_lt_one_of_one_lt₀ hs
  have hscalar : ((Real.sqrt (p : ℝ))⁻¹ : ℝ) • treeAdjacency (α := Fin (p+1)) =
      ((((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) • treeAdjacency (α := Fin (p+1))) := by
    ext f v
    simp [Complex.real_smul]
  rw [hscalar,aeval_S_tree p n _ hr]
  change (Complex.ofReal ((Real.sqrt (p : ℝ))⁻¹))^n *
    (treeMonicChebyshev p n treeRootVector TreeWord.root) = _
  exact tree_poisson_moments p n _ hb

#print axioms treeMonicChebyshev_apply_root
#print axioms treeMonicChebyshev_root_even
#print axioms treeMonicChebyshev_root_odd
#print axioms tree_poisson_moments
#print axioms aeval_S_tree
#print axioms normalized_tree_poisson_moments
end QuantitativeArithmeticTreePlancherel

open Complex Real Set MeasureTheory Metric
namespace QuantitativeArithmeticTreePlancherel

/-- Real-coordinate functions on the unit circle have the arcsine integral.
This change of variables is the bridge from Poisson to an explicit density. -/
theorem circleAverage_real_coordinate (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc (-1) 1)) :
    circleAverage (fun z : ℂ => g z.re) 0 1 =
      (Real.pi)⁻¹ * ∫ x, g x ∂Polynomial.Chebyshev.measureT := by
  have hc : Continuous (fun θ : ℝ => g (Real.cos θ)) := by
    rw [← continuousOn_univ]
    exact hg.comp Real.continuous_cos.continuousOn
      (fun θ _ => ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩)
  have hreflect : (∫ θ in Real.pi..2*Real.pi,g (Real.cos θ)) =
      ∫ θ in 0..Real.pi,g (Real.cos θ) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => g (Real.cos θ)) (a := Real.pi) (b := 2*Real.pi) (2*Real.pi)
    simpa only [Real.cos_two_pi_sub,sub_self,
      show 2*Real.pi-Real.pi=Real.pi by ring] using h
  rw [circleAverage_def,Polynomial.Chebyshev.integral_measureT_eq_integral_cos]
  have hmap (θ : ℝ) : (circleMap 0 1 θ).re=Real.cos θ := by
    simp [circleMap]
  simp_rw [hmap]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 Real.pi) (hc.intervalIntegrable Real.pi (2*Real.pi)),hreflect]
  simp only [smul_eq_mul]
  ring

/-- The regular-tree root density in the parameter r=1/sqrt(p). -/
def rootDensity (r x : ℝ) : ℝ :=
  (1+r^2)/(2*Real.pi)*Real.sqrt (4-x^2)/((1+r^2)^2-r^2*x^2)

def rootBoundaryWeight (r u : ℝ) : ℝ :=
  2*(1+r^2)*(1-u^2)/((1+r^2)^2-4*r^2*u^2)

theorem rootBoundary_den_pos (r u : ℝ) (hr0 : 0≤r) (hr1 : r<1)
    (hu : u∈Icc (-1) 1) : 0<(1+r^2)^2-4*r^2*u^2 := by
  have hr : 0<1-r^2 := by nlinarith
  have hu' : 0≤1-u^2 := by nlinarith [hu.1,hu.2]
  nlinarith [sq_pos_of_pos hr,mul_nonneg (sq_nonneg r) hu']

theorem rootBoundary_continuousOn (r : ℝ) (hr0 : 0≤r) (hr1 : r<1) :
    ContinuousOn (rootBoundaryWeight r) (Icc (-1) 1) := by
  unfold rootBoundaryWeight
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  exact (rootBoundary_den_pos r x hr0 hr1 hx).ne'

/-- Pointwise Jacobian identity, including both endpoints. -/
theorem rootDensity_arcsine_weight (r u : ℝ) (hr0 : 0≤r) (hr1 : r<1)
    (hu : u∈Icc (-1) 1) :
    rootBoundaryWeight r u =
      2*Real.pi*rootDensity r (2*u)*Real.sqrt (1-u^2) := by
  have hu' : 0≤1-u^2 := by nlinarith [hu.1,hu.2]
  have hs : Real.sqrt (4-(2*u)^2)=2*Real.sqrt (1-u^2) := by
    rw [show 4-(2*u)^2=4*(1-u^2) by ring,Real.sqrt_mul (by norm_num)]
    norm_num
  have hd := (rootBoundary_den_pos r u hr0 hr1 hu).ne'
  unfold rootBoundaryWeight rootDensity
  rw [hs,show (1+r^2)^2-r^2*(2*u)^2=(1+r^2)^2-4*r^2*u^2 by ring]
  field_simp
  rw [Real.sq_sqrt hu']

/-- The explicit density integral is the corresponding arcsine integral.
No integrability or moment identity is assumed in this substitution. -/
theorem rootDensity_integral (r : ℝ) (hr0 : 0≤r) (hr1 : r<1) (f : ℝ → ℝ) :
    (∫ x in -2..2,rootDensity r x*f x) =
      Real.pi⁻¹ * ∫ u,rootBoundaryWeight r u*f (2*u)
        ∂Polynomial.Chebyshev.measureT := by
  have hscale : (∫ x in -2..2,rootDensity r x*f x) =
      ∫ u in -1..1,2*(rootDensity r (2*u)*f (2*u)) := by
    rw [intervalIntegral.integral_const_mul]
    simpa only [smul_eq_mul,mul_neg_one,mul_one] using
      (intervalIntegral.smul_integral_comp_mul_left
        (fun x : ℝ => rootDensity r x*f x) (a := -1) (b := 1) 2).symm
  rw [hscale,Polynomial.Chebyshev.integral_measureT,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only
  have hu' : u∈Icc (-1 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ)≤1)] using hu
  rw [rootDensity_arcsine_weight r u hr0 hr1 hu']
  by_cases hz : Real.sqrt (1-u^2)=0
  · have hu0 : 1-u^2=0 := by
      have h := Real.sq_sqrt (show 0≤1-u^2 by nlinarith [hu'.1,hu'.2])
      rw [hz] at h
      nlinarith
    have he : 4-(2*u)^2=0 := by nlinarith
    simp [rootDensity,he]
  · rw [Real.sqrt_inv]
    symm
    calc
      _ = (Real.pi⁻¹*Real.pi)*
          (Real.sqrt (1-u^2)*(Real.sqrt (1-u^2))⁻¹)*
          (2*(rootDensity r (2*u)*f (2*u))) := by ring
      _ = _ := by rw [inv_mul_cancel₀ Real.pi_ne_zero,mul_inv_cancel₀ hz,one_mul,one_mul]

theorem circleMap_power_re (θ : ℝ) (n : ℕ) :
    ((circleMap 0 1 θ)^n).re=Real.cos ((n : ℝ)*θ) := by
  simp [circleMap,← Complex.exp_nat_mul,Complex.exp_re]

theorem unit_chebyshev_boundary (z : ℂ) (hz : ‖z‖=1) (n : ℕ) :
    2*(1-z.re^2)*(Polynomial.Chebyshev.U ℝ (n : ℤ)).eval z.re =
      (z^n-z^(n+2)).re := by
  have hz' : z ∈ sphere (0 : ℂ) |(1 : ℝ)| := by
    simpa only [Metric.mem_sphere,dist_zero_right,abs_one] using hz
  rw [← range_circleMap] at hz'
  obtain ⟨θ,rfl⟩ := hz'
  have hmap : (circleMap 0 1 θ).re=Real.cos θ := by simp [circleMap]
  simp only [hmap,Complex.sub_re,circleMap_power_re]
  have h := chebyshev_boundary θ (n : ℤ)
  have hs := Real.sin_sq_add_cos_sq θ
  norm_num only [Int.cast_natCast,Int.cast_add,Int.cast_ofNat,Nat.cast_add,Nat.cast_ofNat] at h ⊢
  linear_combination h - 2*(Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos θ)*hs

/-- Identification of the computed Poisson moments with a real arcsine
integral; the rational boundary weight is explicit. -/
theorem poissonMoment_re_eq_arcsine (r : ℝ) (hr0 : 0≤r) (hr1 : r<1) (n : ℕ) :
    (poissonMoment r n).re = Real.pi⁻¹ *
      ∫ u,rootBoundaryWeight r u*(Polynomial.Chebyshev.U ℝ (n : ℤ)).eval u
        ∂Polynomial.Chebyshev.measureT := by
  have hr : |r|<1 := by rwa [abs_of_nonneg hr0]
  have hp : ‖(r : ℂ)‖<1 := by simpa using hr
  have hm : ‖(-r : ℂ)‖<1 := by simpa using hp
  let F : ℂ → ℂ := fun z => z^n-z^(n+2)
  have hF : Continuous F := by fun_prop
  have hi : CircleIntegrable (fun z =>
      (poissonKernel 0 (r : ℂ) z+poissonKernel 0 (-r : ℂ) z) • F z) 0 1 := by
    have h := (poisson_circleIntegrable _ hp F hF).add
      (poisson_circleIntegrable _ hm F hF)
    change CircleIntegrable (fun z => poissonKernel 0 (r : ℂ) z • F z +
      poissonKernel 0 (-r : ℂ) z • F z) 0 1 at h
    simpa only [add_smul] using h
  have hi' := hi.const_smul (a := (2*(1-(r : ℂ)^2))⁻¹)
  have hcont : ContinuousOn (fun u : ℝ => rootBoundaryWeight r u*
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval u) (Icc (-1) 1) :=
    (rootBoundary_continuousOn r hr0 hr1).mul (by fun_prop)
  rw [← circleAverage_real_coordinate (fun u : ℝ => rootBoundaryWeight r u*
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval u) hcont]
  change Complex.reCLM (circleAverage
    ((2*(1-(r : ℂ)^2))⁻¹ • (fun z =>
      (poissonKernel 0 (r : ℂ) z+poissonKernel 0 (-r : ℂ) z) • F z)) 0 1) = _
  rw [← Complex.reCLM.circleAverage_comp_comm hi']
  apply circleAverage_congr_sphere
  intro z hz
  have hz' : ‖z‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right,abs_one] using hz
  have hc : (2*(1-(r : ℂ)^2))⁻¹ = (((2*(1-r^2))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have hd : 1-r^2≠0 := by nlinarith
  have hw := symmetric_poisson_weight r hr0 hr1 z hz'
  change (poissonKernel 0 (r : ℂ) z+poissonKernel 0 (-r : ℂ) z)*
    (1-z.re^2)/(1-r^2)=rootBoundaryWeight r z.re at hw
  change (((2*(1-(r : ℂ)^2))⁻¹) *
    ((↑(poissonKernel 0 (r : ℂ) z+poissonKernel 0 (-r : ℂ) z) : ℂ)*
      (z^n-z^(n+2)))).re = _
  rw [hc]
  simp only [Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  rw [← unit_chebyshev_boundary z hz' n,← hw]
  field_simp

/-- Exact Chebyshev moments of the explicit root density. -/
theorem rootDensity_chebyshev_moment (r : ℝ) (hr0 : 0≤r) (hr1 : r<1) (n : ℕ) :
    (∫ x in -2..2,rootDensity r x*(Polynomial.Chebyshev.S ℝ (n : ℤ)).eval x) =
      (poissonMoment r n).re := by
  rw [rootDensity_integral r hr0 hr1,poissonMoment_re_eq_arcsine r hr0 hr1]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  congr 1
  have h := congrArg (Polynomial.eval u)
    (Polynomial.Chebyshev.S_comp_two_mul_X ℝ (n : ℤ))
  simpa only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X] using h

theorem rootDensity_mass_one (r : ℝ) (hr0 : 0≤r) (hr1 : r<1) :
    (∫ x in -2..2,rootDensity r x)=1 := by
  have hr : |r|<1 := by rwa [abs_of_nonneg hr0]
  have h := rootDensity_chebyshev_moment r hr0 hr1 0
  simpa [Polynomial.Chebyshev.S_zero,poissonMoment_eq r hr] using h

#print axioms circleMap_power_re
#print axioms unit_chebyshev_boundary
#print axioms poissonMoment_re_eq_arcsine
#print axioms rootDensity_chebyshev_moment
#print axioms rootDensity_mass_one

#print axioms circleAverage_real_coordinate
#print axioms rootBoundary_den_pos
#print axioms rootBoundary_continuousOn
#print axioms rootDensity_arcsine_weight
#print axioms rootDensity_integral
end QuantitativeArithmeticTreePlancherel

open Complex Real Set MeasureTheory
open QuantitativeMaass
namespace QuantitativeArithmeticTreePlancherel

/-- The Poisson parameterization agrees with the usual unramified density. -/
theorem rootDensity_eq_unramified (p x : ℝ) (hp : 0<p) :
    rootDensity (Real.sqrt p)⁻¹ x = unramifiedDensity p x := by
  have hs : (Real.sqrt p)^2=p := Real.sq_sqrt hp.le
  have hn : p≠0 := hp.ne'
  have hnum : (1+((Real.sqrt p)⁻¹)^2)/(2*Real.pi)*Real.sqrt (4-x^2) =
      (((p+1)/(2*Real.pi))*Real.sqrt (4-x^2))/p := by
    rw [inv_pow,hs]
    field_simp
  have hden : (1+((Real.sqrt p)⁻¹)^2)^2-((Real.sqrt p)⁻¹)^2*x^2 =
      (unramifiedRadius p^2-x^2)/p := by
    unfold unramifiedRadius
    rw [inv_pow,hs,div_pow,hs]
    field_simp
  unfold rootDensity unramifiedDensity
  rw [hnum,hden,div_div_div_cancel_right₀ hn]

/-- All Chebyshev moments of the standard unramified density, without a
spectral-measure identification as a premise. -/
theorem unramified_chebyshev_moment (p : ℝ) (hp : 1<p) (n : ℕ) :
    (∫ x in -2..2,unramifiedDensity p x*(Polynomial.Chebyshev.S ℝ (n : ℤ)).eval x) =
      (poissonMoment (Real.sqrt p)⁻¹ n).re := by
  have hs : 1<Real.sqrt p := by
    nlinarith [Real.sq_sqrt (show 0≤p by linarith),Real.sqrt_nonneg p]
  simpa only [rootDensity_eq_unramified p _ (by linarith)] using
    rootDensity_chebyshev_moment (Real.sqrt p)⁻¹ (by positivity)
      (inv_lt_one_of_one_lt₀ hs) n

theorem unramified_mass_one (p : ℝ) (hp : 1<p) :
    (∫ x in -2..2,unramifiedDensity p x)=1 := by
  have hs : 1<Real.sqrt p := by
    nlinarith [Real.sq_sqrt (show 0≤p by linarith),Real.sqrt_nonneg p]
  simpa only [rootDensity_eq_unramified p _ (by linarith)] using
    rootDensity_mass_one (Real.sqrt p)⁻¹ (by positivity) (inv_lt_one_of_one_lt₀ hs)

/-- The explicit density has exactly the root moments of the actual
normalized adjacency operator on the regular tree. -/
theorem normalized_tree_density_moments (p n : ℕ) (hp : 1<p) :
    (∫ x in -2..2,unramifiedDensity (p : ℝ) x*
      (Polynomial.Chebyshev.S ℝ (n : ℤ)).eval x) =
    ((Polynomial.aeval
      (((Real.sqrt (p : ℝ))⁻¹ : ℝ) • treeAdjacency (α := Fin (p+1)))
      (Polynomial.Chebyshev.S ℂ (n : ℤ))) treeRootVector TreeWord.root).re := by
  rw [normalized_tree_poisson_moments p n hp]
  exact unramified_chebyshev_moment p (by exact_mod_cast hp) n

#print axioms rootDensity_eq_unramified
#print axioms unramified_chebyshev_moment
#print axioms unramified_mass_one
#print axioms normalized_tree_density_moments
end QuantitativeArithmeticTreePlancherel

namespace QuantitativeArithmeticTreePlancherel

/-- The monic Chebyshev polynomials span the polynomial ring. -/
theorem chebyshev_S_span :
    Submodule.span ℝ (Set.range (fun n : ℕ => Polynomial.Chebyshev.S ℝ (n : ℤ))) = ⊤ := by
  let K := Submodule.span ℝ (Set.range (fun n : ℕ => Polynomial.Chebyshev.S ℝ (n : ℤ)))
  have hS (n : ℕ) : Polynomial.Chebyshev.S ℝ (n : ℤ)∈K :=
    Submodule.subset_span ⟨n,rfl⟩
  have hX (P : Polynomial ℝ) (hP : P∈K) : Polynomial.X*P∈K := by
    induction hP using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨n,rfl⟩ := hP
      cases n with
      | zero => simpa using hS 1
      | succ n =>
        have hrec : Polynomial.X*Polynomial.Chebyshev.S ℝ (↑(n+1)) =
            Polynomial.Chebyshev.S ℝ (↑(n+2))+Polynomial.Chebyshev.S ℝ (↑n) := by
          rw [show ((n+2 : ℕ) : ℤ)=(n : ℤ)+2 by omega,Polynomial.Chebyshev.S_add_two]
          rw [show ((n+1 : ℕ) : ℤ)=(n : ℤ)+1 by omega]
          ring
        rw [hrec]
        exact K.add_mem (hS (n+2)) (hS n)
    | zero => simp
    | add P Q _ _ hP hQ => simpa only [mul_add] using K.add_mem hP hQ
    | smul a P _ hP => simpa only [mul_smul_comm] using K.smul_mem a hP
  rw [Submodule.eq_top_iff']
  intro P
  change P∈K
  induction P using Polynomial.induction_on with
  | C a => simpa [Polynomial.smul_eq_C_mul] using K.smul_mem a (hS 0)
  | add P Q hP hQ => exact K.add_mem hP hQ
  | monomial n a h =>
    convert hX _ h using 1
    ring

/-- Explicit polynomial integration against the unramified density. -/
def densityMoment (p : ℝ) (hp : 1<p) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun P := ∫ x in -2..2,unramifiedDensity p x*P.eval x
  map_add' P Q := by
    simp only [Polynomial.eval_add,mul_add]
    apply intervalIntegral.integral_add
    all_goals
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      exact (unramifiedDensity_continuousOn p hp).mul (by fun_prop)
  map_smul' a P := by
    simp only [Polynomial.eval_smul,smul_eq_mul,RingHom.id_apply]
    simp_rw [← mul_assoc, mul_comm (unramifiedDensity p _) a, mul_assoc]
    exact intervalIntegral.integral_const_mul _ _

/-- The actual root matrix coefficient as a real polynomial functional. -/
def treeMoment (p : ℕ) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun P := ((Polynomial.aeval
    (((Real.sqrt (p : ℝ))⁻¹ : ℝ) • treeAdjacency (α := Fin (p+1))) P)
      treeRootVector TreeWord.root).re
  map_add' P Q := by simp
  map_smul' a P := by simp

/-- All polynomial moments, sufficient in particular for the LV polynomial
filter, are those of the explicit unramified density. -/
theorem tree_polynomial_moments (p : ℕ) (hp : 1<p) :
    densityMoment p (by exact_mod_cast hp) = treeMoment p := by
  apply (Submodule.linearMap_eq_iff_of_span_eq_top _ _ chebyshev_S_span).2
  rintro ⟨_,n,rfl⟩
  change (∫ x in -2..2,unramifiedDensity (p : ℝ) x*
    (Polynomial.Chebyshev.S ℝ (n : ℤ)).eval x) = _
  rw [normalized_tree_density_moments p n hp]
  unfold treeMoment
  dsimp only [LinearMap.coe_mk,AddHom.coe_mk]
  have h := Polynomial.aeval_eq_aeval_map
    (R := ℝ) (T := ℂ) (φ := Complex.ofRealHom)
    (by ext x; simp) (Polynomial.Chebyshev.S ℝ (n : ℤ))
    (((Real.sqrt (p : ℝ))⁻¹ : ℝ) • treeAdjacency (α := Fin (p+1)))
  simp only [Polynomial.Chebyshev.map_S] at h
  rw [← h]

#print axioms chebyshev_S_span
#print axioms densityMoment
#print axioms treeMoment
#print axioms tree_polynomial_moments
end QuantitativeArithmeticTreePlancherel

namespace QuantitativeArithmeticTreePlancherel

/-- The finite-place LV filter, expressed as a real polynomial. -/
def treeLVPolynomial (a B : ℝ) (d : ℕ) : Polynomial ℝ :=
  1-(1-Polynomial.C (B^2)⁻¹*(Polynomial.X-Polynomial.C a)^2)^d

/-- The identity coefficient of the actual tree polynomial tends to one,
with the explicit uniform square-root deficit required by the LV argument. -/
theorem tree_lv_root_bounds (p : ℕ) (hp : 1<p) (a B : ℝ)
    (ha : a∈Icc (-2 : ℝ) 2) (hB : 4≤B) (d : ℕ) (hd : 0<d) :
    1-unramifiedDensityBound (p : ℝ)*B*Real.sqrt Real.pi/Real.sqrt (d : ℝ) ≤
      treeMoment p (treeLVPolynomial a B d) ∧
    treeMoment p (treeLVPolynomial a B d)≤1 := by
  have hpR : (1 : ℝ)<p := by exact_mod_cast hp
  rw [← tree_polynomial_moments p hp]
  have hmass : densityMoment p hpR 1=1 := by
    simpa only [densityMoment,LinearMap.coe_mk,AddHom.coe_mk,Polynomial.eval_one,mul_one]
      using unramified_mass_one p hpR
  have hdef : densityMoment p hpR
      ((1-Polynomial.C (B^2)⁻¹*(Polynomial.X-Polynomial.C a)^2)^d) =
      ∫ x in Icc (-2 : ℝ) 2,unramifiedDensity (p : ℝ) x*(1-(x-a)^2/B^2)^d := by
    simp only [densityMoment,LinearMap.coe_mk,AddHom.coe_mk,Polynomial.eval_pow,
      Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,div_eq_mul_inv,mul_comm ((B^2)⁻¹)]
    rw [intervalIntegral.integral_of_le (by norm_num),← integral_Icc_eq_integral_Ioc]
  simp only [treeLVPolynomial,map_sub,hmass,hdef]
  have h := unramified_lv_deficit p hpR a B ha hB d hd
  constructor <;> linarith [h.1,h.2]

/-- Specialization to the precise center and normalization of actualLVFilter. -/
theorem tree_actual_lv_root_bounds (p : ℕ) [Fact p.Prime] (r : ℝ)
    (d : ℕ) (hd : 0<d) :
    1-unramifiedDensityBound (p : ℝ)*lvBound p*Real.sqrt Real.pi/Real.sqrt (d : ℝ) ≤
      treeMoment p (treeLVPolynomial (2*Real.cos (r*Real.log p)) (lvBound p) d) ∧
    treeMoment p (treeLVPolynomial (2*Real.cos (r*Real.log p)) (lvBound p) d)≤1 := by
  apply tree_lv_root_bounds p (Fact.out : p.Prime).one_lt _ _ _ (lvBound_gt_four p).le d hd
  constructor <;> linarith [Real.neg_one_le_cos (r*Real.log p),Real.cos_le_one (r*Real.log p)]

#print axioms tree_lv_root_bounds
#print axioms tree_actual_lv_root_bounds
end QuantitativeArithmeticTreePlancherel

open scoped BigOperators lp
namespace QuantitativeArithmeticTreePlancherel

/-- The root functional on a monomial is the normalized count of closed
walks in the actual regular tree. -/
theorem treeMoment_monomial (p n : ℕ) (a : ℝ) :
    treeMoment p (Polynomial.C a*Polynomial.X^n) =
      a*(Real.sqrt (p : ℝ))⁻¹^n*(treeWalkCount (p+1) n 0 : ℝ) := by
  rw [← Polynomial.smul_eq_C_mul,map_smul]
  have hpow : (((Real.sqrt (p : ℝ))⁻¹ : ℝ) • treeAdjacency (α := Fin (p+1)))^n =
      ((Real.sqrt (p : ℝ))⁻¹)^n • (treeAdjacency (α := Fin (p+1)))^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,ih,pow_succ,pow_succ]
      change (((Real.sqrt (p : ℝ))⁻¹)^n • treeAdjacency^n).comp
        ((Real.sqrt (p : ℝ))⁻¹ • treeAdjacency) = _
      rw [ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,smul_smul]
      rfl
  change a*((Polynomial.aeval
    (((Real.sqrt (p : ℝ))⁻¹ : ℝ) • treeAdjacency (α := Fin (p+1)))
    (Polynomial.X^n)) treeRootVector TreeWord.root).re = _
  rw [map_pow,Polynomial.aeval_X,hpow]
  change a*(((((Real.sqrt (p : ℝ))⁻¹)^n : ℝ) : ℂ)*
    (((treeAdjacency (α := Fin (p+1)))^n) treeRootVector TreeWord.root)).re = _
  rw [treeAdjacency_power_root]
  simp only [Fintype.card_fin,TreeWord.root,List.length_nil,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,zero_mul,sub_zero]
  ring

/-- Exact coefficient formula, not a bound on absolute walk counts. -/
theorem treeMoment_coefficients (p : ℕ) (P : Polynomial ℝ) :
    treeMoment p P = ∑ n ∈ P.support,
      P.coeff n*(Real.sqrt (p : ℝ))⁻¹^n*(treeWalkCount (p+1) n 0 : ℝ) := by
  have h := congrArg (treeMoment p) P.sum_C_mul_X_pow_eq
  simp only [Polynomial.sum,map_sum,treeMoment_monomial] at h
  exact h.symm

/-- The identity-coset coefficient of a polynomial in the normalized Hecke
branch sum is its integral against the explicit unramified density. -/
theorem hecke_identity_coefficient_density (N p : ℕ) [Fact p.Prime]
    (P : Polynomial ℝ) :
    (∑ n ∈ P.support,P.coeff n*(Real.sqrt (p : ℝ))⁻¹^n*
      (HeckeUpper.cosetWalks N p n HeckeUpper.root : ℝ)) =
    ∫ x in -2..2,unramifiedDensity (p : ℝ) x*P.eval x := by
  simp_rw [HeckeUpper.cosetWalks_root_eq_tree]
  rw [← treeMoment_coefficients,← tree_polynomial_moments p (Fact.out : p.Prime).one_lt]
  rfl

#print axioms treeMoment_monomial
#print axioms treeMoment_coefficients
#print axioms hecke_identity_coefficient_density
end QuantitativeArithmeticTreePlancherel
