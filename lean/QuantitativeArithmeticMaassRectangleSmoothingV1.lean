module

public import QuantitativeArithmeticMaassCutoffColumnEnergyV1
public import QuantitativeMaassAbelCutoffDerivativeBoundV1
public import QuantitativeMaassCylinderRectangleMeasureV1

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open scoped ENNReal ContDiff

namespace QuantitativeMaass
open MaassDifferential

/-- An inner approximation to an interval, with a transition of width h
at each end. -/
def innerIntervalCutoff (a b h x : ℝ) : ℝ :=
  Real.smoothTransition ((x-a)/h)*Real.smoothTransition ((b-x)/h)

theorem innerIntervalCutoff_smooth (a b h : ℝ) :
    ContDiff ℝ ∞ (innerIntervalCutoff a b h) := by
  unfold innerIntervalCutoff
  fun_prop

theorem innerIntervalCutoff_bounds (a b h x : ℝ) :
    0≤ innerIntervalCutoff a b h x ∧ innerIntervalCutoff a b h x≤1 := by
  have h1 := Real.smoothTransition.nonneg ((x-a)/h)
  have h2 := Real.smoothTransition.nonneg ((b-x)/h)
  have h3 := Real.smoothTransition.le_one ((x-a)/h)
  have h4 := Real.smoothTransition.le_one ((b-x)/h)
  unfold innerIntervalCutoff
  exact ⟨mul_nonneg h1 h2, (mul_le_of_le_one_left h2 h3).trans h4⟩

theorem innerIntervalCutoff_one (a b h x : ℝ) (hh : 0<h)
    (hx : x∈Icc (a+h) (b-h)) : innerIntervalCutoff a b h x=1 := by
  have h1 : 1≤(x-a)/h := (le_div_iff₀ hh).mpr (by linarith [hx.1])
  have h2 : 1≤(b-x)/h := (le_div_iff₀ hh).mpr (by linarith [hx.2])
  simp [innerIntervalCutoff,Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.one_of_one_le h2]

theorem innerIntervalCutoff_support (a b h : ℝ) (hh : 0<h) :
    Function.support (innerIntervalCutoff a b h) ⊆ Icc a b := by
  intro x hx
  constructor
  · by_contra hn
    have hz := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith : x-a≤0) hh.le)
    exact hx (by simp [innerIntervalCutoff,hz])
  · by_contra hn
    have hz := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith : b-x≤0) hh.le)
    exact hx (by simp [innerIntervalCutoff,hz])

def rectangleCutoffFunction (l r a b h : ℝ) (Z : Point) : ℂ :=
  (innerIntervalCutoff l r h Z.1*innerIntervalCutoff a b h Z.2 : ℝ)

theorem rectangleCutoffFunction_smooth (l r a b h : ℝ) :
    ContDiff ℝ ∞ (rectangleCutoffFunction l r a b h) := by
  exact Complex.ofRealCLM.contDiff.comp
    (((innerIntervalCutoff_smooth l r h).comp contDiff_fst).mul
      ((innerIntervalCutoff_smooth a b h).comp contDiff_snd))

theorem rectangleCutoffFunction_support (l r a b h : ℝ) (hh : 0<h) :
    Function.support (upperFunction (rectangleCutoffFunction l r a b h)) ⊆
      upperRectangle l r a b := by
  intro z hz
  have hx : innerIntervalCutoff l r h z.re≠0 := by
    intro hn
    exact hz (by simp [upperFunction,rectangleCutoffFunction,hn])
  have hy : innerIntervalCutoff a b h z.im≠0 := by
    intro hn
    exact hz (by simp [upperFunction,rectangleCutoffFunction,hn])
  exact ⟨innerIntervalCutoff_support l r h hh hx,innerIntervalCutoff_support a b h hh hy⟩

/-- The concrete smooth seed used to replace a sharp compact rectangle. -/
def rectangleSmoothSeed (l r a b h : ℝ) (ha : 0<a) (hh : 0<h) : SmoothUpperSeed where
  toFun := rectangleCutoffFunction l r a b h
  smooth := (rectangleCutoffFunction_smooth l r a b h).contDiffOn
  compact := (upperRectangle_compact l r a b ha).of_isClosed_subset isClosed_closure
    (closure_minimal (rectangleCutoffFunction_support l r a b h hh)
      (upperRectangle_compact l r a b ha).isClosed)

theorem rectangleSmoothSeed_support (l r a b h : ℝ) (ha : 0<a) (hh : 0<h) :
    tsupport (upperFunction (rectangleSmoothSeed l r a b h ha hh).toFun) ⊆
      upperRectangle l r a b :=
  closure_minimal (rectangleCutoffFunction_support l r a b h hh)
    (upperRectangle_compact l r a b ha).isClosed

theorem rectangleCutoffFunction_bounds (l r a b h : ℝ) (z : ℍ) :
    0≤(upperFunction (rectangleCutoffFunction l r a b h) z).re ∧
    ‖upperFunction (rectangleCutoffFunction l r a b h) z‖≤1 := by
  obtain ⟨hx,hx1⟩ := innerIntervalCutoff_bounds l r h z.re
  obtain ⟨hy,hy1⟩ := innerIntervalCutoff_bounds a b h z.im
  have hm := mul_nonneg hx hy
  refine ⟨hm,?_⟩
  change ‖((innerIntervalCutoff l r h z.re*innerIntervalCutoff a b h z.im : ℝ) : ℂ)‖≤1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm]
  exact (mul_le_of_le_one_left hy hx1).trans hy1

theorem rectangleSmoothSeed_real (l r a b h : ℝ) (ha : 0<a) (hh : 0<h) (Z : Point) :
    star ((rectangleSmoothSeed l r a b h ha hh).toFun Z)=
      (rectangleSmoothSeed l r a b h ha hh).toFun Z := by
  change star ((_:ℝ):ℂ)=((_:ℝ):ℂ)
  simp

/-- Sharp and smooth rectangle cutoffs differ only in the explicitly
specified inner boundary collar, with difference bounded by one. -/
theorem rectangleSmoothSeed_collar (l r a b h : ℝ) (ha : 0<a) (hh : 0<h) (z : ℍ) :
    let S := upperRectangle l r a b
    let I := upperRectangle (l+h) (r-h) (a+h) (b-h)
    let u := upperFunction (rectangleSmoothSeed l r a b h ha hh).toFun
    ‖S.indicator (fun _ => (1:ℂ)) z-u z‖≤1 ∧
      (z∉S\I → S.indicator (fun _ => (1:ℂ)) z=u z) := by
  classical
  intro S I u
  have hbd := rectangleCutoffFunction_bounds l r a b h z
  change 0 ≤ (u z).re ∧ ‖u z‖ ≤ 1 at hbd
  have hre : u z=((u z).re:ℂ) := rfl
  by_cases hz : z∈S
  · rw [Set.indicator_of_mem hz]
    constructor
    · rw [hre,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      have hle : (u z).re≤1 := (Complex.re_le_norm _).trans hbd.2
      rw [abs_of_nonneg (sub_nonneg.mpr hle)]
      linarith [hbd.1]
    · intro hn
      have hi : z∈I := by simpa only [Set.mem_sdiff,hz,true_and,not_not] using hn
      change (1:ℂ)=((innerIntervalCutoff l r h z.re*innerIntervalCutoff a b h z.im : ℝ):ℂ)
      rw [innerIntervalCutoff_one l r h z.re hh hi.1,
        innerIntervalCutoff_one a b h z.im hh hi.2]
      norm_num
  · have hu : u z=0 := by
      by_contra hn
      exact hz (rectangleCutoffFunction_support l r a b h hh hn)
    simp [Set.indicator_of_notMem hz,hu]


/-- Elementary area bound for a compact hyperbolic rectangle. -/
theorem upperRectangle_area_bound (l r a b : ℝ) (hlr : l≤r) (ha : 0<a) (hab : a≤b) :
    volume.real (upperRectangle l r a b) ≤ (r-l)*(b-a)/a^2 := by
  have hi : ‖∫ z in upperRectangle l r a b, (1:ℂ)‖ =
      volume.real (upperRectangle l r a b) := by
    rw [integral_const, norm_smul]
    simp only [measureReal_restrict_apply_univ, norm_one, mul_one,
      Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
  rw [←hi,integral_upperRectangle l r a b ha]
  have hbnd : ∀ Z ∈ Icc l r ×ˢ Icc a b, ‖(1:ℂ)/(Z.2:ℂ)^2‖ ≤ 1/a^2 := by
    intro Z hZ
    rw [norm_div,norm_one,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (ha.trans_le hZ.2.1)]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ ha.le hZ.2.1 2)
  have hm : (volume : Measure Point).real (Icc l r ×ˢ Icc a b)=(r-l)*(b-a) := by
    change ((volume : Measure ℝ).prod volume).real _=_
    rw [measureReal_prod_prod,Real.volume_real_Icc_of_le hlr,Real.volume_real_Icc_of_le hab]
  have hh := norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure Point)) (s := Icc l r ×ˢ Icc a b)
    (f := fun Z => (1:ℂ)/(Z.2:ℂ)^2)
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top hbnd
  rw [hm] at hh
  convert hh using 1
  ring


/-- The inner collar has area linear in its width, with explicit dependence
on the rectangle. This remains useful when the rectangle varies with t. -/
theorem upperRectangle_collar_area (l r a b h : ℝ) (hlr : l≤r)
    (ha : 0<a) (hh : 0<h) (hhb : h≤b-a) :
    volume.real (upperRectangle l r a b \
      upperRectangle (l+h) (r-h) (a+h) (b-h)) ≤
        2*h*((b-a)+(r-l))/a^2 := by
  let S1 := upperRectangle l (l+h) a b
  let S2 := upperRectangle (r-h) r a b
  let S3 := upperRectangle l r a (a+h)
  let S4 := upperRectangle l r (b-h) b
  have hab : a≤b := by linarith
  have htop : 0<b-h := by linarith
  have hc : IsCompact (S1 ∪ S2 ∪ S3 ∪ S4) :=
    (((upperRectangle_compact l (l+h) a b ha).union
      (upperRectangle_compact (r-h) r a b ha)).union
      (upperRectangle_compact l r a (a+h) ha)).union
      (upperRectangle_compact l r (b-h) b htop)
  have hsub : upperRectangle l r a b \
      upperRectangle (l+h) (r-h) (a+h) (b-h) ⊆ S1 ∪ S2 ∪ S3 ∪ S4 := by
    intro z hz
    have hz0 := hz.1
    by_contra hn
    have hout : z∉S1 ∧ z∉S2 ∧ z∉S3 ∧ z∉S4 := by
      simpa only [mem_union,not_or,and_assoc] using hn
    apply hz.2
    change (l+h≤z.re ∧ z.re≤r-h) ∧ (a+h≤z.im ∧ z.im≤b-h)
    have h1 : l+h≤z.re := by
      by_contra hf
      exact hout.1 ⟨⟨hz0.1.1,by linarith⟩,hz0.2⟩
    have h2 : z.re≤r-h := by
      by_contra hf
      exact hout.2.1 ⟨⟨by linarith,hz0.1.2⟩,hz0.2⟩
    have h3 : a+h≤z.im := by
      by_contra hf
      exact hout.2.2.1 ⟨hz0.1,⟨hz0.2.1,by linarith⟩⟩
    have h4 : z.im≤b-h := by
      by_contra hf
      exact hout.2.2.2 ⟨hz0.1,⟨by linarith,hz0.2.2⟩⟩
    exact ⟨⟨h1,h2⟩,h3,h4⟩
  have h1 : volume.real S1≤h*(b-a)/a^2 := by
    simpa only [S1,add_sub_cancel_left] using
      upperRectangle_area_bound l (l+h) a b (by linarith) ha hab
  have h2 : volume.real S2≤h*(b-a)/a^2 := by
    convert upperRectangle_area_bound (r-h) r a b (by linarith) ha hab using 1
    ring
  have h3 : volume.real S3≤(r-l)*h/a^2 := by
    simpa only [S3,add_sub_cancel_left] using
      upperRectangle_area_bound l r a (a+h) hlr ha (by linarith)
  have h4 : volume.real S4≤(r-l)*h/a^2 := by
    have hv := upperRectangle_area_bound l r (b-h) b hlr htop (by linarith)
    have hden : a^2≤(b-h)^2 := pow_le_pow_left₀ ha.le (by linarith) 2
    have hh' : (r-l)*h/(b-h)^2≤(r-l)*h/a^2 :=
      div_le_div_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hlr) hh.le) (by positivity) hden
    apply (show volume.real S4≤(r-l)*h/(b-h)^2 by convert hv using 1; ring).trans hh'
  have hu1 := measureReal_union_le (μ := (volume : Measure ℍ)) S1 S2
  have hu2 := measureReal_union_le (μ := (volume : Measure ℍ)) (S1 ∪ S2) S3
  have hu3 := measureReal_union_le (μ := (volume : Measure ℍ)) (S1 ∪ S2 ∪ S3) S4
  have hm := measureReal_mono (μ := (volume : Measure ℍ)) hsub hc.measure_ne_top
  calc
    _ ≤ 2*(h*(b-a)/a^2)+2*((r-l)*h/a^2) := by linarith
    _ = _ := by ring

/-- Every concrete smoothing has a finite hyperbolic gradient bound on
its fixed compact support; no regularity of the sharp indicator is used. -/
theorem rectangleSmoothSeed_gradient_bound (l r a b h : ℝ) (ha : 0<a) (hh : 0<h) :
    ∃ C : ℝ, 0≤C ∧ ∀ z ∈ upperRectangle l r a b,
      (upperEnergy (rectangleSmoothSeed l r a b h ha hh).toFun
        (rectangleSmoothSeed l r a b h ha hh).toFun z).re ≤ C^2 := by
  let u := rectangleSmoothSeed l r a b h ha hh
  obtain ⟨C,hC⟩ := (upperEnergy_compact_right u.toFun u.toFun u.compact).exists_bound_of_continuous
    (upperEnergy_continuous u.smooth u.smooth)
  refine ⟨|C|+1,by positivity,?_⟩
  intro z _
  have hz := (Complex.re_le_norm (upperEnergy u.toFun u.toFun z)).trans (hC z)
  have hc : C≤|C| := le_abs_self C
  nlinarith [abs_nonneg C]

#print axioms upperRectangle_collar_area
#print axioms rectangleSmoothSeed_gradient_bound
#print axioms upperRectangle_area_bound
#print axioms rectangleSmoothSeed
#print axioms rectangleSmoothSeed_collar

end QuantitativeMaass
