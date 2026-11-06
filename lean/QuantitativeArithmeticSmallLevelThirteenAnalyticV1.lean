module

public import SmallLevelAnalyticRigidityTheoryV4
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

set_option autoImplicit false
@[expose] public noncomputable section
namespace QuantitativeArithmeticSmallLevelThirteen
open Complex Filter Set
open scoped Topology

/-- Equality on a single positive imaginary ray determines a holomorphic
function throughout the upper half-plane. -/
theorem constant_of_imaginary_ray {L : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L {z : ℂ | 0<z.im})
    (hray : ∀ r : ℝ, 0<r → L ((r:ℂ)*I)=L I) :
    ∀ z : ℂ, 0<z.im → L z=L I := by
  have hcl : I∈closure ({z : ℂ | L z=(fun _ : ℂ => L I) z} \ {I}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let r : ℝ := 1+ε/2
    have hr : 0<r := by dsimp [r]; linarith
    refine ⟨(r:ℂ)*I,⟨hray r hr,?_⟩,?_⟩
    · simp only [mem_singleton_iff]
      intro hh
      have hi := congrArg Complex.im hh
      simp only [mul_im,ofReal_re,I_im,mul_one,ofReal_im,I_re,mul_zero,add_zero] at hi
      dsimp [r] at hi
      linarith
    · have he : (r:ℂ)*I-I=((ε/2:ℝ):ℂ)*I := by
        dsimp [r]
        push_cast
        ring
      rw [dist_comm,dist_eq_norm,he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos (by positivity : 0<ε/2)]
      linarith
  have he := hL.eqOn_of_preconnected_of_mem_closure analyticOnNhd_const
    (convex_halfSpace_im_gt 0).isPreconnected (by simp : I∈{z : ℂ | 0<z.im}) hcl
  exact fun z hz => he hz

/-- An analytic function invariant on an imaginary orbit of a dense
additive subgroup of logarithmic dilations is constant. This is the
analytic part of the common-hyperbolic-axis argument. -/
theorem constant_of_dense_dilations {L : ℂ → ℂ} (S : AddSubgroup ℝ)
    (hL : AnalyticOnNhd ℂ L {z : ℂ | 0<z.im}) (hS : Dense (S : Set ℝ))
    (hinv : ∀ t∈S, L ((Real.exp t:ℂ)*I)=L I) :
    ∀ z : ℂ, 0<z.im → L z=L I := by
  have hc : Continuous (fun t : ℝ => L ((Real.exp t:ℂ)*I)) := by
    apply hL.continuousOn.comp_continuous
      ((Complex.continuous_ofReal.comp Real.continuous_exp).mul continuous_const)
    intro t
    change 0<(((Real.exp t:ℝ):ℂ)*I).im
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.I_im,
      mul_one,Complex.ofReal_im,Complex.I_re,mul_zero,add_zero]
    exact Real.exp_pos t
  have hclosed : IsClosed {t : ℝ | L ((Real.exp t:ℂ)*I)=L I} :=
    isClosed_eq hc continuous_const
  have hall : ∀ t : ℝ, L ((Real.exp t:ℂ)*I)=L I := by
    intro t
    exact (closure_minimal hinv hclosed) (hS t)
  apply constant_of_imaginary_ray hL
  intro r hr
  simpa only [Real.exp_log hr] using hall (Real.log r)

/-- Two incommensurable logarithmic dilation periods suffice. The
arithmetic irrationality is explicit and separate from the analytic proof. -/
theorem constant_of_two_dilation_periods {L : ℂ → ℂ} {a b : ℝ}
    (hL : AnalyticOnNhd ℂ L {z : ℂ | 0<z.im}) (hab : Irrational (a/b))
    (hinv : ∀ t∈AddSubgroup.closure ({a,b} : Set ℝ),
      L ((Real.exp t:ℂ)*I)=L I) :
    ∀ z : ℂ, 0<z.im → L z=L I :=
  constant_of_dense_dilations _ hL (dense_addSubgroupClosure_pair_iff.mpr hab) hinv

/-- Logarithmic dilation periods of a function form an additive subgroup. -/
def dilationPeriods (L : ℂ → ℂ) : AddSubgroup ℝ where
  carrier := {t | ∀ z : ℂ, 0<z.im → L ((Real.exp t:ℂ)*z)=L z}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb z hz
    change L ((Real.exp (a+b):ℂ)*z)=L z
    have hp : 0<((Real.exp b:ℂ)*z).im := by
      simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
        using mul_pos (Real.exp_pos b) hz
    rw [Real.exp_add,Complex.ofReal_mul,mul_assoc,ha _ hp,hb _ hz]
  neg_mem' := by
    intro a ha z hz
    change L ((Real.exp (-a):ℂ)*z)=L z
    have hp : 0<((Real.exp (-a):ℂ)*z).im := by
      simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
        using mul_pos (Real.exp_pos (-a)) hz
    have hh := ha _ hp
    rw [← mul_assoc,← Complex.ofReal_mul,← Real.exp_add] at hh
    simpa using hh.symm

/-- Concrete invariance under each of two generators implies all the
closure invariance used by the analytic density argument. -/
theorem constant_of_two_periods {L : ℂ → ℂ} {a b : ℝ}
    (hL : AnalyticOnNhd ℂ L {z : ℂ | 0<z.im}) (hab : Irrational (a/b))
    (ha : ∀ z : ℂ, 0<z.im → L ((Real.exp a:ℂ)*z)=L z)
    (hb : ∀ z : ℂ, 0<z.im → L ((Real.exp b:ℂ)*z)=L z) :
    ∀ z : ℂ, 0<z.im → L z=L I := by
  apply constant_of_two_dilation_periods hL hab
  have hsub : AddSubgroup.closure ({a,b} : Set ℝ)≤dilationPeriods L := by
    apply (AddSubgroup.closure_le _).mpr
    intro t ht
    rcases ht with rfl|ht
    · exact ha
    · have h : t=b := ht
      rw [h]
      exact hb
  intro t ht
  exact hsub ht I (by simp)

/-- Multiplicative independence implies irrationality of the logarithmic
period ratio. The concrete level-13 arithmetic remains a separate input. -/
theorem irrational_log_ratio_of_independent {x y : ℝ} (hx : 0<x) (hy : 0<y)
    (hind : ∀ m n : ℤ, x^m*y^n=1 → m=0 ∧ n=0) :
    Irrational (Real.log x/Real.log y) := by
  have hy1 : y≠1 := by
    intro h
    have hh := hind 0 1 (by simp [h])
    norm_num at hh
  have hly : Real.log y≠0 := by
    intro h
    exact hy1 (Real.exp_log hy ▸ by rw [h]; simp)
  rintro ⟨q,hq⟩
  have hd : (q.den:ℝ)≠0 := by exact_mod_cast q.den_ne_zero
  rw [Rat.cast_def] at hq
  have he : (q.den:ℝ)*Real.log x+(-(q.num:ℤ):ℝ)*Real.log y=0 := by
    field_simp [hd,hly] at hq
    nlinarith [hq]
  have hp : 0<x^(q.den:ℤ)*y^(-q.num) := mul_pos (zpow_pos hx _) (zpow_pos hy _)
  have hl : Real.log (x^(q.den:ℤ)*y^(-q.num))=0 := by
    rw [Real.log_mul (zpow_ne_zero _ hx.ne') (zpow_ne_zero _ hy.ne'),Real.log_zpow,
      Real.log_zpow]
    simpa only [Int.cast_natCast,Int.cast_neg] using he
  have hh := hind (q.den:ℤ) (-q.num) (by rw [← Real.exp_log hp,hl,Real.exp_zero])
  have hn : q.den=0 := by exact_mod_cast hh.1
  exact q.den_ne_zero hn

#print axioms dilationPeriods
#print axioms constant_of_two_periods
#print axioms irrational_log_ratio_of_independent
#print axioms constant_of_imaginary_ray
#print axioms constant_of_dense_dilations
#print axioms constant_of_two_dilation_periods
end QuantitativeArithmeticSmallLevelThirteen
