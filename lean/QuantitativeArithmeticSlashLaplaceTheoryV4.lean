module

public import QuantitativeArithmeticCurvedTaylorTheoryV4
public import QuantitativeArithmeticDilationLaplaceTheoryV4
public import QuantitativeArithmeticSmallLevelThirteenAnalyticV1
public import SmallLevelNormalizedMatricesV1

/-! Consolidated chapter: QuantitativeArithmeticSlashLaplace. Original declarations and local scopes are retained. -/

/-! ## QuantitativeArithmeticSlashLaplaceTransportV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSlashLaplace
open Complex Filter Set Matrix MeasureTheory UpperHalfPlane
open FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped Topology ModularForm MatrixGroups

def logPoint (x t : ℝ) : ℍ := ⟨⟨x,Real.exp t⟩,Real.exp_pos t⟩

theorem logPoint_coe (x t : ℝ) : (logPoint x t:ℂ)=(x:ℂ)+Complex.I*(Real.exp t:ℂ) := by
  apply Complex.ext <;> simp [logPoint,Complex.exp_re]

theorem slash_raw (k : ℕ) (a : ℕ → ℂ) (g : GL (Fin 2) ℝ)
    (hg : (GeneralLinearGroup.det g:ℝ)=1) (x t : ℝ) :
    (((fun z : ℍ => fourier a z) ∣[(k:ℤ)] g) (logPoint x t))=
      QuantitativeArithmeticCurvedTaylor.rawSlashRay k a
        (g 0 0) (g 0 1) (g 1 0) (g 1 1) x (Real.exp t) := by
  rw [SmallLevelNormalized.det_one_slash g hg]
  rw [coe_smul_of_det_pos (by rw [hg]; norm_num),zpow_neg,zpow_natCast]
  simp only [num,denom,logPoint_coe]
  exact mul_comm _ _

/-- Genuine determinant-one slash transforms have the required one-sided
Laplace continuation, derived solely from the additive transform at g∞. -/
theorem slash_laplace_continuation (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) (g : GL (Fin 2) ℝ) (hg : (GeneralLinearGroup.det g:ℝ)=1)
    (hC : g 1 0≠0) (x : ℝ) (hx : x+g 1 1/g 1 0≠0)
    (BG : ℝ) (G : ℂ → ℂ) (hG : ∀ s, MeromorphicAt G s)
    (hGa : ∀ s, s≠(k:ℂ) → AnalyticAt ℂ G s)
    (hGo : (-1:WithTop ℤ)≤meromorphicOrderAt G (k:ℂ))
    (hGF : ∀ s, BG<s.re → G s=SmallLevelAdditive.transform a (g 0 0/g 1 0) s) :
    ∃ (BJ : ℝ) (J : ℂ → ℂ), (∀ s, MeromorphicAt J s) ∧
      (∀ s, s≠0 → AnalyticAt ℂ J s) ∧
      (-1:WithTop ℤ)≤meromorphicOrderAt J 0 ∧
      ∀ s : ℂ, s.re<BJ → J s=
        QuantitativeArithmeticDilationLaplace.transform
          (fun t => (((fun z : ℍ => fourier a z) ∣[(k:ℤ)] g) (logPoint x t))) s := by
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    change (g:Matrix (Fin 2) (Fin 2) ℝ).det=1 at hg
    simpa only [Matrix.det_fin_two] using hg
  obtain ⟨BJ,J,hJ,hJa,hJo,hJF⟩ := QuantitativeArithmeticCurvedTaylor.raw_slash_laplace_continuation
    k ha ha0 (g 0 0) (g 0 1) (g 1 0) (g 1 1) x hC
    (by rw [hd]; exact zero_lt_one) hx BG G hG hGa hGo hGF
  refine ⟨BJ,J,hJ,hJa,hJo,?_⟩
  intro s hs
  simp_rw [slash_raw k a g hg x]
  exact hJF s hs

#print axioms slash_raw
#print axioms slash_laplace_continuation
end QuantitativeArithmeticSlashLaplace
end
end

/-! ## QuantitativeArithmeticRealSlashGrowthV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSlashLaplace
open Complex UpperHalfPlane Matrix
open scoped ModularForm MatrixGroups

theorem real_denom_upper (g : GL (Fin 2) ℝ) {R : ℝ} (hR : 0≤R) (z : ℍ)
    (hx : |z.re|≤R) (hy : 1≤z.im) :
    ‖denom g z‖≤(|g 1 0| *(R+1)+|g 1 1|)*z.im := by
  have hz : ‖(z:ℂ)‖≤(R+1)*z.im := by
    calc
      _≤|z.re|+|z.im| := Complex.norm_le_abs_re_add_abs_im _
      _≤R+z.im := by rw [abs_of_pos z.im_pos]; linarith
      _≤_ := by nlinarith
  unfold denom
  calc
    _≤‖((g 1 0:ℝ):ℂ)*(z:ℂ)‖+‖((g 1 1:ℝ):ℂ)‖ := norm_add_le _ _
    _=|g 1 0| *‖(z:ℂ)‖+|g 1 1| := by simp
    _≤|g 1 0| *((R+1)*z.im)+|g 1 1| *z.im := by
      gcongr
      exact le_mul_of_one_le_right (abs_nonneg _) hy
    _=_ := by ring

theorem real_denom_lower (g : GL (Fin 2) ℝ) (z : ℍ) (hy : 1≤z.im) :
    |g 1 0|≤‖denom g z‖ := by
  calc
    |g 1 0|≤|g 1 0| *z.im := le_mul_of_one_le_right (abs_nonneg _) hy
    _=|(denom g z).im| := by
      simp [denom,Complex.mul_im,abs_mul,abs_of_pos z.im_pos]
    _≤_ := Complex.abs_im_le_norm _

/-- Polynomial height bounds persist under arbitrary real determinant-one
matrices with nonzero lower-left entry; no integrality is needed. -/
theorem real_slash_polynomial_strip (k b : ℕ) (f : ℍ → ℂ) {M R : ℝ}
    (hM : 0≤M) (hR : 0≤R) (hb : ∀ z : ℍ, z.im^b*‖f z‖≤M)
    (g : GL (Fin 2) ℝ) (hg : (GeneralLinearGroup.det g:ℝ)=1) (hc : g 1 0≠0)
    (z : ℍ) (hx : |z.re|≤R) (hy : 1≤z.im) :
    ‖(f ∣[(k:ℤ)] g) z‖≤
      (M*(|g 1 0| *(R+1)+|g 1 1|)^(2*b)*(|g 1 0|^k)⁻¹)*z.im^(2*b) := by
  have hden := real_denom_lower g z hy
  have hdp : 0<‖denom g z‖ := lt_of_lt_of_le (abs_pos.mpr hc) hden
  have hf : ‖f (g • z)‖≤M/(g • z).im^b :=
    (le_div_iff₀ (pow_pos (g • z).im_pos b)).mpr (by simpa only [mul_comm] using hb (g • z))
  have hf' : ‖f (g • z)‖≤M*‖denom g z‖^(2*b) := by
    apply hf.trans
    rw [UpperHalfPlane.im_smul_eq_div_normSq,hg,abs_one,one_mul,
      Complex.normSq_eq_norm_sq,div_pow,div_div_eq_mul_div,← pow_mul]
    exact div_le_self (mul_nonneg hM (pow_nonneg (norm_nonneg _) _)) (one_le_pow₀ hy)
  have hfac : ‖denom g z ^ (-(k:ℤ))‖≤(|g 1 0|^k)⁻¹ := by
    rw [norm_zpow,zpow_neg,zpow_natCast]
    exact inv_anti₀ (pow_pos (abs_pos.mpr hc) k)
      (pow_le_pow_left₀ (abs_nonneg _) hden k)
  rw [SmallLevelNormalized.det_one_slash g hg,norm_mul]
  calc
    _≤(M*‖denom g z‖^(2*b))*(|g 1 0|^k)⁻¹ :=
      mul_le_mul hf' hfac (norm_nonneg _) (by positivity)
    _≤(M*((|g 1 0| *(R+1)+|g 1 1|)*z.im)^(2*b))*(|g 1 0|^k)⁻¹ := by
      gcongr
      exact real_denom_upper g hR z hx hy
    _=_ := by rw [mul_pow]; ring

#print axioms real_slash_polynomial_strip
end QuantitativeArithmeticSlashLaplace
end
end

/-! ## QuantitativeArithmeticSlashLogarithmicGrowthV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSlashLaplace
open Complex UpperHalfPlane Matrix
open FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped Topology Manifold ModularForm MatrixGroups

theorem logPoint_continuous (x : ℝ) : Continuous (logPoint x) := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun t : ℝ => (logPoint x t:ℂ))
  simp_rw [logPoint_coe]
  fun_prop

theorem logarithmic_slash_continuous (k : ℕ) (f : ℍ → ℂ) (hf : MDiff f)
    (g : GL (Fin 2) ℝ) (x : ℝ) :
    Continuous (fun t => (f ∣[(k:ℤ)] g) (logPoint x t)) :=
  (hf.slash (k:ℤ) g).continuous.comp (logPoint_continuous x)

/-- The polynomial coefficient hypothesis supplies exponential growth on the
logarithmic ray for every relevant real slash transform. -/
theorem fourier_logarithmic_growth (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) (g : GL (Fin 2) ℝ) (hg : (GeneralLinearGroup.det g:ℝ)=1)
    (hc : g 1 0≠0) (x : ℝ) :
    ∃ C B : ℝ, ∀ t : ℝ, 0≤t →
      ‖((fun z : ℍ => fourier a z) ∣[(k:ℤ)] g) (logPoint x t)‖≤C*Real.exp (B*t) := by
  obtain ⟨b,M,hM,hb⟩ := SmallLevelTaylor.fourier_boundary_bound ha ha0
  have hbound : ∀ z : ℍ, z.im^b*‖fourier a z‖≤M := by
    intro z
    have hh := (le_div_iff₀ (pow_pos z.im_pos b)).mp (hb z z.im_pos)
    simpa only [mul_comm] using hh
  refine ⟨M*(|g 1 0| *(|x|+1)+|g 1 1|)^(2*b)*(|g 1 0|^k)⁻¹,((2*b:ℕ):ℝ),?_⟩
  intro t ht
  have he : 1≤Real.exp t := Real.one_le_exp_iff.mpr ht
  have hh := real_slash_polynomial_strip k b (fun z : ℍ => fourier a z)
    hM (abs_nonneg x) hbound g hg hc (logPoint x t) (le_refl _) he
  change _≤_*((Real.exp t)^(2*b)) at hh
  rw [← Real.exp_nat_mul] at hh
  exact hh

#print axioms logarithmic_slash_continuous
#print axioms fourier_logarithmic_growth
end QuantitativeArithmeticSlashLaplace
end
end

/-! ## QuantitativeArithmeticSlashLaplaceDataV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSlashLaplace
open Complex MeasureTheory Set Matrix UpperHalfPlane
open FinitenessPolynomialSeries FinitenessFourierConstruction
open scoped Manifold ModularForm MatrixGroups

/-- A continued one-sided transform together with its genuine convergent
initial half-plane. Subtraction therefore preserves the integral identity. -/
structure Data (H : ℝ → ℂ) where
  J : ℂ → ℂ
  R : ℝ
  negative : R<0
  meromorphic : ∀ s, MeromorphicAt J s
  analytic : ∀ s, s≠0 → AnalyticAt ℂ J s
  order : (-1:WithTop ℤ)≤meromorphicOrderAt J 0
  integrable : ∀ s : ℂ, s.re<R → IntegrableOn (fun t : ℝ => H t*exp (s*(t:ℂ))) (Ioi 0)
  initial : ∀ s : ℂ, s.re<R → QuantitativeArithmeticDilationLaplace.transform H s=J s

noncomputable def Data.sub {H K : ℝ → ℂ} (d : Data H) (e : Data K) : Data (H-K) where
  J := d.J-e.J
  R := min d.R e.R
  negative := lt_of_le_of_lt (min_le_left _ _) d.negative
  meromorphic := fun s => (d.meromorphic s).sub (e.meromorphic s)
  analytic := fun s hs => (d.analytic s hs).sub (e.analytic s hs)
  order := by
    rw [sub_eq_add_neg]
    have he : (-1:WithTop ℤ)≤meromorphicOrderAt (-e.J) 0 := by
      rw [← meromorphicOrderAt_neg]
      exact e.order
    exact (le_min d.order he).trans
      (meromorphicOrderAt_add (d.meromorphic 0) (e.meromorphic 0).neg)
  integrable := by
    intro s hs
    have hd := d.integrable s (hs.trans_le (min_le_left _ _))
    have he := e.integrable s (hs.trans_le (min_le_right _ _))
    change IntegrableOn (fun t : ℝ => (H t-K t)*exp (s*(t:ℂ))) (Ioi 0)
    have heq : (fun t : ℝ => (H t-K t)*exp (s*(t:ℂ)))=
        ((fun t : ℝ => H t*exp (s*(t:ℂ)))-(fun t : ℝ => K t*exp (s*(t:ℂ)))) := by
      funext t
      exact sub_mul _ _ _
    rw [heq]
    exact hd.sub he
  initial := by
    intro s hs
    have hd := d.integrable s (hs.trans_le (min_le_left _ _))
    have he := e.integrable s (hs.trans_le (min_le_right _ _))
    have hds := d.initial s (hs.trans_le (min_le_left _ _))
    have hes := e.initial s (hs.trans_le (min_le_right _ _))
    simp only [QuantitativeArithmeticDilationLaplace.transform,Pi.sub_apply,sub_mul] at hds hes ⊢
    rw [integral_sub hd he,hds,hes]

theorem nonempty_data_of_slash (k : ℕ) {a : ℕ → ℂ} (ha : PolynomialBound a)
    (ha0 : a 0=0) (g : GL (Fin 2) ℝ) (hg : (GeneralLinearGroup.det g:ℝ)=1)
    (hC : g 1 0≠0) (x : ℝ) (hx : x+g 1 1/g 1 0≠0)
    (BG : ℝ) (G : ℂ → ℂ) (hG : ∀ s, MeromorphicAt G s)
    (hGa : ∀ s, s≠(k:ℂ) → AnalyticAt ℂ G s)
    (hGo : (-1:WithTop ℤ)≤meromorphicOrderAt G (k:ℂ))
    (hGF : ∀ s, BG<s.re → G s=SmallLevelAdditive.transform a (g 0 0/g 1 0) s) :
    Nonempty (Data (fun t => ((fun z : ℍ => fourier a z) ∣[(k:ℤ)] g) (logPoint x t))) := by
  obtain ⟨BJ,J,hJ,hJa,hJo,hJF⟩ := slash_laplace_continuation k ha ha0 g hg hC x hx BG G hG hGa hGo hGF
  obtain ⟨C,B,hgrowth⟩ := fourier_logarithmic_growth k ha ha0 g hg hC x
  have hh : MDiff (fun z : ℍ => fourier a z) := by
    intro z
    exact (holomorphic ha z.im_pos).mdifferentiableAt.comp z (mdifferentiable_coe z)
  have hH := logarithmic_slash_continuous k _ hh g x
  let R : ℝ := min BJ (min (-1) (-B))
  have hRB : R≤-B := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨{
    J := J
    R := R
    negative := ?_
    meromorphic := hJ
    analytic := hJa
    order := hJo
    integrable := ?_
    initial := ?_
  }⟩
  · exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  · intro s hs
    exact QuantitativeArithmeticDilationLaplace.exponential_growth_integrable _ hH C B hgrowth s (hs.trans_le hRB)
  · intro s hs
    exact (hJF s (hs.trans_le (min_le_left _ _))).symm

#print axioms Data.sub
#print axioms nonempty_data_of_slash
end QuantitativeArithmeticSlashLaplace
end
end

/-! ## QuantitativeArithmeticSlashLaplaceDataRigidityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSlashLaplace
open Complex

theorem Data.constant {H : ℝ → ℂ} (data : Data H) (hH : Continuous H)
    (L : ℝ) (hL : 0<L) (d : ℕ) (a : ℕ → ℂ) (h0 : a 0≠0) (hd : a d≠0)
    (hrec : ∀ t : ℝ, ∑ j∈Finset.range (d+1), a j*H (t+(j:ℝ)*L)=0) :
    ∃ C : ℂ, (∀ t : ℝ, H t=C) ∧ (∑ j∈Finset.range (d+1), a j)*C=0 :=
  QuantitativeArithmeticDilationLaplace.constant_of_meromorphic_continuation H hH L hL d a h0 hd hrec
    data.J (data.meromorphic 0) data.analytic data.order data.R data.negative data.integrable data.initial

theorem Data.zero_eigenfunction {H : ℝ → ℂ} (data : Data H) (hH : Continuous H)
    (L : ℝ) (hL : 0<L) (q : ℂ) (hq : q≠0) (hq1 : q≠1)
    (heig : ∀ t : ℝ, H (t+L)=q*H t) : ∀ t : ℝ, H t=0 := by
  let a : ℕ → ℂ := fun j => if j=0 then -q else 1
  have hrec (t : ℝ) : ∑ j∈Finset.range (1+1),a j*H (t+(j:ℝ)*L)=0 := by
    norm_num [a,Finset.sum_range_succ]
    rw [heig]
    ring
  obtain ⟨C,hC,hp⟩ := data.constant hH L hL 1 a (by simpa [a] using neg_ne_zero.mpr hq) (by simp [a]) hrec
  have hs : (∑ j∈Finset.range (1+1),a j)≠0 := by
    norm_num [a,Finset.sum_range_succ]
    simpa [sub_eq_add_neg,add_comm] using sub_ne_zero.mpr (Ne.symm hq1)
  have hz := (mul_eq_zero.mp hp).resolve_left hs
  exact fun t => (hC t).trans hz
#print axioms Data.zero_eigenfunction
end QuantitativeArithmeticSlashLaplace
end
end

/-! ## QuantitativeArithmeticSlashLogRayIdentityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSlashLaplace
open Complex UpperHalfPlane
open scoped Manifold

theorem zero_of_logarithmic_ray {G : ℍ → ℂ} (hG : MDiff G)
    (hz : ∀ t : ℝ, G (logPoint 0 t)=0) : G=0 := by
  let L : ℂ → ℂ := G ∘ ofComplex
  have hL : AnalyticOnNhd ℂ L {z : ℂ | 0<z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hG).analyticOnNhd isOpen_upperHalfPlaneSet
  have hray (r : ℝ) (hr : 0<r) : L ((r:ℂ)*Complex.I)=0 := by
    have hc : ((logPoint 0 (Real.log r):ℍ):ℂ)=(r:ℂ)*Complex.I := by
      rw [logPoint_coe,Real.exp_log hr]
      simp only [ofReal_zero,zero_add,mul_comm]
    change G (ofComplex ((r:ℂ)*Complex.I))=0
    rw [← hc,ofComplex_apply]
    exact hz _
  have hI : L Complex.I=0 := by simpa using hray 1 zero_lt_one
  have hall := QuantitativeArithmeticSmallLevelThirteen.constant_of_imaginary_ray hL
    (fun r hr => (hray r hr).trans hI.symm)
  funext z
  have he := (hall z z.im_pos).trans hI
  simpa only [L,Function.comp_apply,ofComplex_apply,Pi.zero_apply] using he
#print axioms zero_of_logarithmic_ray
end QuantitativeArithmeticSlashLaplace
end
end

/-! ## QuantitativeArithmeticSlashLogLineIdentityV1 -/
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
@[expose] public noncomputable section
namespace QuantitativeArithmeticSlashLaplace
open Complex UpperHalfPlane SmallLevelNormalized
open scoped Manifold ModularForm

theorem translation_logPoint (x t : ℝ) : translation x • logPoint 0 t=logPoint x t := by
  apply UpperHalfPlane.ext
  rw [translation_point,logPoint_coe,logPoint_coe]
  push_cast
  ring

theorem constant_of_logarithmic_line {G : ℍ → ℂ} (hG : MDiff G)
    (x : ℝ) (C : ℂ) (hz : ∀ t : ℝ,G (logPoint x t)=C) : G=fun _ => C := by
  let H : ℍ → ℂ := G-(fun _ => C)
  have hH : MDiff H := hG.sub mdifferentiable_const
  have ht : MDiff (H ∣[(0:ℤ)] translation x) := hH.slash 0 (translation x)
  have hzero : H ∣[(0:ℤ)] translation x=0 := by
    apply zero_of_logarithmic_ray ht
    intro t
    rw [translation_slash,translation_logPoint]
    exact sub_eq_zero.mpr (hz t)
  have hh : H=0 := (SlashAction.slash_eq_zero_iff _ _ _).mp hzero
  exact sub_eq_zero.mp hh
#print axioms constant_of_logarithmic_line
end QuantitativeArithmeticSlashLaplace
end
end
