module

public import AsymptoticCylinderSeriesV1
public import FinitenessFourierConstructionV1

set_option autoImplicit false
set_option maxHeartbeats 200000
@[expose] public section

namespace AsymptoticCylinder

open MeasureTheory Set Filter AsymptoticFourierNorm FinitenessPolynomialSeries

/-- The disk coordinate on the translation cylinder. -/
noncomputable def qCylinder (z : Cylinder) : ℂ :=
  fourier (T:=1) 1 z.1 * (Real.exp (-2*Real.pi*z.2):ℂ)

theorem qCylinder_norm {z : Cylinder} (hz : 0<z.2) : ‖qCylinder z‖<1 := by
  have hf : ‖fourier (T:=1) 1 z.1‖=1 := Circle.norm_coe _
  rw [qCylinder,norm_mul,hf,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])

theorem fourier_nat_pow (n : ℕ) (x : AddCircle (1:ℝ)) :
    fourier (n:ℤ) x=(fourier 1 x)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ,fourier_add,ih,pow_succ]

/-- For even holomorphic weight the square-root radial definition equals
the expected power of height, capped weight and decaying exponential. -/
theorem sqrt_density_even (h t : ℕ) (r : ℝ) {ε y : ℝ} (hε : 0<ε) (hy : 0≤y) :
    Real.sqrt (density (2*h) t r ε y)=y^h*(min (y/ε) 1)^t*Real.exp (-(r*y)/2) := by
  have hc : 0≤min (y/ε) 1 := le_min (div_nonneg hy hε.le) zero_le_one
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (density_nonneg (2*h) t r hε hy)]
  have he : Real.exp (-(r*y)/2)^2=Real.exp (-(r*y)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [density,AsymptoticGammaTail.kernel,mul_pow,he,← pow_mul]
  rw [Nat.mul_comm h 2,Nat.mul_comm t 2]
  ring

theorem mode_even_eq_qCylinder (h t n : ℕ) {ε : ℝ} (hε : 0<ε)
    {z : Cylinder} (hz : 0≤z.2) :
    mode (2*h) t n (4*Real.pi) ε z=
      (z.2^h*(min (z.2/ε) 1)^t:ℝ)*qCylinder z^(n+1) := by
  rw [mode,sqrt_density_even h t _ hε hz,qCylinder,mul_pow,← fourier_nat_pow]
  simp only [Complex.ofReal_mul,← Complex.ofReal_pow,← Real.exp_nat_mul]
  have he : -((4*Real.pi*(n+1:ℕ))*z.2)/2=(n+1:ℕ)*(-2*Real.pi*z.2) := by ring
  rw [he]
  ring

theorem modes_sum_eq_disk (h t : ℕ) {ε : ℝ} (hε : 0<ε)
    (a : ℕ → ℂ) (ha0 : a 0=0) (hpoly : PolynomialBound a)
    (z : Cylinder) (hz : 0<z.2) :
    (∑' n,a (n+1)*mode (2*h) t n (4*Real.pi) ε z)=
      (z.2^h*(min (z.2/ε) 1)^t:ℝ)*sum a (qCylinder z) := by
  have hsum : Summable (fun n => a n*qCylinder z^n) :=
    FinitenessPolynomialSeries.summable hpoly (qCylinder_norm hz)
  have hshift : Summable (fun n => a (n+1)*qCylinder z^(n+1)) := (summable_nat_add_iff 1).mpr hsum
  have he := tsum_eq_zero_add' (f:=fun n : ℕ => a n*qCylinder z^n) hshift
  rw [ha0,zero_mul,zero_add] at he
  rw [sum_eq_tsum,he,← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [mode_even_eq_qCylinder h t n hε hz.le]
  ring

/-- The L² sum is the literal holomorphic Fourier series multiplied by
w_t y^(k/2-1), on the cylinder. -/
theorem fourierSum_eq_disk_ae (h t d : ℕ) {ε A : ℝ} (hε : 0<ε) (hA : 0≤A)
    (hdegree : 2*d+4≤2*h+2*t+1) (a : ℕ → ℂ) (ha0 : a 0=0)
    (ha : ∀ n,‖a (n+1)‖≤A*(n+1:ℕ)^d) (hpoly : PolynomialBound a) :
    fourierSum (2*h) t (by positivity : 0<4*Real.pi) hε a =ᵐ[measure]
      (fun z => (z.2^h*(min (z.2/ε) 1)^t:ℝ)*sum a (qCylinder z)) :=
  (fourierSum_coeFn (2*h) t d (by positivity) hε hA hdegree a ha).trans
    (height_positive.mono (fun z hz => modes_sum_eq_disk h t hε a ha0 hpoly z hz))

/-- The degree furnished by direct-height reconstruction is h+1+s for
weight k=2h+2. A single choice t=s+3 works for every weight. -/
theorem uniform_weight_fourierSum_eq_disk_ae (h s : ℕ) {ε A : ℝ} (hε : 0<ε) (hA : 0≤A)
    (a : ℕ → ℂ) (ha0 : a 0=0) (ha : ∀ n,‖a (n+1)‖≤A*(n+1:ℕ)^(h+1+s))
    (hpoly : PolynomialBound a) :
    fourierSum (2*h) (s+3) (by positivity : 0<4*Real.pi) hε a =ᵐ[measure]
      (fun z => (z.2^h*(min (z.2/ε) 1)^(s+3):ℝ)*sum a (qCylinder z)) :=
  fourierSum_eq_disk_ae h (s+3) (h+1+s) hε hA (by omega) a ha0 ha hpoly

/-- The cylinder disk coordinate is exactly the q-parameter used by the
existing holomorphic finiteness proof. -/
theorem qCylinder_coe (x y : ℝ) :
    qCylinder ((x:AddCircle (1:ℝ)),y)=Function.Periodic.qParam 1 ((x:ℂ)+(y:ℂ)*Complex.I) := by
  rw [qCylinder,fourier_coe_apply,Function.Periodic.qParam]
  simp only [Complex.ofReal_one,div_one,Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq,sub_eq_add_neg]

/-- On any real lift of the cylinder, the conjugated series is the
original holomorphic function from the existing Fourier construction. -/
theorem modes_sum_eq_original_fourier (h t : ℕ) {ε y : ℝ} (hε : 0<ε) (hy : 0<y)
    (a : ℕ → ℂ) (ha0 : a 0=0) (hpoly : PolynomialBound a) (x : ℝ) :
    (∑' n,a (n+1)*mode (2*h) t n (4*Real.pi) ε ((x:AddCircle (1:ℝ)),y))=
      (y^h*(min (y/ε) 1)^t:ℝ)*FinitenessFourierConstruction.fourier a ((x:ℂ)+(y:ℂ)*Complex.I) := by
  rw [modes_sum_eq_disk h t hε a ha0 hpoly _ hy,qCylinder_coe]
  rfl

#print axioms modes_sum_eq_original_fourier
#print axioms mode_even_eq_qCylinder
#print axioms uniform_weight_fourierSum_eq_disk_ae

end AsymptoticCylinder
