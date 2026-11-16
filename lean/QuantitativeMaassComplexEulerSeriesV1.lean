module

public import QuantitativeMaassComplexBesselDecayV1
public import QuantitativeMaassEulerFourierV1
public import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace QuantitativeMaass

/-- Actual two-complex-coordinate extension of one Fourier--Bessel term. -/
def complexEulerTerm (b : ℕ → ℂ) (r : ℝ) (σ n : ℕ) (x y : ℂ) : ℂ :=
  b (n+1)*principalComplexMoment 0 r (((2*Real.pi*((n+1:ℕ):ℝ):ℝ):ℂ)*y)*
    complexEulerPhase σ (n+1) x

def complexEulerCore (b : ℕ → ℂ) (r : ℝ) (σ : ℕ) (x y : ℂ) : ℂ :=
  ∑' n,complexEulerTerm b r σ n x y

/-- Explicit summable tube-domain bound, depending only on the positive gap
between Re(y) and abs(Im(x)). -/
theorem complexEulerTerm_bound (b : ℕ → ℂ) (r : ℝ) (σ n : ℕ)
    (a : ℝ) (ha : 0<a) (x y : ℂ) (hgap : a≤y.re-|x.im|) :
    ‖complexEulerTerm b r σ n x y‖≤2*principalMomentMajorant b 0 0 (2*Real.pi) a n := by
  let c := 2*Real.pi
  let m : ℝ := ((n+1:ℕ):ℝ)
  have hc : 0<c := by dsimp [c]; positivity
  have hm : 1≤m := by dsimp [m]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hy : a≤y.re := by linarith [abs_nonneg x.im]
  have hy0 : 0<y.re := ha.trans_le hy
  have hre : (((c*m:ℝ):ℂ)*y).re=c*m*y.re := by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hbase : c*a≤(((c*m:ℝ):ℂ)*y).re := by
    rw [hre]
    calc
      c*a ≤ c*y.re := mul_le_mul_of_nonneg_left hy hc.le
      _ = c*1*y.re := by ring
      _ ≤ _ := by gcongr
  have hmoment := principalComplexMoment_decay_from 0 r (c*a) (((c*m:ℝ):ℂ)*y) (mul_pos hc ha) hbase
  have hphase := complexEulerPhase_norm_bound σ (n+1) x
  have he : Real.exp (c*a-(((c*m:ℝ):ℂ)*y).re)*Real.exp (c*m*|x.im|)≤
      Real.exp (c*a)*Real.exp (-(c*a)*m) := by
    rw [←Real.exp_add,←Real.exp_add,hre]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hgap (show 0≤c*m by positivity)]
  have hM : 0≤MaassKBessel.moment 0 0 (c*a) := MaassKBessel.zero_moment_nonneg _ _
  change ‖b (n+1)*principalComplexMoment 0 r (((c*m:ℝ):ℂ)*y)*complexEulerPhase σ (n+1) x‖≤_
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (‖b (n+1)‖*(Real.exp (c*a-(((c*m:ℝ):ℂ)*y).re)*MaassKBessel.moment 0 0 (c*a)))*
        (2*Real.exp (c*m*|x.im|)) := by gcongr
    _ = (2*‖b (n+1)‖*MaassKBessel.moment 0 0 (c*a))*
        (Real.exp (c*a-(((c*m:ℝ):ℂ)*y).re)*Real.exp (c*m*|x.im|)) := by ring
    _ ≤ (2*‖b (n+1)‖*MaassKBessel.moment 0 0 (c*a))*
        (Real.exp (c*a)*Real.exp (-(c*a)*m)) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by unfold principalMomentMajorant; simp only [pow_zero,mul_one]; ring

theorem complexEulerTerm_summable {b : ℕ → ℂ} (hb : MaassOriginal.PolynomialGrowth b)
    (r : ℝ) (σ : ℕ) (x y : ℂ) (hgap : |x.im|<y.re) :
    Summable (fun n => complexEulerTerm b r σ n x y) := by
  let a := y.re-|x.im|
  have ha : 0<a := sub_pos.mpr hgap
  apply Summable.of_norm_bounded
    ((principalMomentMajorant_summable hb 0 0 (2*Real.pi) a (by positivity) ha).mul_left 2)
  intro n
  exact complexEulerTerm_bound b r σ n a ha x y le_rfl

theorem complexEulerTerm_ofReal (b : ℕ → ℂ) (r : ℝ) (σ n : ℕ) (x y : ℝ) :
    complexEulerTerm b r σ n (x:ℂ) (y:ℂ)=principalEulerTerm b r σ n (x,y) := by
  unfold complexEulerTerm principalEulerTerm
  rw [←Complex.ofReal_mul,principalComplexMoment_ofReal,complexEulerPhase_ofReal]

theorem complexEulerCore_ofReal (b : ℕ → ℂ) (r : ℝ) (σ : ℕ) (x y : ℝ) :
    complexEulerCore b r σ (x:ℂ) (y:ℂ)=principalEulerCore b r σ (x,y) := by
  unfold complexEulerCore principalEulerCore
  exact tsum_congr (fun n => complexEulerTerm_ofReal b r σ n x y)

#print axioms complexEulerTerm_bound
#print axioms complexEulerTerm_summable
#print axioms complexEulerTerm_ofReal
#print axioms complexEulerCore_ofReal

end QuantitativeMaass
