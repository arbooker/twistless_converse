module

public import QuantitativeMaassAllCuspOperatorV1

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix UpperHalfPlane MeasureTheory
open AsymptoticCongruenceStrip
open scoped MatrixGroups BigOperators Interval

namespace QuantitativeMaass

def planeWavePair (r : ℝ) (A B : ℂ) (u : ℝ) : ℂ :=
  A*Complex.exp (((r*u:ℝ):ℂ)*Complex.I) +
  B*Complex.exp ((((-r)*u:ℝ):ℂ)*Complex.I)

theorem planeWavePair_shift (r u t : ℝ) (A B : ℂ) :
    planeWavePair r A B (u+t)+planeWavePair r A B (u-t)=
      (2*Complex.cos ((r*t:ℝ):ℂ))*planeWavePair r A B u := by
  have hp := symmetric_shift_exponential r u t
  have hn := symmetric_shift_exponential (-r) u t
  have hc : Complex.cos (((-r)*t:ℝ):ℂ)=Complex.cos ((r*t:ℝ):ℂ) := by simp
  calc
    _ = A*(Complex.exp (((r*(u+t):ℝ):ℂ)*Complex.I)+
        Complex.exp (((r*(u-t):ℝ):ℂ)*Complex.I)) +
      B*(Complex.exp ((((-r)*(u+t):ℝ):ℂ)*Complex.I)+
        Complex.exp ((((-r)*(u-t):ℝ):ℂ)*Complex.I)) := by unfold planeWavePair; ring
    _ = _ := by rw [hp,hn,hc]; unfold planeWavePair; ring

theorem normalizedCuspHecke_continuous (N p : ℕ) [Fact p.Prime]
    (f : ℍ → ℂ) (hf : Continuous f) : Continuous (normalizedCuspHecke N p f) := by
  unfold normalizedCuspHecke cuspHeckeSum
  exact (continuous_finsetSum _ (fun j _ =>
    hf.comp (continuous_const_smul (cuspBranchGL N p j)))).const_smul ((Real.sqrt (p:ℝ))⁻¹)

theorem cuspConstant_const_mul (N : ℕ) (s : SL(2,ℤ)) (f : ℍ → ℂ)
    (c : ℂ) (y : ℝ) : cuspConstant N s (fun z => c*f z) y=c*cuspConstant N s f y := by
  have he : cuspProfile N s (fun z => c*f z) = fun x y => c*cuspProfile N s f x y := by
    funext x y
    by_cases hy : 0<y <;> simp [cuspProfile,hy]
  unfold cuspConstant zeroFourier
  rw [he]
  exact intervalIntegral.integral_const_mul _ _

theorem cuspConstant_sub (N : ℕ) (s : SL(2,ℤ)) (f g : ℍ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (y : ℝ) :
    cuspConstant N s (fun z => f z-g z) y=cuspConstant N s f y-cuspConstant N s g y := by
  have he : cuspProfile N s (fun z => f z-g z) =
      fun x y => cuspProfile N s f x y-cuspProfile N s g x y := by
    funext x y
    by_cases hy : 0<y <;> simp [cuspProfile,hy]
  unfold cuspConstant zeroFourier
  rw [he]
  exact intervalIntegral.integral_sub
    ((cuspProfile_continuous N s f hf y).intervalIntegrable _ _)
    ((cuspProfile_continuous N s g hg y).intervalIntegrable _ _)

/-- For an actual continuous automorphic function whose constant term is a
pair of height plane waves, the Hecke-minus-cosine defect has zero constant
term. The plane-wave form is explicit; no Hecke intertwining law is assumed.
This does not identify a wave operator or construct Eisenstein series. -/
theorem cuspPlaneWave_defect_zero (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (hpN : (p:ZMod N)=1)
    (s : SL(2,ℤ)) (f : ℍ → ℂ) (hf : Continuous f)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, f (g.val • z)=f z)
    (r : ℝ) (A B : ℂ)
    (hshape : ∀ y, 0<y → cuspConstant N s f y=
      Real.sqrt y • planeWavePair r A B (Real.log y))
    (y : ℝ) (hy : 0<y) :
    cuspConstant N s (fun z => normalizedCuspHecke N p f z-
      (2*Complex.cos ((r*Real.log (p:ℝ):ℝ):ℂ))*f z) y=0 := by
  have hc : Continuous (fun z : ℍ => (2*Complex.cos ((r*Real.log (p:ℝ):ℝ):ℂ))*f z) :=
    continuous_const.mul hf
  have hs := cuspConstant_sub N s (normalizedCuspHecke N p f)
    (fun z => (2*Complex.cos ((r*Real.log (p:ℝ):ℝ):ℂ))*f z)
    (normalizedCuspHecke_continuous N p f hf) hc y
  rw [hs,cuspConstant_const_mul,
    normalizedCuspHecke_halfDensity N p hNp hpN s f hf hinv
      (planeWavePair r A B) hshape y hy,
    planeWavePair_shift,hshape y hy]
  change (((Real.sqrt y:ℝ):ℂ)*((2*Complex.cos ((r*Real.log (p:ℝ):ℝ):ℂ))*
    planeWavePair r A B (Real.log y))) -
    (2*Complex.cos ((r*Real.log (p:ℝ):ℝ):ℂ))*
      (((Real.sqrt y:ℝ):ℂ)*planeWavePair r A B (Real.log y))=0
  ring

#print axioms cuspPlaneWave_defect_zero

end QuantitativeMaass
