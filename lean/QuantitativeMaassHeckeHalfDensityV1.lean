module

public import QuantitativeMaassCuspPlaneWaveDefectV1
public import QuantitativeMaassCuspWaveIntertwiningV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticClassicalPetersson AsymptoticCongruenceStrip
open scoped Topology MatrixGroups InnerProductSpace

namespace QuantitativeMaass

theorem halfWeight_sqrt_exp (x : ℝ) :
    Real.exp (-x/2)*Real.sqrt (Real.exp x)=1 := by
  rw [← Real.exp_half,← Real.exp_add]
  have he : -x/2+x/2=0 := by ring
  rw [he,Real.exp_zero]

theorem logHalfDensity_shape (C : ℝ → ℂ) (y : ℝ) (hy : 0<y) :
    C y=Real.sqrt y • logHalfDensity C (Real.log y) := by
  unfold logHalfDensity
  rw [Real.exp_log hy,Complex.real_smul,← mul_assoc,← Complex.ofReal_mul]
  have h := halfWeight_sqrt_exp (Real.log y)
  rw [Real.exp_log hy] at h
  rw [mul_comm (Real.sqrt y),h,Complex.ofReal_one,one_mul]

/-- The previously checked cusp correspondence acts by literal log-height
translations on the actual scalar half-density, without a shape assumption. -/
theorem normalizedCuspHecke_logHalfDensity (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (hpres : (p:ZMod N)=1) (s : SL(2,ℤ))
    (f : ℍ → ℂ) (hf : Continuous f)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, f (g.val • z)=f z) (x : ℝ) :
    logHalfDensity (cuspConstant N s (normalizedCuspHecke N p f)) x=
      logHalfDensity (cuspConstant N s f) (x+Real.log (p:ℝ))+
        logHalfDensity (cuspConstant N s f) (x-Real.log (p:ℝ)) := by
  change (Real.exp (-x/2):ℂ)*cuspConstant N s (normalizedCuspHecke N p f) (Real.exp x)=_
  rw [normalizedCuspHecke_halfDensity N p hNp hpres s f hf hinv
    (logHalfDensity (cuspConstant N s f)) (logHalfDensity_shape _) _ (Real.exp_pos x),
    Real.log_exp,Complex.real_smul,← mul_assoc,← Complex.ofReal_mul,
    halfWeight_sqrt_exp,Complex.ofReal_one,one_mul]

theorem heckeRepresentative_continuous (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (hNp : (N:ZMod p)≠0)
    (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (f : AutomorphicL2.representatives (gamma N) (quotientMeasure N))
    (hf : Continuous f.val) :
    Continuous (HeckeL2.heckeRepresentative N p hN hpN a b hab f).val := by
  rw [← normalizedCuspHecke_eq_representative N p hN hpN hNp a b hab f]
  exact normalizedCuspHecke_continuous N p f.val hf

#print axioms normalizedCuspHecke_logHalfDensity
#print axioms heckeRepresentative_continuous

end QuantitativeMaass
