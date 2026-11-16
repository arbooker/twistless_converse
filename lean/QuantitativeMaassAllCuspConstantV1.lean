module

public import QuantitativeMaassCuspHeckeProfileV1

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix UpperHalfPlane
open AsymptoticCongruenceStrip
open scoped MatrixGroups BigOperators

namespace QuantitativeMaass

/-- The normalized actual p+1 correspondence in common-period cusp representatives. -/
def normalizedCuspHecke (N p : ℕ) [Fact p.Prime] (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z => (Real.sqrt (p:ℝ))⁻¹ • cuspHeckeSum N p f z

/-- The average constant term in any integral cusp chart. The period N is
rescaled to one; thus this is the average, rather than the unnormalized
integral over an interval of length N. -/
def cuspConstant (N : ℕ) (s : SL(2,ℤ)) (f : ℍ → ℂ) (y : ℝ) : ℂ :=
  zeroFourier (cuspProfile N s f) y

theorem cuspProfile_smul (N : ℕ) (s : SL(2,ℤ)) (f : ℍ → ℂ) (c : ℝ) :
    cuspProfile N s (fun z => c • f z) = fun x y => c • cuspProfile N s f x y := by
  funext x y
  by_cases hy : 0<y <;> simp [cuspProfile,hy]

theorem cuspProfile_continuous (N : ℕ) (s : SL(2,ℤ)) (f : ℍ → ℂ)
    (hf : Continuous f) (y : ℝ) : Continuous (fun x => cuspProfile N s f x y) := by
  by_cases hy : 0<y
  · have hc : Continuous (fun x : ℝ => horocyclePoint ((N:ℝ)*x) y hy) := by
      apply continuous_induced_rng.mpr
      change Continuous (fun x : ℝ => (⟨(N:ℝ)*x,y⟩ : ℂ))
      have he : (fun x : ℝ => (⟨(N:ℝ)*x,y⟩ : ℂ)) =
          (fun x : ℝ => (((N:ℝ)*x : ℝ):ℂ)+(y:ℂ)*Complex.I) := by
        funext x
        apply Complex.ext <;> simp
      rw [he]
      fun_prop
    simp only [cuspProfile,dite_eq_left hy]
    exact hf.comp ((continuous_const_smul (SpecialLinearGroup.mapGL ℝ s)).comp hc)
  · simp only [cuspProfile,dite_eq_right hy]
    exact continuous_const

/-- Exact zero-channel intertwining at every integral cusp. The arithmetic
hypotheses produce the branch permutation; continuity gives the ordinary
interval integrals. No cusp-wise intertwining law is assumed. -/
theorem normalizedCuspHecke_constant (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (hpN : (p:ZMod N)=1)
    (s : SL(2,ℤ)) (f : ℍ → ℂ) (hf : Continuous f)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, f (g.val • z)=f z) (y : ℝ) :
    cuspConstant N s (normalizedCuspHecke N p f) y =
      (Real.sqrt (p:ℝ))⁻¹ • cuspConstant N s f ((p:ℝ)*y) +
      Real.sqrt (p:ℝ) • cuspConstant N s f (y/p) := by
  have hprofile : cuspProfile N s (normalizedCuspHecke N p f) =
      normalizedHecke p (cuspProfile N s f) := by
    unfold normalizedCuspHecke
    rw [cuspProfile_smul]
    funext x y
    exact cuspProfile_heckeSum N p hNp hpN s f hinv x y
  unfold cuspConstant
  rw [hprofile]
  exact normalizedHecke_zeroFourier _ (cuspProfile_continuous N s f hf)
    (cuspProfile_periodic N s f hinv) p (Fact.out : p.Prime).pos y

/-- On half-density constant terms, the same actual correspondence is the
sum of the two translations by log p, at every integral cusp. -/
theorem normalizedCuspHecke_halfDensity (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (hpN : (p:ZMod N)=1)
    (s : SL(2,ℤ)) (f : ℍ → ℂ) (hf : Continuous f)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, f (g.val • z)=f z)
    (a : ℝ → ℂ) (hshape : ∀ y, 0<y → cuspConstant N s f y=Real.sqrt y • a (Real.log y))
    (y : ℝ) (hy : 0<y) :
    cuspConstant N s (normalizedCuspHecke N p f) y = Real.sqrt y •
      (a (Real.log y+Real.log (p:ℝ))+a (Real.log y-Real.log (p:ℝ))) := by
  have hprofile : cuspProfile N s (normalizedCuspHecke N p f) =
      normalizedHecke p (cuspProfile N s f) := by
    unfold normalizedCuspHecke
    rw [cuspProfile_smul]
    funext x y
    exact cuspProfile_heckeSum N p hNp hpN s f hinv x y
  unfold cuspConstant
  rw [hprofile]
  exact normalizedHecke_halfDensity _ a (cuspProfile_continuous N s f hf)
    (cuspProfile_periodic N s f hinv) hshape p (Fact.out : p.Prime).pos y hy

#print axioms normalizedCuspHecke_constant
#print axioms normalizedCuspHecke_halfDensity

end QuantitativeMaass
