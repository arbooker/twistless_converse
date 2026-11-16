module

public import QuantitativeMaassCuspBranchCoordinatesV1
public import QuantitativeMaassHeckeConstantV1

set_option autoImplicit false
@[expose] public noncomputable section

open Matrix UpperHalfPlane
open AsymptoticCongruenceLabels AsymptoticCongruenceStrip
open AsymptoticClassicalCusp
open scoped MatrixGroups BigOperators

namespace QuantitativeMaass

/-- The actual function in an integral cusp chart, with the common period
N rescaled to one. The zero extension at nonpositive height is only a
convenience for the Cartesian constant-term API. -/
def cuspProfile (N : ℕ) (s : SL(2,ℤ)) (f : ℍ → ℂ) (x y : ℝ) : ℂ :=
  if hy : 0<y then f (SpecialLinearGroup.mapGL ℝ s • horocyclePoint ((N:ℝ)*x) y hy) else 0

theorem cuspProfile_periodic (N : ℕ) (s : SL(2,ℤ)) (f : ℍ → ℂ)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, f (g.val • z)=f z) (y : ℝ) :
    Function.Periodic (fun x => cuspProfile N s f x y) 1 := by
  intro x
  by_cases hy : 0<y
  · simp only [cuspProfile,dite_eq_left hy]
    have hh := cusp_chart_periodic N s f hinv y hy ((N:ℝ)*x)
    dsimp only at hh
    rw [integralLabel_action,integralLabel_action] at hh
    rw [show (N:ℝ)*(x+1)=(N:ℝ)*x+N by ring]
    exact hh
  · simp [cuspProfile,hy]

theorem sum_zmod_val (p : ℕ) [NeZero p] (F : ℕ → ℂ) :
    (∑ u : ZMod p, F u.val)=∑ a ∈ Finset.range p, F a := by
  cases p with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ p => exact Fin.sum_univ_eq_sum_range F (p+1)

/-- The actual all-cusp Hecke correspondence becomes precisely the standard
Cartesian p+1 formula, not merely a formal shift operator. -/
theorem cuspProfile_heckeSum (N p : ℕ) [Fact p.Prime]
    (hNp : (N:ZMod p)≠0) (hpN : (p:ZMod N)=1)
    (s : SL(2,ℤ)) (f : ℍ → ℂ)
    (hinv : ∀ g : gamma N, ∀ z : ℍ, f (g.val • z)=f z) (x y : ℝ) :
    (Real.sqrt (p:ℝ))⁻¹ • cuspProfile N s (cuspHeckeSum N p f) x y =
      normalizedHecke p (cuspProfile N s f) x y := by
  have hpR : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  by_cases hy : 0<y
  · have hpy := mul_pos hpR hy
    have hyp := div_pos hy hpR
    simp only [cuspProfile,dite_eq_left hy,normalizedHecke,dite_eq_left hpy,dite_eq_left hyp]
    congr 1
    rw [cuspHeckeSum_chart N p hNp hpN s f hinv,cuspHeckeSum,Fintype.sum_option]
    rw [cuspBranchGL_none_point]
    have hfirst : (p:ℝ)*((N:ℝ)*x)=(N:ℝ)*((p:ℝ)*x) := by ring
    rw [hfirst]
    congr 1
    simp_rw [cuspBranchGL_some_point]
    have hcoord (u : ZMod p) : ((N:ℝ)*x+(N:ℝ)*u.val)/p=
        (N:ℝ)*((x+(u.val:ℝ))/p) := by ring
    simp_rw [hcoord]
    exact sum_zmod_val p (fun a => f (SpecialLinearGroup.mapGL ℝ s •
      horocyclePoint ((N:ℝ)*((x+(a:ℝ))/p)) (y/p) hyp))
  · have hpy : ¬0<(p:ℝ)*y := by nlinarith [le_of_not_gt hy]
    have hyp : ¬0<y/(p:ℝ) := by exact not_lt.mpr (div_nonpos_of_nonpos_of_nonneg
      (le_of_not_gt hy) hpR.le)
    simp [cuspProfile,hy,normalizedHecke,hpy,hyp]

#print axioms cuspProfile_periodic
#print axioms cuspProfile_heckeSum

end QuantitativeMaass
