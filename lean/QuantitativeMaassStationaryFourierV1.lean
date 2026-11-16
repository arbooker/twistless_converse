module

public import QuantitativeMaassStationaryMeanV1
public import Mathlib.Analysis.Fourier.AddCircle

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace QuantitativeMaass

section General
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Modulation by a unitary character preserves stationarity of the
actual Hilbert-valued Gram kernel. -/
theorem stationary_column_modulation (c : ℝ→H)
    (hs : ∀ r x y,inner ℂ (c (x+r)) (c (y+r))=inner ℂ (c x) (c y))
    (γ : ℝ→ℂ) (hadd : ∀ x y,γ (x+y)=γ x*γ y)
    (hu : ∀ x,star (γ x)*γ x=1) (r x y : ℝ) :
    inner ℂ (γ (x+r) • c (x+r)) (γ (y+r) • c (y+r))=
      inner ℂ (γ x • c x) (γ y • c y) := by
  simp only [inner_smul_left,inner_smul_right,hadd,map_mul,hs,starRingEnd_apply]
  calc
    _=(star (γ r)*γ r)*(star (γ x)*γ y*inner ℂ (c x) (c y)) := by ring
    _=_ := by rw [hu,one_mul]; ring

/-- Every Fourier coefficient of a stationary periodic Gram kernel is
the squared norm of the corresponding modulated column mean. -/
theorem stationary_column_character_energy (c : ℝ→H) (hc : Continuous c)
    (hp : Function.Periodic c 1)
    (hs : ∀ r x y,inner ℂ (c (x+r)) (c (y+r))=inner ℂ (c x) (c y))
    (γ : ℝ→ℂ) (hγ : Continuous γ) (hγp : Function.Periodic γ 1)
    (hadd : ∀ x y,γ (x+y)=γ x*γ y) (hu : ∀ x,star (γ x)*γ x=1) (h0 : γ 0=1) :
    (∫ y in Icc (0:ℝ) 1,γ y*inner ℂ (c 0) (c y)).re=
      ‖∫ y in Icc (0:ℝ) 1,γ y • c y‖^2 := by
  let d := fun x => γ x • c x
  have hd : Continuous d := hγ.smul hc
  have hdp : Function.Periodic d 1 := fun x => by simp only [d,hγp x,hp x]
  have hds : ∀ r x y,inner ℂ (d (x+r)) (d (y+r))=inner ℂ (d x) (d y) :=
    stationary_column_modulation c hs γ hadd hu
  have he := congrArg Complex.re (stationary_column_mean_pairing d hd hdp hds 0)
  rw [←integral_inner hd.integrableOn_Icc] at he
  simp only [d,h0,one_smul,inner_smul_right] at he
  exact he.trans (inner_self_eq_norm_sq (𝕜:=ℂ) _)

end General

/-- The ordinary integer Fourier character, on real coordinates. -/
def periodCharacter (n : ℤ) (x : ℝ) : ℂ :=
  fourier n (x : AddCircle (1:ℝ))

theorem periodCharacter_continuous (n : ℤ) : Continuous (periodCharacter n) :=
  (fourier n).continuous.comp continuous_quotient_mk'

theorem periodCharacter_periodic (n : ℤ) : Function.Periodic (periodCharacter n) 1 := by
  intro x
  simp only [periodCharacter,AddCircle.coe_add_period]

theorem periodCharacter_add (n : ℤ) (x y : ℝ) :
    periodCharacter n (x+y)=periodCharacter n x*periodCharacter n y := by
  simp only [periodCharacter,AddCircle.coe_add,fourier_apply,zsmul_add,
    AddCircle.toCircle_add,Circle.coe_mul]

theorem periodCharacter_unit (n : ℤ) (x : ℝ) :
    star (periodCharacter n x)*periodCharacter n x=1 := by
  simp only [periodCharacter,Complex.star_def,←fourier_neg,←fourier_add,
    neg_add_cancel,fourier_zero]

theorem periodCharacter_zero (n : ℤ) : periodCharacter n 0=1 := by
  simp only [periodCharacter,AddCircle.coe_zero,fourier_eval_zero]

#print axioms stationary_column_modulation
#print axioms stationary_column_character_energy
#print axioms periodCharacter_add
#print axioms periodCharacter_unit

end QuantitativeMaass
