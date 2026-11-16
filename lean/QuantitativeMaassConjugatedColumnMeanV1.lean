module

public import QuantitativeMaassConjugatedColumnBoundV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory ContinuousLinearMap

namespace QuantitativeMaass.LogBands

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (l : α → ℝ) (hl : Measurable l)

/-- Along a curve of constant weight, conjugation commutes with the
literal Hilbert-valued period average. -/
theorem conjugatedColumn_curve_mean (c : α → Lp ℂ 2 μ) (J : ℕ) (x : α)
    (γ : ℝ → α) (hγ : ∀ y,l (γ y)=l x)
    (hc : IntegrableOn (fun y => c (γ y)) (Icc (0:ℝ) 1) volume) :
    (∫ y in Icc (0:ℝ) 1,conjugatedColumn μ l hl c J (γ y))=
      conjugatedColumn μ l hl (fun _ => ∫ y in Icc (0:ℝ) 1,c (γ y)) J x := by
  simp only [conjugatedColumn,hγ]
  have hi : IntegrableOn (fun y => (Real.exp (l x):ℂ) • c (γ y)) (Icc (0:ℝ) 1) volume :=
    hc.smul (Real.exp (l x):ℂ)
  rw [(rowInverseSum μ l hl J ⌊l x⌋).adjoint.integral_comp_comm hi,integral_smul]

/-- The centered weighted column has the same uniform propagation bound
as any column difference, without assuming a bounded global inverse weight. -/
theorem conjugatedColumn_centered_bound (c : α → Lp ℂ 2 μ) (J : ℕ) (x : α)
    (γ : ℝ → α) (hγ : ∀ y,l (γ y)=l x)
    (hc : IntegrableOn (fun y => c (γ y)) (Icc (0:ℝ) 1) volume) :
    ‖conjugatedColumn μ l hl c J x-
      ∫ y in Icc (0:ℝ) 1,conjugatedColumn μ l hl c J (γ y)‖≤
      (((2*J+1:ℕ):ℝ)*Real.exp ((J:ℝ)+1))*
        ‖c x-∫ y in Icc (0:ℝ) 1,c (γ y)‖ := by
  rw [conjugatedColumn_curve_mean μ l hl c J x γ hγ hc]
  exact conjugatedColumn_sub_bound μ l hl c (fun _ => ∫ y in Icc (0:ℝ) 1,c (γ y)) J x

#print axioms conjugatedColumn_curve_mean
#print axioms conjugatedColumn_centered_bound

end QuantitativeMaass.LogBands
