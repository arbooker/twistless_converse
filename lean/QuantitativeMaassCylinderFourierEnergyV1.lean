module

public import QuantitativeMaassStationaryFourierV1
public import QuantitativeMaassCylinderStationaryV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane
open AsymptoticClassicalPetersson
open scoped Topology ContDiff SchwartzMap

namespace QuantitativeMaass

/-- Integer Fourier coefficients of the actual cylinder square kernel
are squared norms of modulated Hilbert columns. -/
theorem cylinderTimeSquare_period_coefficient (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (n : ℤ) (z : ℍ) :
    (∫ x in Icc (0:ℝ) 1,periodCharacter n x*
      radialPoincareKernel 0 (abelProfile (evenCoshLift (timeConvolution f f))) (x+ᵥz) z).re=
      ‖∫ x in Icc (0:ℝ) 1,periodCharacter n x • cylinderTimeColumn f hc he R hR hs (x+ᵥz)‖^2 := by
  let c := fun x : ℝ => cylinderTimeColumn f hc he R hR hs (x+ᵥz)
  have hcont : Continuous c :=
    (cylinderAbelColumn_continuous _ _ R hR _).comp (cylinder_vadd_continuous z)
  have hstat (r x y : ℝ) : inner ℂ (c (x+r)) (c (y+r))=inner ℂ (c x) (c y) := by
    dsimp only [c]
    rw [cylinderTimeSquare_kernel_cross f hc he hr R hR hs,
      cylinderTimeSquare_kernel_cross f hc he hr R hR hs]
    rw [add_comm x r,add_comm y r,add_vadd,add_vadd,cylinderRadialKernel_translation]
  have hh := stationary_column_character_energy c hcont
    (cylinderTimeColumn_periodic f hc he R hR hs z) hstat
    (periodCharacter n) (periodCharacter_continuous n) (periodCharacter_periodic n)
    (periodCharacter_add n) (periodCharacter_unit n) (periodCharacter_zero n)
  simpa only [c,zero_vadd,cylinderTimeSquare_kernel_cross f hc he hr R hR hs] using hh

theorem cylinderTimeSquare_period_coefficient_nonneg (f : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (f : ℝ→ℂ)) (he : Function.Even f)
    (hr : ∀ t,star (f t)=f t) (R : ℝ) (hR : 0≤R)
    (hs : Function.support f⊆Icc (-R) R) (n : ℤ) (z : ℍ) :
    0≤(∫ x in Icc (0:ℝ) 1,periodCharacter n x*
      radialPoincareKernel 0 (abelProfile (evenCoshLift (timeConvolution f f))) (x+ᵥz) z).re := by
  rw [cylinderTimeSquare_period_coefficient f hc he hr R hR hs n z]
  exact sq_nonneg _

#print axioms cylinderTimeSquare_period_coefficient
#print axioms cylinderTimeSquare_period_coefficient_nonneg

end QuantitativeMaass
