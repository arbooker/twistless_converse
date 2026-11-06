module

public import AsymptoticRegularFunctionalCalculusV1
public import QuantitativeSpectralNormalizedRowV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace QuantitativeSpectralRegularInverse

/-- A globally continuous reciprocal agreeing with inversion above one. -/
def clippedInverse (x : ℝ) : ℝ := (max 1 x)⁻¹

theorem clippedInverse_continuous : Continuous clippedInverse := by
  exact (continuous_const.max continuous_id).inv₀
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 x)))

theorem inverse_eq_cfc {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (a : A) (ha : 1 ≤ a) : Ring.inverse a = cfc clippedInverse a := by
  have hp : IsStrictlyPositive a := .of_le isStrictlyPositive_one ha
  have hs : IsSelfAdjoint a := hp.nonneg.isSelfAdjoint
  rw [← cfc_ringInverse_id (R := ℝ) a hp.isUnit hs]
  apply cfc_congr
  intro x hx
  have hh : 1 ≤ x := (algebraMap_le_iff_le_spectrum hs).mp (by simpa using ha) x hx
  simp only [clippedInverse, max_eq_right hh]

open AsymptoticRegularTrace MeasureTheory
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- Uniformly coercive measurable covariant families have measurable
covariant inverses, with no Borel-functional-calculus assumption. -/
theorem inverse_regular (B : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h, Measurable (fun x => matrix (B x) g h)) (hc : Covariant B)
    (hp : ∀ x, 1 ≤ B x) (M : ℝ) (hM : ∀ x, ‖B x‖ ≤ M) :
    (∀ g h, Measurable (fun x => matrix (Ring.inverse (B x)) g h)) ∧
      Covariant (fun x => Ring.inverse (B x)) := by
  have he (x : α) : Ring.inverse (B x) = AsymptoticFunctionalCalculus.value clippedInverse (B x) :=
    inverse_eq_cfc (B x) (hp x)
  simp only [he]
  exact cfc_regular B hm hc
    (fun x => (IsStrictlyPositive.of_le isStrictlyPositive_one (hp x)).nonneg.isSelfAdjoint)
    M hM clippedInverse clippedInverse_continuous

#print axioms inverse_eq_cfc
#print axioms inverse_regular

end QuantitativeSpectralRegularInverse
