module

public import AsymptoticDecodedQuotientV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set UpperHalfPlane AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticCongruenceQuotient AsymptoticOrbitDecode AsymptoticIntegralSubgroup
open AsymptoticCompactBranch AsymptoticCompactTranslation AsymptoticMassTransport

namespace QuantitativeMaass

/-- Rechoose the integral-translation representative at another point. -/
def refoldStrip (N : ℕ) (z w : ℍ) (g : Strip N z) : Strip N w :=
  ⟨⟨foldLabel w g.val.val,by
    have hh := (gamma N).mul_mem (translation_mem N (-Int.floor (g.val.val • w).re))
      g.val.property
    simpa only [foldLabel,Int.cast_neg] using hh⟩,foldLabel_mem w g.val.val⟩

theorem refoldStrip_inverse (N : ℕ) (z w : ℍ) (g : Strip N z) :
    refoldStrip N w z (refoldStrip N z w g)=g := by
  apply Subtype.ext
  apply Subtype.ext
  change foldLabel z (translationLabel (-(Int.floor (g.val.val • w).re:ℚ))*g.val.val)=g.val.val
  have hh := foldLabel_integer z g.val.val (-Int.floor (g.val.val • w).re)
  simpa only [Int.cast_neg,foldLabel_self z g.val.val g.property] using hh

def stripRefoldEquiv (N : ℕ) (z w : ℍ) : Strip N z ≃ Strip N w where
  toFun := refoldStrip N z w
  invFun := refoldStrip N w z
  left_inv := refoldStrip_inverse N z w
  right_inv := refoldStrip_inverse N w z

theorem refoldStrip_cap (N : ℕ) (z w : ℍ) (g : Strip N z) (ε : ℝ) (v : ℕ) :
    cap ε v ((refoldStrip N z w g).val.val • w)=cap ε v (g.val.val • w) := by
  change cap ε v ((translationLabel (-(Int.floor (g.val.val • w).re:ℚ))*g.val.val) • w)=_
  rw [mul_smul,cap_translate]

/-- The actual orbit weight can be summed over one fixed translation
transversal. No discontinuous strip indicator then depends on the variable. -/
theorem quotientWeight_fixed_index (N : ℕ) (z w : ℍ) (ε : ℝ) (v : ℕ) :
    weight N ε v w=∑' g : Strip N z,cap ε v (g.val.val • w)^2 := by
  have hw : weight N ε v w=∑' g : Strip N w,cap ε v (g.val.val • w)^2 := by
    unfold weight
    exact (tsum_subtype {g : gamma N | g.val • w∈strip}
      (fun g => cap ε v (g.val • w)^2)).symm
  rw [hw]
  calc
    _ = ∑' g : Strip N z,cap ε v ((stripRefoldEquiv N z w g).val.val • w)^2 :=
      ((stripRefoldEquiv N z w).tsum_eq _).symm
    _ = _ := tsum_congr (fun g => by rw [show stripRefoldEquiv N z w g=refoldStrip N z w g from rfl,
      refoldStrip_cap])

theorem quotientWeight_fixed_summable (N : ℕ) (z w : ℍ) {ε : ℝ} (hε : 0<ε)
    {v : ℕ} (hv : 1≤v) :
    Summable (fun g : Strip N z => cap ε v (g.val.val • w)^2) := by
  have hh := (strip_summable N hε hv w).comp_injective (stripRefoldEquiv N z w).injective
  apply hh.congr
  intro g
  exact congrArg (fun x : ℝ => x^2) (refoldStrip_cap N z w g ε v)

#print axioms refoldStrip_inverse
#print axioms refoldStrip_cap
#print axioms quotientWeight_fixed_index
#print axioms quotientWeight_fixed_summable

end QuantitativeMaass
