module

public import SmallLevelTwentyOneTenthMellinV1
public import SmallLevelRamanujanReflectionOrderV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace SmallLevelTwentyOneChiFive
open Complex SmallLevelTwentyOneTenthMellin SmallLevelTaylor

/-- Both center integrals have finite order after unscaling and are
exchanged by reflection with the original common sign. -/
theorem original_center_laws {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε) :
    ∀ b : Bool, FinitenessFiniteOrder.Bound (centerEntire m f b) ∧
      ∀ s : ℂ, centerEntire m f b s=ε*(Real.sqrt 2100:ℂ)^(((2*m:ℕ):ℂ)-2*s)*
        centerEntire m f (!b) (((2*m:ℕ):ℂ)-s) := by
  intro b
  have h := original_scaled_centers hm hf ε hε hlaw b
  exact ⟨SmallLevelMellinUnscale.finite_order_at_one (by decide : 0<2100) _ h.2.1,
    SmallLevelMellinUnscale.reflection_pair (by decide : 0<2100) _ _ ε h.2.2⟩

theorem root_five (f : ℕ → ℂ) : FinitenessNormalizedTwistProduct.root 21 f 5=1 := by
  simp [FinitenessNormalizedTwistProduct.root,(by decide : Nat.Prime 5).primeFactors,
    FinitenessNormalizedTwistLocal.sign]

theorem original_ramanujan_five_laws {m : ℕ} (hm : 0<m) {f : ℕ → ℂ}
    (hf : FinitenessOriginalInput.IsSolution 21 (2*m) f) (ε : ℂ)
    (hε : ε=1 ∨ ε= -1)
    (hlaw : QuantitativeArithmeticCoherentTaylor.CoherentLaw 21 (2*m) f ε) :
    FinitenessFiniteOrder.Bound (ramanujanEntire 21 (2*m) f 5) ∧
      ∀ s : ℂ, ramanujanEntire 21 (2*m) f 5 s=
        ε*(Real.sqrt 525:ℂ)^(((2*m:ℕ):ℂ)-2*s)*ramanujanEntire 21 (2*m) f 5 (((2*m:ℕ):ℂ)-s) := by
  simpa only [root_five,one_mul,show Nat.lcm 21 (5^2)=525 from rfl,Nat.cast_ofNat] using
    SmallLevelRamanujanReflectionOrder.original_ramanujan_laws (by decide : 0<21)
      (by omega) hf ε hε hlaw (by decide : 0<5)

#print axioms original_center_laws
#print axioms original_ramanujan_five_laws
end SmallLevelTwentyOneChiFive
