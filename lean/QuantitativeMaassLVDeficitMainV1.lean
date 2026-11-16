module

public import QuantitativeMaassLVDeficitExpansionV1
public import QuantitativeMaassMixedExpansionFunctionalV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology FourierTransform SchwartzMap
namespace QuantitativeMaass

/-- Uniform spherical trace bound for the positive complementary LV
polynomial, directly from the proved finite-place density estimate. -/
theorem finitePlaceSymbol_deficit_bounds (p : ℕ) [Fact p.Prime]
    (d : ℕ) (hd : 0<d) (r : ℝ) :
    0≤finitePlaceSymbol p (fun z => 1-lvScalarSymbol p d z) r ∧
      finitePlaceSymbol p (fun z => 1-lvScalarSymbol p d z) r≤lvSphericalDeficit p d := by
  have hh := actual_lv_normalization_deficit p r d hd
  simpa only [finitePlaceSymbol,lvScalarSymbol,sub_sub_cancel,lvSphericalDeficit,
    mul_comm r (Real.log p)] using hh

theorem windowSymbolIdentity_deficit_bounds (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (a₀ b₀ : ℤ) (hab₀ : (p:ℤ)*a₀+(N:ℤ)*b₀=1)
    (K : SchwartzMap ℝ ℝ) (he : Function.Even K)
    (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ))))
    (hK : ∀ x,0≤K x) (hm : (∫ x,K x)=1)
    (R : ℝ) (hR : 0<R) (a b : ℝ) (ha : 0<a) (hab : a≤b) (d : ℕ) (hd : 0<d) :
    0≤windowSymbolIdentity p K R a b (fun z => 1-lvScalarSymbol p d z) ∧
      windowSymbolIdentity p K R a b (fun z => 1-lvScalarSymbol p d z)≤
        lvSphericalDeficit p d*(windowIdentityContribution K hc R hR a b).re := by
  let w := fun r => (smoothedWindow K R (Icc a b∪Icc (-b) (-a)) r)^2*windowPlancherelWeight r
  have hw : Integrable w := (symmetric_squaredWindow_plancherel_mass a b ha hab K hK hm R hR).1
  have hw0 (r : ℝ) : 0≤w r := mul_nonneg (sq_nonneg _) (windowPlancherelWeight_nonneg r)
  have hmem := MixedExpansion.eval_mem N p hN hpN a₀ b₀ hab₀ (MixedExpansion.deficitExpression p d)
  rw [MixedExpansion.eval_deficitExpression] at hmem
  have hi : Integrable (fun r => w r*finitePlaceSymbol p (fun z => 1-lvScalarSymbol p d z) r) :=
    mixedHeckeSpan_weight_integrable N p hN hpN a₀ b₀ hab₀ w hw hmem
  have hupper := integral_mono hi (hw.mul_const (lvSphericalDeficit p d))
    (fun r => mul_le_mul_of_nonneg_left (finitePlaceSymbol_deficit_bounds p d hd r).2 (hw0 r))
  rw [integral_mul_const] at hupper
  have heq : (windowIdentityContribution K hc R hR a b).re=(1/(4*Real.pi))*(∫ r,w r) := by
    rw [windowIdentityContribution_eq_mass K he hc R hR a b ha]
    have hcast : (1/(4*Real.pi):ℂ)=((1/(4*Real.pi):ℝ):ℂ) := by push_cast;rfl
    rw [hcast,←Complex.ofReal_mul,Complex.ofReal_re]
  rw [heq]
  constructor
  · apply mul_nonneg (by positivity : 0≤1/(4*Real.pi))
    apply integral_nonneg
    intro r
    exact mul_nonneg (hw0 r) (finitePlaceSymbol_deficit_bounds p d hd r).1
  · have hh := mul_le_mul_of_nonneg_left hupper (by positivity : 0≤1/(4*Real.pi))
    change (1/(4*Real.pi))*(∫ r,w r*finitePlaceSymbol p (fun z => 1-lvScalarSymbol p d z) r)≤_
    convert hh using 1
    ring

#print axioms finitePlaceSymbol_deficit_bounds
#print axioms windowSymbolIdentity_deficit_bounds
end QuantitativeMaass
