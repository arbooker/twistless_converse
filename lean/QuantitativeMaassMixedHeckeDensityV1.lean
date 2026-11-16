module

public import QuantitativeMaassMixedHeckePolynomialV1
public import QuantitativeArithmeticTreePlancherelV4

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson

namespace QuantitativeMaass

/-- Integrate the finite-place coordinate of a joint scalar symbol against
the genuine normalized tree Plancherel density. -/
def finitePlaceSymbol (p : ℕ) (F : (ℝ × ℝ) → ℝ) (r : ℝ) : ℝ :=
  ∫ x in Icc (-2:ℝ) 2,unramifiedDensity (p:ℝ) x*F (x,r)

theorem finitePlaceSymbol_integrable (p : ℕ) [Fact p.Prime]
    (F : (ℝ × ℝ) → ℝ) (hF : Continuous F) (r : ℝ) :
    IntegrableOn (fun x => unramifiedDensity (p:ℝ) x*F (x,r)) (Icc (-2:ℝ) 2) := by
  have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact ((unramifiedDensity_continuousOn p hp).mul
    (hF.comp (continuous_id.prodMk continuous_const)).continuousOn).integrableOn_compact isCompact_Icc

theorem finitePlaceSymbol_add (p : ℕ) [Fact p.Prime]
    (F G : (ℝ × ℝ) → ℝ) (hF : Continuous F) (hG : Continuous G) :
    finitePlaceSymbol p (F+G)=finitePlaceSymbol p F+finitePlaceSymbol p G := by
  funext r
  unfold finitePlaceSymbol
  simp only [Pi.add_apply,mul_add]
  exact integral_add (finitePlaceSymbol_integrable p F hF r) (finitePlaceSymbol_integrable p G hG r)

theorem finitePlaceSymbol_smul (p : ℕ) (F : (ℝ × ℝ) → ℝ) (c : ℝ) :
    finitePlaceSymbol p (c • F)=c • finitePlaceSymbol p F := by
  funext r
  simp only [finitePlaceSymbol,Pi.smul_apply,smul_eq_mul]
  simp_rw [← mul_assoc,mul_comm (unramifiedDensity (p:ℝ) _) c,mul_assoc]
  exact integral_const_mul _ _

/-- The actual tree moment is exactly the finite-place integral of each
mixed monomial, leaving its time cosine unchanged. -/
theorem finitePlaceSymbol_monomial (p : ℕ) [Fact p.Prime] (n : ℕ) (τ r : ℝ) :
    finitePlaceSymbol p (fun z => z.1^n*Real.cos (τ*z.2)) r=
      (Real.sqrt (p:ℝ))⁻¹^n*(treeWalkCount (p+1) n 0:ℝ)*Real.cos (τ*r) := by
  have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hh := congrArg (fun L : Polynomial ℝ →ₗ[ℝ] ℝ => L (Polynomial.C 1*Polynomial.X^n))
    (QuantitativeArithmeticTreePlancherel.tree_polynomial_moments p (Fact.out : p.Prime).one_lt)
  rw [QuantitativeArithmeticTreePlancherel.treeMoment_monomial] at hh
  change (∫ x in -2..2,unramifiedDensity (p:ℝ) x*(Polynomial.C (1:ℝ)*Polynomial.X^n).eval x)=_ at hh
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,one_mul] at hh
  rw [intervalIntegral.integral_of_le (by norm_num : (-2:ℝ)≤2),
    ← integral_Icc_eq_integral_Ioc] at hh
  unfold finitePlaceSymbol
  simp only [← mul_assoc]
  rw [integral_mul_const,hh]

theorem mixedHeckeSpan_symbol_continuous (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    {v : HeckeWavePair N} (hv : v∈mixedHeckeSpan N p hN hpN a b hab) : Continuous v.2 := by
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨⟨n,τ⟩,rfl⟩ := hv;exact (continuous_fst.pow n).mul (Real.continuous_cos.comp (continuous_snd.const_mul τ))
  | zero => exact continuous_const
  | add u v hu hv hcu hcv => exact hcu.add hcv
  | smul c u hu hcu => exact hcu.const_smul c

/-- Every finite mixed symbol is integrable against an arbitrary integrable
spectral weight. Finite-place integration uses the true tree density. -/
theorem mixedHeckeSpan_weight_integrable (N p : ℕ) [Fact p.Prime]
    (hN : 0<N) (hpN : ¬p∣N) (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
    (w : ℝ → ℝ) (hw : Integrable w) {v : HeckeWavePair N}
    (hv : v∈mixedHeckeSpan N p hN hpN a b hab) :
    Integrable (fun r => w r*finitePlaceSymbol p v.2 r) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨n,τ⟩,rfl⟩ := hv
    change Integrable (fun r => w r*finitePlaceSymbol p (fun z => z.1^n*Real.cos (τ*z.2)) r)
    simp_rw [finitePlaceSymbol_monomial,← mul_assoc]
    have hcos : AEStronglyMeasurable (fun r : ℝ => Real.cos (τ*r)) volume := by fun_prop
    exact ((hw.mul_const _).mul_const _).mul_bdd hcos
      (Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (τ*r)))
  | zero => simp only [Prod.snd_zero,finitePlaceSymbol,Pi.zero_apply,mul_zero,integral_zero];exact integrable_zero ℝ ℝ volume
  | add u v hu hv hi hj =>
    rw [Prod.snd_add,finitePlaceSymbol_add p u.2 v.2
      (mixedHeckeSpan_symbol_continuous N p hN hpN a b hab hu)
      (mixedHeckeSpan_symbol_continuous N p hN hpN a b hab hv)]
    simp only [Pi.add_apply,mul_add]
    exact hi.add hj
  | smul c u hu hi =>
    change Integrable (fun r => w r*finitePlaceSymbol p (c • u.2) r)
    rw [finitePlaceSymbol_smul]
    simpa only [Pi.smul_apply,smul_eq_mul,mul_left_comm] using hi.const_mul c

#print axioms finitePlaceSymbol_integrable
#print axioms finitePlaceSymbol_add
#print axioms finitePlaceSymbol_smul
#print axioms finitePlaceSymbol_monomial
#print axioms mixedHeckeSpan_symbol_continuous
#print axioms mixedHeckeSpan_weight_integrable

end QuantitativeMaass
