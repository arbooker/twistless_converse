module

public import QuantitativeMaassBroadExpressionTraceV1
public import QuantitativeMaassLVDeficitMainV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap

namespace QuantitativeMaass

/-- The finite-place deficit multiplies only the positive broad spherical
mass. Its inverse-square-root degree saving is uniform in frequency and width. -/
theorem broadSymbolIdentity_deficit_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N p : ℕ) [Fact p.Prime]
      (_hN : 0 < N) (_hpN : ¬p∣N) (a b : ℤ), (p:ℤ)*a+(N:ℤ)*b=1 →
      ∀ (L : ℝ), 0 < L → ∀ (t : ℝ) (d : ℕ), 0 < d →
      0 ≤ broadSymbolIdentity p L t (fun z => 1-lvScalarSymbol p d z) ∧
      broadSymbolIdentity p L t (fun z => 1-lvScalarSymbol p d z) ≤
        lvSphericalDeficit p d*C*(|t| * L+L^2) := by
  obtain ⟨C,hC,hbound⟩ := broadSpectralWeight_mass_bound
  refine ⟨(1/(4*Real.pi))*C, by positivity, ?_⟩
  intro N p _ hN hpN a b hab L hL t d hd
  have hw := (hbound L hL t).1
  have hmem := MixedExpansion.eval_mem N p hN hpN a b hab (MixedExpansion.deficitExpression p d)
  rw [MixedExpansion.eval_deficitExpression] at hmem
  have hi := mixedHeckeSpan_weight_integrable N p hN hpN a b hab _ hw hmem
  have hD : 0 ≤ lvSphericalDeficit p d :=
    (finitePlaceSymbol_deficit_bounds p d hd 0).1.trans (finitePlaceSymbol_deficit_bounds p d hd 0).2
  have hu := integral_mono hi (hw.mul_const (lvSphericalDeficit p d))
    (fun r => mul_le_mul_of_nonneg_left (finitePlaceSymbol_deficit_bounds p d hd r).2
      (broadSpectralWeight_nonneg L t r))
  rw [integral_mul_const] at hu
  constructor
  · apply mul_nonneg (by positivity : (0:ℝ) ≤ 1/(4*Real.pi))
    exact integral_nonneg (fun r => mul_nonneg (broadSpectralWeight_nonneg L t r)
      (finitePlaceSymbol_deficit_bounds p d hd r).1)
  · have hh := mul_le_mul_of_nonneg_left
      (hu.trans (mul_le_mul_of_nonneg_right (hbound L hL t).2 hD))
      (by positivity : (0:ℝ) ≤ 1/(4*Real.pi))
    change (1/(4*Real.pi))*(∫ r : ℝ, broadSpectralWeight L t r*
      finitePlaceSymbol p (fun z => 1-lvScalarSymbol p d z) r) ≤ _
    convert hh using 1
    ring

/-- Degree-uniform trace error for the literal positive LV complement
on the full quotient, using the actual broad packet columns. -/
theorem broadActualDeficit_volume_trace_error (o : ℍ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N p : ℕ) [NeZero N] [Fact p.Prime]
      (hN : 0 < N) (hpN : ¬p∣N) (_hNp : (N:ZMod p) ≠ 0)
      (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (S L t : ℝ) (hL : 1 ≤ L), 0 ≤ S → 1 ≤ t →
      ∀ (K : Set ℍ), IsCompact K → K ⊆ Metric.closedBall o S → ∀ d : ℕ,
      |broadVolumeOperatorTrace N L (lt_of_lt_of_le zero_lt_one hL) t K
          (actualLVDeficit N p hN hpN a b hab d) -
        volume.real K*broadSymbolIdentity p L t (fun z => 1-lvScalarSymbol p d z)| ≤
        (2*(2:ℝ)^d)*(max 1 (heckeWordErrorGrowth p))^(2*d)*C*
          (1+2*(d:ℝ)*|Real.log p|)*Real.sqrt t*L^6*
            Real.exp (30*S+20*(d:ℝ)*|Real.log p|) := by
  obtain ⟨C,hC,hbound⟩ := broadExpression_volume_trace_error o
  refine ⟨C,hC,?_⟩
  intro N p _ _ hN hpN hNp a b hab S L t hL hS ht K hK hKS d
  obtain ⟨hmass,hdegree⟩ := MixedExpansion.deficitExpression_bounds p d
  have hh := hbound N p hN hpN hNp a b hab S L t hL hS ht K hK hKS
    (MixedExpansion.deficitExpression p d) (2*d) (2*(d:ℝ)*|Real.log p|) (by positivity) hdegree
  rw [MixedExpansion.eval_deficitExpression] at hh
  apply hh.trans
  rw [show 10*(2*(d:ℝ)*|Real.log p|)=20*(d:ℝ)*|Real.log p| by ring]
  gcongr

#print axioms broadSymbolIdentity_deficit_bound
#print axioms broadActualDeficit_volume_trace_error

end QuantitativeMaass
