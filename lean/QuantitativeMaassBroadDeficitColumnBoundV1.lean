module

public import QuantitativeMaassBroadDeficitTraceV1
public import QuantitativeMaassLVExponentialCostV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap

namespace QuantitativeMaass

theorem broadActualDeficit_exponential_trace_error (o : ℍ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N p : ℕ) [NeZero N] [Fact p.Prime]
      (hN : 0 < N) (hpN : ¬p∣N) (_hNp : (N:ZMod p) ≠ 0)
      (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (S L t : ℝ) (hL : 1 ≤ L), 0 ≤ S → 1 ≤ t →
      ∀ (K : Set ℍ), IsCompact K → K ⊆ Metric.closedBall o S → ∀ d : ℕ,
      |broadVolumeOperatorTrace N L (lt_of_lt_of_le zero_lt_one hL) t K
          (actualLVDeficit N p hN hpN a b hab d) -
        volume.real K*broadSymbolIdentity p L t (fun z => 1-lvScalarSymbol p d z)| ≤
        C*Real.sqrt t*L^6*Real.exp (30*S+
          (2+2*max 1 (heckeWordErrorGrowth p)+22*|Real.log p|)*(d:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := broadActualDeficit_volume_trace_error o
  refine ⟨2*C, by positivity, ?_⟩
  intro N p _ _ hN hpN hNp a b hab S L t hL hS ht K hK hKS d
  apply (hbound N p hN hpN hNp a b hab S L t hL hS ht K hK hKS d).trans
  have hh := mul_le_mul_of_nonneg_right
    (lv_degree_cost_bound (max 1 (heckeWordErrorGrowth p)) |Real.log p|
      (le_trans zero_le_one (le_max_left _ _)) (abs_nonneg _) d)
    (show 0 ≤ C*Real.sqrt t*L^6*Real.exp (30*S) by positivity)
  simp only [Real.exp_add] at hh ⊢
  convert hh using 1 <;> ring

/-- The literal broad LV deficit columns have a quantitative compact
energy bound on the full quotient. The main term has inverse-square-root
degree decay; the remainder has the square-root frequency saving. -/
theorem broadActualDeficit_column_energy_bound (o : ℍ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (N p : ℕ) [NeZero N] [Fact p.Prime]
      (hN : 0 < N) (hpN : ¬p∣N) (_hNp : (N:ZMod p) ≠ 0)
      (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (S L t : ℝ) (hL : 1 ≤ L), 0 ≤ S → 1 ≤ t →
      ∀ (K : Set ℍ), IsCompact K → K ⊆ Metric.closedBall o S → ∀ d : ℕ, 0 < d →
      (∫ z in K, ‖actualLVDeficit N p hN hpN a b hab d
        (broadAbelColumn N L (lt_of_lt_of_le zero_lt_one hL) t z)‖^2) ≤
        volume.real K*lvSphericalDeficit p (2*d)*A*(t*L+L^2) +
        B*Real.sqrt t*L^6*Real.exp (30*S+
          (4+4*max 1 (heckeWordErrorGrowth p)+44*|Real.log p|)*(d:ℝ)) := by
  obtain ⟨A,hA,hmain⟩ := broadSymbolIdentity_deficit_bound
  obtain ⟨B,hB,herror⟩ := broadActualDeficit_exponential_trace_error o
  refine ⟨A,B,hA,hB,?_⟩
  intro N p _ _ hN hpN hNp a b hab S L t hL hS ht K hK hKS d hd
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hm := (hmain N p hN hpN a b hab L hLp t (2*d) (by omega)).2
  rw [abs_of_nonneg (by linarith : 0 ≤ t)] at hm
  have he := herror N p hN hpN hNp a b hab S L t hL hS ht K hK hKS (2*d)
  have he' := (le_abs_self _).trans he
  have hm' := mul_le_mul_of_nonneg_left hm (measureReal_nonneg : 0 ≤ volume.real K)
  simp_rw [actualLVDeficit_norm_square N p hN hpN a b hab d]
  change broadVolumeOperatorTrace N L hLp t K (actualLVDeficit N p hN hpN a b hab (2*d)) ≤ _
  have hexp : (2+2*max 1 (heckeWordErrorGrowth p)+22*|Real.log p|)*((2*d:ℕ):ℝ) =
      (4+4*max 1 (heckeWordErrorGrowth p)+44*|Real.log p|)*(d:ℝ) := by
    push_cast
    ring
  rw [hexp] at he'
  nlinarith

#print axioms broadActualDeficit_exponential_trace_error
#print axioms broadActualDeficit_column_energy_bound

end QuantitativeMaass
