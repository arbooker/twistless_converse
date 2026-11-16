module

public import QuantitativeMaassBroadTraceLinearV1
public import QuantitativeMaassMixedExpansionFunctionalV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set MeasureTheory UpperHalfPlane
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open scoped Topology SchwartzMap

namespace QuantitativeMaass

local instance (N : ℕ) : Ring (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) := ContinuousLinearMap.ring
local instance (N : ℕ) : Algebra ℝ (AutomorphicSpace N →L[ℂ] AutomorphicSpace N) := ContinuousLinearMap.algebra

/-- The common operator/symbol expansion gives a uniform broad-packet
trace error with explicit coefficient mass, degree and propagation. -/
theorem broadExpression_volume_trace_error (o : ℍ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N p : ℕ) [NeZero N] [Fact p.Prime]
      (hN : 0 < N) (hpN : ¬p∣N) (_hNp : (N:ZMod p) ≠ 0)
      (a b : ℤ) (hab : (p:ℤ)*a+(N:ℤ)*b=1)
      (S L t : ℝ) (hL : 1 ≤ L), 0 ≤ S → 1 ≤ t →
      ∀ (K : Set ℍ), IsCompact K → K ⊆ Metric.closedBall o S →
      ∀ (E : MixedExpansion.Expression) (m : ℕ) (T : ℝ), 0 ≤ T → MixedExpansion.Bounded m T E →
      let v := MixedExpansion.eval N p hN hpN a b hab E
      |broadVolumeOperatorTrace N L (lt_of_lt_of_le zero_lt_one hL) t K v.1 -
        volume.real K*broadSymbolIdentity p L t v.2| ≤
        MixedExpansion.mass E*(max 1 (heckeWordErrorGrowth p))^m*C*(1+T)*
          Real.sqrt t*L^6*Real.exp (30*S+10*T) := by
  obtain ⟨C,hC,hbound⟩ := broadAbelColumn_mixed_volume_trace_bound o
  refine ⟨C,hC,?_⟩
  intro N p _ _ hN hpN hNp a b hab S L t hL hS ht K hK hKS E m T hT hE v
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let f : HeckeWavePair N → ℝ := fun u =>
    broadVolumeOperatorTrace N L hLp t K u.1 - volume.real K*broadSymbolIdentity p L t u.2
  have h0 : f 0 = 0 := by
    simp only [f, Prod.fst_zero, Prod.snd_zero, broadVolumeOperatorTrace,
      zero_apply, inner_zero_left, Complex.zero_re, integral_zero,
      broadSymbolIdentity, finitePlaceSymbol, Pi.zero_apply, mul_zero, sub_zero]
  have hadd : ∀ u ∈ mixedHeckeSpan N p hN hpN a b hab,
      ∀ v ∈ mixedHeckeSpan N p hN hpN a b hab, f (u+v) = f u+f v := by
    intro u hu v hv
    dsimp only [f]
    rw [broadSymbolIdentity_add N p hN hpN a b hab L hLp t hu hv]
    dsimp only [Prod.fst_add]
    rw [broadVolumeOperatorTrace_add N L hLp t K hK]
    ring
  have hsmul : ∀ c : ℝ, ∀ u ∈ mixedHeckeSpan N p hN hpN a b hab, f (c • u) = c*f u := by
    intro c u _
    change broadVolumeOperatorTrace N L hLp t K (c • u.1) -
      volume.real K*broadSymbolIdentity p L t (c • u.2) = _
    rw [broadVolumeOperatorTrace_smul, broadSymbolIdentity_smul]
    dsimp only [f]
    ring
  let B := (max 1 (heckeWordErrorGrowth p))^m*C*(1+T)*Real.sqrt t*L^6*Real.exp (30*S+10*T)
  have hmono (u : MixedExpansion.Term) (hu : u ∈ E) :
      |f (mixedHeckeSymbol N p hN hpN a b hab u.degree u.time)| ≤ B := by
    have hb := hbound N p hN hpN hNp a b hab S L t u.time hL hS ht K hK hKS u.degree
    change |broadVolumeOperatorTrace N L hLp t K
      (Wave.shiftedQuotientWave N u.time*(HeckeL2.operator N p hN hpN a b hab)^u.degree) -
      volume.real K*broadSymbolIdentity p L t (fun z => z.1^u.degree*Real.cos (u.time*z.2))| ≤ _
    rw [broadSymbolIdentity_monomial p L hLp t u.degree u.time]
    apply hb.trans
    have hu' := hE u hu
    have hq : 0 ≤ heckeWordErrorGrowth p := by unfold heckeWordErrorGrowth; positivity
    have hp : (heckeWordErrorGrowth p)^u.degree ≤ (max 1 (heckeWordErrorGrowth p))^m :=
      (pow_le_pow_left₀ hq (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hu'.1)
    dsimp only [B]
    gcongr <;> exact hu'.2
  have hh := MixedExpansion.eval_functional_bound N p hN hpN a b hab f h0 hadd hsmul E B hmono
  convert hh using 1
  dsimp only [B]
  ring

#print axioms broadExpression_volume_trace_error

end QuantitativeMaass
