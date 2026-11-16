module

public import QuantitativeMaassWindowTailTraceV1
public import QuantitativeMaassWindowVariationExponentialV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand QuantitativeSpectralObservability
open scoped Topology InnerProductSpace MatrixGroups ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- A uniform bound on the number of admissible parabolic residues. -/
theorem cuspAdmissibleResidues_card_le (N : ℕ) (A : SL(2,ℤ)) :
    Fintype.card (cuspAdmissibleResidues N A)≤N := by
  simpa using Fintype.card_subtype_le (fun r : Fin N => (N:ℤ)∣(r.val:ℤ)*(A 1 0)^2)

/-- Exponential-radius tail bound, uniform over the actual integral cusp charts. -/
theorem windowWavePacket_tail_uniform {ι : Type*} (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ H B D : ℝ,0<H ∧ 0<B ∧ 0<D ∧ ∀ (N : ℕ) [NeZero N],∀ hN : 0<N,
      ∀ R : ℝ,∀ hR : 1≤R,∀ ε : ℝ,0≤ε → ε≤1 → ∀ t : ℝ,1≤t →
      ∀ (v : ι → AutomorphicSpace N),Orthonormal ℂ v →
      (∀ i,v i∈localCuspidalSpace N hN) → ∀ (A : SL(2,ℤ)) (Y : ℝ),∀ hY : 2≤Y,
      H*R<Real.log Y →
      (∑' i,ENNReal.ofReal (‖cuspTailRestriction N N A Y hY
        (windowWavePacket N K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) (v i))‖^2))≤
        ENNReal.ofReal ((N:ℝ)^2*D*R^3*ε^2*t*Real.sqrt t*Real.exp (B*R)/Y) := by
  obtain ⟨H,B,D,hH,hB,hD,hbound⟩ := windowWavePacket_cusp_tail_trace (ι:=ι) K he hc
  refine ⟨H,2*B,D*(B+6),hH,by positivity,by positivity,?_⟩
  intro N _ hN R hR ε hε hε1 t ht v hv hcus A Y hY hhigh
  apply (hbound N hN R hR ε hε hε1 t ht v hv hcus A Y hY hhigh).trans
  apply ENNReal.ofReal_le_ofReal
  have hcard : (Fintype.card (cuspAdmissibleResidues N A):ℝ)≤(N:ℝ) :=
    Nat.cast_le.mpr (cuspAdmissibleResidues_card_le N A)
  calc
    _ ≤ (N:ℝ)*D*R^2*ε^2*((B+6)*R*t*Real.sqrt t*Real.exp (2*B*R))*(N:ℝ)/Y := by
      gcongr
      exact window_variation_radius_majorant B R t hB hR ht
    _ = _ := by ring

#print axioms cuspAdmissibleResidues_card_le
#print axioms windowWavePacket_tail_uniform

end QuantitativeMaass
