module

public import QuantitativeMaassCuspTailBesselV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane Matrix
open AsymptoticCongruenceStrip AsymptoticClassicalPetersson
open QuantitativeArithmeticMaassCuspBand
open scoped Topology InnerProductSpace MatrixGroups ENNReal SchwartzMap FourierTransform

namespace QuantitativeMaass

/-- Uniform quantitative trace bound for the actual window operator followed
by restriction to an entire cusp tail. It applies to every orthonormal cusp
family; no eigenbasis, trace formula or finite-dimensional hypothesis is needed. -/
theorem windowWavePacket_cusp_tail_trace {ι : Type*} (K : SchwartzMap ℝ ℝ)
    (he : Function.Even K) (hc : HasCompactSupport (𝓕 (fun x => (K x:ℂ)))) :
    ∃ H B D : ℝ,0<H ∧ 0<B ∧ 0<D ∧ ∀ (N : ℕ) [NeZero N],∀ hN : 0<N,
      ∀ R : ℝ,∀ hR : 1≤R,∀ ε : ℝ,0≤ε → ε≤1 → ∀ t : ℝ,1≤t →
      ∀ (v : ι → AutomorphicSpace N),Orthonormal ℂ v →
      (∀ i,v i∈localCuspidalSpace N hN) → ∀ (A : SL(2,ℤ)) (Y : ℝ),∀ hY : 2≤Y,
      H*R<Real.log Y →
      (∑' i,ENNReal.ofReal (‖cuspTailRestriction N N A Y hY
        (windowWavePacket N K hc R (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) (v i))‖^2))≤
        ENNReal.ofReal ((Fintype.card (cuspAdmissibleResidues N A):ℝ)*D*R^2*ε^2*
          ((Real.cosh (B*R)+1)^2+t*Real.sqrt t*(Real.sqrt (B*R)+1))*(N:ℝ)/Y) := by
  obtain ⟨H,B,D,hH,hB,hD,hbound⟩ := windowAbelColumn_centered_tail_growth K he hc
  refine ⟨H,B,D,hH,hB,hD,?_⟩
  intro N _ hN R hR ε hε hε1 t ht v hv hcus A Y hY hhigh
  exact (windowWavePacket_tail_centered_bessel N hN K he hc R
    (lt_of_lt_of_le zero_lt_one hR) (t-ε) (t+ε) v hv hcus A Y hY).trans
    (hbound N hN R hR ε hε hε1 t ht A Y (by linarith) hhigh)

#print axioms windowWavePacket_cusp_tail_trace

end QuantitativeMaass
