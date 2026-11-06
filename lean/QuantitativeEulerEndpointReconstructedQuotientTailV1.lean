module

public import QuantitativeEulerEndpointQuotientTailStackV1
public import QuantitativeSpectralExceptionalReconstructionTailAreaV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointPrepared
open UpperHalfPlane MeasureTheory ContinuousLinearMap
open AsymptoticRegularTrace AsymptoticPolarIsometry AsymptoticCornerKernel
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns QuantitativeHolomorphic
open QuantitativeSpectralObservability QuantitativeSpectralExceptionalReconstructionTail
open AsymptoticRegularCompactBranch (Space)
open scoped Classical ENNReal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (hN : 0<N)
  (P : Parameters A) (e : Sector N) {I : Type*} [Fintype I]
  (H : I → ℝ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
  (B : ℍ → I → Space →L[ℂ] Space)
  (hm : ∀ i g k,Measurable (fun x => matrix (B x i) g k))
  (hc : ∀ i,Covariant (fun x => B x i))
  (M : I → ℝ) (hM : ∀ i,0≤M i) (hb : ∀ x i,‖B x i‖≤M i)

def reconstructedQuotientTail (x : ℍ) :=
  (quotientTailStack N H hε ht B x).comp
    (normalizedRegularAmbientCountReconstruction A hN P e x)

include hm hc hM hb in
/-- Pulling back all old/sign quotient tails through normalized reconstruction
costs the same geometric ranks as the original tails. -/
theorem reconstructedQuotientTail_rank (hH : ∀ i,0<H i) :
    trace volume (fun x => (reconstructedQuotientTail A hN P e H hε ht B x).kerᗮ.starProjection)≤
      ∑ i,(CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal (H i)⁻¹) := by
  obtain ⟨K,_hK,hbound,hr⟩ := quotientTailStack_absolute_regular N hN H hε ht B hm hc M hM hb
  have hh := row_rank_le A hN P e (fun x => absolute (quotientTailStack N H hε ht B x)) hr.1 hr.2 K hbound
  simp only [row,absolute_comp_ker,absolute_ker] at hh
  exact hh.trans (quotientTailStack_source_rank N hN H hH hε ht B hm hc M hM hb)

variable (V : ℍ → Submodule ℂ Space) [∀ x,CompleteSpace (V x)]
  (hmV : ∀ g k,Measurable (fun x => matrix (V x).starProjection g k))
  (hcV : Covariant (fun x => (V x).starProjection))

include hm hc hM hb hmV hcV in
theorem reconstructedQuotientTail_survivor_regular :
    (∀ g k,Measurable (fun x => matrix
      (remaining (V x) (reconstructedQuotientTail A hN P e H hε ht B x)).starProjection g k)) ∧
      Covariant (fun x => (remaining (V x) (reconstructedQuotientTail A hN P e H hε ht B x)).starProjection) := by
  obtain ⟨K,_hK,hbound,hr⟩ := quotientTailStack_absolute_regular N hN H hε ht B hm hc M hM hb
  have hh := survivor_regular A hN P e V hmV hcV
    (fun x => absolute (quotientTailStack N H hε ht B x)) hr.1 hr.2 K hbound
  simpa only [remaining,row,absolute_comp_ker,reconstructedQuotientTail] using hh

include hm hc hM hb hmV hcV in
theorem reconstructedQuotientTail_survivor_trace (hH : ∀ i,0<H i) :
    trace volume (fun x => (V x).starProjection)≤
      trace volume (fun x => (remaining (V x)
        (reconstructedQuotientTail A hN P e H hε ht B x)).starProjection)+
          ∑ i,(CongruenceSubgroup.Gamma0 N).index*(3*ENNReal.ofReal (H i)⁻¹) := by
  obtain ⟨K,_hK,hbound,hr⟩ := quotientTailStack_absolute_regular N hN H hε ht B hm hc M hM hb
  have hh := survivor_trace A hN P e V hmV hcV
    (fun x => absolute (quotientTailStack N H hε ht B x)) hr.1 hr.2 K hbound
  simp only [remaining,row,absolute_comp_ker,absolute_ker] at hh
  exact hh.trans (add_le_add le_rfl (quotientTailStack_source_rank N hN H hH hε ht B hm hc M hM hb))

#print axioms reconstructedQuotientTail_rank
#print axioms reconstructedQuotientTail_survivor_regular
#print axioms reconstructedQuotientTail_survivor_trace
end QuantitativeEulerEndpointPrepared
