module

public import QuantitativeEulerEndpointLocalIdealV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open QuantitativeEulerDiamondDecode AsymptoticCongruenceStrip
open scoped Classical

/-- The unnormalized trace of the literal inverse coset representatives. -/
def cosetTraceRow {J : Subgroup G} {ι : Type*} [Fintype ι] (r : ι → J) : Ring :=
  ∑ i, symbol (r i).val⁻¹

/-- Changing representatives adds only finite translated Gamma0 defects.
The representatives can be arbitrary quotient choices. -/
theorem cosetTraceRow_sub_mem (N p : ℕ) (hN : 0<N) (hp : 0<p) (w δ : ℂ)
    {J : Subgroup G} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → J) (s : κ → J) (e : ι ≃ κ)
    (he : ∀ i, (QuotientGroup.mk (r i) : J ⧸ (gamma N).subgroupOf J)=
      QuotientGroup.mk (s (e i))) :
    cosetTraceRow r-cosetTraceRow s∈localRowSpan N p hN hp w δ := by
  have hterm (i : ι) : symbol (r i).val⁻¹-symbol (s (e i)).val⁻¹∈
      localRowSpan N p hN hp w δ := by
    have hm := QuotientGroup.eq.mp (he i)
    change (r i).val⁻¹*(s (e i)).val∈gamma N at hm
    let γ : gamma N := ⟨(r i).val⁻¹*(s (e i)).val,hm⟩
    have hh := localTranslatedRow_mem N p hN hp w δ (.inl γ,(s (e i)).val⁻¹)
    simpa only [localTranslatedRow,localObservationRow,γ,sub_mul,one_mul,
      ←map_mul,mul_inv_cancel_right] using hh
  have hh := (localRowSpan N p hN hp w δ).sum_mem
    (fun i (_ : i∈(Finset.univ : Finset ι)) => hterm i)
  have hs : (∑ i : ι, symbol (s (e i)).val⁻¹)=∑ j : κ, symbol (s j).val⁻¹ :=
    e.sum_comp (fun j => symbol (s j).val⁻¹)
  simpa only [Finset.sum_sub_distrib,hs,cosetTraceRow] using hh

theorem cosetTraceRow_mem_of_equiv (N p : ℕ) (hN : 0<N) (hp : 0<p) (w δ : ℂ)
    {J : Subgroup G} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → J) (s : κ → J) (e : ι ≃ κ)
    (he : ∀ i, (QuotientGroup.mk (r i) : J ⧸ (gamma N).subgroupOf J)=
      QuotientGroup.mk (s (e i)))
    (hs : cosetTraceRow s∈localRowSpan N p hN hp w δ) :
    cosetTraceRow r∈localRowSpan N p hN hp w δ := by
  have hh := (localRowSpan N p hN hp w δ).add_mem
    (cosetTraceRow_sub_mem N p hN hp w δ r s e he) hs
  simpa only [sub_add_cancel] using hh

#print axioms cosetTraceRow_sub_mem
#print axioms cosetTraceRow_mem_of_equiv
end QuantitativeEulerEndpointPrepared
