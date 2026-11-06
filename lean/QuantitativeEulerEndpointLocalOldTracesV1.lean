module

public import QuantitativeEulerEndpointLocalCosetSpanV1
public import AsymptoticAtkinLehnerTraceCosetsV1
public import AsymptoticFrickeCosetTransportV1

set_option autoImplicit false
set_option maxHeartbeats 1600000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open QuantitativeEulerDiamondDecode AsymptoticCongruenceStrip AsymptoticFreshMatrices
open AsymptoticAtkinLehner AsymptoticRamifiedCosets AsymptoticCongruenceLabels
open scoped Classical

theorem cosetTraceRow_mem_of_sections (N p : ℕ) (hN : 0<N) (hp : 0<p) (w δ : ℂ)
    {J : Subgroup G} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → J) (s : κ → J)
    (e : ι ≃ J ⧸ (gamma N).subgroupOf J) (f : κ ≃ J ⧸ (gamma N).subgroupOf J)
    (he : ∀ i,e i=QuotientGroup.mk (r i)) (hf : ∀ j,f j=QuotientGroup.mk (s j))
    (hs : cosetTraceRow s∈localRowSpan N p hN hp w δ) :
    cosetTraceRow r∈localRowSpan N p hN hp w δ := by
  apply cosetTraceRow_mem_of_equiv N p hN hp w δ r s (e.trans f.symm) ?_ hs
  intro i
  exact (he i).symm.trans ((f.apply_symm_apply (e i)).symm.trans (hf (f.symm (e i))))

theorem cosetTraceRow_fricke (N d : ℕ) (hN : 0<N) {ι : Type*} [Fintype ι]
    (r : ι → gamma d) :
    cosetTraceRow (fun i => frickeSubgroupMap N d hN (r i))=
      symbol (frickeLabel N hN)*cosetTraceRow r*symbol ((frickeLabel N hN)⁻¹) := by
  unfold cosetTraceRow
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [←map_mul,←map_mul]
  congr 1
  change (frickeLabel N hN*(r i).val*(frickeLabel N hN)⁻¹)⁻¹=_
  group

theorem cosetTraceRow_fricke_mem_iff (N d p : ℕ) (hN : 0<N) (hp : 0<p)
    (w δ : ℂ) (hw : w*w=1) {ι : Type*} [Fintype ι] (r : ι → gamma d) :
    cosetTraceRow (fun i => frickeSubgroupMap N d hN (r i))∈localRowSpan N p hN hp w δ ↔
      cosetTraceRow r∈localRowSpan N p hN hp w δ := by
  rw [cosetTraceRow_fricke]
  constructor
  · intro h
    have hh := localRowSpan_fricke_conjugate N p hN hp w δ hw h
    rw [frickeLabel_inv] at hh
    have hWW : symbol (frickeLabel N hN)*symbol (frickeLabel N hN)=1 := by
      rw [←map_mul,frickeLabel_mul_self,map_one]
    have he : symbol (frickeLabel N hN)*
        (symbol (frickeLabel N hN)*cosetTraceRow r*symbol (frickeLabel N hN))*
        symbol (frickeLabel N hN)=cosetTraceRow r := by
      calc
        _ = (symbol (frickeLabel N hN)*symbol (frickeLabel N hN))*cosetTraceRow r*
            (symbol (frickeLabel N hN)*symbol (frickeLabel N hN)) := by noncomm_ring
        _ = _ := by rw [hWW,one_mul,mul_one]
    rwa [he] at hh
  · exact localRowSpan_fricke_conjugate N p hN hp w δ hw

theorem simple_lower_cosetTrace_mem (M p : ℕ) [Fact p.Prime]
    (hM : 0<M) (hpM : ¬p∣M) (w δ : ℂ) (hδ : δ^2=1)
    {ι : Type*} [Fintype ι] (r : ι → gamma M)
    (e : ι ≃ gamma M ⧸ (gamma (p*M)).subgroupOf (gamma M))
    (he : ∀ i,e i=QuotientGroup.mk (r i)) :
    cosetTraceRow r∈localRowSpan (p*M) p (Nat.mul_pos (Fact.out : p.Prime).pos hM)
      (Fact.out : p.Prime).pos w δ := by
  have hc := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM
  have hab : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1 := by
    have h := Nat.gcd_eq_gcd_ab p M
    rw [hc.gcd_eq_one,Nat.cast_one] at h
    exact h.symm
  apply cosetTraceRow_mem_of_sections (p*M) p _ _ w δ r
    (traceRepresentative M p (Nat.gcdA p M) (Nat.gcdB p M) hab) e
    (traceCosetEquiv M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hab) he (fun _ => rfl)
  simpa only [cosetTraceRow,Fintype.sum_option,traceRepresentative,Subgroup.coe_one,
    inv_one,map_one,inv_inv,simpleTraceRow] using
    simpleTraceRow_mem_localRowSpan M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hab w δ hδ

theorem simple_fricke_cosetTrace_mem (M p : ℕ) [Fact p.Prime]
    (hM : 0<M) (hpM : ¬p∣M) (w δ : ℂ) (hw : w*w=1) (hδ : δ^2=1)
    {ι : Type*} [Fintype ι]
    (r : ι → frickeOldGroup (p*M) M (Nat.mul_pos (Fact.out : p.Prime).pos hM))
    (e : ι ≃ frickeOldGroup (p*M) M (Nat.mul_pos (Fact.out : p.Prime).pos hM) ⧸
      (gamma (p*M)).subgroupOf (frickeOldGroup (p*M) M (Nat.mul_pos (Fact.out : p.Prime).pos hM)))
    (he : ∀ i,e i=QuotientGroup.mk (r i)) :
    cosetTraceRow r∈localRowSpan (p*M) p (Nat.mul_pos (Fact.out : p.Prime).pos hM)
      (Fact.out : p.Prime).pos w δ := by
  have hc := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpM
  have hab : (p:ℤ)*Nat.gcdA p M+(M:ℤ)*Nat.gcdB p M=1 := by
    have h := Nat.gcd_eq_gcd_ab p M
    rw [hc.gcd_eq_one,Nat.cast_one] at h
    exact h.symm
  let s := traceRepresentative M p (Nat.gcdA p M) (Nat.gcdB p M) hab
  let f := traceCosetEquiv M p hM hpM (Nat.gcdA p M) (Nat.gcdB p M) hab
  apply cosetTraceRow_mem_of_sections (p*M) p _ _ w δ r
    (fun i => frickeSubgroupMap (p*M) M (Nat.mul_pos (Fact.out : p.Prime).pos hM) (s i)) e
    (f.trans (frickeRelativeEquiv (p*M) M (Nat.mul_pos (Fact.out : p.Prime).pos hM))) he (fun _ => rfl)
  apply (cosetTraceRow_fricke_mem_iff (p*M) M p _ _ w δ hw s).mpr
  exact simple_lower_cosetTrace_mem M p hM hpM w δ hδ s f (fun _ => rfl)

theorem repeated_fricke_cosetTrace_mem (M p : ℕ) (hM : 0<M) (hp : 0<p) (hpM : p∣M)
    (w : ℂ) {ι : Type*} [Fintype ι] (r : ι → frickeOldGroup (p*M) M (Nat.mul_pos hp hM))
    (e : ι ≃ frickeOldGroup (p*M) M (Nat.mul_pos hp hM) ⧸
      (gamma (p*M)).subgroupOf (frickeOldGroup (p*M) M (Nat.mul_pos hp hM)))
    (he : ∀ i,e i=QuotientGroup.mk (r i)) :
    cosetTraceRow r∈localRowSpan (p*M) p (Nat.mul_pos hp hM) hp w 0 := by
  apply cosetTraceRow_mem_of_sections (p*M) p _ _ w 0 r
    (frickeRepresentative M p hM hp) e (frickeCosetEquiv M p hM hp hpM) he (fun _ => rfl)
  simpa only [cosetTraceRow,frickeRepresentative_inv] using
    repeated_translation_trace_mem (p*M) p (Nat.mul_pos hp hM) hp w

theorem repeated_lower_cosetTrace_mem (M p : ℕ) (hM : 0<M) (hp : 0<p) (hpM : p∣M)
    (w : ℂ) (hw : w*w=1) {ι : Type*} [Fintype ι] (r : ι → gamma M)
    (e : ι ≃ gamma M ⧸ (gamma (p*M)).subgroupOf (gamma M))
    (he : ∀ i,e i=QuotientGroup.mk (r i)) :
    cosetTraceRow r∈localRowSpan (p*M) p (Nat.mul_pos hp hM) hp w 0 := by
  apply (cosetTraceRow_fricke_mem_iff (p*M) M p _ hp w 0 hw r).mp
  apply repeated_fricke_cosetTrace_mem M p hM hp hpM w _
    (e.trans (frickeRelativeEquiv (p*M) M (Nat.mul_pos hp hM)))
  intro i
  exact congrArg (frickeRelativeEquiv (p*M) M (Nat.mul_pos hp hM)) (he i)

#print axioms cosetTraceRow_mem_of_sections
#print axioms cosetTraceRow_fricke_mem_iff
#print axioms simple_lower_cosetTrace_mem
#print axioms simple_fricke_cosetTrace_mem
#print axioms repeated_fricke_cosetTrace_mem
#print axioms repeated_lower_cosetTrace_mem
end QuantitativeEulerEndpointPrepared
