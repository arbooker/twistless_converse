module

public import QuantitativeEulerEndpointLocalSpanV1
public import AsymptoticRamifiedOldBranchesV1

set_option autoImplicit false
set_option maxHeartbeats 1200000
@[expose] public noncomputable section

namespace QuantitativeEulerEndpointPrepared
open QuantitativeEulerDiamondDecode AsymptoticFreshMatrices AsymptoticOrbitDecode
open AsymptoticCongruenceLabels AsymptoticIntegralSubgroup
open scoped Classical

variable (N p : ℕ) (hN : 0<N) (hp : 0<p) (w δ : ℂ)

theorem localTranslatedRow_mem (i : LocalRowIndex N × G) :
    localTranslatedRow N p hN hp w δ i∈localRowSpan N p hN hp w δ :=
  Submodule.subset_span ⟨i,rfl⟩

theorem localRowSpan_mul_symbol {A : Ring} (hA : A∈localRowSpan N p hN hp w δ) (g : G) :
    A*symbol g∈localRowSpan N p hN hp w δ := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · intro a ha
    obtain ⟨⟨i,h⟩,rfl⟩ := ha
    have he : localTranslatedRow N p hN hp w δ (i,h)*symbol g=
        localTranslatedRow N p hN hp w δ (i,h*g) := by
      simp only [localTranslatedRow,map_mul,mul_assoc]
    rw [he]
    exact localTranslatedRow_mem N p hN hp w δ _
  · simpa only [zero_mul] using (localRowSpan N p hN hp w δ).zero_mem
  · intro a b _ha _hb ia ib
    simpa only [add_mul] using (localRowSpan N p hN hp w δ).add_mem ia ib
  · intro c a _ha ia
    simpa only [smul_mul_assoc] using (localRowSpan N p hN hp w δ).smul_mem c ia

theorem localRowSpan_mul_right {A : Ring} (hA : A∈localRowSpan N p hN hp w δ) (E : Ring) :
    A*E∈localRowSpan N p hN hp w δ := by
  induction E using MonoidAlgebra.induction_on with
  | of g => exact localRowSpan_mul_symbol N p hN hp w δ hA g
  | add E F hE hF =>
    simpa only [mul_add] using (localRowSpan N p hN hp w δ).add_mem hE hF
  | smul c E hE =>
    simpa only [mul_smul_comm] using (localRowSpan N p hN hp w δ).smul_mem c hE

theorem frickeRow_mem_localRowSpan : frickeRow N hN w∈localRowSpan N p hN hp w δ := by
  have h := localTranslatedRow_mem N p hN hp w δ (.inr 0,1)
  change frickeRow N hN w*symbol 1∈localRowSpan N p hN hp w δ at h
  simpa only [map_one,mul_one] using h

theorem ramifiedRow_mem_localRowSpan : ramifiedRow p hp δ∈localRowSpan N p hN hp w δ := by
  have h := localTranslatedRow_mem N p hN hp w δ (.inr 1,1)
  change ramifiedRow p hp δ*symbol 1∈localRowSpan N p hN hp w δ at h
  simpa only [map_one,mul_one] using h

/-- Fricke left multiplication preserves the residual span because its
own original residual is among the generators. -/
theorem localRowSpan_fricke_left (hw : w*w=1) {A : Ring}
    (hA : A∈localRowSpan N p hN hp w δ) :
    symbol (frickeLabel N hN)*A∈localRowSpan N p hN hp w δ := by
  have hr := localRowSpan_mul_right N p hN hp w δ
    (frickeRow_mem_localRowSpan N p hN hp w δ) A
  have he : w • (A-frickeRow N hN w*A)=symbol (frickeLabel N hN)*A := by
    rw [frickeRow,sub_mul,one_mul,smul_mul_assoc,sub_sub_cancel,smul_smul,hw,one_smul]
  rw [←he]
  exact (localRowSpan N p hN hp w δ).smul_mem w
    ((localRowSpan N p hN hp w δ).sub_mem hA hr)

theorem localRowSpan_fricke_conjugate (hw : w*w=1) {A : Ring}
    (hA : A∈localRowSpan N p hN hp w δ) :
    symbol (frickeLabel N hN)*A*symbol ((frickeLabel N hN)⁻¹)∈localRowSpan N p hN hp w δ := by
  exact localRowSpan_mul_symbol N p hN hp w δ
    (localRowSpan_fricke_left N p hN hp w δ hw hA) _

/-- The repeated-prime second trace is exactly the zero-eigenvalue
ramified row followed by a dilation, in the actual projective algebra. -/
theorem repeated_translation_trace_identity :
    (∑ a : Fin p, symbol (translationLabel ((a.val:ℚ)/p)))=
      ramifiedRow p hp 0*symbol (dilationLabel p hp) := by
  simp only [ramifiedRow,zero_smul,sub_zero,Finset.sum_mul,←map_mul,
    ramifiedLabel_mul_dilation]

theorem repeated_translation_trace_mem :
    (∑ a : Fin p, symbol (translationLabel ((a.val:ℚ)/p)))∈localRowSpan N p hN hp w 0 := by
  rw [repeated_translation_trace_identity p hp]
  exact localRowSpan_mul_symbol N p hN hp w 0 (ramifiedRow_mem_localRowSpan N p hN hp w 0) _

#print axioms localRowSpan_mul_right
#print axioms localRowSpan_fricke_conjugate
#print axioms repeated_translation_trace_identity
#print axioms repeated_translation_trace_mem
end QuantitativeEulerEndpointPrepared
