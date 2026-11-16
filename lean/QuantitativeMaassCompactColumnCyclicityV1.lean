module

public import QuantitativeMaassMixedAdjointTraceV1
public import QuantitativeMaassCompactFullInputV1
public import QuantitativeMaassCylinderPacketAlgebraV1

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Set Filter MeasureTheory UpperHalfPlane ContinuousLinearMap
open AsymptoticClassicalPetersson
open scoped SchwartzMap
namespace QuantitativeMaass

/-- A concrete finite-energy column trace equals its adjoint basis trace.
Both mixed series are proved absolutely convergent before changing sides. -/
theorem columnLinearTrace_adjoint_basis {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (c : α→Lp ℂ 2 μ) (hc : MemLp c 2 μ)
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (T : Lp ℂ 2 μ→L[ℂ]Lp ℂ 2 μ) :
    let V := finiteEnergyColumnOperator μ c hc
    columnLinearTrace μ c T=
      ∑' i,(inner ℂ (V.adjoint (basis i)) (T (V.adjoint (basis i)))).re := by
  intro V
  have ht := hc.continuousLinearMap_comp T
  have hp := finiteEnergyColumn_pair_trace μ c (fun z => T (c z)) hc ht basis
  have hcomp : V.comp T.adjoint=finiteEnergyColumnOperator μ (fun z => T (c z)) ht := by
    simpa only [adjoint_adjoint] using finiteEnergyColumnOperator_comp μ c hc T.adjoint
  rw [←hcomp] at hp
  have hV := finiteEnergyColumnOperator_summable μ c hc basis
  have hVT := (right_comp_energy_bound basis V T.adjoint hV).1
  have hsym : (∫ z,(inner ℂ (c z) (T (c z))).re ∂μ)=columnLinearTrace μ c T := by
    apply integral_congr_ae
    filter_upwards with z
    exact inner_re_symm (𝕜:=ℂ) _ _
  rw [hsym] at hp
  rw [←hp,hilbertSchmidt_pair_adjoint basis V (V.comp T.adjoint) hV hVT]
  simp only [adjoint_comp,adjoint_adjoint,comp_apply]

variable (f : SchwartzMap ℝ ℂ) (hc : HasCompactSupport (f : ℝ→ℂ))
  (he : Function.Even f) (hr : ∀ t,star (f t)=f t)
  (R : ℝ) (hR : 0≤R) (hs : Function.support f⊆Icc (-R) R)

include hr in
/-- The global compact-input column operator is the actual cylinder wave
composed with the input projection, not a replacement spectral packet. -/
theorem compact_input_column_operator {a : ℝ} (ha : 0<a) (b : ℝ) :
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
      (upperRectangle_compact _ _ _ _ ha).measurableSet
    finiteEnergyColumnOperator (quotientMeasure 0)
      (fun z => P (cylinderTimeColumn f hc he R hR hs z))
      (cylinderTimeColumn_compact_input_memLp f hc he R hR hs ha b)=
      (cylinderTimePacket f (f.smooth ⊤) hc).comp P := by
  intro P
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [finiteEnergyColumnOperator_coeFn (quotientMeasure 0)
      (fun z => P (cylinderTimeColumn f hc he R hR hs z))
      (cylinderTimeColumn_compact_input_memLp f hc he R hR hs ha b) v,
    cylinderTimePacket_column_coeFn f (f.smooth ⊤) he hc hr R hR hs
      (evenCoshLift_support_of_time_support f R hR hs) (P v)] with z hcol hwave
  change _=cylinderTimePacket f (f.smooth ⊤) hc (P v) z
  rw [hcol,hwave]
  have hp : P.adjoint=P := AsymptoticRegionL2.projection_adjoint _ _ _
  simpa only [hp,cylinderTimeColumn] using (P.adjoint_inner_right (cylinderTimeColumn f hc he R hR hs z) v).symm

include hr in
/-- Exact cyclic transfer of the full-output compact-input trace to the
compact-output wave trace. Compactness, square summability and self-adjointness
are all proved for the actual packet. -/
theorem compact_input_column_trace_cyclic {ι : Type*} [Countable ι]
    (basis : HilbertBasis ι ℂ (Lp ℂ 2 (quotientMeasure 0)))
    {a : ℝ} (ha : 0<a) (b : ℝ)
    (T : Lp ℂ 2 (quotientMeasure 0)→L[ℂ]Lp ℂ 2 (quotientMeasure 0)) :
    let P := AsymptoticRegionL2.projection (quotientMeasure 0) (upperRectangle 0 1 a b)
      (upperRectangle_compact _ _ _ _ ha).measurableSet
    let W := cylinderTimePacket f (f.smooth ⊤) hc
    columnLinearTrace (quotientMeasure 0)
      (fun z => P (cylinderTimeColumn f hc he R hR hs z)) T=
      ∑' i,(inner ℂ (P (W (basis i))) (T (P (W (basis i))))).re := by
  intro P W
  rw [columnLinearTrace_adjoint_basis _ _
    (cylinderTimeColumn_compact_input_memLp f hc he R hR hs ha b) basis T,
    compact_input_column_operator f hc he hr R hR hs ha b,adjoint_comp,
    AsymptoticRegionL2.projection_adjoint,
    (cylinderTimePacket_isSelfAdjoint f (f.smooth ⊤) hc hr).adjoint_eq]
  rfl

#print axioms columnLinearTrace_adjoint_basis
#print axioms compact_input_column_operator
#print axioms compact_input_column_trace_cyclic
end QuantitativeMaass
