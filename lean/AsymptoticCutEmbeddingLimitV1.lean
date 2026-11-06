module

public import AsymptoticInvariantCutTraceV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCoordinateCut

open MeasureTheory Filter ContinuousLinearMap AsymptoticRegularTrace AsymptoticOrbitDiagonal
open scoped lp ENNReal Topology

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- Bounded injective maps on exhausting coordinate cuts suffice for
a trace-dimension comparison on the full source. The ambient finite
trace controls all dimension lost at the cuts. -/
theorem trace_le_of_cut_embeddings (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (U S V : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ x,CompleteSpace (U x)] [∀ x,CompleteSpace (S x)] [∀ x,CompleteSpace (V x)]
    (hUS : ∀ x,U x≤S x)
    (hmU : ∀ g h,Measurable (fun x => matrix (U x).starProjection g h))
    (hmS : ∀ g h,Measurable (fun x => matrix (S x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection))
    (hcS : Covariant (fun x => (S x).starProjection))
    (hfin : trace μ (fun x => (S x).starProjection)<∞)
    (s : ℕ → Set α) (hs : ∀ n,MeasurableSet (s n))
    (hinv : ∀ n x v,v∈S x → corner (s n) x v∈S x)
    (hexhaust : ∀ x,∀ᶠ n in atTop,x∈s n)
    (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hmB : ∀ n g h,Measurable (fun x => matrix (B n x) g h))
    (hcB : ∀ n,Covariant (B n)) (M : ℕ → ℝ) (hM : ∀ n x,‖B n x‖≤M n)
    (hinj : ∀ n x v,v∈cutSpace (U x) (s n) x → B n x v=0 → v=0)
    (hmap : ∀ n x v,v∈cutSpace (U x) (s n) x → B n x v∈V x) :
    trace μ (fun x => (U x).starProjection)≤trace μ (fun x => (V x).starProjection) := by
  by_cases hv : trace μ (fun x => (V x).starProjection)=∞
  · rw [hv]
    exact le_top
  have huf := projection_trace_finite_of_le μ U S hUS hfin
  apply (ENNReal.toReal_le_toReal huf.ne hv).mp
  have hcut := fun n => cutSpace_regular (fun g => (hmp g).measurable) U hmU hcU (s n) (hs n)
  have hbound (n : ℕ) :
      (trace μ (fun x => (cutSpace (U x) (s n) x).starProjection)).toReal≤
        (trace μ (fun x => (V x).starProjection)).toReal := by
    apply ENNReal.toReal_mono hv
    exact trace_le_of_injective_map μ hmp (fun x => cutSpace (U x) (s n) x) V
      (hcut n).1 (hcut n).2 (B n) (hmB n) (hcB n) (M n) (hM n) (hinj n) (hmap n)
  have hdef (n : ℕ) := remaining_trace_deficit μ hmp U S hUS hmU hmS hcU hcS
    (fun x => 1-corner (s n) x)
    (matrix_sub_measurable _ _ (fun _ _ => measurable_const)
      (corner_matrix_measurable (fun g => (hmp g).measurable) (hs n)))
    (covariant_sub _ _ covariant_one (corner_covariant (s n))) 2 (complement_norm_le (s n)) hfin
  have hlim := trace_toReal_cutSpace_tendsto μ S (hmS 1 1) s hs hinv hexhaust hfin
  have ht : Tendsto (fun n => (trace μ (fun x => (V x).starProjection)).toReal+
      ((trace μ (fun x => (S x).starProjection)).toReal-
        (trace μ (fun x => (cutSpace (S x) (s n) x).starProjection)).toReal)) atTop
      (𝓝 (trace μ (fun x => (V x).starProjection)).toReal) := by
    have hS : Tendsto (fun _ : ℕ => (trace μ (fun x => (S x).starProjection)).toReal) atTop
        (𝓝 (trace μ (fun x => (S x).starProjection)).toReal) := tendsto_const_nhds
    have hV : Tendsto (fun _ : ℕ => (trace μ (fun x => (V x).starProjection)).toReal) atTop
        (𝓝 (trace μ (fun x => (V x).starProjection)).toReal) := tendsto_const_nhds
    simpa only [sub_self,add_zero] using hV.add (hS.sub hlim)
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds ht
  intro n
  have hdn := hdef n
  change (trace μ (fun x => (U x).starProjection)).toReal≤
    (trace μ (fun x => (cutSpace (U x) (s n) x).starProjection)).toReal+
      ((trace μ (fun x => (S x).starProjection)).toReal-
        (trace μ (fun x => (cutSpace (S x) (s n) x).starProjection)).toReal) at hdn
  linarith [hbound n]

#print axioms trace_le_of_cut_embeddings

end AsymptoticCoordinateCut
