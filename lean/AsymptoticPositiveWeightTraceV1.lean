module

public import AsymptoticPositiveCoordinateWeightV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticPositiveCoordinateWeight

open MeasureTheory AsymptoticRegularTrace AsymptoticCoordinateCut AsymptoticOrbitDiagonal
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

/-- A positive finite coordinate weight gives a trace-dimension
inequality whenever its pointwise multiplication transports the kernel
equations. The product is only required to be square summable when it
is an actual target vector; no global multiplier domain is imposed. -/
theorem trace_le_of_positive_weight (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (U S V : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ x,CompleteSpace (U x)] [∀ x,CompleteSpace (S x)] [∀ x,CompleteSpace (V x)]
    (hUS : ∀ x,U x≤S x)
    (hmU : ∀ g h,Measurable (fun x => matrix (U x).starProjection g h))
    (hmS : ∀ g h,Measurable (fun x => matrix (S x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection))
    (hcS : Covariant (fun x => (S x).starProjection))
    (hfin : trace μ (fun x => (S x).starProjection)<∞)
    (b : α → ℝ) (hb : ∀ x,0<b x) (hmb : Measurable b)
    (hinv : ∀ n x v,v∈S x → corner (region b n) x v∈S x)
    (htransport : ∀ x (u v : ℓ²(G,ℂ)),u∈U x →
      (∀ g,v g=(b (g • x):ℂ)*u g) → v∈V x) :
    trace μ (fun x => (U x).starProjection)≤trace μ (fun x => (V x).starProjection) := by
  apply trace_le_of_cut_embeddings μ hmp U S V hUS hmU hmS hcU hcS hfin
    (region b) (region_measurable b hmb) hinv (region_exhaust b) (multiplier b hb)
    (fun n => multiplier_matrix_measurable (fun g => (hmp g).measurable) b hb hmb n)
    (multiplier_covariant b hb) (fun n => ((n+1:ℕ):ℝ)) (multiplier_norm_le b hb)
  · exact fun n x v hv hz => multiplier_injective_on_cut b hb n x (U x) v hv hz
  · intro n x u hu
    apply htransport x u (multiplier b hb n x u) ((cutSpace_mem _ _ _ _).mp hu).1
    exact multiplier_on_cut b hb n x (U x) u hu

/-- Positive coordinate weights preserve kernel trace dimension.
Applying the same one-sided truncation argument to the reciprocal
weight proves the reverse inequality. -/
theorem trace_eq_of_positive_weight (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (U S V : α → Submodule ℂ ℓ²(G,ℂ))
    [∀ x,CompleteSpace (U x)] [∀ x,CompleteSpace (S x)] [∀ x,CompleteSpace (V x)]
    (hUS : ∀ x,U x≤S x) (hVS : ∀ x,V x≤S x)
    (hmU : ∀ g h,Measurable (fun x => matrix (U x).starProjection g h))
    (hmS : ∀ g h,Measurable (fun x => matrix (S x).starProjection g h))
    (hmV : ∀ g h,Measurable (fun x => matrix (V x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection))
    (hcS : Covariant (fun x => (S x).starProjection))
    (hcV : Covariant (fun x => (V x).starProjection))
    (hfin : trace μ (fun x => (S x).starProjection)<∞)
    (b : α → ℝ) (hb : ∀ x,0<b x) (hmb : Measurable b)
    (hinv : ∀ n x v,v∈S x → corner (region b n) x v∈S x)
    (hinv' : ∀ n x v,v∈S x → corner (region (fun x => (b x)⁻¹) n) x v∈S x)
    (hforward : ∀ x (u v : ℓ²(G,ℂ)),u∈U x →
      (∀ g,v g=(b (g • x):ℂ)*u g) → v∈V x)
    (hbackward : ∀ x (u v : ℓ²(G,ℂ)),v∈V x →
      (∀ g,v g=(b (g • x):ℂ)*u g) → u∈U x) :
    trace μ (fun x => (U x).starProjection)=trace μ (fun x => (V x).starProjection) := by
  apply le_antisymm
  · exact trace_le_of_positive_weight μ hmp U S V hUS hmU hmS hcU hcS hfin b hb hmb hinv hforward
  · apply trace_le_of_positive_weight μ hmp V S U hVS hmV hmS hcV hcS hfin
      (fun x => (b x)⁻¹) (fun x => inv_pos.mpr (hb x)) hmb.inv hinv'
    intro x v u hv he
    apply hbackward x u v hv
    intro g
    rw [he g,Complex.ofReal_inv,← mul_assoc,mul_inv_cancel₀
      (Complex.ofReal_ne_zero.mpr (hb (g • x)).ne'),one_mul]

#print axioms trace_le_of_positive_weight
#print axioms trace_eq_of_positive_weight

end AsymptoticPositiveCoordinateWeight
