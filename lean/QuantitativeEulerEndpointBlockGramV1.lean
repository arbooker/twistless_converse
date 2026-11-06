module

public import QuantitativeEulerEndpointSubcornerSharpV1
public import QuantitativeEulerEndpointCompressedMassV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointBlockGram
open ContinuousLinearMap AsymptoticRegularTrace QuantitativeSpectralCut
open QuantitativeEulerEndpointSubcorner QuantitativeEulerEndpointSubcornerSourceGram MeasureTheory
open scoped lp ENNReal

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h))
  (hcB : ∀ i, Covariant (B i)) (C : ℕ → ℝ) (hC : ∀ i x, ‖B i x‖≤C i)
  (hsource : ∀ i x, B i x*QuantitativeSpectralRegularAlgebra.representation G α hact s hs p x=B i x)
local notation "𝔄" => Subcorner hact s hs p hp
local notation "ρ" => representation hact s hs p hp

def gramSum (n : ℕ) : 𝔄 :=
  ∑ i : Fin n, gramElement hact s hs p hp (B i) (hmB i) (hcB i) (C i) (hC i) (hsource i)

theorem representation_gramSum (n : ℕ) (x : α) :
    ρ (gramSum hact s hs p hp B hmB hcB C hC hsource n) x=
      ∑ i : Fin n, star (B i x)*B i x := by
  simp only [gramSum,map_sum,Finset.sum_apply,representation_gramElement]

theorem gramSum_nonneg (n : ℕ) : 0≤gramSum hact s hs p hp B hmB hcB C hC hsource n :=
  Finset.sum_nonneg (fun i _ => gramElement_nonneg hact s hs p hp (B i) (hmB i) (hcB i)
    (C i) (hC i) (hsource i))

theorem gramSum_norm_le (n : ℕ) :
    ‖gramSum hact s hs p hp B hmB hcB C hC hsource n‖≤∑ i : Fin n, (C i)^2 := by
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun i _ => gramElement_norm_le hact s hs p hp (B i) (hmB i) (hcB i)
    (C i) (hC i) (hsource i))

theorem gramSum_le_one (n : ℕ) (hbound : (∑ i : Fin n, (C i)^2)≤1) :
    gramSum hact s hs p hp B hmB hcB C hC hsource n≤1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (gramSum_nonneg hact s hs p hp B hmB hcB C hC hsource n)).mp
    ((gramSum_norm_le hact s hs p hp B hmB hcB C hC hsource n).trans hbound)

variable (q : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hq : IsStarProjection q)
local notation "Q" => QuantitativeSpectralRegularAlgebra.representation G α hact s hs q

def rows (i : ℕ) (x : α) : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) := B i x*Q x

include hmB in
theorem rows_measurable (i : ℕ) :
    ∀ g h, Measurable (fun x => matrix (rows hact s hs B q i x) g h) :=
  matrix_comp_measurable _ _ (hmB i)
    (QuantitativeSpectralRegularAlgebra.representation_matrix_measurable G α hact s hs q)

include hcB in
theorem rows_covariant (i : ℕ) : Covariant (rows hact s hs B q i) :=
  covariant_comp _ _ (hcB i)
    (QuantitativeSpectralRegularAlgebra.representation_covariant G α hact s hs q)

include hq in
theorem projection_family (x : α) : IsStarProjection (Q x) := by
  constructor
  · exact congrArg (fun a => QuantitativeSpectralRegularAlgebra.representation G α hact s hs a x)
      hq.isIdempotentElem.eq
  · exact congrArg (fun a => QuantitativeSpectralRegularAlgebra.representation G α hact s hs a x)
      hq.isSelfAdjoint.star_eq

include hq hC in
theorem rows_norm (i : ℕ) (x : α) : ‖rows hact s hs B q i x‖≤C i := by
  have hproj := projection_family hact s hs q hq x
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hproj.nonneg).mpr hproj.le_one
  exact (norm_mul_le_of_le (hC i x) hn).trans_eq (mul_one _)

include hq in
theorem rows_source (i : ℕ) (x : α) : rows hact s hs B q i x*Q x=rows hact s hs B q i x := by
  change (B i x*Q x)*Q x=B i x*Q x
  rw [mul_assoc,(projection_family hact s hs q hq x).isIdempotentElem.eq]

/-- Restricting the actual residual rows gives precisely the hard
compression of their collective Gram, with no new energy assumption. -/
theorem restricted_gramSum (n : ℕ) (x : α) :
    representation hact s hs q hq
      (gramSum hact s hs q hq (rows hact s hs B q)
        (rows_measurable hact s hs B hmB q) (rows_covariant hact s hs B hcB q)
        C (rows_norm hact s hs B C hC q hq) (rows_source hact s hs B q hq) n) x=
      Q x*ρ (gramSum hact s hs p hp B hmB hcB C hC hsource n) x*Q x := by
  rw [representation_gramSum,representation_gramSum,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  change star (B i x*Q x)*(B i x*Q x)=Q x*(star (B i x)*B i x)*Q x
  rw [star_mul,(projection_family hact s hs q hq x).isSelfAdjoint.star_eq]
  simp only [mul_assoc]

#print axioms gramSum_nonneg
#print axioms gramSum_norm_le
#print axioms gramSum_le_one
#print axioms rows_measurable
#print axioms rows_covariant
#print axioms projection_family
#print axioms rows_norm
#print axioms rows_source
#print axioms restricted_gramSum
end QuantitativeEulerEndpointBlockGram
