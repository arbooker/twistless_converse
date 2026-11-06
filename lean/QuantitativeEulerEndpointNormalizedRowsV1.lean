module

public import QuantitativeEulerEndpointBlockNormalizationV1

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1500000
@[expose] public noncomputable section
namespace QuantitativeEulerEndpointNormalizedRows
open ContinuousLinearMap QuantitativeSpectralDeflationChain
open QuantitativeEulerEndpointBlockNormalization QuantitativeEulerEndpointBlockRestriction
open AsymptoticRegularTrace MeasureTheory
open scoped lp

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance closedSubmodule_complete (U : ClosedSubmodule ℂ H) :
    CompleteSpace U.toSubmodule := U.isClosed.completeSpace_coe

/-- Restriction by a larger ambient source also leaves the hard packet
unchanged. The ambient operator need only fix the initial subspace. -/
theorem chain_restrict_ambient (U : ClosedSubmodule ℂ H) (B : ℕ → H →L[ℂ] H)
    (P : H →L[ℂ] H) (hPU : P*U.toSubmodule.starProjection=U.toSubmodule.starProjection)
    (c : ℝ) (n : ℕ) : chain U (fun i => B i*P) c n=chain U B c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [chain,chain,ih]
    apply step_eq_of_restriction
    have hle : chain U B c n≤U := chain_antitone U B c (Nat.zero_le n)
    have hu : U.toSubmodule.starProjection*(chain U B c n).toSubmodule.starProjection=
        (chain U B c n).toSubmodule.starProjection :=
      ContinuousLinearMap.ext (fun v => U.toSubmodule.starProjection_eq_self_iff.mpr
        (hle ((chain U B c n).toSubmodule.starProjection_apply_mem v)))
    have hp : P*(chain U B c n).toSubmodule.starProjection=
        (chain U B c n).toSubmodule.starProjection := by
      calc
        _ = P*(U.toSubmodule.starProjection*(chain U B c n).toSubmodule.starProjection) := by rw [hu]
        _ = _ := by rw [← mul_assoc,hPU,hu]
    rw [mul_assoc,hp]
theorem chain_scale_restrict (U : ClosedSubmodule ℂ H) (B : ℕ → H →L[ℂ] H)
    (P : H →L[ℂ] H) (hPU : P*U.toSubmodule.starProjection=U.toSubmodule.starProjection)
    {r : ℝ} (hr : 0<r) (c : ℝ) (n : ℕ) :
    chain U (fun i => (r:ℂ) • (B i*P)) (r*c) n=chain U B c n := by
  have hh := chain_positive_scale U (fun i => B i*P) hr c n
  rw [chain_restrict_ambient U B P hPU c n] at hh
  have he : (fun i => r • (B i*P))=(fun i => (r:ℂ) • (B i*P)) := by
    funext i
    exact RCLike.real_smul_eq_coe_smul (K:=ℂ) r (B i*P)
  rw [he] at hh
  exact hh
end Hilbert

variable {G α : Type*} [Group G] [Countable G] [TopologicalSpace α] [DiscreteTopology α]
  [MeasurableSpace α] [MulAction G α]
variable (hact : ∀ g : G, Measurable (fun x : α => g • x)) (s : Set α) (hs : MeasurableSet s)
  (p : QuantitativeSpectralRegularAlgebra.FiniteCorner G α hact s hs) (hp : IsStarProjection p)
  (B : ℕ → α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
  (hmB : ∀ i g h, Measurable (fun x => matrix (B i x) g h))
  (hcB : ∀ i, Covariant (B i)) (C : ℕ → ℝ) (hC : ∀ i x, ‖B i x‖≤C i)
local notation "P" => QuantitativeSpectralRegularAlgebra.representation G α hact s hs p

def row (n i : ℕ) (x : α) : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) := ((factor C n : ℝ):ℂ) • (B i x*P x)

def bound (n i : ℕ) : ℝ := factor C n*C i

include hmB in
theorem row_measurable (n i : ℕ) :
    ∀ g h, Measurable (fun x => matrix (row hact s hs p B C n i x) g h) :=
  matrix_smul_measurable ((factor C n : ℝ) : ℂ) _
    (matrix_comp_measurable _ _ (hmB i)
      (QuantitativeSpectralRegularAlgebra.representation_matrix_measurable G α hact s hs p))

include hcB in
theorem row_covariant (n i : ℕ) : Covariant (row hact s hs p B C n i) :=
  covariant_smul ((factor C n : ℝ) : ℂ) _
    (covariant_comp _ _ (hcB i)
      (QuantitativeSpectralRegularAlgebra.representation_covariant G α hact s hs p))

include hp hC in
theorem row_norm (n i : ℕ) (x : α) : ‖row hact s hs p B C n i x‖≤bound C n i := by
  have hb := QuantitativeEulerEndpointBlockGram.rows_norm hact s hs B C hC p hp i x
  rw [row,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (factor_pos C n)]
  exact mul_le_mul_of_nonneg_left hb (factor_pos C n).le

include hp in
theorem row_source (n i : ℕ) (x : α) : row hact s hs p B C n i x*P x=row hact s hs p B C n i x := by
  rw [row,smul_mul_assoc,mul_assoc,
    (QuantitativeEulerEndpointBlockGram.projection_family hact s hs p hp x).isIdempotentElem.eq]

theorem bound_square_sum (n : ℕ) : (∑ i : Fin n, (bound C n i)^2)≤1 :=
  normalized_square_sum C n

/-- The normalized, ambient-restricted rows have exactly the original
hard packet, for any initial source fixed by the ambient projection. -/
theorem projectionFamily_eq (U : α → ClosedSubmodule ℂ ℓ²(G,ℂ))
    (hPU : ∀ x, P x*(U x).toSubmodule.starProjection=(U x).toSubmodule.starProjection)
    (c : ℝ) (n j : ℕ) :
    QuantitativeSpectralRegularPacket.projectionFamily U (row hact s hs p B C n) (factor C n*c) j=
      QuantitativeSpectralRegularPacket.projectionFamily U B c j := by
  funext x
  change (chain (U x) (fun i => ((factor C n:ℝ):ℂ) • (B i x*P x)) (factor C n*c) j).toSubmodule.starProjection=
    (chain (U x) (fun i => B i x) c j).toSubmodule.starProjection
  rw [chain_scale_restrict _ _ _ (hPU x) (factor_pos C n)]

theorem row_kills (n i : ℕ) (E : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hPE : ∀ x, P x*E x=E x) (hBE : ∀ x, B i x*E x=0) (x : α) :
    row hact s hs p B C n i x*E x=0 := by
  rw [row,smul_mul_assoc,mul_assoc,hPE,hBE]
  apply ContinuousLinearMap.ext
  intro v
  simp only [_root_.smul_apply,_root_.zero_apply,smul_zero]

#print axioms chain_restrict_ambient
#print axioms row_measurable
#print axioms row_covariant
#print axioms row_norm
#print axioms row_source
#print axioms bound_square_sum
#print axioms projectionFamily_eq
#print axioms row_kills
end QuantitativeEulerEndpointNormalizedRows
