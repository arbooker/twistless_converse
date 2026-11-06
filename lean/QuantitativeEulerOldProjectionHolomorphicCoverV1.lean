module

public import QuantitativeEulerOldProjectionHolomorphicV1
public import QuantitativeEulerOldEmbeddingV1

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace QuantitativeEulerOldProjectionHolomorphic

open UpperHalfPlane AsymptoticClassicalCusp AsymptoticClassicalPetersson
open scoped InnerProduct ComplexConjugate

variable (N M : ℕ) [NeZero N] [NeZero M] (k : ℤ) (hMN : M ∣ N)

/-- The weight-k Hilbert trace counts each finite covering sheet once. -/
theorem trace_inclusion (v : space M k) :
    trace N k M hMN (inclusion N k M hMN v) =
      (QuantitativeEulerOldEmbedding.coverIndex N M : ℂ) • v := by
  obtain ⟨f, rfl⟩ := (realization M k).surjective v
  rw [inclusion_realization, trace_realization]
  let : (level N).IsFiniteRelIndex (level M) :=
    ((Subgroup.IsArithmetic.is_commensurable (𝒢 := level N)).trans
      (Subgroup.IsArithmetic.is_commensurable (𝒢 := level M)).symm).1
  have he : arithmeticTrace (level N) (level M) k (restrict k (level_antitone hMN) f) =
      (Nat.card (level M ⧸ (level N).subgroupOf (level M)) : ℂ) • f :=
    trace_restrict k (level_antitone hMN) f
  rw [he, map_smul]
  congr 1
  exact_mod_cast Nat.card_congr (AsymptoticClassicalCosets.traceEquiv N M)

private theorem adjoint_scaled_norm_sq {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (I : E →L[ℂ] F) (d : ℕ) (v : E) (h : I.adjoint (I v) = (d : ℂ) • v) :
    ‖I v‖^2 = (d : ℝ) * ‖v‖^2 := by
  have he := I.adjoint_inner_left v (I v)
  rw [h, inner_smul_left, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K] at he
  have hr := congrArg Complex.re he
  simpa [← Complex.ofReal_pow] using hr.symm

/-- Exact covering factor in the actual weighted Petersson Hilbert norm. -/
theorem inclusion_norm_sq (v : space M k) :
    ‖inclusion N k M hMN v‖^2 =
      (QuantitativeEulerOldEmbedding.coverIndex N M : ℝ) * ‖v‖^2 :=
  adjoint_scaled_norm_sq (inclusion N k M hMN) _ v (trace_inclusion N M k hMN v)

#print axioms trace_inclusion
#print axioms inclusion_norm_sq
end QuantitativeEulerOldProjectionHolomorphic
