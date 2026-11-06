module

public import AsymptoticClassicalCuspTraceV1

set_option autoImplicit false
@[expose] public noncomputable section

namespace AsymptoticClassicalCusp

open UpperHalfPlane
open scoped ModularForm

variable {G H : Subgroup (GL (Fin 2) ℝ)} [G.HasDetOne] [H.HasDetOne]
  [G.IsFiniteRelIndex H] (k : ℤ) (h : G ≤ H)

omit [G.HasDetOne] [H.HasDetOne] in
theorem index_complex_ne_zero : (Nat.card (H ⧸ G.subgroupOf H) : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.card_pos (α := H ⧸ G.subgroupOf H)).ne'

/-- A right inverse of the classical trace, obtained by dividing the old
 inclusion by the finite relative index. -/
def traceSection : CuspForm H k →ₗ[ℂ] CuspForm G k :=
  (Nat.card (H ⧸ G.subgroupOf H) : ℂ)⁻¹ • restrict k h

theorem trace_section (f : CuspForm H k) : trace k (traceSection k h f) = f := by
  change trace k ((Nat.card (H ⧸ G.subgroupOf H) : ℂ)⁻¹ • restrict k h f) = f
  rw [map_smul, trace_restrict, smul_smul,
    inv_mul_cancel₀ (index_complex_ne_zero (G := G) (H := H)), one_smul]

include h in
theorem trace_surjective : Function.Surjective (trace k : CuspForm G k →ₗ[ℂ] CuspForm H k) :=
  fun f => ⟨traceSection k h f, trace_section k h f⟩

/-- The new part relative to one lower level is killed by its actual trace. -/
def traceComplement : CuspForm G k →ₗ[ℂ] CuspForm G k :=
  LinearMap.id - (traceSection k h).comp (trace k)

theorem trace_complement (f : CuspForm G k) : trace (H := H) k (traceComplement k h f) = 0 := by
  change trace k (f - traceSection k h (trace k f)) = 0
  rw [map_sub, trace_section, sub_self]

theorem old_new_decomposition (f : CuspForm G k) :
    f = traceComplement k h f + traceSection k h (trace k f) := by
  change f = (f - traceSection k h (trace k f)) + traceSection k h (trace k f)
  exact (sub_add_cancel _ _).symm

theorem old_trace_kernel_disjoint :
    Disjoint (LinearMap.range (restrict k h))
      (LinearMap.ker (trace k : CuspForm G k →ₗ[ℂ] CuspForm H k)) := by
  rw [Submodule.disjoint_def]
  rintro f ⟨g, rfl⟩ hg
  have he : (Nat.card (H ⧸ G.subgroupOf H) : ℂ) • g = 0 :=
    (trace_restrict k h g).symm.trans hg
  have hg0 : g = 0 := (smul_eq_zero.mp he).resolve_left
    (index_complex_ne_zero (G := G) (H := H))
  simp [hg0]

#print axioms index_complex_ne_zero
#print axioms trace_section
#print axioms trace_surjective
#print axioms trace_complement
#print axioms old_new_decomposition
#print axioms old_trace_kernel_disjoint

end AsymptoticClassicalCusp
