module

public import QuantitativeMaassOrbitIntegralV1
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QuantitativeMaass.AutomorphicL2

variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]

/-- Actual measurable invariant functions of finite quotient L² norm. -/
def representatives (H : Subgroup G) (ν : Measure α) : Submodule ℂ (α → ℂ) where
  carrier := {f | Measurable f ∧ (∀ g : H, ∀ x, f (g.val • x) = f x) ∧ MemLp f 2 ν}
  zero_mem' := ⟨measurable_const, by simp, MemLp.zero⟩
  add_mem' := by
    rintro f g ⟨hf,hfi,hfL⟩ ⟨hg,hgi,hgL⟩
    exact ⟨hf.add hg, by intro a x; simp only [Pi.add_apply,hfi,hgi], hfL.add hgL⟩
  smul_mem' := by
    rintro c f ⟨hf,hfi,hfL⟩
    exact ⟨hf.const_smul c, by intro a x; simp only [Pi.smul_apply,hfi], hfL.const_smul c⟩

/-- Passage to genuine almost-everywhere classes, with no injectivity claim
for pointwise representatives. -/
def embedding (H : Subgroup G) (ν : Measure α) : representatives H ν →ₗ[ℂ] Lp ℂ 2 ν where
  toFun f := f.property.2.2.toLp f.val
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(f+g).property.2.2.coeFn_toLp, f.property.2.2.coeFn_toLp,
      g.property.2.2.coeFn_toLp, Lp.coeFn_add (f.property.2.2.toLp _) (g.property.2.2.toLp _)]
      with x hfg hf hg ha
    simp only [ha, hf, hg, Pi.add_apply]
    simpa only [Submodule.coe_add, Pi.add_apply] using hfg
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(c • f).property.2.2.coeFn_toLp, f.property.2.2.coeFn_toLp,
      Lp.coeFn_smul c (f.property.2.2.toLp _)] with x hcf hf hs
    simp only [RingHom.id_apply, hs, hf, Pi.smul_apply]
    simpa only [Submodule.coe_smul, Pi.smul_apply] using hcf

/-- The Hilbert completion of actual automorphic functions in their
quotient norm, realized as a closed subspace of the concrete quotient L². -/
def space (H : Subgroup G) (ν : Measure α) : Submodule ℂ (Lp ℂ 2 ν) :=
  (LinearMap.range (embedding H ν)).topologicalClosure

instance space_complete (H : Subgroup G) (ν : Measure α) : CompleteSpace (space H ν) :=
  (LinearMap.range (embedding H ν)).isClosed_topologicalClosure.completeSpace_coe

def denseEmbedding (H : Subgroup G) (ν : Measure α) : representatives H ν →ₗ[ℂ] space H ν :=
  (embedding H ν).codRestrict (space H ν) (fun f =>
    (LinearMap.range (embedding H ν)).le_topologicalClosure (LinearMap.mem_range_self _ f))

theorem denseEmbedding_dense (H : Subgroup G) (ν : Measure α) :
    DenseRange (denseEmbedding H ν) := by
  let e := embedding H ν
  have hd : DenseRange (Set.inclusion
      (show Set.range e ⊆ closure (Set.range e) from subset_closure)) :=
    (denseRange_inclusion_iff subset_closure).2 subset_rfl
  have hs : Function.Surjective (Set.rangeFactorization e) := Set.rangeFactorization_surjective
  exact hd.comp hs.denseRange (continuous_inclusion subset_closure)

theorem embedding_norm (H : Subgroup G) (ν : Measure α) (f : representatives H ν) :
    ‖denseEmbedding H ν f‖ = (eLpNorm f.val 2 ν).toReal :=
  Lp.norm_toLp f.val f.property.2.2

#print axioms denseEmbedding_dense
#print axioms embedding_norm

end QuantitativeMaass.AutomorphicL2
