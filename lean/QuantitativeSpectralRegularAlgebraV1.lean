module

public import QuantitativeSpectralCornerAlgebraV1
public import AsymptoticRegularSignedTraceV1
public import AsymptoticRegularStrongTraceV1
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Topology.Sequences

set_option autoImplicit false
@[expose] public section

open MeasureTheory ContinuousLinearMap
open scoped lp Topology

namespace QuantitativeSpectralRegularAlgebra

open AsymptoticRegularTrace

local instance complexCommSemiring : CommSemiring ℂ :=
  (inferInstance : CommRing ℂ).toCommSemiring

variable (G α : Type*) [Group G] [TopologicalSpace α]

/-- Uniformly bounded operator families. The discrete topology is used only
to realize the supremum-norm algebra; it imposes no continuity condition on
the original measurable base. -/
abbrev BoundedFamily := BoundedContinuousFunction α (ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))

noncomputable local instance familySemiring : Semiring (BoundedFamily G α) :=
  (inferInstance : Ring (BoundedFamily G α)).toSemiring

variable [MeasurableSpace α] [MulAction G α] [Countable G]

/-- The actual measurable covariant regular families form a star algebra. -/
def regularSubalgebra : StarSubalgebra ℂ (BoundedFamily G α) where
  carrier := {B | (∀ g h, Measurable (fun x => matrix (B x) g h)) ∧ Covariant B}
  zero_mem' := ⟨fun _ _ => measurable_const, by intro x a g h; simp [matrix]⟩
  one_mem' := ⟨fun _ _ => measurable_const, covariant_one⟩
  add_mem' hB hC := ⟨matrix_add_measurable _ _ hB.1 hC.1, covariant_add _ _ hB.2 hC.2⟩
  mul_mem' hB hC := ⟨matrix_comp_measurable _ _ hB.1 hC.1, covariant_comp _ _ hB.2 hC.2⟩
  algebraMap_mem' c := ⟨fun _ _ => measurable_const, by
    rw [Algebra.algebraMap_eq_smul_one]
    exact covariant_smul c (fun _ : α => (1 : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))) covariant_one⟩
  star_mem' hB := ⟨matrix_adjoint_measurable _ hB.1, covariant_adjoint _ hB.2⟩

/-- Uniform operator limits preserve both the measurable matrix entries and
the covariance equations. Thus this is a concrete closed C*-subalgebra. -/
theorem regular_isClosed : IsClosed (regularSubalgebra G α : Set (BoundedFamily G α)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro B C hB ht
  have he (x : α) : Filter.Tendsto (fun n => B n x) Filter.atTop (𝓝 (C x)) :=
    (continuous_eval_const x).continuousAt.tendsto.comp ht
  have hm (x : α) (g h : G) :
      Filter.Tendsto (fun n => matrix (B n x) g h) Filter.atTop (𝓝 (matrix (C x) g h)) :=
    (matrixCLM g h).continuous.continuousAt.tendsto.comp (he x)
  refine ⟨?_, ?_⟩
  · intro g h
    exact measurable_of_tendsto_metrizable (fun n => (hB n).1 g h)
      (tendsto_pi_nhds.mpr (fun x => hm x g h))
  · intro x a g h
    exact tendsto_nhds_unique (hm (a • x) g h)
      ((hm x (g*a) (h*a)).congr' (Filter.Eventually.of_forall (fun n => ((hB n).2 x a g h).symm)))

noncomputable instance regularCStar : CStarAlgebra (regularSubalgebra G α) := by
  letI : IsClosed (regularSubalgebra G α : Set (BoundedFamily G α)) := regular_isClosed G α
  letI : SubringClass (StarSubalgebra ℂ (BoundedFamily G α)) (BoundedFamily G α) :=
    @StarSubalgebra.subringClass ℂ (BoundedFamily G α) _ _ _ _ _ _
  exact StarSubalgebra.cstarAlgebra (regularSubalgebra G α)

#print axioms regularCStar

open AsymptoticOrbitDiagonal QuantitativeSpectralCornerAlgebra

variable [DiscreteTopology α]

variable (hact : ∀ g : G, Measurable (fun x : α => g • x))
  (s : Set α) (hs : MeasurableSet s)

/-- The geometric region projection as an element of the concrete algebra. -/
noncomputable def regionProjection : regularSubalgebra G α := by
  let B : BoundedFamily G α := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (corner (G:=G) s) 1 (fun x => by
      classical
      exact operator_norm_le _ _ _)
  exact ⟨B, corner_matrix_measurable hact hs, corner_covariant s⟩

@[simp] theorem regionProjection_apply (x : α) :
    (regionProjection G α hact s hs).val x = corner s x := rfl

theorem regionProjection_idempotent :
    IsIdempotentElem (regionProjection G α hact s hs) := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  exact corner_idempotent (G:=G) s x

theorem regionProjection_selfAdjoint :
    IsSelfAdjoint (regionProjection G α hact s hs) := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  exact corner_adjoint (G:=G) s x

/-- The actual finite geometric corner, whose unit is the region projection. -/
def FiniteCorner : Type _ := cornerSubalgebra (regionProjection G α hact s hs)
  (regionProjection_idempotent G α hact s hs)
  (regionProjection_selfAdjoint G α hact s hs)

noncomputable instance finiteCornerCStar : CStarAlgebra (FiniteCorner G α hact s hs) :=
  inferInstanceAs (CStarAlgebra (cornerSubalgebra (regionProjection G α hact s hs)
    (regionProjection_idempotent G α hact s hs)
    (regionProjection_selfAdjoint G α hact s hs)))

/-- Evaluation in the regular representation of the finite corner. -/
noncomputable def representation : FiniteCorner G α hact s hs →ₗ[ℝ]
    (α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) where
  toFun a x := a.val.val x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem representation_matrix_measurable (a : FiniteCorner G α hact s hs) (g h : G) :
    Measurable (fun x => matrix (representation G α hact s hs a x) g h) := a.val.property.1 g h

theorem representation_covariant (a : FiniteCorner G α hact s hs) :
    Covariant (representation G α hact s hs a) := a.val.property.2

theorem representation_norm_le (a : FiniteCorner G α hact s hs) (x : α) :
    ‖representation G α hact s hs a x‖ ≤ ‖a‖ := by
  exact a.val.val.norm_coe_le_norm x

theorem representation_mul (a b : FiniteCorner G α hact s hs) (x : α) :
    representation G α hact s hs (a*b) x =
      (representation G α hact s hs a x).comp (representation G α hact s hs b x) := rfl

theorem representation_star (a : FiniteCorner G α hact s hs) (x : α) :
    representation G α hact s hs (star a) x =
      (representation G α hact s hs a x).adjoint := rfl

theorem representation_supported (a : FiniteCorner G α hact s hs) (x : α) :
    (representation G α hact s hs a x).comp (corner s x) =
      representation G α hact s hs a x := by
  have he := ((Subsemigroup.mem_corner_iff
    (regionProjection_idempotent G α hact s hs)).mp a.property).2
  exact congrArg (fun b : regularSubalgebra G α => b.val x) he

#print axioms representation_supported
#print axioms representation_matrix_measurable

end QuantitativeSpectralRegularAlgebra
