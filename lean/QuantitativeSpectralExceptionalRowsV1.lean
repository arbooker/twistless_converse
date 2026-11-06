module

public import AsymptoticRankSubadditivityV1
public import AsymptoticOrbitRegionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public noncomputable section

namespace QuantitativeSpectralExceptionalRows

open MeasureTheory ContinuousLinearMap AsymptoticRegularTrace
open AsymptoticOrbitDiagonal AsymptoticPolarIsometry AsymptoticObservationStack
open scoped lp ENNReal InnerProductSpace

variable {G α : Type*} [Group G] [MulAction G α]

/-- The literal omitted output of an observation, with no restriction
or normalization imposed on its source. -/
def omitted (s : Set α) (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (x : α) :
    ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) := (corner s x).comp (T x)

def retained (s : Set α) (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (x : α) :
    ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) := (corner sᶜ x).comp (T x)

theorem retained_add_omitted (s : Set α) (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (x : α) :
    retained s T x + omitted s T x = T x := by
  classical
  ext v g
  simp only [retained, omitted, add_apply, comp_apply, lp.coeFn_add, Pi.add_apply,
    corner_apply, Set.mem_compl_iff]
  by_cases hg : g • x ∈ s <;> simp [hg]

theorem omitted_fixed (s : Set α) (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (x : α) :
    (corner s x).comp (omitted s T x) = omitted s T x := by
  rw [omitted, ← comp_assoc, corner_idempotent]

theorem omitted_norm_le (s : Set α) (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (x : α) :
    ‖omitted s T x‖ ≤ ‖T x‖ := by
  exact (opNorm_comp_le _ _).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (AsymptoticOrbitRegion.corner_norm_le (G := G) s x) (norm_nonneg (T x)))

theorem region_projection (s : Set α) (x : α) :
    (AsymptoticOrbitRegion.Space (G := G) s x).starProjection = corner s x := by
  apply ContinuousLinearMap.ext
  intro v
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (AsymptoticOrbitRegion.mem_space s x _).mpr
    exact congrArg (fun B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) => B v) (corner_idempotent s x)
  · intro w hw
    have hw' := (AsymptoticOrbitRegion.mem_space s x w).mp hw
    change inner ℂ (v - corner s x v) w = 0
    rw [inner_sub_left, ← (corner s x).adjoint_inner_right, corner_adjoint, hw', sub_self]

/-- The closed output range is contained in the genuine geometric
corner even when the observation has nonclosed range. -/
theorem omitted_output_le (s : Set α) (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ)) (x : α) :
    outputSpace (omitted s T x) ≤ AsymptoticOrbitRegion.Space s x := by
  apply Submodule.topologicalClosure_minimal
  · rintro v ⟨u, rfl⟩
    apply (AsymptoticOrbitRegion.mem_space s x _).mpr
    exact congrArg (fun B : ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ) => B u) (omitted_fixed s T x)
  · exact (corner s x - ContinuousLinearMap.id ℂ _).isClosed_ker

variable [Countable G] [MeasurableSpace α]

theorem omitted_regular
    (hact : ∀ g : G, Measurable (fun x : α => g • x))
    {s : Set α} (hs : MeasurableSet s)
    (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h, Measurable (fun x => matrix (T x) g h)) (hc : Covariant T) :
    (∀ g h, Measurable (fun x => matrix (omitted s T x) g h)) ∧
      Covariant (omitted s T) :=
  ⟨matrix_comp_measurable _ _ (corner_matrix_measurable hact hs) hm,
    covariant_comp _ _ (corner_covariant s) hc⟩

/-- The actual polar rank of an omitted row is bounded by its geometric
output area, with no multiplication by its operator norm. -/
theorem omitted_rank_le_area (μ : Measure α)
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    {s : Set α} (hs : MeasurableSet s)
    (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h, Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x, ‖T x‖ ≤ M) :
    trace μ (fun x => (omitted s T x).kerᗮ.starProjection) ≤ μ s := by
  have hr := omitted_regular (fun g => (hmp g).measurable) hs T hm hc
  rw [support_trace_eq μ hmp _ hr.1 hr.2 M
    (fun x => (omitted_norm_le s T x).trans (hM x))]
  calc
    _ ≤ trace μ (fun x => (AsymptoticOrbitRegion.Space (G := G) s x).starProjection) :=
      projection_trace_mono μ _ _ (omitted_output_le s T)
    _ = μ s := by simp only [region_projection, trace_corner μ hs]

/-- Finite labelled omitted rows have total actual polar rank at most
one geometric output area per label. No closed-range assumption occurs. -/
theorem omitted_stack_rank_le_area {ι : Type*} [Fintype ι] (μ : Measure α)
    (hmp : ∀ g : G, MeasurePreserving (fun x : α => g • x) μ μ)
    {s : Set α} (hs : MeasurableSet s)
    (T : α → ι → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ i g h, Measurable (fun x => matrix (T x i) g h))
    (hc : ∀ i, Covariant (fun x => T x i))
    (M : ι → ℝ) (hM0 : ∀ i, 0 ≤ M i) (hM : ∀ x i, ‖T x i‖ ≤ M i) :
    trace μ (fun x => (stack (fun i => omitted s (fun y => T y i) x)).kerᗮ.starProjection) ≤
      (Fintype.card ι : ℝ≥0∞) * μ s := by
  have hr (i : ι) := omitted_regular (fun g => (hmp g).measurable) hs
    (fun x => T x i) (hm i) (hc i)
  have hbound (x : α) := stack_norm_le
    (fun i => omitted s (fun y => T y i) x) M hM0
    (fun i => (omitted_norm_le s (fun y => T y i) x).trans (hM x i))
  apply (stack_rank_le_sum μ hmp _ (fun i => (hr i).1) (fun i => (hr i).2)
    _ hbound).trans
  calc
    _ ≤ ∑ _i : ι, μ s := Finset.sum_le_sum (fun i _ =>
      omitted_rank_le_area μ hmp hs (fun x => T x i) (hm i) (hc i) (M i) (fun x => hM x i))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

#print axioms retained_add_omitted
#print axioms omitted_output_le
#print axioms omitted_rank_le_area
#print axioms omitted_stack_rank_le_area

end QuantitativeSpectralExceptionalRows
