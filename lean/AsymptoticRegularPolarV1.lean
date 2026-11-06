module

public import AsymptoticRegularFunctionalCalculusV1
public import AsymptoticPolarBoundsV1
public import AsymptoticIdentityObservationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory ContinuousLinearMap AsymptoticPolarIsometry AsymptoticObservation
open scoped lp

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]

theorem absolute_regular (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M) :
    (∀ g h,Measurable (fun x => matrix (absolute (T x)) g h)) ∧
      Covariant (fun x => absolute (T x)) := by
  have hb (x : α) : ‖(T x).adjoint.comp (T x)‖≤M^2 := by
    rw [norm_adjoint_comp_self]
    nlinarith [hM x,norm_nonneg (T x)]
  have hr := sqrt_regular (fun x => (T x).adjoint.comp (T x))
    (matrix_comp_measurable _ _ (matrix_adjoint_measurable T hm) hm)
    (covariant_comp _ _ (covariant_adjoint T hc) hc)
    (fun x => nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self (T x))) (M^2) hb
  simpa only [← absolute_eq_positiveRoot] using hr

theorem penaltyRoot_regular (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M) :
    (∀ g h,Measurable (fun x => matrix (penaltyRoot (T x)) g h)) ∧
      Covariant (fun x => penaltyRoot (T x)) := by
  obtain ⟨ha,hca⟩ := absolute_regular T hm hc M hM
  have hr := sqrt_regular (fun x => absolute (T x)) ha hca
    (fun x => absolute_nonneg (T x)) M (fun x => by rw [absolute_opNorm]; exact hM x)
  simpa only [← penaltyRoot_eq_positiveRoot] using hr

theorem resolvent_regular (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M) (n : ℕ) :
    (∀ g h,Measurable (fun x => matrix (AsymptoticPolarIsometry.resolvent (T x) n) g h)) ∧
      Covariant (fun x => AsymptoticPolarIsometry.resolvent (T x) n) := by
  obtain ⟨hr,hcr⟩ := penaltyRoot_regular T hm hc M hM
  have hb (x : α) : ‖(((n+1:ℕ):ℂ) • penaltyRoot (T x))‖≤((n+1:ℕ):ℝ)*Real.sqrt M := by
    rw [norm_smul,Complex.norm_natCast,penaltyRoot_opNorm]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hM x)) (by positivity)
  have he := identity_observation_regular (fun x => (((n+1:ℕ):ℂ) • penaltyRoot (T x)))
    (matrix_smul_measurable _ _ hr) (covariant_smul _ _ hcr) _ hb
  simpa only [AsymptoticPolarIsometry.resolvent,amplified] using he

theorem regularizedPolar_regular (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M) (n : ℕ) :
    (∀ g h,Measurable (fun x => matrix (regularizedPolar (T x) n) g h)) ∧
      Covariant (fun x => regularizedPolar (T x) n) := by
  obtain ⟨hr,hcr⟩ := resolvent_regular T hm hc M hM n
  exact ⟨matrix_smul_measurable _ _ (matrix_comp_measurable _ _ hm hr),
    covariant_smul _ _ (covariant_comp _ _ hc hcr)⟩

/-- The actual polar family is measurable and covariant. These are
consequences of regularity of the input, not additional hypotheses on
its polar decomposition. -/
theorem polar_regular (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M) :
    (∀ g h,Measurable (fun x => matrix (polar (T x)) g h)) ∧
      Covariant (fun x => polar (T x)) := by
  have hr := regularizedPolar_regular T hm hc M hM
  have ht := fun x v => regularizedPolar_strong_limit (T x) v
  exact ⟨strong_limit_matrix_measurable _ _ (fun n => (hr n).1) ht,
    covariant_of_strong_limit _ _ (fun n => (hr n).2) ht⟩

/-- The two support projections of a uniformly bounded regular operator
family have equal rooted trace. The equality allows infinite trace and
nonclosed ranges. -/
theorem support_trace_eq (μ : Measure α)
    (hmp : ∀ g : G,MeasurePreserving (fun x : α => g • x) μ μ)
    (T : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hm : ∀ g h,Measurable (fun x => matrix (T x) g h)) (hc : Covariant T)
    (M : ℝ) (hM : ∀ x,‖T x‖≤M) :
    trace μ (fun x => (T x).kerᗮ.starProjection)=
      trace μ (fun x => (outputSpace (T x)).starProjection) := by
  obtain ⟨hp,hcp⟩ := polar_regular T hm hc M hM
  exact support_trace_eq_of_polar_covariant μ hmp T hp hcp

#print axioms absolute_regular
#print axioms penaltyRoot_regular
#print axioms resolvent_regular
#print axioms regularizedPolar_regular
#print axioms polar_regular
#print axioms support_trace_eq

end AsymptoticRegularTrace
