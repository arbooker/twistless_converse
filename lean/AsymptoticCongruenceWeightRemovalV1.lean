module

public import AsymptoticPositiveWeightTraceV1
public import AsymptoticDecodedQuotientV1
public import AsymptoticCongruenceProjectionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCongruenceQuotient

open UpperHalfPlane MeasureTheory AsymptoticCongruenceStrip AsymptoticCongruenceWeight
open AsymptoticRegularTrace AsymptoticOrbitDiagonal
open scoped lp ENNReal

/-- Congruence-invariant coordinate regions preserve the constructed
quotient Hilbert space. No regularity of the quotient representatives
chosen to express the factorization is required. -/
theorem corner_preserves_quotient (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (s : Set ℍ) (hs : ∀ h : gamma N,∀ z : ℍ,h.val • z∈s ↔ z∈s)
    (z : ℍ) (v : ℓ²(AsymptoticRationalGroup.Group,ℂ)) (hv : v∈quotientSpace N hε ht z) :
    corner s z v∈quotientSpace N hε ht z := by
  classical
  obtain ⟨f,rfl⟩ := hv
  have hinv (h : gamma N) (g : AsymptoticRationalGroup.Group) :
      (if (h.val*g) • z∈s then f (classOf N (h.val*g)) else 0)=
        if g • z∈s then f (classOf N g) else 0 := by
    simp only [mul_smul,hs,classOf_mul]
  obtain ⟨F,hF⟩ := factors N (fun g => if g • z∈s then f (classOf N g) else 0) hinv
  change corner s z (induction N hε ht z f)∈
    (AsymptoticFiberIsometry.linear (classOf N) (fun g => amplitude N ε t (g • z))
      (fibre_amplitude_hasSum N hε ht z)).range
  apply (AsymptoticFiberIsometry.range_iff _ _ _ _).mpr
  refine ⟨F,?_⟩
  intro g
  rw [corner_apply,induction_apply,← hF g]
  by_cases hg : g • z∈s <;> simp [hg]

/-- Positive weight removal inside the actual quotient realization.
Invariance of the weight discharges every cutoff-preservation condition. -/
theorem trace_le_of_quotient_weight (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (U V : ℍ → Submodule ℂ ℓ²(AsymptoticRationalGroup.Group,ℂ))
    [∀ x,CompleteSpace (U x)] [∀ x,CompleteSpace (V x)]
    (hU : ∀ x,U x≤quotientSpace N hε ht x)
    (hmU : ∀ g h,Measurable (fun x => matrix (U x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection))
    (hfin : trace volume (projection N hε ht)<∞)
    (b : ℍ → ℝ) (hb : ∀ x,0<b x) (hmb : Measurable b)
    (hbΓ : ∀ h : gamma N,∀ x,b (h.val • x)=b x)
    (htransport : ∀ x (u v : ℓ²(AsymptoticRationalGroup.Group,ℂ)),u∈U x →
      (∀ g,v g=(b (g • x):ℂ)*u g) → v∈V x) :
    trace volume (fun x => (U x).starProjection)≤trace volume (fun x => (V x).starProjection) := by
  apply AsymptoticPositiveCoordinateWeight.trace_le_of_positive_weight volume
    AsymptoticRationalGroup.measurePreserving U (quotientSpace N hε ht) V hU hmU
    (projection_matrix_measurable N hε ht) hcU (projection_covariant N hε ht) hfin b hb hmb
    _ htransport
  intro n x v hv
  apply corner_preserves_quotient N hε ht (AsymptoticPositiveCoordinateWeight.region b n) _ x v hv
  intro h y
  change b (h.val • y)≤((n+1:ℕ):ℝ) ↔ b y≤((n+1:ℕ):ℝ)
  rw [hbΓ]

/-- The actual positive coordinate weight taking normalized quotient
coordinates to the unweighted incidence equations. -/
noncomputable def normalizer (N : ℕ) (ε : ℝ) (t : ℕ) (z : ℍ) : ℝ :=
  (Real.sqrt (weight N ε t z))⁻¹

theorem normalizer_pos (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t) (z : ℍ) :
    0<normalizer N ε t z := inv_pos.mpr (Real.sqrt_pos.mpr (weight_pos N hε ht z))

theorem normalizer_measurable (N : ℕ) (ε : ℝ) (t : ℕ) : Measurable (normalizer N ε t) :=
  (weight_measurable N ε t).sqrt.inv

theorem normalizer_invariant (N : ℕ) (ε : ℝ) (t : ℕ) (h : gamma N) (z : ℍ) :
    normalizer N ε t (h.val • z)=normalizer N ε t z := by
  simp only [normalizer,weight_invariant]

theorem trace_le_of_normalized_transport (N : ℕ) {ε : ℝ} (hε : 0<ε) {t : ℕ} (ht : 1≤t)
    (U V : ℍ → Submodule ℂ ℓ²(AsymptoticRationalGroup.Group,ℂ))
    [∀ x,CompleteSpace (U x)] [∀ x,CompleteSpace (V x)]
    (hU : ∀ x,U x≤quotientSpace N hε ht x)
    (hmU : ∀ g h,Measurable (fun x => matrix (U x).starProjection g h))
    (hcU : Covariant (fun x => (U x).starProjection))
    (hfin : trace volume (projection N hε ht)<∞)
    (htransport : ∀ x (u v : ℓ²(AsymptoticRationalGroup.Group,ℂ)),u∈U x →
      (∀ g,v g=(normalizer N ε t (g • x):ℂ)*u g) → v∈V x) :
    trace volume (fun x => (U x).starProjection)≤trace volume (fun x => (V x).starProjection) :=
  trace_le_of_quotient_weight N hε ht U V hU hmU hcU hfin
    (normalizer N ε t) (normalizer_pos N hε ht) (normalizer_measurable N ε t)
    (normalizer_invariant N ε t) htransport

#print axioms corner_preserves_quotient
#print axioms trace_le_of_quotient_weight
#print axioms normalizer_pos
#print axioms normalizer_measurable
#print axioms normalizer_invariant
#print axioms trace_le_of_normalized_transport

end AsymptoticCongruenceQuotient
