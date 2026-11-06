module

public import AsymptoticInversePolynomialV1
public import AsymptoticSharedNormalBoundV1
public import AsymptoticRegularCutTerminalTraceV1
public import AsymptoticSignedCornerContinuityV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticRegularTrace

open MeasureTheory AsymptoticCoerciveNeumann
open scoped lp

variable {G α : Type*} [Group G] [MulAction G α]

theorem polynomial_covariant (C : ℝ) (M : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hM : Covariant M) (n : ℕ) : Covariant (fun x => polynomial C (M x) n) := by
  apply covariant_smul
  apply covariant_finsetSum
  intro j _
  exact covariant_pow _ (step_covariant C M hM) j

omit [Group G] [MulAction G α] in
theorem polynomial_matrix_measurable [MeasurableSpace α] [Countable G]
    (C : ℝ) (M : α → ℓ²(G,ℂ) →L[ℂ] ℓ²(G,ℂ))
    (hM : ∀ a b,Measurable (fun x => matrix (M x) a b)) (n : ℕ) (a b : G) :
    Measurable (fun x => matrix (polynomial C (M x) n) a b) := by
  apply matrix_smul_measurable
  intro u v
  apply matrix_finsetSum_measurable
  intro j _ x y
  exact matrix_pow_measurable _ (step_matrix_measurable C M hM) j x y

#print axioms polynomial_covariant
#print axioms polynomial_matrix_measurable

end AsymptoticRegularTrace

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap Filter AsymptoticRegularTrace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCoerciveNeumann
open AsymptoticRegularFoldedLow (Space)
open AsymptoticCompactObservationCount (Row)
open scoped Topology

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- The shared polynomial scale represents the same actual inverse. -/
theorem cutInverse_eq_shared_series (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (z : ℍ) :
    cutInverse A hN P r s hs e Y z=
      inverse (AsymptoticSharedApproximation.normalBound A hN P r s hs) (cutNormal A hN P r s hs e Y z) :=
  (inverse_eq_of_left_inverse _ _
    ((cutNormal_norm_le A hN P r s hs e Y z).trans (AsymptoticSharedApproximation.regular_bound_le A hN P r s hs))
    (cutNormal_coercive A hN P r s hs e Y hY z) _ (cutInverse_mul A hN P r s hs e Y hY z)).symm

noncomputable def cutInversePolynomial (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (n : ℕ) (z : ℍ) : Space →L[ℂ] Space :=
  polynomial (AsymptoticSharedApproximation.normalBound A hN P r s hs) (cutNormal A hN P r s hs e Y z) n

theorem cutInversePolynomial_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (n : ℕ) (z : ℍ) :
    ‖cutInversePolynomial A hN P r s hs e Y n z-cutInverse A hN P r s hs e Y z‖≤
      polynomialError (AsymptoticSharedApproximation.normalBound A hN P r s hs) n := by
  rw [cutInverse_eq_shared_series A hN P r s hs e Y hY z]
  exact polynomial_error _ _
    ((cutNormal_norm_le A hN P r s hs e Y z).trans (AsymptoticSharedApproximation.regular_bound_le A hN P r s hs))
    (cutNormal_coercive A hN P r s hs e Y hY z) n

theorem cutInversePolynomial_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) (n : ℕ) (z : ℍ) :
    ‖cutInversePolynomial A hN P r s hs e Y n z‖≤
      polynomialError (AsymptoticSharedApproximation.normalBound A hN P r s hs) n+1 := by
  calc
    _ = ‖(cutInversePolynomial A hN P r s hs e Y n z-cutInverse A hN P r s hs e Y z)+
      cutInverse A hN P r s hs e Y z‖ := by rw [sub_add_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add
      (cutInversePolynomial_error A hN P r s hs e Y hY n z) (cutInverse_norm_le A hN P r s hs e Y hY z))

theorem cutInversePolynomial_covariant (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (n : ℕ) :
    Covariant (cutInversePolynomial A hN P r s hs e Y n) :=
  polynomial_covariant _ _ (cutNormal_covariant A hN P r s hs e Y) n

theorem cutInversePolynomial_matrix_measurable (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (Y : ℝ) (n : ℕ)
    (a b : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix (cutInversePolynomial A hN P r s hs e Y n z) a b) :=
  polynomial_matrix_measurable _ _ (cutNormal_matrix_measurable A hN P r s hs e Y) n a b

/-- A common finite polynomial degree approximates the actual cutoff
inverse at all orbit roots and in all sectors. -/
theorem cutInversePolynomial_tendstoUniformly (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℝ)
    (hY : Y≤(AsymptoticReconstructedCount.parameters A P).ε) :
    TendstoUniformly
      (fun n (ez : Sector N × ℍ) => cutInversePolynomial A hN P r s hs ez.1 Y n ez.2)
      (fun ez : Sector N × ℍ => cutInverse A hN P r s hs ez.1 Y ez.2) atTop := by
  simp_rw [cutInverse_eq_shared_series A hN P r s hs _ Y hY]
  exact polynomial_tendstoUniformly _ _
    (fun ez => (cutNormal_norm_le A hN P r s hs ez.1 Y ez.2).trans
      (AsymptoticSharedApproximation.regular_bound_le A hN P r s hs))
    (fun ez => cutNormal_coercive A hN P r s hs ez.1 Y hY ez.2)

#print axioms cutInverse_eq_shared_series
#print axioms cutInversePolynomial_error
#print axioms cutInversePolynomial_norm_le
#print axioms cutInversePolynomial_covariant
#print axioms cutInversePolynomial_matrix_measurable
#print axioms cutInversePolynomial_tendstoUniformly

end AsymptoticRegularObservation
