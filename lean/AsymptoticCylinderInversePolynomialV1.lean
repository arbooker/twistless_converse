module

public import AsymptoticInversePolynomialV1
public import AsymptoticSharedNormalBoundV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap

variable {G H J : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

theorem normal_norm_le_of_bounds (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (BR BL : ℝ) (hR : ‖R‖≤BR) (hL : ‖L‖≤BL) : ‖normal R L‖≤BR^2+(BL*BR)^2 := by
  have hL0 := (norm_nonneg L).trans hL
  have hLR : ‖L.comp R‖≤BL*BR :=
    (opNorm_comp_le _ _).trans (mul_le_mul hL hR (norm_nonneg R) hL0)
  have hn := norm_add_le (R.adjoint.comp R) ((L.comp R).adjoint.comp (L.comp R))
  apply hn.trans
  rw [norm_adjoint_comp_self,norm_adjoint_comp_self]
  simpa only [pow_two] using add_le_add (pow_le_pow_left₀ (norm_nonneg R) hR 2)
    (pow_le_pow_left₀ (norm_nonneg (L.comp R)) hLR 2)

/-- The inverse used by the positive observation construction equals
the explicit common-scale series inverse, by uniqueness. -/
theorem normal_inverse_eq_series (R : G →L[ℂ] H) (L : H →L[ℂ] J)
    (hR : ∀ g,‖g‖≤‖R g‖) (C : ℝ) (hC : ‖normal R L‖≤C) :
    (normalEquiv R L hR).symm.toContinuousLinearMap=AsymptoticCoerciveNeumann.inverse C (normal R L) := by
  apply ContinuousLinearMap.ext
  intro g
  have hi := AsymptoticCoerciveNeumann.inverse_apply_mul C (normal R L) hC (normal_coercive R L hR)
    ((normalEquiv R L hR).symm g)
  have hn : normal R L ((normalEquiv R L hR).symm g)=g :=
    (normalEquiv R L hR).apply_symm_apply g
  rw [hn] at hi
  exact hi.symm

#print axioms normal_norm_le_of_bounds
#print axioms normal_inverse_eq_series

end AsymptoticObservation

namespace AsymptoticCylinderObservation

open UpperHalfPlane Set ContinuousLinearMap Filter
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder AsymptoticObservation AsymptoticReconstructedCount AsymptoticCoerciveNeumann
open AsymptoticCompactObservationCount (Row)
open scoped Topology

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)


noncomputable def cutNormal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N) (Y : ℝ) :
    AsymptoticCylinderTerminal.Space (parameters A P).ε →L[ℂ] AsymptoticCylinderTerminal.Space (parameters A P).ε :=
  normal (cutReconstruction A hN P h e Y)
    (AsymptoticCompactObservationCount.observations hN r s hs (parameters A P).epsilon_pos
      ((parameters A P).s+4) (h+1) e)

theorem cutNormal_norm_le (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N) (Y : ℝ) :
    ‖cutNormal A hN P r s hs h e Y‖≤normalBound A hN P r s hs :=
  normal_norm_le_of_bounds _ _ _ _ (cutReconstruction_norm_le A hN P h e Y)
    (AsymptoticCompactObservationCount.observations_norm_le hN r s hs (parameters A P).epsilon_pos
      ((parameters A P).s+4) (h+1) e)

noncomputable def cutTerminalInverse (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY : Y≤(parameters A P).ε) :
    AsymptoticCylinderTerminal.Space (parameters A P).ε →L[ℂ] AsymptoticCylinderTerminal.Space (parameters A P).ε :=
  (normalEquiv (cutReconstruction A hN P h e Y)
    (AsymptoticCompactObservationCount.observations hN r s hs (parameters A P).epsilon_pos
      ((parameters A P).s+4) (h+1) e) (cutReconstruction_norm_ge A hN P h e Y hY)).symm.toContinuousLinearMap

theorem cutTerminalInverse_eq_series (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY : Y≤(parameters A P).ε) :
    cutTerminalInverse A hN P r s hs h e Y hY=
      inverse (AsymptoticSharedApproximation.normalBound A hN P r s hs) (cutNormal A hN P r s hs h e Y) :=
  normal_inverse_eq_series _ _ _ _ ((cutNormal_norm_le A hN P r s hs h e Y).trans (AsymptoticSharedApproximation.cylinder_bound_le A hN P r s hs))

noncomputable def cutInversePolynomial (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N) (Y : ℝ) (n : ℕ) :
    AsymptoticCylinderTerminal.Space (parameters A P).ε →L[ℂ] AsymptoticCylinderTerminal.Space (parameters A P).ε :=
  polynomial (AsymptoticSharedApproximation.normalBound A hN P r s hs) (cutNormal A hN P r s hs h e Y) n

theorem cutInversePolynomial_error (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (h : ℕ) (e : Sector N)
    (Y : ℝ) (hY : Y≤(parameters A P).ε) (n : ℕ) :
    ‖cutInversePolynomial A hN P r s hs h e Y n-cutTerminalInverse A hN P r s hs h e Y hY‖≤
      polynomialError (AsymptoticSharedApproximation.normalBound A hN P r s hs) n := by
  rw [cutTerminalInverse_eq_series]
  exact polynomial_error _ _ ((cutNormal_norm_le A hN P r s hs h e Y).trans (AsymptoticSharedApproximation.cylinder_bound_le A hN P r s hs))
    (normal_coercive _ _ (cutReconstruction_norm_ge A hN P h e Y hY)) n

theorem cutInversePolynomial_tendstoUniformly (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (Y : ℝ) (hY : Y≤(parameters A P).ε) :
    TendstoUniformly
      (fun n (he : ℕ × Sector N) => cutInversePolynomial A hN P r s hs he.1 he.2 Y n)
      (fun he : ℕ × Sector N => cutTerminalInverse A hN P r s hs he.1 he.2 Y hY) atTop := by
  simp_rw [cutTerminalInverse_eq_series]
  exact polynomial_tendstoUniformly _
    (fun he : ℕ × Sector N => cutNormal A hN P r s hs he.1 he.2 Y)
    (fun he => (cutNormal_norm_le A hN P r s hs he.1 he.2 Y).trans (AsymptoticSharedApproximation.cylinder_bound_le A hN P r s hs))
    (fun he => normal_coercive _ _ (cutReconstruction_norm_ge A hN P he.1 he.2 Y hY))

#print axioms cutNormal_norm_le
#print axioms cutTerminalInverse_eq_series
#print axioms cutInversePolynomial_error
#print axioms cutInversePolynomial_tendstoUniformly

end AsymptoticCylinderObservation
