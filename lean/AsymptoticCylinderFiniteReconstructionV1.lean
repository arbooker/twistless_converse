module

public import AsymptoticFiniteFoldReconstructionV1
public import AsymptoticCylinderCutTraceV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCylinderReconstruction

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight
open AsymptoticCylinderLift AsymptoticCylinder
open AsymptoticCertificateOperators (lowConstant terminalConstant)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Transport the actual finite depth/fold expression to the cylinder. -/
noncomputable def finiteExtension (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (d : ℕ) (I : Finset ℤ) (m : ℕ) : AsymptoticCylinderTerminal.Space P.ε →L[ℂ] Space :=
  lift.toContinuousLinearMap.adjoint.comp
    ((AsymptoticGeometricReconstruction.finiteFoldExtension A hN P χ d I m).comp (terminalLift A P))

theorem finiteExtension_norm_le (hN : 0<N) (P : Parameters A)
    (hP : P.ρ^(P.s+3-1)*lowConstant A P≤1/2) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (d : ℕ) (I : Finset ℤ) (m : ℕ) :
    ‖finiteExtension A hN P χ d I m‖≤1+2*terminalConstant A P := by
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right lift_adjoint_norm_le (norm_nonneg _)).trans
  rw [one_mul]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left (terminalLift_norm_le A P) (norm_nonneg _)).trans
  simpa only [mul_one] using
    AsymptoticGeometricReconstruction.finiteFoldExtension_norm_le A hN P hP χ hχ d I m

theorem finiteExtension_error (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (d : ℕ) (I : Finset ℤ) (m : ℕ) :
    ‖finiteExtension A hN P χ d I m-extension A hN P χ m‖≤
      ‖AsymptoticGeometricReconstruction.finiteFoldExtension A hN P χ d I m-
        AsymptoticGeometricReconstruction.extension A hN P χ m‖ := by
  have he : finiteExtension A hN P χ d I m-extension A hN P χ m=
      lift.toContinuousLinearMap.adjoint.comp
        ((AsymptoticGeometricReconstruction.finiteFoldExtension A hN P χ d I m-
          AsymptoticGeometricReconstruction.extension A hN P χ m).comp (terminalLift A P)) := by
    simp only [finiteExtension,extension,comp_sub,sub_comp]
  rw [he]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right lift_adjoint_norm_le (norm_nonneg _)).trans
  rw [one_mul]
  apply (opNorm_comp_le _ _).trans
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (terminalLift_norm_le A P) (norm_nonneg _)

#print axioms finiteExtension_norm_le
#print axioms finiteExtension_error

end AsymptoticCylinderReconstruction

namespace AsymptoticReconstructedCount

open ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticCylinder

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def finiteReconstruction (hN : 0<N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (d : ℕ) (I : Finset ℤ) : AsymptoticCylinderTerminal.Space (parameters A P).ε →L[ℂ] Space :=
  AsymptoticCylinderReconstruction.finiteExtension A hN (parameters A P) (multiplier e) d I (h+1)

theorem finiteReconstruction_norm_le (hN : 0<N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (d : ℕ) (I : Finset ℤ) :
    ‖finiteReconstruction A hN P h e d I‖≤1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P) :=
  AsymptoticCylinderReconstruction.finiteExtension_norm_le A hN _ (parameters_bound A P).le
    (multiplier e) (fun q _ => multiplier_norm e q) d I (h+1)

/-- The cutoff before the extra capped-weight inclusion. -/
noncomputable def cutBaseReconstruction (hN : 0<N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (Y : ℝ) : AsymptoticCylinderTerminal.Space (parameters A P).ε →L[ℂ] Space :=
  (AsymptoticCylinderTerminal.projection Y).comp (reconstruction A hN P h e)

noncomputable def finiteCutBaseReconstruction (hN : 0<N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) :
    AsymptoticCylinderTerminal.Space (parameters A P).ε →L[ℂ] Space :=
  (AsymptoticCylinderTerminal.projection Y).comp (finiteReconstruction A hN P h e d I)

noncomputable def finiteCutReconstruction (hN : 0<N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) :
    AsymptoticCylinderTerminal.Space (parameters A P).ε →L[ℂ] Space :=
  (inclusion (parameters A P).epsilon_pos).comp (finiteCutBaseReconstruction A hN P h e Y d I)

theorem cutBaseReconstruction_norm_le (hN : 0<N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (Y : ℝ) :
    ‖cutBaseReconstruction A hN P h e Y‖≤1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P) := by
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (AsymptoticCylinderTerminal.projection_norm_le Y) (norm_nonneg _)).trans
  simpa only [one_mul] using reconstruction_norm_le A hN P h e

theorem finiteCutBaseReconstruction_norm_le (hN : 0<N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) :
    ‖finiteCutBaseReconstruction A hN P h e Y d I‖≤
      1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P) := by
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (AsymptoticCylinderTerminal.projection_norm_le Y) (norm_nonneg _)).trans
  simpa only [one_mul] using finiteReconstruction_norm_le A hN P h e d I

theorem finiteCutReconstruction_norm_le (hN : 0<N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) :
    ‖finiteCutReconstruction A hN P h e Y d I‖≤
      1+2*AsymptoticCertificateOperators.terminalConstant A (parameters A P) := by
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (inclusion_norm_le (parameters A P).epsilon_pos) (norm_nonneg _)).trans
  simpa only [one_mul] using finiteCutBaseReconstruction_norm_le A hN P h e Y d I

/-- The same unweighted reconstruction error controls every cutoff,
which is stronger than merely controlling the final weighted operator. -/
theorem finiteCutBaseReconstruction_error (hN : 0<N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) :
    ‖finiteCutBaseReconstruction A hN P h e Y d I-cutBaseReconstruction A hN P h e Y‖≤
      ‖AsymptoticGeometricReconstruction.finiteFoldExtension A hN (parameters A P) (multiplier e) d I (h+1)-
        AsymptoticGeometricReconstruction.extension A hN (parameters A P) (multiplier e) (h+1)‖ := by
  change ‖(AsymptoticCylinderTerminal.projection Y).comp (finiteReconstruction A hN P h e d I)-
    (AsymptoticCylinderTerminal.projection Y).comp (reconstruction A hN P h e)‖≤_
  rw [← comp_sub]
  apply (opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (AsymptoticCylinderTerminal.projection_norm_le Y) (norm_nonneg _)).trans
  rw [one_mul]
  exact AsymptoticCylinderReconstruction.finiteExtension_error A hN _ (multiplier e) d I (h+1)

#print axioms finiteReconstruction_norm_le
#print axioms cutBaseReconstruction_norm_le
#print axioms finiteCutBaseReconstruction_norm_le
#print axioms finiteCutReconstruction_norm_le
#print axioms finiteCutBaseReconstruction_error

end AsymptoticReconstructedCount
