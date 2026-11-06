module

public import AsymptoticCylinderTerminalV1
public import AsymptoticAnalyticReconstructionV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticCylinderReconstruction

open MeasureTheory ContinuousLinearMap FinitenessCertificate FinitenessGlobalHeight
open FinitenessAnalyticReconstruction AsymptoticCylinderLift AsymptoticCylinderTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

/-- Terminal cylinder data as terminal hyperbolic-strip data. -/
noncomputable def terminalLift (P : Parameters A) :
    AsymptoticCylinderTerminal.Space P.ε →L[ℂ] AsymptoticGeometricReconstruction.TerminalSpace A P :=
  (lift.toContinuousLinearMap.comp (AsymptoticCylinderTerminal.Space P.ε).subtypeL).codRestrict
    (AsymptoticGeometricReconstruction.TerminalSpace A P) (by
      intro g
      apply (AsymptoticRegionL2.mem_space _ _ _ _).mpr
      change hyperProjection P.ε (lift (g:AsymptoticCylinder.Space))=lift (g:AsymptoticCylinder.Space)
      rw [← lift_projection]
      have hg : projection P.ε (g:AsymptoticCylinder.Space)=(g:AsymptoticCylinder.Space) :=
        (AsymptoticRegionL2.mem_space _ _ _ _).mp g.property
      rw [hg])

theorem terminalLift_coe (P : Parameters A) (g : AsymptoticCylinderTerminal.Space P.ε) :
    (terminalLift A P g:AsymptoticHyperbolicSlash.Space)=lift (g:AsymptoticCylinder.Space) := rfl

theorem terminalLift_norm (P : Parameters A) (g : AsymptoticCylinderTerminal.Space P.ε) :
    ‖terminalLift A P g‖=‖g‖ := lift_norm (g:AsymptoticCylinder.Space)

theorem terminalLift_norm_le (P : Parameters A) : ‖terminalLift A P‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simp only [terminalLift_norm,one_mul,le_refl]

theorem lift_adjoint_norm_le : ‖lift.toContinuousLinearMap.adjoint‖≤1 := by
  rw [ContinuousLinearMap.adjoint.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖lift f‖≤1*‖f‖
  rw [lift_norm,one_mul]

/-- The bounded reconstruction operator in the actual cylinder L²
realization used by the Fourier trace estimates. -/
noncomputable def extension (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (m : ℕ) :
    AsymptoticCylinderTerminal.Space P.ε →L[ℂ] AsymptoticCylinder.Space :=
  lift.toContinuousLinearMap.adjoint.comp
    ((AsymptoticGeometricReconstruction.extension A hN P χ m).comp (terminalLift A P))

theorem extension_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (m : ℕ)
    (hK : ‖AsymptoticCertificateOperators.low A hN P χ (P.s+3) m‖<1)
    (g : AsymptoticCylinderTerminal.Space P.ε) :
    projection P.ε (extension A hN P χ m g)=(g:AsymptoticCylinder.Space) := by
  change projection P.ε (lift.toContinuousLinearMap.adjoint
    (AsymptoticGeometricReconstruction.extension A hN P χ m (terminalLift A P g)))=_
  rw [adjoint_projection]
  have hh := AsymptoticGeometricReconstruction.extension_terminal A hN P χ m hK (terminalLift A P g)
  change hyperProjection P.ε
    (AsymptoticGeometricReconstruction.extension A hN P χ m (terminalLift A P g))=
      lift (g:AsymptoticCylinder.Space) at hh
  rw [hh,adjoint_lift]

/-- The terminal norm survives the extra capped-weight inclusion used
in the common Fourier Gram bound. -/
theorem extension_inclusion_norm_ge (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (m : ℕ)
    (hK : ‖AsymptoticCertificateOperators.low A hN P χ (P.s+3) m‖<1)
    (g : AsymptoticCylinderTerminal.Space P.ε) :
    ‖g‖≤‖(AsymptoticCylinder.inclusion P.epsilon_pos).comp (extension A hN P χ m) g‖ := by
  change ‖g‖≤‖AsymptoticCylinder.inclusion P.epsilon_pos (extension A hN P χ m g)‖
  have he : projection P.ε (AsymptoticCylinder.inclusion P.epsilon_pos (extension A hN P χ m g))=
      (g:AsymptoticCylinder.Space) :=
    (projection_inclusion P.epsilon_pos _).trans (extension_terminal A hN P χ m hK g)
  calc
    ‖g‖=‖projection P.ε (AsymptoticCylinder.inclusion P.epsilon_pos (extension A hN P χ m g))‖ := by rw [he]; rfl
    _ ≤ ‖projection P.ε‖*‖AsymptoticCylinder.inclusion P.epsilon_pos (extension A hN P χ m g)‖ :=
      (projection P.ε).le_opNorm _
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (projection_norm_le P.ε) (norm_nonneg (AsymptoticCylinder.inclusion P.epsilon_pos (extension A hN P χ m g)))

theorem extension_norm_le (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (hχ : ∀ q,q∣Q → ‖χ q‖=1) (m : ℕ)
    (hK : ‖AsymptoticCertificateOperators.low A hN P χ (P.s+3) m‖<1/2) :
    ‖extension A hN P χ m‖≤1+2*AsymptoticCertificateOperators.terminalConstant A P := by
  have h₁ := opNorm_comp_le lift.toContinuousLinearMap.adjoint
    ((AsymptoticGeometricReconstruction.extension A hN P χ m).comp (terminalLift A P))
  have h₂ := opNorm_comp_le (AsymptoticGeometricReconstruction.extension A hN P χ m) (terminalLift A P)
  have he : ‖extension A hN P χ m‖≤‖AsymptoticGeometricReconstruction.extension A hN P χ m‖ := by
    apply h₁.trans
    apply le_trans (mul_le_mul_of_nonneg_right lift_adjoint_norm_le (norm_nonneg _))
    rw [one_mul]
    apply h₂.trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (terminalLift_norm_le A P) (norm_nonneg _)
  exact he.trans (AsymptoticGeometricReconstruction.extension_norm_le A hN P χ hχ m hK)

theorem terminalLift_restrict (P : Parameters A) (f : AsymptoticCylinder.Space) :
    terminalLift A P (AsymptoticRegionL2.restrict AsymptoticCylinder.measure
      (region P.ε) (region_measurable P.ε) f)=
      AsymptoticRegionL2.restrict volume (AsymptoticCertificateOperators.highStrip P.ε)
        (AsymptoticCertificateOperators.highStrip_measurable P.ε) (lift f) := by
  apply Subtype.ext
  exact lift_projection P.ε f

theorem extension_of_FE (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ) (m : ℕ)
    (F : ℂ → ℂ) (hp : ∀ z,F (z+1)=F z)
    (hFE : ∀ q : ℕ,q∣Q → ∀ z : ℂ,0<z.im →
      twist F q z=χ q/((Real.sqrt (Nat.lcm N (q^2)):ℂ)*z)^(2*m)*
        twist F q (-1/((Nat.lcm N (q^2):ℕ)*z)))
    (f : AsymptoticCylinder.Space)
    (hf : lift f =ᵐ[volume] AsymptoticWeightedBranches.stripSection P.ε (P.s+3) m F)
    (hK : ‖AsymptoticCertificateOperators.low A hN P χ (P.s+3) m‖<1) :
    extension A hN P χ m (AsymptoticRegionL2.restrict AsymptoticCylinder.measure
      (region P.ε) (region_measurable P.ε) f)=f := by
  change lift.toContinuousLinearMap.adjoint
    (AsymptoticGeometricReconstruction.extension A hN P χ m (terminalLift A P _))=f
  rw [terminalLift_restrict,
    AsymptoticAnalyticReconstruction.extension_of_FE A hN P χ m F hp hFE (lift f) hf hK,
    adjoint_lift]

#print axioms extension_terminal
#print axioms extension_inclusion_norm_ge
#print axioms extension_norm_le
#print axioms extension_of_FE

end AsymptoticCylinderReconstruction
