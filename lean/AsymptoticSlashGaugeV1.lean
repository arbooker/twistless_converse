module

public import AsymptoticOrbitDiagonalV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticSlashGauge

open UpperHalfPlane AsymptoticRationalGroup AsymptoticRationalFreeness
open AsymptoticRegularTrace ContinuousLinearMap InnerProductSpace MeasureTheory
open scoped lp ComplexConjugate

theorem phase_projective_eq {g h : GL (Fin 2) ℝ}
    (hgh : Matrix.ProjGenLinGroup.mk g=Matrix.ProjGenLinGroup.mk h) (m : ℕ) (z : ℍ) :
    AsymptoticHyperbolicSlash.phase g (2*m) z=AsymptoticHyperbolicSlash.phase h (2*m) z := by
  obtain ⟨u,rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hgh
  rw [AsymptoticHyperbolicSlash.phase_mul g _ (AsymptoticHyperbolicSlash.scalar_det_pos u),
    AsymptoticHyperbolicSlash.scalar_smul,AsymptoticHyperbolicSlash.phase_scalar,mul_one]

noncomputable def representative (g : AsymptoticRationalGroup.Group) : GL (Fin 2) ℚ :=
  Classical.choose g.val.property

theorem representative_spec (g : AsymptoticRationalGroup.Group) :
    rationalMap (representative g)=g.val.val := Classical.choose_spec g.val.property

theorem representative_action (g : AsymptoticRationalGroup.Group) (z : ℍ) :
    realMatrix (representative g) • z=g • z := by
  rw [← pglMk_smul]
  change rationalMap (representative g) • z=g • z
  rw [representative_spec]
  rfl

/-- The even-weight slash phase on the actual rational projective group.
Scalar independence makes the chosen rational representative immaterial. -/
noncomputable def phase (g : AsymptoticRationalGroup.Group) (m : ℕ) (z : ℍ) : ℂ :=
  AsymptoticHyperbolicSlash.phase (realMatrix (representative g)) (2*m) z

theorem phase_continuous (g : AsymptoticRationalGroup.Group) (m : ℕ) : Continuous (phase g m) :=
  AsymptoticHyperbolicSlash.phase_continuous _ _

theorem phase_norm (g : AsymptoticRationalGroup.Group) (m : ℕ) (z : ℍ) : ‖phase g m z‖=1 :=
  AsymptoticHyperbolicSlash.phase_norm _ _ _

theorem phase_one (m : ℕ) (z : ℍ) : phase 1 m z=1 := by
  have he : Matrix.ProjGenLinGroup.mk (realMatrix (representative 1))=
      Matrix.ProjGenLinGroup.mk 1 := by
    change rationalMap (representative 1)=_
    rw [representative_spec,map_one]
    rfl
  exact (phase_projective_eq he m z).trans (AsymptoticHyperbolicSlash.phase_one _ _)

theorem phase_mul (g h : AsymptoticRationalGroup.Group) (m : ℕ) (z : ℍ) :
    phase (g*h) m z=phase g m (h • z)*phase h m z := by
  have he : Matrix.ProjGenLinGroup.mk (realMatrix (representative (g*h)))=
      Matrix.ProjGenLinGroup.mk (realMatrix (representative g)*realMatrix (representative h)) := by
    rw [map_mul]
    change rationalMap (representative (g*h))=
      rationalMap (representative g)*rationalMap (representative h)
    rw [representative_spec,representative_spec,representative_spec]
    rfl
  unfold phase
  rw [phase_projective_eq he m z,
    AsymptoticHyperbolicSlash.phase_mul _ _ (representative_positive h (representative_spec h)),
    representative_action]

/-- A diagonal isometry on the counting coordinates of a rooted orbit.
On the proved conull free set these coordinates are the distinct points
of the actual rational orbit. -/
noncomputable def gauge (m : ℕ) (z : ℍ) :
    ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ) :=
  AsymptoticOrbitDiagonal.operator (fun g => phase g m z) zero_le_one
    (fun g => (phase_norm g m z).le)

theorem gauge_norm (m : ℕ) (z : ℍ) (f : ℓ²(AsymptoticRationalGroup.Group,ℂ)) :
    ‖gauge m z f‖=‖f‖ :=
  AsymptoticOrbitDiagonal.unit_norm _ (fun g => phase_norm g m z) f

theorem gauge_delta (m : ℕ) (z : ℍ) (g : AsymptoticRationalGroup.Group) :
    gauge m z (delta g)=phase g m z • delta g :=
  AsymptoticOrbitDiagonal.operator_delta _ _ _ g

theorem gauge_root (m : ℕ) (z : ℍ) : gauge m z (delta 1)=delta 1 := by
  rw [gauge_delta,phase_one,one_smul]

theorem gauge_adjoint_mul (m : ℕ) (z : ℍ) :
    (gauge m z).adjoint.comp (gauge m z)=ContinuousLinearMap.id ℂ _ :=
  AsymptoticOrbitDiagonal.unit_adjoint_mul _ (fun g => phase_norm g m z)

theorem gauge_mul_adjoint (m : ℕ) (z : ℍ) :
    (gauge m z).comp (gauge m z).adjoint=ContinuousLinearMap.id ℂ _ :=
  AsymptoticOrbitDiagonal.unit_mul_adjoint _ (fun g => phase_norm g m z)

/-- Conjugating an arbitrary bounded orbit operator gives precisely the
endpoint phases; all fixed signs and geometric amplitudes are unchanged. -/
theorem gauge_matrix (m : ℕ) (z : ℍ)
    (B : ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (g h : AsymptoticRationalGroup.Group) :
    matrix ((gauge m z).adjoint.comp (B.comp (gauge m z))) g h=
      conj (phase g m z)*phase h m z*matrix B g h := by
  rw [matrix,← delta_inner,comp_apply,adjoint_inner_right,comp_apply,
    gauge_delta,gauge_delta,map_smul,inner_smul_left,inner_smul_right,delta_inner]
  simp only [matrix]
  ring

/-- The endpoint phases on a rational branch reduce to its actual slash
phase by the cocycle. This is the weight-removal identity. -/
theorem branch_phase (a g : AsymptoticRationalGroup.Group) (m : ℕ) (z : ℍ) :
    conj (phase g m z)*phase (a*g) m z=phase a m (g • z) := by
  rw [phase_mul]
  calc
    conj (phase g m z)*(phase a m (g • z)*phase g m z)=
        phase a m (g • z)*(conj (phase g m z)*phase g m z) := by ring
    _ = _ := by rw [Complex.conj_mul',phase_norm]; simp

/-- Rooted traces are independent of the weight after the exact slash
gauge conjugation. No values of a holomorphic function are put in ℓ². -/
theorem trace_gauge (m : ℕ)
    (B : ℍ → ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ)) :
    trace volume (fun z => (gauge m z).adjoint.comp ((B z).comp (gauge m z)))=trace volume B := by
  simp only [trace,gauge_matrix,phase_one,map_one,one_mul]

theorem gauge_matrix_measurable (m : ℕ)
    (B : ℍ → ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hB : ∀ g h, Measurable (fun z => matrix (B z) g h))
    (g h : AsymptoticRationalGroup.Group) :
    Measurable (fun z => matrix ((gauge m z).adjoint.comp ((B z).comp (gauge m z))) g h) := by
  simp only [gauge_matrix]
  exact (((Complex.continuous_conj.comp (phase_continuous g m)).measurable).mul
    (phase_continuous h m).measurable).mul (hB g h)

/-- Re-rooting changes the gauge by a scalar of modulus one, which
cancels on conjugation. Thus the gauged family remains an orbit operator. -/
theorem gauge_covariant (m : ℕ)
    (B : ℍ → ℓ²(AsymptoticRationalGroup.Group,ℂ) →L[ℂ] ℓ²(AsymptoticRationalGroup.Group,ℂ))
    (hB : Covariant B) :
    Covariant (fun z => (gauge m z).adjoint.comp ((B z).comp (gauge m z))) := by
  intro z a g h
  simp only [gauge_matrix,hB z a g h,phase_mul,map_mul]
  symm
  calc
    conj (phase g m (a • z))*conj (phase a m z)*
        (phase h m (a • z)*phase a m z)*matrix (B z) (g*a) (h*a)=
      (conj (phase a m z)*phase a m z)*
        (conj (phase g m (a • z))*phase h m (a • z)*matrix (B z) (g*a) (h*a)) := by ring
    _ = _ := by rw [Complex.conj_mul',phase_norm]; simp

#print axioms phase_mul
#print axioms gauge_adjoint_mul
#print axioms gauge_mul_adjoint
#print axioms branch_phase
#print axioms trace_gauge
#print axioms gauge_matrix_measurable
#print axioms gauge_covariant

end AsymptoticSlashGauge
