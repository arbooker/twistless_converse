module

public import AsymptoticFiniteBranchSupportV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight AsymptoticCylinderLift AsymptoticSectorSigns
open AsymptoticHyperbolicSlash (Space)

theorem holomorphicSum_singleton (b : Branch) (m : ℕ) : holomorphicSum [b] m=holomorphic b m := add_zero _

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem holomorphicSum_cutFull_formula (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (Y : ℝ) (n : ℕ) (I : Finset ℤ) (m : ℕ) :
    holomorphicSum (cutFullExpression A hN P χ Y n I) m=
      (holomorphic (heightCorner Y) m).comp ((holomorphic (weight P.epsilon_pos) m).comp
        (holomorphicSum (fullExpression A hN P χ n I) m)) := by
  rw [cutFullExpression,holomorphicSum_compose,holomorphicSum_compose,
    holomorphicSum_singleton,holomorphicSum_singleton]

theorem holomorphicSum_cutFull_left_strip (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (Y : ℝ) (n : ℕ) (I : Finset ℤ) (m : ℕ) :
    stripProjection.comp (holomorphicSum (cutFullExpression A hN P χ Y n I) m)=
      holomorphicSum (cutFullExpression A hN P χ Y n I) m := by
  rw [holomorphicSum_cutFull_formula]
  ext1 f
  have hf := congrArg (fun T : Space →L[ℂ] Space => T f)
    (holomorphicSum_full_left_strip A hN P χ n I m)
  have hz := (AsymptoticRegionL2.projection_eq_self_iff volume AsymptoticMassTransport.strip
    AsymptoticMassTransport.strip_measurable _).mp hf
  obtain ⟨g,hg⟩ := exists_lift_of_support _ hz
  simp only [comp_apply]
  erw [← hg,← lift_inclusion,← lift_heightCorner]
  exact (AsymptoticRegionL2.projection_eq_self_iff volume AsymptoticMassTransport.strip
    AsymptoticMassTransport.strip_measurable _).mpr (lift_zero_off_strip _)

theorem holomorphicSum_cutFull_right_terminal (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (Y : ℝ) (n : ℕ) (I : Finset ℤ) (m : ℕ) :
    (holomorphicSum (cutFullExpression A hN P χ Y n I) m).comp (AsymptoticCertificateOperators.highProjection A P)=
      holomorphicSum (cutFullExpression A hN P χ Y n I) m := by
  rw [holomorphicSum_cutFull_formula]
  ext1 f
  exact congrArg (fun u : Space => holomorphic (heightCorner Y) m (holomorphic (weight P.epsilon_pos) m u))
    (congrArg (fun T : Space →L[ℂ] Space => T f) (holomorphicSum_full_right_terminal A hN P χ n I m))

/-- Lifting the actual finite cylinder reconstruction equals restricting
the common ambient branch expression to terminal data. -/
theorem lift_finiteCutReconstruction (hN : 0<N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) :
    lift.toContinuousLinearMap.comp (AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I)=
      (holomorphicSum (cutFullExpression A hN (AsymptoticReconstructedCount.parameters A P)
        (multiplier e) Y d I) (h+1)).comp
          (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let R := holomorphicSum (cutFullExpression A hN P' (multiplier e) Y d I) (h+1)
  let S := AsymptoticCylinderTerminal.ambientLift P'.ε
  have he : lift.toContinuousLinearMap.adjoint.comp (R.comp S)=
      AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I :=
    cylinder_cutFullExpression A hN P' (multiplier e) Y d I (h+1)
  have hr : stripProjection.comp R=R := holomorphicSum_cutFull_left_strip A hN P' (multiplier e) Y d I (h+1)
  ext1 g
  have heg := congrArg (fun T : AsymptoticCylinderTerminal.Space P'.ε →L[ℂ] AsymptoticCylinder.Space => T g) he
  change lift (AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I g)=R (S g)
  calc
    _ = lift (lift.toContinuousLinearMap.adjoint (R (S g))) := congrArg lift heg.symm
    _ = stripProjection (R (S g)) :=
      congrArg (fun T : Space →L[ℂ] Space => T (R (S g))) lift_comp_adjoint
    _ = _ := congrArg (fun T : Space →L[ℂ] Space => T (S g)) hr

/-- Exact identification on the entire ambient space, using the terminal
projection identity and the reconstruction's actual support. -/
theorem holomorphicSum_cutFull_eq_cylinder (hN : 0<N) (P : Parameters A) (h : ℕ)
    (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) :
    holomorphicSum (cutFullExpression A hN (AsymptoticReconstructedCount.parameters A P)
      (multiplier e) Y d I) (h+1)=
      lift.toContinuousLinearMap.comp
        ((AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I).comp
          (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε).adjoint) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let R := holomorphicSum (cutFullExpression A hN P' (multiplier e) Y d I) (h+1)
  let S := AsymptoticCylinderTerminal.ambientLift P'.ε
  have ht : S.comp S.adjoint=AsymptoticCertificateOperators.highProjection A P' :=
    AsymptoticCylinderTerminal.ambientLift_self_adjoint P'.ε
  have hr : R.comp (AsymptoticCertificateOperators.highProjection A P')=R :=
    holomorphicSum_cutFull_right_terminal A hN P' (multiplier e) Y d I (h+1)
  calc
    R = R.comp (S.comp S.adjoint) := by rw [ht,hr]
    _ = (R.comp S).comp S.adjoint := (comp_assoc _ _ _).symm
    _ = _ := by rw [← lift_finiteCutReconstruction]; rfl

#print axioms holomorphicSum_cutFull_formula
#print axioms holomorphicSum_cutFull_left_strip
#print axioms holomorphicSum_cutFull_right_terminal
#print axioms lift_finiteCutReconstruction
#print axioms holomorphicSum_cutFull_eq_cylinder

end AsymptoticFiniteBranch
