module

public import AsymptoticFiniteBranchReconstructionV1
public import AsymptoticRegularFiniteReconstructionV1
public import AsymptoticCylinderFiniteReconstructionV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane MeasureTheory Filter Set ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight AsymptoticCylinderLift

/-- The extra capped height factor, as a common branch datum. -/
noncomputable def weight {ε : ℝ} (hε : 0<ε) : Branch where
  label := 1
  coefficient z := (AsymptoticRegularInclusion.weight ε z:ℂ)
  measurable := (Complex.continuous_ofReal.comp (AsymptoticRegularInclusion.weight_continuous ε)).measurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := AsymptoticRegularInclusion.weight_norm_le hε

theorem holomorphic_weight {ε : ℝ} (hε : 0<ε) (m : ℕ) :
    holomorphic (weight hε) m=AsymptoticL2Multiplier.operator (weight hε).coefficient
      (weight hε).measurable.aestronglyMeasurable (Eventually.of_forall (weight hε).norm_le) :=
  AsymptoticConcreteRationalBranch.operator_one_label _ _ _ m

theorem regular_weight {ε : ℝ} (hε : 0<ε) (z : ℍ) :
    regular (weight hε) z=AsymptoticRegularInclusion.inclusion hε z := rfl

theorem holomorphic_weight_adjoint {ε : ℝ} (hε : 0<ε) (m : ℕ) :
    (holomorphic (weight hε) m).adjoint=holomorphic (weight hε) m := by
  rw [holomorphic_weight]
  exact AsymptoticL2Multiplier.operator_adjoint _ _ _
    (Eventually.of_forall (fun z => by simp [weight]))

theorem lift_inclusion {ε : ℝ} (hε : 0<ε) (m : ℕ) (f : AsymptoticCylinder.Space) :
    lift (AsymptoticCylinder.inclusion hε f)=holomorphic (weight hε) m (lift f) := by
  rw [holomorphic_weight]
  apply Lp.ext
  filter_upwards [lift_coeFn_of_ae _ _ (AsymptoticCylinder.inclusion_coeFn hε f),
    AsymptoticL2Multiplier.operator_coeFn (weight hε).coefficient
      (weight hε).measurable.aestronglyMeasurable (Eventually.of_forall (weight hε).norm_le) (lift f),
    lift_coeFn f] with z hl hw hf
  rw [hl,hw,hf]
  classical
  by_cases hs : z∈AsymptoticMassTransport.strip
  · simp only [Set.indicator_of_mem hs]
    change (z.im:ℂ)*(((min (z.im/ε) 1:ℝ):ℂ)*f (AsymptoticStripCoordinates.cylinder z))=_
    change _=((min (z.im/ε) 1:ℝ):ℂ)*((z.im:ℂ)*f (AsymptoticStripCoordinates.cylinder z))
    ring
  · simp [hs]

theorem adjoint_inclusion {ε : ℝ} (hε : 0<ε) (m : ℕ) :
    (AsymptoticCylinder.inclusion hε).comp lift.toContinuousLinearMap.adjoint=
      lift.toContinuousLinearMap.adjoint.comp (holomorphic (weight hε) m) := by
  have he : lift.toContinuousLinearMap.comp (AsymptoticCylinder.inclusion hε)=
      (holomorphic (weight hε) m).comp lift.toContinuousLinearMap := by
    ext1 f
    exact lift_inclusion hε m f
  have hh := congrArg ContinuousLinearMap.adjoint he
  simpa only [adjoint_comp,AsymptoticCylinder.inclusion_adjoint,holomorphic_weight_adjoint] using hh

noncomputable def heightCorner (Y : ℝ) : Branch :=
  corner (AsymptoticRegularHeightCutoff.region Y) (AsymptoticRegularHeightCutoff.region_measurable Y)

theorem lift_heightCorner (Y : ℝ) (m : ℕ) (f : AsymptoticCylinder.Space) :
    lift (AsymptoticCylinderTerminal.projection Y f)=holomorphic (heightCorner Y) m (lift f) := by
  rw [heightCorner,holomorphic_corner]
  apply Lp.ext
  filter_upwards [lift_coeFn_of_ae _ _ (AsymptoticCylinderTerminal.projection_coeFn Y f),
    AsymptoticRegionL2.projection_coeFn volume (AsymptoticRegularHeightCutoff.region Y)
      (AsymptoticRegularHeightCutoff.region_measurable Y) (lift f),lift_coeFn f] with z hl hp hf
  rw [hl,hp]
  classical
  by_cases hs : z∈AsymptoticMassTransport.strip <;> by_cases hy : Y≤z.im <;>
    simp [hs,hy,hf,AsymptoticRegularHeightCutoff.region,AsymptoticCylinderTerminal.region,
      AsymptoticStripCoordinates.cylinder]

theorem adjoint_heightCorner (Y : ℝ) (m : ℕ) :
    (AsymptoticCylinderTerminal.projection Y).comp lift.toContinuousLinearMap.adjoint=
      lift.toContinuousLinearMap.adjoint.comp (holomorphic (heightCorner Y) m) := by
  have he : lift.toContinuousLinearMap.comp (AsymptoticCylinderTerminal.projection Y)=
      (holomorphic (heightCorner Y) m).comp lift.toContinuousLinearMap := by
    ext1 f
    exact lift_heightCorner Y m f
  have hh := congrArg ContinuousLinearMap.adjoint he
  simpa only [adjoint_comp,AsymptoticCylinderTerminal.projection_adjoint,heightCorner,
    holomorphic_corner,AsymptoticRegionL2.projection_adjoint] using hh

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def cutFullExpression (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (Y : ℝ) (n : ℕ) (I : Finset ℤ) : Expression :=
  composeExpression [heightCorner Y]
    (composeExpression [weight P.epsilon_pos] (fullExpression A hN P χ n I))

theorem regularSum_cutFullExpression (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (Y : ℝ) (n : ℕ) (I : Finset ℤ) (z : ℍ) :
    regularSum (cutFullExpression A hN P χ Y n I) z=
      AsymptoticRegularReconstruction.finiteCutFull A hN P χ Y n I z := by
  rw [cutFullExpression,regularSum_compose,regularSum_compose,regularSum_fullExpression]
  simp only [regularSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    regular_weight,heightCorner,regular_corner]
  rfl

theorem cylinder_fullExpression (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (n : ℕ) (I : Finset ℤ) (m : ℕ) :
    lift.toContinuousLinearMap.adjoint.comp
      ((holomorphicSum (fullExpression A hN P χ n I) m).comp
        (lift.toContinuousLinearMap.comp (AsymptoticCylinderTerminal.Space P.ε).subtypeL))=
      AsymptoticCylinderReconstruction.finiteExtension A hN P χ n I m := by
  have ht : lift.toContinuousLinearMap.comp (AsymptoticCylinderTerminal.Space P.ε).subtypeL=
      (AsymptoticGeometricReconstruction.TerminalSpace A P).subtypeL.comp
        (AsymptoticCylinderReconstruction.terminalLift A P) := rfl
  rw [ht,← comp_assoc (holomorphicSum (fullExpression A hN P χ n I) m),
    holomorphicSum_fullExpression_on_terminal]
  rfl

theorem cylinder_cutFullExpression (hN : 0<N) (P : Parameters A) (χ : ℕ → ℂ)
    (Y : ℝ) (n : ℕ) (I : Finset ℤ) (m : ℕ) :
    lift.toContinuousLinearMap.adjoint.comp
      ((holomorphicSum (cutFullExpression A hN P χ Y n I) m).comp
        (lift.toContinuousLinearMap.comp (AsymptoticCylinderTerminal.Space P.ε).subtypeL))=
      (AsymptoticCylinder.inclusion P.epsilon_pos).comp
        ((AsymptoticCylinderTerminal.projection Y).comp
          (AsymptoticCylinderReconstruction.finiteExtension A hN P χ n I m)) := by
  rw [cutFullExpression,holomorphicSum_compose,holomorphicSum_compose]
  have hs (b : Branch) : holomorphicSum [b] m=holomorphic b m := by
    simp only [holomorphicSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  rw [hs,hs]
  apply ContinuousLinearMap.ext
  intro g
  have hp (u : AsymptoticHyperbolicSlash.Space) :
      lift.toContinuousLinearMap.adjoint (holomorphic (heightCorner Y) m u)=
        AsymptoticCylinderTerminal.projection Y (lift.toContinuousLinearMap.adjoint u) :=
    (congrArg (fun T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticCylinder.Space => T u)
      (adjoint_heightCorner Y m)).symm
  have hw (u : AsymptoticHyperbolicSlash.Space) :
      lift.toContinuousLinearMap.adjoint (holomorphic (weight P.epsilon_pos) m u)=
        AsymptoticCylinder.inclusion P.epsilon_pos (lift.toContinuousLinearMap.adjoint u) :=
    (congrArg (fun T : AsymptoticHyperbolicSlash.Space →L[ℂ] AsymptoticCylinder.Space => T u)
      (adjoint_inclusion P.epsilon_pos m)).symm
  simp only [comp_apply]
  rw [hp,hw]
  have hf := congrArg (fun T : AsymptoticCylinderTerminal.Space P.ε →L[ℂ] AsymptoticCylinder.Space => T g)
    (cylinder_fullExpression A hN P χ n I m)
  simp only [comp_apply] at hf
  rw [hf]
  exact congrArg (fun T : AsymptoticCylinder.Space →L[ℂ] AsymptoticCylinder.Space =>
    T (AsymptoticCylinderReconstruction.finiteExtension A hN P χ n I m g))
      (AsymptoticCylinderTerminal.projection_comp_inclusion P.epsilon_pos Y)

#print axioms holomorphic_weight
#print axioms regular_weight
#print axioms holomorphic_weight_adjoint
#print axioms lift_inclusion
#print axioms adjoint_inclusion
#print axioms lift_heightCorner
#print axioms adjoint_heightCorner
#print axioms regularSum_cutFullExpression
#print axioms cylinder_fullExpression
#print axioms cylinder_cutFullExpression

end AsymptoticFiniteBranch
