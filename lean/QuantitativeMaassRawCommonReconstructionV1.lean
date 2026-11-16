module

public import QuantitativeMaassFullRegularSourceV1
public import QuantitativeMaassRawTerminalSupportV1
public import QuantitativeEulerEndpointCommonReconstructionV1

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace QuantitativeMaass.RawCommonReconstruction
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open QuantitativeHolomorphic QuantitativeHolomorphic.Schedule AsymptoticFiniteBranch
open ContinuousLinearMap QuantitativeMaass.EulerHilbert.FullTerminal

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ) (P : Parameters A)

/-- A single finite raw weight-zero reconstruction, chosen before the sector
or regular orbit root. No included extra weight is inserted. -/
def expression (hN : 0<N) (s : ℝ) (e : Sector N) : Expression :=
  let t := Real.exp (-8*s)
  let n := newtonDepth A P 2 t
  let j := reconstructionDepth A P 2 t n
  let J := foldCutoff A P 2 t j n
  normalizedReconstructionExpression (scaledFullExpression A hN P e j J) n

theorem zero_cut_error_le {Y : ℝ} (hY : 0≤Y) (j J n : ℕ) :
    normalizedCutError A P 0 j J n≤normalizedCutError A P Y j J n := by
  unfold normalizedCutError cutCountReconstructionError
  simp only [zero_div,zero_mul,add_zero]
  have hε := (AsymptoticReconstructedCount.parameters A P).epsilon_pos.le
  have hC := (zero_lt_one.trans_le (countReconstructionBound_one_le A P)).le
  have h := mul_nonneg (div_nonneg hY hε) hC
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact le_add_of_nonneg_right h

theorem scheduled_error (s : ℝ) :
    let t := Real.exp (-8*s)
    let n := newtonDepth A P 2 t
    let j := reconstructionDepth A P 2 t n
    let J := foldCutoff A P 2 t j n
    0<J ∧ normalizedCutError A P 0 j J n≤t/2 := by
  have h := QuantitativeEulerEndpointCommonReconstruction.scheduled_error A P s
  exact ⟨h.1,(zero_cut_error_le A P h.2.1.le _ _ _).trans h.2.2⟩

theorem regular_error (hN : 0<N) (s : ℝ) (e : Sector N) (x : UpperHalfPlane) :
    ‖regularSum (expression A P hN s e) x-
      normalizedRegularAmbient A hN P e x‖≤Real.exp (-8*s)/2 := by
  have h := scheduled_error A P s
  exact (normalizedFullExpression_regular_error A hN P e _ _ _ h.1 x).trans h.2

theorem physical_error (hN : 0<N) (s : ℝ) (e : Sector N) :
    ‖holomorphicSum (expression A P hN s e) 0-
      (physicalIsometry A hN P e).toContinuousLinearMap.comp
        (AsymptoticCylinderTerminal.ambientLift
          (AsymptoticReconstructedCount.parameters A P).ε).adjoint‖≤Real.exp (-8*s)/2 := by
  let t := Real.exp (-8*s)
  let n := newtonDepth A P 2 t
  let j := reconstructionDepth A P 2 t n
  let J := foldCutoff A P 2 t j n
  let S := AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
  let L := AsymptoticCylinderLift.lift.toContinuousLinearMap
  have h := scheduled_error A P s
  have he := norm_isometric_transport_difference_le S
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _) L
    AsymptoticCylinderLift.lift.adjoint_comp_self
    (finiteNormalizedReconstruction A hN P e n j J) (QuantitativeMaass.EulerHilbert.normalized A hN P e)
  have hb := he.trans (finiteNormalizedReconstruction_error A hN P e n j J h.1)
  change ‖holomorphicSum (normalizedReconstructionExpression (scaledFullExpression A hN P e j J) n) 0-
    (L.comp (QuantitativeMaass.EulerHilbert.normalized A hN P e)).comp S.adjoint‖≤_
  rw [normalizedFullExpression_eq_ambient,comp_assoc]
  apply hb.trans
  simpa only [normalizedCutError,cutCountReconstructionError,zero_div,zero_mul,add_zero] using h.2

theorem regular_norm (hN : 0<N) (s : ℝ) (e : Sector N) (x : UpperHalfPlane) :
    ‖regularSum (expression A P hN s e) x‖≤1 := by
  let t := Real.exp (-8*s)
  let n := newtonDepth A P 2 t
  let j := reconstructionDepth A P 2 t n
  let J := foldCutoff A P 2 t j n
  let S := (AsymptoticRegularReconstruction.TerminalSpace A
    (AsymptoticReconstructedCount.parameters A P) x).subtypeL
  have hS : S.adjoint.comp S=1 := AsymptoticOrbitRegion.adjoint_comp_subtype _ x
  have he := norm_isometric_transport_difference_le S hS
    (1 : AsymptoticRegularFoldedLow.Space→L[ℂ]AsymptoticRegularFoldedLow.Space)
    ((norm_map_iff_adjoint_comp_self
      (1 : AsymptoticRegularFoldedLow.Space→L[ℂ]AsymptoticRegularFoldedLow.Space)).1 (fun _ => rfl))
    (finiteNormalizedRegularReconstruction A hN P e x n j J) 0
  simp only [zero_comp,comp_zero,sub_zero,one_def,id_comp] at he
  change ‖regularSum (normalizedReconstructionExpression (scaledFullExpression A hN P e j J) n) x‖≤1
  rw [normalizedFullExpression_regular]
  exact he.trans (finiteNormalizedRegularReconstruction_norm A hN P e x n j J)

theorem physical_norm (hN : 0<N) (s : ℝ) (e : Sector N) :
    ‖holomorphicSum (expression A P hN s e) 0‖≤1 := by
  let t := Real.exp (-8*s)
  let n := newtonDepth A P 2 t
  let j := reconstructionDepth A P 2 t n
  let J := foldCutoff A P 2 t j n
  have he := norm_isometric_transport_difference_le
    (AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε)
    (AsymptoticCylinderTerminal.ambientLift_adjoint_self _)
    AsymptoticCylinderLift.lift.toContinuousLinearMap AsymptoticCylinderLift.lift.adjoint_comp_self
    (finiteNormalizedReconstruction A hN P e n j J) 0
  simp only [zero_comp,comp_zero,sub_zero] at he
  change ‖holomorphicSum (normalizedReconstructionExpression (scaledFullExpression A hN P e j J) n) 0‖≤1
  rw [normalizedFullExpression_eq_ambient]
  exact he.trans (finiteNormalizedReconstruction_norm A hN P e n j J)

theorem regular_right_terminal (hN : 0<N) (s : ℝ) (e : Sector N) (x : UpperHalfPlane) :
    (regularSum (expression A P hN s e) x).comp
      (AsymptoticOrbitDiagonal.corner
        (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) x)=
      regularSum (expression A P hN s e) x := by
  let t := Real.exp (-8*s)
  let n := newtonDepth A P 2 t
  let j := reconstructionDepth A P 2 t n
  let J := foldCutoff A P 2 t j n
  let S := (AsymptoticRegularReconstruction.TerminalSpace A
    (AsymptoticReconstructedCount.parameters A P) x).subtypeL
  have hS : S.adjoint.comp S=1 := AsymptoticOrbitRegion.adjoint_comp_subtype _ x
  have hc : AsymptoticOrbitDiagonal.corner
      (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε) x=
      S.comp S.adjoint := (AsymptoticOrbitRegion.subtype_comp_adjoint _ x).symm
  dsimp only [expression]
  rw [normalizedFullExpression_regular]
  exact (congrArg (fun T =>
    ((finiteNormalizedRegularReconstruction A hN P e x n j J).comp S.adjoint).comp T) hc).trans
      (QuantitativeEulerEndpointTerminalAlgebra.extension_right S
        (finiteNormalizedRegularReconstruction A hN P e x n j J) hS)

#print axioms scheduled_error
#print axioms regular_error
#print axioms physical_error
#print axioms regular_norm
#print axioms physical_norm
#print axioms regular_right_terminal
end QuantitativeMaass.RawCommonReconstruction
