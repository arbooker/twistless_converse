module

public import AsymptoticFiniteBranchNormalV1
public import AsymptoticFiniteCylinderTransportV1
public import AsymptoticPolynomialTransportV1
public import AsymptoticCylinderFinitePolynomialV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticFiniteBranch

open UpperHalfPlane Set ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns AsymptoticCylinderLift
open AsymptoticHyperbolicSlash (Space)
open AsymptoticCompactObservationCount (Row)

variable {ι : Type*} [Fintype ι]

noncomputable def holomorphicRows {N : ℕ} (hN : 0<N) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε) (t m : ℕ) (e : Sector N) :
    Space →L[ℂ] PiLp 2 (fun _ : ι => Space) :=
  AsymptoticObservationStack.stack (fun i => holomorphicSum (rowExpression hN (r i) e (hs i) hε t) m)

omit [Fintype ι] in
theorem holomorphicRows_comp_lift {N : ℕ} (hN : 0<N) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε) (t m : ℕ) (e : Sector N) :
    (holomorphicRows hN r s hs hε t m e).comp lift.toContinuousLinearMap=
      AsymptoticCompactObservationCount.observations hN r s hs hε t m e := by
  ext1 f
  apply PiLp.ext
  intro i
  exact congrArg (fun T : AsymptoticCylinder.Space →L[ℂ] Space => T f)
    (cylinder_rowExpression hN (r i) e (hs i) hε t m)

theorem holomorphicSum_rowGram {N : ℕ} (hN : 0<N) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε) (t m : ℕ) (e : Sector N) :
    holomorphicSum (gramExpression (fun i => rowExpression hN (r i) e (hs i) hε t)) m=
      (holomorphicRows hN r s hs hε t m e).adjoint.comp (holomorphicRows hN r s hs hε t m e) :=
  (holomorphicSum_gramExpression _ m).trans (AsymptoticObservationStack.stack_gram _).symm

theorem holomorphicSum_completedNormalExpression (R G : Expression) (P : Branch) (m : ℕ) :
    holomorphicSum (completedNormalExpression R G P) m=
      (holomorphicSum R m).adjoint.comp ((1+holomorphicSum G m).comp (holomorphicSum R m))+
        (1+(-1:ℂ) • holomorphic P m) := by
  simp only [completedNormalExpression,holomorphicSum_append,holomorphicSum_compose,
    holomorphicSum_adjoint,holomorphicSum_scale,holomorphicSum_singleton,holomorphic_identity]

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

theorem holomorphicSum_finiteNormalExpression (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) (m : ℕ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    holomorphicSum (finiteNormalExpression A hN P r s hs e Y d I) m=
      AsymptoticObservation.completedNormal (AsymptoticCertificateOperators.highProjection A P')
        (holomorphicSum (cutFullExpression A hN P' (multiplier e) Y d I) m)
        (holomorphicRows hN r s hs P'.epsilon_pos (P'.s+4) m e) := by
  dsimp only
  rw [finiteNormalExpression,holomorphicSum_completedNormalExpression,holomorphicSum_rowGram,holomorphic_corner,
    AsymptoticObservation.completedNormal,AsymptoticObservation.normal_formula]
  have hj : (-1 : ℂ) • AsymptoticRegionL2.projection MeasureTheory.volume
      (AsymptoticCertificateOperators.highStrip (AsymptoticReconstructedCount.parameters A P).ε)
      (AsymptoticCertificateOperators.highStrip_measurable _) =
      -AsymptoticCertificateOperators.highProjection A (AsymptoticReconstructedCount.parameters A P) := by
    ext1 f
    exact neg_one_smul ℂ (AsymptoticCertificateOperators.highProjection A
      (AsymptoticReconstructedCount.parameters A P) f)
  rw [hj]
  abel

/-- The common ambient completed normal operator intertwines with the
actual cylinder normal operator on terminal data. -/
theorem finiteNormal_intertwines (hN : 0<N) (P : Parameters A)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (h : ℕ) (e : Sector N) (Y : ℝ) (d : ℕ) (I : Finset ℤ) :
    let S := AsymptoticCylinderTerminal.ambientLift (AsymptoticReconstructedCount.parameters A P).ε
    (holomorphicSum (finiteNormalExpression A hN P r s hs e Y d I) (h+1)).comp S=
      S.comp (AsymptoticCylinderObservation.finiteCutNormal A hN P r s hs h e Y d I) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let S := AsymptoticCylinderTerminal.ambientLift P'.ε
  let R := AsymptoticReconstructedCount.finiteCutReconstruction A hN P h e Y d I
  let O := holomorphicRows hN r s hs P'.epsilon_pos (P'.s+4) (h+1) e
  have hS : S.adjoint.comp S=1 := AsymptoticCylinderTerminal.ambientLift_adjoint_self P'.ε
  have hP : S.comp S.adjoint=AsymptoticCertificateOperators.highProjection A P' :=
    AsymptoticCylinderTerminal.ambientLift_self_adjoint P'.ε
  have hO : O.comp lift.toContinuousLinearMap=
      AsymptoticCompactObservationCount.observations hN r s hs P'.epsilon_pos (P'.s+4) (h+1) e :=
    holomorphicRows_comp_lift hN r s hs P'.epsilon_pos (P'.s+4) (h+1) e
  rw [holomorphicSum_finiteNormalExpression,holomorphicSum_cutFull_eq_cylinder]
  ext1 g
  have ht := AsymptoticObservation.completedNormal_on_source S hS (lift.toContinuousLinearMap.comp R) O g
  rw [hP,AsymptoticObservation.normal_isometric_output _ lift.adjoint_comp_self,hO] at ht
  exact ht

#print axioms holomorphicRows_comp_lift
#print axioms holomorphicSum_rowGram
#print axioms holomorphicSum_completedNormalExpression
#print axioms holomorphicSum_finiteNormalExpression
#print axioms finiteNormal_intertwines

end AsymptoticFiniteBranch
