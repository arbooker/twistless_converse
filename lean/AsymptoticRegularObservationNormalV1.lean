module

public import AsymptoticRegularObservationGramV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticObservation

open ContinuousLinearMap InnerProductSpace

variable {H J : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

/-- Complete the terminal normal operator by the identity on the
orthogonal complement. This puts the inverse problem on one fixed
Hilbert space instead of root-dependent terminal subspaces. -/
noncomputable def completedNormal (P R : H →L[ℂ] H) (L : H →L[ℂ] J) : H →L[ℂ] H :=
  normal R L+1-P

theorem projection_inner (P : H →L[ℂ] H) (hsa : P.adjoint=P) (hp : P.comp P=P) (x : H) :
    (⟪P x,x⟫_ℂ).re=‖P x‖^2 := by
  have hpx : P (P x)=P x := congrArg (fun T : H →L[ℂ] H => T x) hp
  have he : ⟪P x,P x⟫_ℂ=⟪P x,x⟫_ℂ := by
    calc
      _ = ⟪P.adjoint (P x),x⟫_ℂ := (adjoint_inner_left P x (P x)).symm
      _ = _ := by rw [hsa,hpx]
  exact (congrArg Complex.re he).symm.trans (norm_sq_eq_re_inner (𝕜:=ℂ) (P x)).symm

theorem completedNormal_coercive (P R : H →L[ℂ] H) (L : H →L[ℂ] J)
    (hsa : P.adjoint=P) (hp : P.comp P=P) (hn : ‖P‖≤1)
    (hr : ∀ x,P (R x)=P x) (x : H) :
    ‖x‖^2≤(⟪completedNormal P R L x,x⟫_ℂ).re := by
  have hlow : ‖P x‖≤‖R x‖ := by
    calc
      _ = ‖P (R x)‖ := congrArg norm (hr x).symm
      _ ≤ _ := by simpa only [one_mul] using P.le_of_opNorm_le hn (R x)
  have hself : (⟪x,x⟫_ℂ).re=‖x‖^2 := (norm_sq_eq_re_inner (𝕜:=ℂ) x).symm
  have he : (⟪completedNormal P R L x,x⟫_ℂ).re=
      ‖R x‖^2+‖L (R x)‖^2+‖x‖^2-‖P x‖^2 := by
    simp only [completedNormal,sub_apply,add_apply,ContinuousLinearMap.one_def,id_apply,inner_sub_left,inner_add_left,
      Complex.sub_re,Complex.add_re,normal_re_inner,projection_inner P hsa hp,
      hself]
  rw [he]
  nlinarith [norm_nonneg (P x),norm_nonneg (R x),sq_nonneg ‖L (R x)‖]

#print axioms completedNormal_coercive

end AsymptoticObservation

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Set ContinuousLinearMap AsymptoticRegularTrace InnerProductSpace
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)
open AsymptoticRegularReconstruction AsymptoticRegularCertificate

variable {ι : Type*} [Fintype ι]
variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def wholeNormal (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) : Space →L[ℂ] Space :=
  let P' := AsymptoticReconstructedCount.parameters A P
  AsymptoticObservation.completedNormal (highProjection A P' z)
    (includedFull A hN P' (multiplier e) z)
    (observations hN r s hs P'.epsilon_pos (P'.s+4) e z)

theorem wholeNormal_coercive (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) (x : Space) :
    ‖x‖^2≤(⟪wholeNormal A hN P r s hs e z x,x⟫_ℂ).re := by
  apply AsymptoticObservation.completedNormal_coercive
  · exact AsymptoticOrbitDiagonal.corner_adjoint _ _
  · exact AsymptoticOrbitDiagonal.corner_idempotent _ _
  · exact highProjection_norm_le A _ z
  · exact includedFull_terminal A hN _ (multiplier e) z
      (lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num))

/-- The normal family has a description using only adjoints, finite sums
and products of the proved measurable covariant families. -/
theorem wholeNormal_formula (hN : 0<N) (P : Parameters A) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    let P' := AsymptoticReconstructedCount.parameters A P
    let R := includedFull A hN P' (multiplier e) z
    wholeNormal A hN P r s hs e z=
      R.adjoint.comp ((1+gram hN r s hs P'.epsilon_pos (P'.s+4) e z).comp R)+
        (1+(-1:ℂ) • highProjection A P' z) := by
  let P' := AsymptoticReconstructedCount.parameters A P
  let R := includedFull A hN P' (multiplier e) z
  let L := observations hN r s hs P'.epsilon_pos (P'.s+4) e z
  change AsymptoticObservation.normal R L+1-highProjection A P' z=
    R.adjoint.comp ((1+L.adjoint.comp L).comp R)+(1+(-1:ℂ) • highProjection A P' z)
  have he := congrArg (fun T : Space →L[ℂ] Space => T+1-highProjection A P' z)
    (AsymptoticObservation.normal_formula R L)
  have hneg : (-1:ℂ) • highProjection A P' z= -highProjection A P' z :=
    neg_one_smul ℂ (highProjection A P' z)
  apply he.trans
  calc
    _ = R.adjoint.comp ((1+L.adjoint.comp L).comp R)+(1+ -highProjection A P' z) := by abel
    _ = _ := congrArg (fun T : Space →L[ℂ] Space =>
      R.adjoint.comp ((1+L.adjoint.comp L).comp R)+(1+T)) hneg.symm

#print axioms wholeNormal_coercive
#print axioms wholeNormal_formula

end AsymptoticRegularObservation
