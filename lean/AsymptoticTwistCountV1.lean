module

public import AsymptoticCylinderTwistV1
public import AsymptoticObservationStackV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticTwistCount

open UpperHalfPlane Set FinitenessCertificate FinitenessGlobalHeight
open AsymptoticSectorSigns AsymptoticCylinder AsymptoticTwistObservation
open AsymptoticDiagonalTrace AsymptoticObservation FinitenessOriginalInput

variable {ι : Type*} [Fintype ι]

noncomputable def observations (N : ℕ) (hN : 0<N) (q : ι → ℕ) (hq : ∀ i,0<q i)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε)
    (t m : ℕ) (e : Sector N) : Space →L[ℂ] PiLp 2 (fun _ : ι => AsymptoticHyperbolicSlash.Space) :=
  AsymptoticObservationStack.stack (fun i =>
    AsymptoticCylinderTwist.operator N (q i) hN (hq i) (hs i) hε t m (multiplier e (q i)))

theorem observations_norm_le (N : ℕ) (hN : 0<N) (q : ι → ℕ) (hq : ∀ i,0<q i)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε)
    (t m : ℕ) (e : Sector N) :
    ‖observations N hN q hq s hs hε t m e‖≤
      ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => AsymptoticHyperbolicSlash.Space)).symm.toContinuousLinearMap‖*
        ∑ i,(translationBound (q i) (hs i) hε t+reflectionBound N (q i) hN (hq i) (hs i) hε t) := by
  apply AsymptoticObservationStack.stack_norm_le
  · intro i
    apply add_nonneg <;> exact Finset.sum_nonneg (fun a _ => branchBound_nonneg _ _ _ _)
  · intro i
    exact AsymptoticCylinderTwist.operator_norm_le N (q i) hN (hq i) (hs i) hε t m e

omit [Fintype ι] in
theorem sector_annihilated {N Q : ℕ} {hQ : 0<Q} {A : Certificate N Q hQ}
    (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (q : ι → ℕ) (hq : ∀ i,0<q i) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (w : holomorphicSpace (2*h) (P.s+4) (by positivity : 0<4*Real.pi) P.epsilon_pos)
    (hw : w∈eulerCylinderSector P h e) :
    observations N hN q hq s hs P.epsilon_pos (P.s+4) (h+1) e (w:Space)=0 :=
  (AsymptoticObservationStack.stack_eq_zero_iff _ _).mpr (fun i =>
    AsymptoticCylinderTwist.sector_annihilated hN P h e (q i) (hq i) (hs i) w hw)

/-- Count-to-trace for any finite family of literal compact twist laws.
Both reconstruction and annihilation are proved for the actual sectors. -/
theorem count_le_traces {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)
    (hN : 0<N) (P : Parameters A) (h : ℕ)
    (q : ι → ℕ) (hq : ∀ i,0<q i) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ((S N (2*(h+1))).ncard:ℝ)≤∑ e : Sector N,
      trace (fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos)
        (holomorphicOperator ((inclusion P'.epsilon_pos).comp
          (AsymptoticReconstructedCount.reconstruction A hN P h e))
          (observations N hN q hq s hs P'.epsilon_pos (P'.s+4) (h+1) e)
          (AsymptoticReconstructedCount.terminal_lower_bound A hN P h e)
          (holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos)) := by
  apply AsymptoticReconstructedCount.count_le_traces
  intro e w hw
  exact sector_annihilated hN _ h e q hq s hs w hw

#print axioms observations_norm_le
#print axioms sector_annihilated
#print axioms count_le_traces

end AsymptoticTwistCount
