module

public import AsymptoticCylinderRamifiedV1
public import AsymptoticTwistCountV1

set_option autoImplicit false
@[expose] public section

namespace AsymptoticCompactObservationCount

open UpperHalfPlane Set FinitenessCertificate FinitenessGlobalHeight
open AsymptoticSectorSigns AsymptoticCylinder
open AsymptoticDiagonalTrace AsymptoticObservation FinitenessOriginalInput

/-- Only equations known for the Euler sectors are available as rows. -/
inductive Row (N : ℕ) where
  | twist (q : ℕ) (hq : 0<q)
  | ramified (p : ℕ) (hp : p.Prime) (hpN : p∣N)

noncomputable def rowOperator {N : ℕ} (hN : 0<N) (r : Row N) (e : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t m : ℕ) :
    Space →L[ℂ] AsymptoticHyperbolicSlash.Space :=
  match r with
  | .twist q hq => AsymptoticCylinderTwist.operator N q hN hq hs hε t m (multiplier e q)
  | .ramified p hp _ => AsymptoticCylinderRamified.operator e p hp hs hε t m

noncomputable def rowBound {N : ℕ} (hN : 0<N) (r : Row N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) : ℝ :=
  match r with
  | .twist q hq => AsymptoticTwistObservation.translationBound q hs hε t+
      AsymptoticTwistObservation.reflectionBound N q hN hq hs hε t
  | .ramified p hp _ => AsymptoticRamifiedObservation.bound p hp.pos hs hε t+
      AsymptoticTwistObservation.branchBound 1 hs hε t

theorem rowBound_nonneg {N : ℕ} (hN : 0<N) (r : Row N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t : ℕ) :
    0≤rowBound hN r hs hε t := by
  cases r with
  | twist q hq =>
    apply add_nonneg <;> exact Finset.sum_nonneg
      (fun a _ => AsymptoticTwistObservation.branchBound_nonneg _ _ _ _)
  | ramified p hp hpN =>
    exact add_nonneg (AsymptoticRamifiedObservation.bound_nonneg p hp.pos hs hε t)
      (AsymptoticTwistObservation.branchBound_nonneg 1 hs hε t)

theorem rowOperator_norm_le {N : ℕ} (hN : 0<N) (r : Row N) (e : Sector N)
    {s : Set ℍ} (hs : IsCompact s) {ε : ℝ} (hε : 0<ε) (t m : ℕ) :
    ‖rowOperator hN r e hs hε t m‖≤rowBound hN r hs hε t := by
  cases r with
  | twist q hq => exact AsymptoticCylinderTwist.operator_norm_le N q hN hq hs hε t m e
  | ramified p hp hpN => exact AsymptoticCylinderRamified.operator_norm_le e p hp hs hε t m

theorem row_sector_annihilated {N Q : ℕ} {hQ : 0<Q} {A : Certificate N Q hQ}
    (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N) (r : Row N)
    {s : Set ℍ} (hs : IsCompact s)
    (w : holomorphicSpace (2*h) (P.s+4) (by positivity : 0<4*Real.pi) P.epsilon_pos)
    (hw : w∈eulerCylinderSector P h e) :
    rowOperator hN r e hs P.epsilon_pos (P.s+4) (h+1) (w:Space)=0 := by
  cases r with
  | twist q hq => exact AsymptoticCylinderTwist.sector_annihilated hN P h e q hq hs w hw
  | ramified p hp hpN => exact AsymptoticCylinderRamified.sector_annihilated P h e p hp hpN hs w hw

variable {ι : Type*} [Fintype ι]

noncomputable def observations {N : ℕ} (hN : 0<N) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε)
    (t m : ℕ) (e : Sector N) : Space →L[ℂ] PiLp 2 (fun _ : ι => AsymptoticHyperbolicSlash.Space) :=
  AsymptoticObservationStack.stack (fun i => rowOperator hN (r i) e (hs i) hε t m)

theorem observations_norm_le {N : ℕ} (hN : 0<N) (r : ι → Row N)
    (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) {ε : ℝ} (hε : 0<ε)
    (t m : ℕ) (e : Sector N) :
    ‖observations hN r s hs hε t m e‖≤
      ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => AsymptoticHyperbolicSlash.Space)).symm.toContinuousLinearMap‖*
        ∑ i,rowBound hN (r i) (hs i) hε t :=
  AsymptoticObservationStack.stack_norm_le _ _ (fun i => rowBound_nonneg hN (r i) (hs i) hε t)
    (fun i => rowOperator_norm_le hN (r i) e (hs i) hε t m)

omit [Fintype ι] in
theorem sector_annihilated {N Q : ℕ} {hQ : 0<Q} {A : Certificate N Q hQ}
    (hN : 0<N) (P : Parameters A) (h : ℕ) (e : Sector N)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i))
    (w : holomorphicSpace (2*h) (P.s+4) (by positivity : 0<4*Real.pi) P.epsilon_pos)
    (hw : w∈eulerCylinderSector P h e) :
    observations hN r s hs P.epsilon_pos (P.s+4) (h+1) e (w:Space)=0 :=
  (AsymptoticObservationStack.stack_eq_zero_iff _ _).mpr (fun i =>
    row_sector_annihilated hN P h e (r i) (hs i) w hw)

/-- The actual Euler count is bounded by sector traces for each finite
compact family of known twist and ramified equations. Neither
reconstruction nor observation annihilation is left as a hypothesis. -/
theorem count_le_traces {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)
    (hN : 0<N) (P : Parameters A) (h : ℕ)
    (r : ι → Row N) (s : ι → Set ℍ) (hs : ∀ i,IsCompact (s i)) :
    let P' := AsymptoticReconstructedCount.parameters A P
    ((S N (2*(h+1))).ncard:ℝ)≤∑ e : Sector N,
      trace (fourierBasis (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos)
        (holomorphicOperator ((inclusion P'.epsilon_pos).comp
          (AsymptoticReconstructedCount.reconstruction A hN P h e))
          (observations hN r s hs P'.epsilon_pos (P'.s+4) (h+1) e)
          (AsymptoticReconstructedCount.terminal_lower_bound A hN P h e)
          (holomorphicSpace (2*h) (P'.s+4) (by positivity : 0<4*Real.pi) P'.epsilon_pos)) := by
  apply AsymptoticReconstructedCount.count_le_traces
  intro e w hw
  exact sector_annihilated hN _ h e r s hs w hw

#print axioms rowOperator_norm_le
#print axioms row_sector_annihilated
#print axioms observations_norm_le
#print axioms sector_annihilated
#print axioms count_le_traces

end AsymptoticCompactObservationCount
