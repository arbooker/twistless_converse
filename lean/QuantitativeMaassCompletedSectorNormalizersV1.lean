module

public import QuantitativeMaassLocalAtkinNewSpaceV1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open QuantitativeNinaMaass QuantitativeNewGap
namespace QuantitativeMaass

/-- Fricke exchanges the two defining trace equations at each prime. -/
theorem completedFricke_newSpace (N : ℕ) [NeZero N] (hN : 0<N)
    (x : AutomorphicSpace N) (hx : x∈newSpace N hN) :
    frickeIsometry N hN x∈newSpace N hN := by
  simp only [newSpace,Submodule.mem_iInf] at hx ⊢
  intro p
  change levelTrace (Nat.div_dvd_of_dvd p.property.2) (frickeIsometry N hN x)=0 ∧
    levelTrace (Nat.div_dvd_of_dvd p.property.2) (frickeIsometry N hN (frickeIsometry N hN x))=0
  rw [frickeIsometry_involutive]
  exact ⟨(hx p).2,(hx p).1⟩

def completedSectorNormalizer (N : ℕ) (hN : 0<N) :
    Option (SimplePrime N) → AutomorphicSpace N →L[ℂ] AutomorphicSpace N
  | none => (frickeIsometry N hN).toContinuousLinearMap
  | some p => (quotientNormalizerPullback N (completedLocalAtkinNormalizer N hN p)).toContinuousLinearMap

theorem completedSectorNormalizer_selfAdjoint (N : ℕ) (hN : 0<N) (i : Option (SimplePrime N)) :
    IsSelfAdjoint (completedSectorNormalizer N hN i) := by
  cases i with
  | none => exact frickeIsometry_selfAdjoint N hN
  | some p => exact completedLocalAtkin_selfAdjoint N hN p

theorem completedSectorNormalizer_involutive (N : ℕ) (hN : 0<N) (i : Option (SimplePrime N)) :
    Function.Involutive (completedSectorNormalizer N hN i) := by
  cases i with
  | none => exact frickeIsometry_involutive N hN
  | some p => exact completedLocalAtkin_involutive N hN p

theorem completedSectorNormalizers_commute (N : ℕ) (hN : 0<N) (i j : Option (SimplePrime N)) :
    Commute (completedSectorNormalizer N hN i) (completedSectorNormalizer N hN j) := by
  cases i with
  | none =>
    cases j with
    | none => exact Commute.refl _
    | some p => exact (completedLocalAtkin_fricke_commute N hN p).symm
  | some p =>
    cases j with
    | none => exact completedLocalAtkin_fricke_commute N hN p
    | some q => exact completedLocalAtkin_pair_commute N hN p q

theorem completedSectorNormalizer_cuspidalNew (N : ℕ) [NeZero N] (hN : 0<N)
    (i : Option (SimplePrime N)) (x : AutomorphicSpace N) (hx : x∈completedCuspidalNewSpace N hN) :
    completedSectorNormalizer N hN i x∈completedCuspidalNewSpace N hN := by
  cases i with
  | none => exact ⟨fricke_mem_cuspidal N hN x hx.1,completedFricke_newSpace N hN x hx.2⟩
  | some p => exact completedLocalAtkin_cuspidalNewSpace N hN p x hx

theorem completedSectorNormalizer_new_commute (N : ℕ) [NeZero N] (hN : 0<N)
    (i : Option (SimplePrime N)) :
    Commute (completedCuspidalNewSpace N hN).starProjection (completedSectorNormalizer N hN i) :=
  invariantSpace_projection_commute _ _ (completedSectorNormalizer_selfAdjoint N hN i)
    (completedSectorNormalizer_cuspidalNew N hN i)

#print axioms completedFricke_newSpace
#print axioms completedSectorNormalizer_selfAdjoint
#print axioms completedSectorNormalizer_involutive
#print axioms completedSectorNormalizers_commute
#print axioms completedSectorNormalizer_cuspidalNew
#print axioms completedSectorNormalizer_new_commute
end QuantitativeMaass
