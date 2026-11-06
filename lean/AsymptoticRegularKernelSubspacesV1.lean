module

public import AsymptoticRegularKernelApproximationV1

set_option autoImplicit false
set_option maxHeartbeats 800000
@[expose] public section

namespace AsymptoticRegularObservation

open UpperHalfPlane MeasureTheory Filter ContinuousLinearMap
open FinitenessCertificate FinitenessGlobalHeight AsymptoticSectorSigns
open AsymptoticRegularReconstruction
open AsymptoticRegularCompactBranch (Space)
open AsymptoticCompactObservationCount (Row)

variable {N Q : ℕ} {hQ : 0<Q} (A : Certificate N Q hQ)

noncomputable def finiteKernelSpace (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (n : ℕ) (z : ℍ) : Submodule ℂ Space :=
  let P' := AsymptoticReconstructedCount.parameters A P
  AsymptoticObservation.survivingSpace (includedExtension A hN P' (multiplier e) z)
    (observations hN (fun i : Fin n => r i) (fun i => s i) (fun i => hs i)
      P'.epsilon_pos (P'.s+4) e z)

noncomputable def infiniteKernelSpace (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) : Submodule ℂ Space :=
  let P' := AsymptoticReconstructedCount.parameters A P
  (includedExtension A hN P' (multiplier e) z).range⊓
    ⨅ i,(AsymptoticRegularObservationRows.row hN (r i) e (hs i) P'.epsilon_pos (P'.s+4) z).ker

theorem finiteKernelSpace_closed (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (n : ℕ) (z : ℍ) :
    IsClosed (finiteKernelSpace A hN P r s hs e n z : Set Space) :=
  AsymptoticObservation.survivingSpace_closed _ _
    (includedExtension_norm_ge A hN (AsymptoticReconstructedCount.parameters A P) (multiplier e) z
      (lt_trans (parameters_contraction A hN P (multiplier e) (fun q _ => multiplier_norm e q) z) (by norm_num)))

noncomputable instance finiteKernelSpace_complete (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (n : ℕ) (z : ℍ) :
    CompleteSpace (finiteKernelSpace A hN P r s hs e n z) :=
  (finiteKernelSpace_closed A hN P r s hs e n z).completeSpace_coe

theorem finiteKernelSpace_mem (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (n : ℕ) (z : ℍ) (v : Space) :
    let P' := AsymptoticReconstructedCount.parameters A P
    v∈finiteKernelSpace A hN P r s hs e n z ↔
      v∈(includedExtension A hN P' (multiplier e) z).range ∧
        ∀ i : Fin n,AsymptoticRegularObservationRows.row hN (r i) e (hs i)
          P'.epsilon_pos (P'.s+4) z v=0 := by
  change (_ ∧ observations _ _ _ _ _ _ _ _ v=0) ↔ _
  exact and_congr_right (fun _ => AsymptoticObservationStack.stack_eq_zero_iff _ v)

theorem finiteKernelSpace_antitone (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    Antitone (fun n => finiteKernelSpace A hN P r s hs e n z) := by
  intro n m hnm v hv
  have hv := (finiteKernelSpace_mem A hN P r s hs e m z v).mp hv
  apply (finiteKernelSpace_mem A hN P r s hs e n z v).mpr
  refine ⟨hv.1,?_⟩
  intro i
  exact hv.2 ⟨i.val,lt_of_lt_of_le i.isLt hnm⟩

theorem infiniteKernelSpace_eq_iInf (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    infiniteKernelSpace A hN P r s hs e z=⨅ n,finiteKernelSpace A hN P r s hs e n z := by
  ext v
  simp only [Submodule.mem_iInf,finiteKernelSpace_mem,infiniteKernelSpace,Submodule.mem_inf,
    LinearMap.mem_ker]
  constructor
  · intro hv n
    exact ⟨hv.1,fun i => hv.2 i.val⟩
  · intro hv
    exact ⟨(hv 0).1,fun i => (hv (i+1)).2 ⟨i,Nat.lt_succ_self i⟩⟩

theorem infiniteKernelSpace_closed (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    IsClosed (infiniteKernelSpace A hN P r s hs e z : Set Space) := by
  rw [infiniteKernelSpace_eq_iInf,Submodule.coe_iInf]
  exact isClosed_iInter (fun n => finiteKernelSpace_closed A hN P r s hs e n z)

noncomputable instance infiniteKernelSpace_complete (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (z : ℍ) :
    CompleteSpace (infiniteKernelSpace A hN P r s hs e z) :=
  (infiniteKernelSpace_closed A hN P r s hs e z).completeSpace_coe

theorem finiteKernelProjection_eq (hN : 0<N) (P : Parameters A) (r : ℕ → Row N)
    (s : ℕ → Set ℍ) (hs : ∀ i,IsCompact (s i)) (e : Sector N) (n : ℕ) (z : ℍ) :
    (finiteKernelSpace A hN P r s hs e n z).starProjection=
      jointKernelProjection A hN P (fun i : Fin n => r i) (fun i => s i) (fun i => hs i) e z := rfl

#print axioms finiteKernelSpace_closed
#print axioms finiteKernelSpace_mem
#print axioms finiteKernelSpace_antitone
#print axioms infiniteKernelSpace_eq_iInf
#print axioms infiniteKernelSpace_closed
#print axioms finiteKernelProjection_eq

end AsymptoticRegularObservation
