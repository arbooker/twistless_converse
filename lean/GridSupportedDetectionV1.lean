module

public import GridActualIncidenceV1

@[expose] public section

namespace GridSupportedDetection

open SpanningTraceAlgebra SpanningCyclicCoordinates CompleteRowCosets
  GridCarrier GridRestrictedRows GridLabelDetection GridActualIncidence

theorem cyclic_residue {K : Type*} {Q : ℕ} (hQ : 0<Q) (f : ℤ → K)
    (hf : Cyclic Q f) (j : ℤ) : f (residue hQ j).val=f j := by
  have hQ0 : (Q:ℤ)≠0 := by exact_mod_cast Nat.ne_of_gt hQ
  simp only [residue,Int.toNat_of_nonneg (Int.emod_nonneg j hQ0)]
  exact cyclic_emod hf j

theorem grid_evaluation {K : Type*} {G v J : ℕ} (hG : 0<G) (hv : 0<v)
    (f : ℤ → K) (hf : Cyclic (G*v) f) (x : Fin G × Offsets J) :
    f (gridIndex hG hv J x).val=f ((x.1.val:ℤ)*v+x.2.val) :=
  cyclic_residue (Nat.mul_pos hG hv) f hf _

theorem restricted_labelHit {K : Type*} [AddCommMonoid K] {G : ℕ}
    (a : Fin G) (f : Fin G → K) :
    restrictedSum (fun z:Fin G => Nat.ModEq (labelModulus a) z.val a.val) f=
      ∑z∈labelHit a,f z := by
  classical
  simp only [restrictedSum,labelHit,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> rfl

#print axioms grid_evaluation
#print axioms restricted_labelHit

end GridSupportedDetection
