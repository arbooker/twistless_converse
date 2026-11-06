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

/-- The literal coset rows and two special rows detect every cyclic
vector supported on the grid. Window admissibility is a separate input
to selecting these rows, not an axiom in the incidence argument. -/
theorem grid_detect_of_rows {K : Type*} [AddCommMonoid K] {G v J : ℕ}
    (hG : 0<G) (hv : 0<v) (hJv : 2*J<v)
    (r w c : Fin G → ℕ)
    (hw : ∀a,2<labelOrder a → 0<w a)
    (hvw : ∀a,2<labelOrder a → v=r a*w a)
    (hD : ∀a,2<labelOrder a → labelModulus a*w a∣G*v)
    (hJw : ∀a,2<labelOrder a → 2*J<w a)
    (hc : ∀a,2<labelOrder a → Nat.Coprime (labelModulus a) (r a))
    (ha : ∀a,2<labelOrder a → Nat.ModEq (labelModulus a) (r a*a.val) (c a))
    (f : ℤ → K) (hcyc : Cyclic (G*v) f)
    (hsupport : ∀j:Fin (G*v),j∉Set.range (gridIndex hG hv J) → f j.val=0)
    (hrows : ∀a,2<labelOrder a → ∀t:Offsets J,
      cosetSum (G*v) (labelModulus a*w a) ((c a:ℤ)*w a+t.val) f=0)
    (hzero : ∀t:Offsets J,f t.val=0)
    (hpair : ∀a:Fin G,2*a.val=G → ∀t:Offsets J,f t.val+f ((a.val:ℤ)*v+t.val)=0) : f=0 := by
  have hgrid : ∀x:Fin G × Offsets J,f (gridIndex hG hv J x).val=0 := by
    intro x
    let g := fun z:Fin G => f (gridIndex hG hv J (z,x.2)).val
    have hg : g=0 := label_detect hG g (by
        intro a hahi
        have he := selected_coset_sum hG hv (hw a hahi) (hvw a hahi) (hD a hahi)
          hJv (hJw a hahi) a x.2 (hc a hahi) (ha a hahi) f hsupport
        rw [restricted_labelHit] at he
        exact he.symm.trans (hrows a hahi x.2))
      (by simpa only [g,grid_evaluation hG hv f hcyc,Nat.cast_zero,zero_mul,zero_add]
            using hzero x.2)
      (by intro a haa
          simpa only [g,grid_evaluation hG hv f hcyc,Nat.cast_zero,zero_mul,zero_add]
            using hpair a haa x.2)
    exact congrFun hg x.1
  have hfin : ∀j:Fin (G*v),f j.val=0 := by
    intro j
    by_cases hj : j∈Set.range (gridIndex hG hv J)
    · obtain ⟨x,rfl⟩ := hj; exact hgrid x
    · exact hsupport j hj
  funext j
  change f j=0
  rw [←cyclic_residue (Nat.mul_pos hG hv) f hcyc j]
  exact hfin _

#print axioms grid_detect_of_rows

end GridSupportedDetection
