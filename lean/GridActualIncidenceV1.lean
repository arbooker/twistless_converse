module

public import GridLabelDetectionV1

@[expose] public section

namespace GridActualIncidence

open GridCarrier GridRestrictedRows CompleteRowCosets GridLabelDetection

theorem gridIndex_mod_iff {G v J D : ℕ} (hG : 0<G) (hv : 0<v) (hD : D∣G*v)
    (x : Fin G × Offsets J) (u : ℤ) :
    Int.ModEq D (gridIndex hG hv J x).val u ↔ Int.ModEq D ((x.1.val:ℤ)*v+x.2.val) u := by
  have hh := (residue_mod (Nat.mul_pos hG hv) ((x.1.val:ℤ)*v+x.2.val)).of_dvd
    (show (D:ℤ)∣(G*v:ℕ) by exact_mod_cast hD)
  exact ⟨fun h => hh.symm.trans h,fun h => hh.trans h⟩

theorem unit_label_iff {m r z a c : ℕ} (hc : Nat.Coprime m r)
    (ha : Nat.ModEq m (r*a) c) :
    Nat.ModEq m (z*r) c ↔ Nat.ModEq m z a := by
  constructor
  · intro h
    apply Nat.ModEq.cancel_right_of_coprime hc
    simpa only [Nat.mul_comm a r] using h.trans ha.symm
  · intro h
    exact (h.mul_right r).trans (by simpa only [Nat.mul_comm a r] using ha)

theorem selected_incidence_iff {G v J m w r c : ℕ} (hG : 0<G) (hv : 0<v)
    (hw : 0<w) (hvw : v=r*w) (hD : m*w∣G*v) (hJ : 2*J<w)
    (a : Fin G) (t : Offsets J) (x : Fin G × Offsets J)
    (hc : Nat.Coprime m r) (ha : Nat.ModEq m (r*a.val) c) :
    Int.ModEq ((m*w:ℕ):ℤ) (gridIndex hG hv J x).val ((c:ℤ)*w+t.val) ↔
      x.2=t ∧ Nat.ModEq m x.1.val a.val := by
  rw [gridIndex_mod_iff hG hv hD]
  have hh := row_incidence_iff
    (m:=(m:ℤ)) (w:=(w:ℤ)) (r:=(r:ℤ)) (z:=(x.1.val:ℤ)) (c:=(c:ℤ))
    (t:=t.val) (t':=x.2.val) (J:=(J:ℤ))
    (by exact_mod_cast hw) (by exact_mod_cast hJ)
    (abs_le.mpr (Finset.mem_Icc.mp t.property)) (abs_le.mpr (Finset.mem_Icc.mp x.2.property))
  rw [hvw]
  simp only [Nat.cast_mul]
  rw [hh]
  have he : x.2.val=t.val ↔ x.2=t := ⟨Subtype.ext,congrArg Subtype.val⟩
  rw [he,←Nat.cast_mul,Int.natCast_modEq_iff,unit_label_iff hc ha]

theorem selected_coset_sum {K : Type*} [AddCommMonoid K] {G v J m w r c : ℕ}
    (hG : 0<G) (hv : 0<v) (hw : 0<w) (hvw : v=r*w)
    (hD : m*w∣G*v) (hJv : 2*J<v) (hJw : 2*J<w)
    (a : Fin G) (t : Offsets J) (hc : Nat.Coprime m r) (ha : Nat.ModEq m (r*a.val) c)
    (f : ℤ → K) (hf : ∀j:Fin (G*v),j∉Set.range (gridIndex hG hv J) → f j.val=0) :
    cosetSum (G*v) (m*w) ((c:ℤ)*w+t.val) f=
      restrictedSum (fun z:Fin G => Nat.ModEq m z.val a.val)
        (fun z => f (gridIndex hG hv J (z,t)).val) := by
  classical
  rw [grid_coset_sum hG hv hJv _ f hf]
  unfold restrictedSum
  simp_rw [selected_incidence_iff hG hv hw hvw hD hJw a t _ hc ha]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : Nat.ModEq m z.val a.val
  · simp [hz]
  · simp [hz]

#print axioms selected_coset_sum

end GridActualIncidence
